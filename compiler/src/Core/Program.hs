{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | Linking Core: many modules in, one reachable program out.
--
-- The JS backend does not read an IR. It reads an 'AST.Optimized.GlobalGraph':
-- a single flat table for the whole program, already reduced to what the roots
-- can reach. @docs/m1a-js-on-core.md@ §J1 is the inventory of what that means,
-- and its two hardest rows are that Core has no linker and no reachability.
-- This module is both.
--
-- Three things it produces that a backend needs and one module's Core cannot
-- have:
--
--   * __One table, reachable only__ ('_progBindings'). Dead code is dropped
--     here rather than by each backend, because "reachable" is a property of the
--     program and every backend agrees about it.
--   * __A specified order__ ('_progBindings' again). C14's, which "Core.Order"
--     implements and a module's own definitions are in as well: dependency
--     order, the least-named ready group first. That is reproducible from that
--     sentence, which is the property @docs/m1a-determinism.md@ §T2 wanted and
--     which a library's depth-first search does not have.
--   * __The field set__ ('_progFields'), which @--optimize@'s field shortening
--     needs and which is only knowable program-wide.
--
-- And one thing it produces that is a measurement rather than an output:
-- '_progMissing', the names reachable code refers to and no Core module
-- defines. Today that is every kernel function, every effect manager and every
-- port, which is @docs/m1a-js-on-core.md@ §J3 items 3 and 5 — the two pieces of
-- M1a that need a decision before they need code. Printing the list is how the
-- size of those two decisions stops being a guess.
module Core.Program
  ( Program (..),
    Missing (..),
    MissingKind (..),
    link,
    qualToChars,
    render,
  )
where

import Core.AST qualified as Core
import Core.Order qualified as Order
import Core.Refs (Refs (..), global, refsIn)
import Data.ByteString.Builder qualified as B
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set (Set)
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg

-- PROGRAM

data Program = Program
  { _progRoots :: [Core.QualName],
    -- | Reachable bindings, in link order.
    _progBindings :: [(Core.QualName, Core.Bind)],
    -- | The reachable subset of the modules' recursive groups, so a backend that
    -- has to emit a group together still can.
    _progRecursive :: [[Core.QualName]],
    -- | Datatypes with at least one reachable constructor.
    _progData :: [Core.DataDecl],
    -- | Every record field named by reachable code.
    _progFields :: Set Name,
    -- | The @effect module@ managers a runtime has to register, because an entry
    -- binding of each is reachable. Empty once P3 lands.
    _progManagers :: [(ModuleName.Canonical, Core.Manager)],
    -- | What reachable code refers to and Core does not define.
    _progMissing :: [Missing]
  }

-- | A name Core cannot supply, and the least-named binding that wanted it.
data Missing = Missing
  { _missingName :: Core.QualName,
    _missingKind :: MissingKind,
    _missingUsedBy :: Core.QualName
  }
  deriving (Eq, Show)

data MissingKind
  = -- | A @gren\/kernel@ function: JavaScript spliced in by @Gren.Kernel@, with
    -- no Gren source and so no Core (§J3 item 3).
    MissingKernel
  | -- | A @Debug@ value, which the frontend routes through its own module.
    MissingDebug
  | -- | Anything else: a port or an effect manager today (§J3 item 5), and a
    -- lowering bug if it is neither.
    MissingValue
  deriving (Eq, Ord, Show)

-- LINK

link :: Map ModuleName.Canonical Core.Module -> [Core.QualName] -> Program
link modules roots =
  let defs = Map.fromList (concatMap moduleBindings (Map.toAscList modules))
      ctorOwner = Map.fromList (concatMap moduleCtors (Map.toAscList modules))
      datas = Map.fromList (concatMap moduleDatas (Map.toAscList modules))
      refs = Map.unionWith (<>) (managerRefs modules) (Map.map (refsIn . Core._bindValue) defs)

      reached = walk defs refs (Set.fromList roots) roots
      reachedDefs = Map.restrictKeys defs reached
      reachedRefs = Map.restrictKeys refs reached

      reachedCtors = Set.unions (map _refCtors (Map.elems reachedRefs))
      reachedDataNames =
        Set.fromList (Maybe.mapMaybe (`Map.lookup` ctorOwner) (Set.toAscList reachedCtors))
      reachedDatas = Map.elems (Map.restrictKeys datas reachedDataNames)

      groups = ordered reachedDefs (Map.map (Set.intersection reached . _refGlobals) reachedRefs)
   in Program
        { _progRoots = roots,
          _progBindings = [(q, defs Map.! q) | group <- groups, q <- group],
          _progRecursive = [group | group <- groups, length group > 1],
          _progData = reachedDatas,
          _progFields = Set.unions (map _refFields (Map.elems reachedRefs)),
          _progManagers = reachedManagers reached modules,
          _progMissing = missing defs ctorOwner datas roots reachedRefs
        }

-- | The extra edges an @effect module@'s manager puts in the graph: from each
-- entry binding — @command@, @subscription@ — to the five functions the manager
-- is assembled from.
--
-- They are edges rather than a separate root set for two reasons. Reaching
-- @Task.command@ is exactly what makes the @Task@ manager live, which is the
-- rule the old pipeline gets from its @Opt.Link@ to @$fx$@; and a runtime
-- registers a manager at load time, reading those five names, so they have to be
-- emitted before the entry is — which is what an edge says and a root set does
-- not.
managerRefs :: Map ModuleName.Canonical Core.Module -> Map Core.QualName Refs
managerRefs modules =
  Map.fromList
    [ (entry, foldMap global (managerImpl m))
    | modul <- Map.elems modules,
      Just m <- [Core._moduleManager modul],
      entry <- Core._managerEntries m
    ]

-- | The functions a manager is assembled from, in the order a runtime wants
-- them.
managerImpl :: Core.Manager -> [Core.QualName]
managerImpl m =
  [ Core._managerInit m,
    Core._managerOnEffects m,
    Core._managerOnSelfMsg m
  ]
    ++ Maybe.maybeToList (Core._managerCmdMap m)
    ++ Maybe.maybeToList (Core._managerSubMap m)

-- | The managers a program has to register: the ones an entry binding reached.
reachedManagers :: Set Core.QualName -> Map ModuleName.Canonical Core.Module -> [(ModuleName.Canonical, Core.Manager)]
reachedManagers reached modules =
  [ (home, m)
  | (home, modul) <- Map.toAscList modules,
    Just m <- [Core._moduleManager modul],
    any (`Set.member` reached) (Core._managerEntries m)
  ]

moduleBindings :: (ModuleName.Canonical, Core.Module) -> [(Core.QualName, Core.Bind)]
moduleBindings (home, m) =
  [(Core.QualName home (Core._binderName (Core._bindBinder b)), b) | b <- Core._moduleDefs m]

moduleCtors :: (ModuleName.Canonical, Core.Module) -> [(Core.QualName, Core.QualName)]
moduleCtors (_, m) =
  [(Core._ctorName c, Core._dataName d) | d <- Core._moduleData m, c <- Core._dataCtors d]

moduleDatas :: (ModuleName.Canonical, Core.Module) -> [(Core.QualName, Core.DataDecl)]
moduleDatas (_, m) =
  [(Core._dataName d, d) | d <- Core._moduleData m]

-- | Breadth-first from the roots. A name with no binding is not followed; it is
-- reported by 'missing' instead.
walk ::
  Map Core.QualName Core.Bind ->
  Map Core.QualName Refs ->
  Set Core.QualName ->
  [Core.QualName] ->
  Set Core.QualName
walk defs refs seen frontier =
  case frontier of
    [] -> seen
    _ ->
      let next =
            Set.unions
              [ maybe Set.empty _refGlobals (Map.lookup q refs)
              | q <- frontier
              ]
          fresh = Set.filter (\q -> not (Set.member q seen) && Map.member q defs) next
       in walk defs refs (Set.union seen fresh) (Set.toAscList fresh)

-- ORDER

-- | Reachable bindings as groups, in link order.
--
-- The order is C14's, which "Core.Order" implements and every other list of
-- Core bindings is in as well: strongly connected components in dependency
-- order, the least-named ready group first, each group's members by name. A
-- definition therefore follows everything it uses, and the result is
-- reproducible from that description alone.
ordered :: Map Core.QualName Core.Bind -> Map Core.QualName (Set Core.QualName) -> [[Core.QualName]]
ordered defs deps = Order.groups (Map.keys defs) deps

-- MISSING

-- | A root with no binding is missing too, and names itself as the user: the
-- alternative is a program that quietly has no entry point.
missing ::
  Map Core.QualName Core.Bind ->
  Map Core.QualName Core.QualName ->
  Map Core.QualName Core.DataDecl ->
  [Core.QualName] ->
  Map Core.QualName Refs ->
  [Missing]
missing defs ctorOwner datas roots reachedRefs =
  let undefined_ target =
        not (Map.member target defs)
          && not (Map.member target ctorOwner)
          && not (Map.member target datas)

      wanted =
        Map.fromListWith
          min
          ( [(root, root) | root <- roots, undefined_ root]
              ++ [ (target, user)
                 | (user, refs) <- Map.toAscList reachedRefs,
                   target <- Set.toAscList (_refGlobals refs),
                   undefined_ target
                 ]
          )
   in [ Missing target (classify target) user
      | (target, user) <- Map.toAscList wanted
      ]

classify :: Core.QualName -> MissingKind
classify (Core.QualName home@(ModuleName.Canonical pkg _) _)
  | pkg == Pkg.kernel = MissingKernel
  | home == ModuleName.debug = MissingDebug
  | otherwise = MissingValue

-- RENDER

-- | A summary, for @GENG_DUMP_LINK@.
--
-- Deliberately not the program itself: the bindings are the whole of @core@ and
-- @node@ and a checked-in copy would be reviewed by nobody
-- (@GENG_DUMP_PROGRAM_CORE@ already writes the Core). What is here is what a
-- reader can act on — the counts, the missing names classified, and a digest of
-- the link order so that a reordering is visible without storing the order.
render :: Program -> B.Builder
render p =
  mconcat
    [ "roots " <> int (length (_progRoots p)) <> "\n",
      mconcat ["  " <> qualB q <> "\n" | q <- _progRoots p],
      "bindings " <> int (length (_progBindings p)) <> "\n",
      "recursive-groups " <> int (length (_progRecursive p)) <> "\n",
      mconcat
        [ "  " <> B.stringUtf8 (List.intercalate ", " (map qualToChars group)) <> "\n"
        | group <- _progRecursive p
        ],
      "data " <> int (length (_progData p)) <> "\n",
      "fields " <> int (Set.size (_progFields p)) <> "\n",
      "managers " <> int (length (_progManagers p)) <> "\n",
      mconcat
        [ "  " <> B.stringUtf8 (ModuleName.toChars raw) <> " " <> managerKind m <> " " <> B.stringUtf8 (List.intercalate ", " (map qualToChars (managerImpl m))) <> "\n"
        | (ModuleName.Canonical _ raw, m) <- _progManagers p
        ],
      "missing " <> int (length (_progMissing p)) <> "\n",
      mconcat
        [ "  " <> kind (_missingKind m) <> " " <> qualB (_missingName m) <> " <- " <> qualB (_missingUsedBy m) <> "\n"
        | m <- _progMissing p
        ]
    ]
  where
    int = B.stringUtf8 . show
    kind k =
      case k of
        MissingKernel -> "kernel"
        MissingDebug -> "debug "
        MissingValue -> "value "

managerKind :: Core.Manager -> B.Builder
managerKind m =
  case Core._managerKind m of
    Core.ManagerCmd -> "cmd"
    Core.ManagerSub -> "sub"
    Core.ManagerFx -> "fx "

qualB :: Core.QualName -> B.Builder
qualB = B.stringUtf8 . qualToChars

-- | Package, module and name. The package is in it because a program holds many
-- packages and two of them may expose the same module name; a package name has
-- a slash in it and a module name does not, so @:@ keeps the three readable.
qualToChars :: Core.QualName -> String
qualToChars (Core.QualName (ModuleName.Canonical pkg raw) n) =
  Pkg.toChars pkg ++ ":" ++ ModuleName.toChars raw ++ "." ++ Name.toChars n
