{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | Linking Core: many modules in, one reachable program out.
--
-- The JS backend used not to read an IR. It read an @AST.Optimized.GlobalGraph@:
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
-- And it takes one thing in that Core does not carry and no backend can do
-- without: a 'Backend', which is everything the build system knows about the
-- target that Core deliberately does not say. Two halves, both names and neither
-- code, which is C16 exactly — the JavaScript stays out of the IR and out of
-- here.
--
-- And one thing it produces that is a measurement rather than an output:
-- '_progMissing', the names reachable code refers to and no Core module
-- defines. It is every kernel function and nothing else now — effect managers
-- closed at C17 and ports at C18 — which is C16's decision that kernel
-- JavaScript stays in the build system, and the list is what says so rather
-- than a claim that it does.
module Core.Program
  ( Program (..),
    Linked (..),
    Backend (..),
    Kernel (..),
    Missing (..),
    MissingKind (..),
    link,
    kernelName,
    qualToChars,
    render,
  )
where

import Core.AST qualified as Core
import Core.Order qualified as Order
import Core.Refs (Refs (..), ctor, global, mainRefs, portRefs, refsIn, strictIn, strictPort)
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
    -- | Everything the program is made of, in link order: one list, because a
    -- backend emits into one file and the order between a binding, a port and a
    -- kernel module is exactly what stops a name being used before it is
    -- defined. @compiler#387@ is what that costs when it is got wrong. The three
    -- fields below are views of this one.
    _progLinked :: [Linked],
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
    -- | The reachable @port@s, in link order among themselves. A port is a
    -- declaration and not a 'Core.AST.Bind', so it is not in '_progBindings';
    -- it is ordered with them all the same, so that a backend emitting a port
    -- has already emitted the converter's dependencies. Empty once P3 lands.
    _progPorts :: [(ModuleName.Canonical, Core.Port)],
    -- | The kernel modules reachable code reaches, in link order among the
    -- rest. Empty once @ffi.md@ F7 retires the kernel.
    _progKernels :: [Name],
    -- | What each root's @main@ is (C19), in root order. A root whose module
    -- declares no @main@ is not here, and is a 'Missing' instead.
    _progMains :: [(ModuleName.Canonical, Core.Main)],
    -- | What reachable code refers to and Core does not define.
    _progMissing :: [Missing]
  }

-- | One thing a backend emits, under the order it is emitted in.
--
-- A port and a kernel module are not bindings and cannot be ('Core.AST.Port' is
-- a declaration, C18; kernel JavaScript is not Core at all, C16), but all three
-- define names the others use, so all three are ordered together.
data Linked
  = LBind !Core.QualName !Core.Bind
  | LPort !ModuleName.Canonical !Core.Port
  | LKernel !Name

-- | What the build system tells the linker about the backend it is linking for.
--
-- Core says what a program /is/; a backend knows what its runtime does with it,
-- and the two meet here rather than in the IR. Both fields are names.
data Backend = Backend
  { -- | The kernel modules, by short name (C16, §J7). @core@'s kernel files call
    -- back into Gren, so their references are edges in the program's graph like
    -- any other and a linker that does not know them drops code the kernel
    -- calls; they name record fields too, which @--optimize@ has to shorten
    -- alongside the ones Gren code names.
    _backendKernels :: Map Name Kernel,
    -- | Extra edges, from a declaration to the name a runtime enters it through.
    --
    -- A @port@'s runtime constructor lives in a kernel module and reads
    -- module-level state in it, so the chunk has to be emitted first; a static
    -- @main@ is handed to one. __Which__ name that is is the backend's business
    -- and Core names none of them (C16, C18, C19), so the backend says so here.
    --
    -- Edges and not roots: a root makes the kernel module reachable and says
    -- nothing about /when/, and when is the whole content of @compiler#387@.
    _backendEdges :: Map Core.QualName Refs
  }

-- | One kernel module, as the linker needs it: names, never code.
--
-- Measured over @core@ and @node@'s 26 kernel files (§J7): 123 distinct
-- @__Module_name@ references, of which 18 are Gren globals and the rest name
-- another kernel module, and 113 distinct record fields.
data Kernel = Kernel
  { -- | Gren top-level names the JavaScript calls. Constructors among them are
    -- sorted out here rather than by the caller, because whether a name is a
    -- constructor is a fact about Core and the build system holds neither.
    _kernelGren :: Set Core.QualName,
    -- | Kernel modules the JavaScript splices, by short name.
    _kernelKernels :: Set Name,
    -- | Record fields the JavaScript names.
    _kernelFields :: Set Name
  }

-- | A kernel module's node in the graph.
--
-- The same name @AST.Optimized.toKernelGlobal@ gave it, and for the same
-- reason: a kernel module is reached as a whole — one chunk list, spliced or
-- not — so its functions are not separate nodes and @$@ is the name no Gren
-- module can collide with.
kernelName :: Name -> Core.QualName
kernelName short =
  Core.QualName (ModuleName.Canonical Pkg.kernel short) Name.dollar

-- | The kernel module a name belongs to, if it is a kernel name at all.
kernelHome :: Core.QualName -> Maybe Name
kernelHome (Core.QualName (ModuleName.Canonical pkg raw) _)
  | pkg == Pkg.kernel = Just raw
  | otherwise = Nothing

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
  | -- | Anything else, which is now a lowering bug: every value a program can
    -- refer to is either a binding, a constructor, a datatype or a port, and
    -- Core carries all four.
    MissingValue
  deriving (Eq, Ord, Show)

-- LINK

link :: Backend -> Map ModuleName.Canonical Core.Module -> [Core.QualName] -> Program
link backend modules roots =
  let binds = Map.fromList (concatMap moduleBindings (Map.toAscList modules))
      ports = Map.fromList (concatMap modulePorts (Map.toAscList modules))
      kernelNodes = Map.mapKeys kernelName (_backendKernels backend)
      -- A port and a kernel module define a name the same way a binding does, so
      -- reachability and the order are computed over the three together and
      -- split apart afterwards.
      defined = Set.unions [Map.keysSet binds, Map.keysSet ports, Map.keysSet kernelNodes]
      ctorOwner = Map.fromList (concatMap moduleCtors (Map.toAscList modules))
      datas = Map.fromList (concatMap moduleDatas (Map.toAscList modules))
      refs =
        Map.unionsWith
          (<>)
          [ managerRefs modules,
            entryRefs modules,
            _backendEdges backend,
            Map.map (refsIn . Core._bindValue) binds,
            Map.map (portRefs . snd) ports,
            Map.map (kernelRefs ctorOwner) kernelNodes
          ]

      reached = walk defined refs (Set.fromList roots) roots
      reachedRefs = Map.restrictKeys refs reached

      reachedCtors = Set.unions (map _refCtors (Map.elems reachedRefs))
      reachedDataNames =
        Set.fromList (Maybe.mapMaybe (`Map.lookup` ctorOwner) (Set.toAscList reachedCtors))
      reachedDatas = Map.elems (Map.restrictKeys datas reachedDataNames)

      groups =
        ordered
          (Set.toAscList (Set.intersection reached defined))
          (Map.map (Set.intersection reached . Set.map resolve . _refGlobals) reachedRefs)
      strict =
        Map.unionsWith
          Set.union
          [ Map.map (Set.map resolve . strictIn . Core._bindValue) binds,
            -- A port's runtime call runs when the port is emitted, so the kernel
            -- module it lands in is strict too — which is the ordering
            -- @compiler#387@ is about, stated where every other order is.
            Map.map (Set.map resolve . strictPort . snd) ports,
            Map.map (Set.map resolve . _refGlobals) (Map.restrictKeys (_backendEdges backend) (Map.keysSet ports))
          ]
      items = Maybe.mapMaybe (linkedItem binds ports) (concatMap (settle strict) groups)
   in Program
        { _progRoots = roots,
          _progLinked = items,
          _progBindings = [(q, b) | LBind q b <- items],
          _progRecursive = [group | group <- groups, length group > 1],
          _progData = reachedDatas,
          _progFields = Set.unions (map _refFields (Map.elems reachedRefs)),
          _progManagers = reachedManagers reached modules,
          _progPorts = [(home, p) | LPort home p <- items],
          _progKernels = [short | LKernel short <- items],
          _progMains = mains modules roots,
          _progMissing = missing defined ctorOwner datas roots reachedRefs
        }

-- | The extra edges a module's @main@ declaration puts in the graph: from the
-- @main@ binding to whatever its flags decoder names (C19).
--
-- Edges rather than roots, exactly as 'managerRefs' are: a @main@ that nothing
-- links from is not an entry point, and a decoder is needed precisely when the
-- @main@ it decodes for is emitted.
entryRefs :: Map ModuleName.Canonical Core.Module -> Map Core.QualName Refs
entryRefs modules =
  Map.fromList
    [ (Core.QualName home Name._main, mainRefs m)
    | (home, modul) <- Map.toAscList modules,
      Just m <- [Core._moduleMain modul]
    ]

-- | Each root's @main@, in root order.
--
-- Keyed by the root's module rather than collected from every module, because
-- what a backend needs is the entry points of /this/ program: a library module
-- in the dependency graph may well declare a @main@ nothing links to.
mains :: Map ModuleName.Canonical Core.Module -> [Core.QualName] -> [(ModuleName.Canonical, Core.Main)]
mains modules roots =
  [ (home, m)
  | Core.QualName home name <- roots,
    name == Name._main,
    Just modul <- [Map.lookup home modules],
    Just m <- [Core._moduleMain modul]
  ]

-- | What one kernel module's JavaScript refers to, as a 'Refs'.
--
-- The only work here is telling a constructor from a binding: @Maybe.Just@ and
-- @Result.Ok@ are among the 18 Gren globals §J7 counted, and a constructor
-- keeps its datatype alive rather than looking for a definition that does not
-- exist. The build system that supplied the names cannot make that distinction
-- — it is a fact about Core.
kernelRefs :: Map Core.QualName Core.QualName -> Kernel -> Refs
kernelRefs ctorOwner k =
  foldMap classify (Set.toAscList (_kernelGren k))
    <> mempty
      { _refGlobals = Set.map kernelName (_kernelKernels k),
        _refFields = _kernelFields k
      }
  where
    classify q
      | Map.member q ctorOwner = ctor q
      | otherwise = global q

-- | The node a reference lands on: a kernel function is not a node of its own,
-- its module is.
resolve :: Core.QualName -> Core.QualName
resolve q =
  maybe q kernelName (kernelHome q)

-- | Which of the three kinds of thing a linked name is. A name that is none of
-- them is not emitted: it is a 'Missing', and the roots are in the order for
-- exactly that reason.
linkedItem ::
  Map Core.QualName Core.Bind ->
  Map Core.QualName (ModuleName.Canonical, Core.Port) ->
  Core.QualName ->
  Maybe Linked
linkedItem binds ports q =
  case Map.lookup q binds of
    Just b -> Just (LBind q b)
    Nothing ->
      case Map.lookup q ports of
        Just (home, p) -> Just (LPort home p)
        Nothing -> LKernel <$> kernelHome q

-- | The extra edges an @effect module@'s manager puts in the graph: from each
-- entry binding — @command@, @subscription@ — to the five functions the manager
-- is assembled from.
--
-- They are edges rather than a separate root set for two reasons. Reaching
-- @Task.command@ is exactly what makes the @Task@ manager live, which is the
-- rule the old pipeline got from its @Opt.Link@ to @$fx$@; and a runtime
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

-- | A port, under the name it defines, with its module beside it — a backend
-- registering one needs the module for nothing but the record it builds, and
-- carrying it here saves every consumer a second lookup.
modulePorts :: (ModuleName.Canonical, Core.Module) -> [(Core.QualName, (ModuleName.Canonical, Core.Port))]
modulePorts (home, m) =
  [ (Core.QualName home (Core._binderName (Core._portBinder p)), (home, p))
  | p <- Core._modulePorts m
  ]

moduleCtors :: (ModuleName.Canonical, Core.Module) -> [(Core.QualName, Core.QualName)]
moduleCtors (_, m) =
  [(Core._ctorName c, Core._dataName d) | d <- Core._moduleData m, c <- Core._dataCtors d]

moduleDatas :: (ModuleName.Canonical, Core.Module) -> [(Core.QualName, Core.DataDecl)]
moduleDatas (_, m) =
  [(Core._dataName d, d) | d <- Core._moduleData m]

-- | Breadth-first from the roots. A name with no binding is not followed; it is
-- reported by 'missing' instead.
walk ::
  Set Core.QualName ->
  Map Core.QualName Refs ->
  Set Core.QualName ->
  [Core.QualName] ->
  Set Core.QualName
walk defined refs seen frontier =
  case frontier of
    [] -> seen
    _ ->
      let next =
            Set.unions
              [ maybe Set.empty (Set.map resolve . _refGlobals) (Map.lookup q refs)
              | q <- frontier
              ]
          fresh = Set.filter (\q -> not (Set.member q seen) && Set.member q defined) next
       in walk defined refs (Set.union seen fresh) (Set.toAscList fresh)

-- ORDER

-- | The order within one group.
--
-- C14's relation is \"refers to\", which is the right one for deciding what must
-- be emitted before what /exists/. Inside a cycle it decides nothing, because
-- every member refers to every other, and something still has to go first — and
-- for a backend with load-time initialization the choice is not free: a
-- definition whose right-hand side is evaluated when it is emitted must follow
-- what that right-hand side __reads__.
--
-- The two relations differ only inside a lambda, so this re-runs C14's own
-- algorithm over the group with the strict relation ("Core.Refs.strictIn"), and
-- the result is the same specification applied twice. @Array.length@ is the case
-- that found it: it is @_Array_length@ and nothing else, it is in a cycle with
-- the kernel @Array@ module that defines that name, and emitted first it reads
-- an @undefined@.
--
-- A kernel module has no entry here and so no strict references, which says that
-- kernel JavaScript calls back into Gren from inside its functions rather than
-- while it loads. That is an assumption about @core@'s kernel files, and it is
-- the same one the old pipeline's depth-first traversal made.
settle :: Map Core.QualName (Set Core.QualName) -> [Core.QualName] -> [Core.QualName]
settle strict group =
  case group of
    [_] -> group
    _ -> concat (Order.groups group strict)

-- | Reachable bindings as groups, in link order.
--
-- The order is C14's, which "Core.Order" implements and every other list of
-- Core bindings is in as well: strongly connected components in dependency
-- order, the least-named ready group first, each group's members by name. A
-- definition therefore follows everything it uses, and the result is
-- reproducible from that description alone.
ordered :: [Core.QualName] -> Map Core.QualName (Set Core.QualName) -> [[Core.QualName]]
ordered defined deps = Order.groups defined deps

-- MISSING

-- | A root with no binding is missing too, and names itself as the user: the
-- alternative is a program that quietly has no entry point.
missing ::
  Set Core.QualName ->
  Map Core.QualName Core.QualName ->
  Map Core.QualName Core.DataDecl ->
  [Core.QualName] ->
  Map Core.QualName Refs ->
  [Missing]
missing defined ctorOwner datas roots reachedRefs =
  let undefined_ target =
        not (Set.member target defined)
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
      "mains " <> int (length (_progMains p)) <> "\n",
      mconcat
        [ "  " <> B.stringUtf8 (ModuleName.toChars raw) <> " " <> mainKind m <> "\n"
        | (ModuleName.Canonical _ raw, m) <- _progMains p
        ],
      "kernels " <> int (length (_progKernels p)) <> "\n",
      mconcat ["  " <> B.stringUtf8 (Name.toChars short) <> "\n" | short <- _progKernels p],
      "ports " <> int (length (_progPorts p)) <> "\n",
      mconcat
        [ "  " <> B.stringUtf8 (ModuleName.toChars raw) <> "." <> B.stringUtf8 (Name.toChars (Core._binderName (Core._portBinder port))) <> " " <> portFlow port <> "\n"
        | (ModuleName.Canonical _ raw, port) <- _progPorts p
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

-- | Which way a port's payload crosses, and whether it crosses as bytes: the
-- two things a reader of the summary would otherwise have to open the Core to
-- find.
portFlow :: Core.Port -> B.Builder
portFlow (Core.Port _ flow) =
  case flow of
    Core.PortOut c -> "out " <> bytes c
    Core.PortIn c -> "in " <> bytes c
    Core.PortTask input output ->
      "task " <> maybe "()" bytes input <> " -> " <> bytes output
  where
    bytes c = if Core._convBytes c then "bytes" else "json"

-- | Which of the three things a runtime does with @main@, and for a program
-- whether its flags cross as bytes: what a reader would otherwise open the Core
-- to find, as with 'portFlow'.
mainKind :: Core.Main -> B.Builder
mainKind m =
  case m of
    Core.MainString -> "string"
    Core.MainHtml -> "html"
    Core.MainProgram c -> "program " <> if Core._convBytes c then "bytes" else "json"

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
