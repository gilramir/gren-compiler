{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | Build the JS backend's input from Core (@docs/m1a-js-on-core.md@ §J3 item 6).
--
-- M1a's criterion is that the JS backend reads Core. The backend's input is an
-- 'AST.Optimized.GlobalGraph' — §J1 — so the shortest honest route to that
-- criterion is to build the graph's __value definitions__ from Core instead of
-- from @Optimize.*@, and leave the rest of the graph alone. Every definition's
-- body then comes from Core; what stays is what Core does not carry yet:
-- constructor, kernel, effect-manager and port nodes, the record-field census,
-- and each root's @main@.
--
-- That is a deliberate first step rather than the destination. It retires the
-- risk that matters — whether Core carries enough to generate code from — while
-- reusing a JS emitter, a minifier and a source-map writer that already work.
-- The nodes it does not build are exactly the ones §J3 items 3 and 5 are about,
-- and §J7 measures them: 298 kernel functions and ten manager fields.
--
-- __Where this differs from the existing pipeline, on purpose:__
--
--   * __Pattern matching is naive.__ Alternatives are tested in source order,
--     as a right-nested 'Opt.Chain', so a shared test is repeated and no branch
--     body is ever duplicated. Decision trees are C4's optional Core→Core pass
--     and §J6's decision; this needs neither, which is also §J6's point — the
--     join-point question is an optimization question, not a correctness one.
--   * __No tail-call rewriting.__ 'Opt.TailCall' and 'Opt.DefineTailFunc' are
--     `Optimize.Expression`'s work and §J3 item 4's decision. Deep self-recursion
--     in Gren source will grow the JS stack here where it did not before.
--   * __Recursive groups become ordinary definitions.__ 'Opt.Cycle' exists for
--     value cycles, and Canonical rejects those: a cycle that survives
--     `detectBadCycles` goes through a function, and a function body does not run
--     until it is called, so plain @var@ definitions in any order are correct.
module Generate.FromCore
  ( redefine,
    Gap,
    gap,
    renderGap,
  )
where

import AST.Canonical qualified as Can
import AST.Optimized qualified as Opt
import Control.Monad.Trans.State.Strict (State, runState, state)
import Core.AST qualified as Core
import Core.Refs qualified as Refs
import Data.ByteString.Builder qualified as B
import Data.Index qualified as Index
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Utf8 qualified as Utf8
import Gren.Float qualified as EF
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Gren.String qualified as ES
import Optimize.DecisionTree qualified as DT
import Reporting.Annotation qualified as A

-- ENTRY

-- | Replace every value definition in the graph with one built from Core.
--
-- 'Map.union' is left-biased, so a Core definition wins over the one
-- @Optimize.Module@ produced for the same name, and every other kind of node
-- stays. The field census stays too: kernel JavaScript names fields that no Gren
-- expression mentions (§J7), so a census taken from Core alone would be short.
redefine :: Map ModuleName.Canonical Core.Module -> Opt.GlobalGraph -> Opt.GlobalGraph
redefine cores (Opt.GlobalGraph nodes fields) =
  let defined =
        Map.fromList
          [ (global, keepDeps nodes global node)
          | (global, node) <- coreNodes cores
          ]
   in Opt.GlobalGraph (Map.union defined nodes) fields

-- | Every value definition Core supplies, as a backend node, before 'keepDeps'
-- widens anything. 'redefine' and 'gap' walk the same list, which is what makes
-- the measurement a measurement of what is shipped.
coreNodes :: Map ModuleName.Canonical Core.Module -> [(Opt.Global, Opt.Node)]
coreNodes cores =
  let ctors = Map.fromList (concatMap ctorEntries (Map.elems cores))
   in concatMap (moduleNodes ctors) (Map.toAscList cores)

-- | Keep the dependencies of the node being replaced, for @main@ and only for
-- @main@.
--
-- A @main@ whose type is a @Program@ has a generated flags decoder hanging off
-- its definition node — @Optimize.Module@ passes it in as @mainDeps@, and
-- @Node.SimpleProgram@ and a browser @main@ each register a kernel module the
-- same way. That is `Optimize.Port`'s work and Core does not carry it (§J3 item
-- 5), so the dependencies are attached to a definition whose body says nothing
-- about them, and dropping them emits a program that refers to a `Json.Decode`
-- function nobody defined.
--
-- It applied to every definition until §J10 measured what that was covering for:
-- two dependencies the Core path was missing — @Basics.identity@ behind an
-- unboxed constructor and the kernel @Utils@ module behind a character literal,
-- both now recorded by 'need' — and two the old pipeline records and does not
-- use. @harness\/deps-gap.py@ is the standing check that the list stays that
-- short. Outside @main@ the two walks now agree or the Core one is tighter, so
-- the union has nothing left to do there.
keepDeps :: Map Opt.Global Opt.Node -> Opt.Global -> Opt.Node -> Opt.Node
keepDeps nodes global@(Opt.Global _ name) node
  | name /= Name._main = node
  | otherwise =
      case (node, Map.lookup global nodes) of
        (Opt.Define r body ds, Just (Opt.Define _ _ old)) -> Opt.Define r body (Set.union ds old)
        (Opt.Define r body ds, Just (Opt.Cycle _ _ _ old)) -> Opt.Define r body (Set.union ds old)
        (Opt.Define r body ds, Just (Opt.DefineTailFunc _ _ _ old)) -> Opt.Define r body (Set.union ds old)
        _ -> node

-- MEASURING THE UNION

-- | What 'keepDeps' actually adds, definition by definition (§J10).
--
-- The union is a superset, so a passing corpus does not show that the Core walk
-- is complete: a dependency Core failed to reach would be supplied by the old
-- node and nothing would go wrong. This measures the difference instead, and the
-- claim it can support is narrow but real — if the only definitions whose old
-- dependency set is not a subset of the Core one are the roots' @main@, then
-- outside @main@ the Core walk reaches everything @Optimize.Module@ reached, and
-- 'keepDeps' can be narrowed to the case that needs it.
data Gap = Gap
  { -- | Definitions Core supplied, by the kind of node they replaced.
    _gapDefs :: [(Opt.Global, Kind)],
    -- | Those whose two dependency sets differ, either way round.
    _gapDiffs :: [Diff]
  }

data Diff = Diff
  { _diffDef :: Opt.Global,
    -- | The kind of node being replaced. A @link@ is a cycle member, and the
    -- group carries every member's dependencies together, so one is widened by
    -- its siblings' as a matter of course.
    _diffWas :: Kind,
    -- | In the replaced node and not reached from Core: what the union adds, and
    -- the whole reason 'keepDeps' exists.
    _diffOnlyOld :: [(Opt.Global, Kind)],
    -- | Reached from Core and not in the replaced node. Not a hazard — a
    -- dependency too many keeps a node alive that nothing calls — but it says
    -- where the two walks disagree in the other direction.
    _diffOnlyCore :: [(Opt.Global, Kind)]
  }

-- | Which kind of node a name resolves to, so that a difference can be read
-- without looking every name up by hand.
data Kind
  = KDefine
  | KTailFunc
  | KCycle
  | KLink
  | KCtor
  | KKernel
  | KManager
  | KPort
  | -- | Nothing in the graph defines it. For a definition, that means Core
    -- supplied one @Optimize.Module@ did not; for a dependency, it is a
    -- dangling reference and a bug in whichever walk produced it.
    KAbsent
  deriving (Eq, Ord)

gap :: Map ModuleName.Canonical Core.Module -> Opt.GlobalGraph -> Gap
gap cores (Opt.GlobalGraph nodes _) =
  let kindOf global = maybe KAbsent nodeKind (Map.lookup global nodes)
      classify = map (\g -> (g, kindOf g)) . Set.toList
      entries = coreNodes cores
      -- A cycle member's node is a `Link` to the group, and the group carries
      -- every member's dependencies together. Following the link is what makes
      -- the comparison meaningful: Core defines each member on its own, so its
      -- set is the member's and the old one is the group's.
      oldDeps global =
        case Map.lookup global nodes of
          Just (Opt.Link linked) -> maybe Set.empty nodeDeps (Map.lookup linked nodes)
          Just old -> nodeDeps old
          Nothing -> Set.empty
      diff (global, node) =
        let core = nodeDeps node
            old = oldDeps global
            onlyOld = Set.difference old core
            onlyCore = Set.difference core old
         in if Set.null onlyOld && Set.null onlyCore
              then Nothing
              else Just (Diff global (kindOf global) (classify onlyOld) (classify onlyCore))
   in Gap
        [(global, kindOf global) | (global, _) <- entries]
        (Maybe.mapMaybe diff entries)

nodeDeps :: Opt.Node -> Set Opt.Global
nodeDeps node =
  case node of
    Opt.Define _ _ ds -> ds
    Opt.DefineTailFunc _ _ _ ds -> ds
    Opt.Cycle _ _ _ ds -> ds
    Opt.Kernel _ ds -> ds
    Opt.PortIncoming _ _ ds -> ds
    Opt.PortOutgoing _ _ ds -> ds
    Opt.PortTask _ _ _ _ ds -> ds
    -- A `Link` carries none of its own; 'gap' follows it to the cycle.
    Opt.Link _ -> Set.empty
    Opt.Ctor _ _ -> Set.empty
    Opt.Enum _ -> Set.empty
    Opt.Box -> Set.empty
    Opt.Manager _ -> Set.empty

nodeKind :: Opt.Node -> Kind
nodeKind node =
  case node of
    Opt.Define {} -> KDefine
    Opt.DefineTailFunc {} -> KTailFunc
    Opt.Cycle {} -> KCycle
    Opt.Link _ -> KLink
    Opt.Ctor _ _ -> KCtor
    Opt.Enum _ -> KCtor
    Opt.Box -> KCtor
    Opt.Kernel _ _ -> KKernel
    Opt.Manager _ -> KManager
    Opt.PortIncoming {} -> KPort
    Opt.PortOutgoing {} -> KPort
    Opt.PortTask {} -> KPort

renderGap :: Gap -> B.Builder
renderGap (Gap defs diffs) =
  mconcat
    [ "definitions " <> int (length defs) <> "\n",
      mconcat
        [ "  replaced " <> kindB k <> " " <> int n <> "\n"
        | (k, n) <- tally (map snd defs)
        ],
      "differing " <> int (length diffs) <> "\n",
      "  widened " <> int (length [d | d <- diffs, not (null (_diffOnlyOld d))]) <> "\n",
      "  core-only " <> int (length [d | d <- diffs, not (null (_diffOnlyCore d))]) <> "\n",
      "only-old-by-kind\n",
      mconcat
        [ "  " <> kindB k <> " " <> int n <> "\n"
        | (k, n) <- tally (map snd (concatMap _diffOnlyOld diffs))
        ],
      "only-core-by-kind\n",
      mconcat
        [ "  " <> kindB k <> " " <> int n <> "\n"
        | (k, n) <- tally (map snd (concatMap _diffOnlyCore diffs))
        ],
      mconcat (map renderDiff diffs)
    ]
  where
    int = B.stringUtf8 . show

renderDiff :: Diff -> B.Builder
renderDiff (Diff global was onlyOld onlyCore) =
  mconcat
    [ globalB global <> " was " <> kindB was <> "\n",
      mconcat ["  only-old  " <> kindB k <> " " <> globalB g <> "\n" | (g, k) <- onlyOld],
      mconcat ["  only-core " <> kindB k <> " " <> globalB g <> "\n" | (g, k) <- onlyCore]
    ]

-- | How many of each, most first, so the shape of a difference is the first
-- thing in the file rather than something to be counted by eye.
tally :: [Kind] -> [(Kind, Int)]
tally ks =
  List.sortOn (negate . snd) (Map.toList (Map.fromListWith (+) [(k, 1 :: Int) | k <- ks]))

kindB :: Kind -> B.Builder
kindB k =
  case k of
    KDefine -> "define  "
    KTailFunc -> "tailfunc"
    KCycle -> "cycle   "
    KLink -> "link    "
    KCtor -> "ctor    "
    KKernel -> "kernel  "
    KManager -> "manager "
    KPort -> "port    "
    KAbsent -> "absent  "

globalB :: Opt.Global -> B.Builder
globalB (Opt.Global (ModuleName.Canonical pkg raw) name) =
  B.stringUtf8 (Pkg.toChars pkg ++ ":" ++ ModuleName.toChars raw ++ "." ++ Name.toChars name)

-- | What a constructor needs to be built and to be tested for. The tag is on the
-- Core node, so it is not here.
data Ctor = Ctor
  { _opts :: !Can.CtorOpts,
    -- | How many constructors the datatype has. A one-constructor type is
    -- irrefutable and gets no test at all, which is what keeps a record-shaped
    -- @type@ from being compared against itself.
    _alts :: !Int
  }

ctorEntries :: Core.Module -> [(Core.QualName, Ctor)]
ctorEntries m =
  [ (Core._ctorName c, Ctor (ctorOpts d) (length (Core._dataCtors d)))
  | d <- Core._moduleData m,
    c <- Core._dataCtors d
  ]

-- | The representation choice, derived the way `Canonicalize.Environment.Local`
-- derives it from source: one constructor with one field is unboxed, all-nullary
-- constructors are an enum, anything else is a tagged record.
ctorOpts :: Core.DataDecl -> Can.CtorOpts
ctorOpts d =
  case Core._dataCtors d of
    [c] | length (Core._ctorFields c) == 1 -> Can.Unbox
    cs | all (null . Core._ctorFields) cs -> Can.Enum
    _ -> Can.Normal

moduleNodes :: Map Core.QualName Ctor -> (ModuleName.Canonical, Core.Module) -> [(Opt.Global, Opt.Node)]
moduleNodes ctors (home, m) =
  map (define (Env ctors Map.empty home)) (Core._moduleDefs m)

define :: Env -> Core.Bind -> (Opt.Global, Opt.Node)
define env (Core.Bind binder value) =
  let name = Core._binderName binder
      r = region (Core._binderSpan binder)
      node =
        case tailShape value of
          Nothing ->
            let (body, needed) = runFresh (expr env value)
             in Opt.Define r body (Set.union (deps value) needed)
          Just (params, join, loop) ->
            let (body, needed) = runFresh (expr (entering name params join env) loop)
             in Opt.DefineTailFunc r [A.At r p | p <- params] body (Set.union (deps value) needed)
   in (Opt.Global (_home env) name, node)

-- | A function whose body is a join over its own parameters, entered once with
-- them: what "Core.Pass.TailCall" produces, and the one join shape the JS
-- backend has a real jump for.
--
-- @Opt.DefineTailFunc@ labels the generated @while (true)@ with the function's
-- own name and @Opt.TailCall@ reassigns the parameters and @continue@s it, so
-- Core's entry join and Opt's tail function are the same construct written
-- twice. Every other join is a call (see 'joins'), because @Opt@ has no general
-- labelled block — @docs/core.md@ C15.
tailShape :: Core.Expr -> Maybe ([Name], Name, Core.Expr)
tailShape value =
  case Core._exprValue value of
    Core.ELam params body ->
      case Core._exprValue body of
        Core.EJoin [Core.Bind joinBinder joinValue] entry
          | Core.EJump jumped args <- Core._exprValue entry,
            jumped == Core._binderName joinBinder,
            Core.ELam loopParams loop <- Core._exprValue joinValue,
            names loopParams == names params,
            [a | Core.Expr (Core.EVar a) _ _ <- args] == names params ->
              Just (names params, jumped, loop)
        _ -> Nothing
    _ -> Nothing
  where
    names = map Core._binderName

entering :: Name -> [Name] -> Name -> Env -> Env
entering label params join env =
  env {_tails = Map.insert join (Tail label params) (_tails env)}

-- | Which graph nodes a definition's body /names/.
--
-- The globals and constructors "Core.Refs" already collects for the linker,
-- mapped into the backend's namespace: a kernel reference is a dependency on the
-- whole kernel module, because that is the granularity `Gren.Kernel` splices at,
-- and a `Debug` reference is a dependency on the @Debug@ module the way
-- @Optimize.Names@ records it.
--
-- This is half of a definition's dependency set. The other half is what the
-- /translation/ names and Core does not — 'need' — and the two are kept apart
-- because they answer different questions: this one is a fact about the Core,
-- and belongs to the linker as much as to the backend; the other is a fact about
-- the JavaScript, and would be a different set for a different backend.
--
-- @Basics.True@ and @Basics.False@ are excluded, and stay excluded: both paths
-- compile them to JavaScript literals, so neither refers to the enum node
-- @Optimize.Module@ made for them (§J10).
deps :: Core.Expr -> Set Opt.Global
deps value =
  let refs = Refs.refsIn value
      globals = Set.map toGlobal (Refs._refGlobals refs)
      ctors =
        Set.fromList
          [ Opt.Global home name
          | q@(Core.QualName home name) <- Set.toList (Refs._refCtors refs),
            not (isBool q)
          ]
   in Set.union globals ctors

toGlobal :: Core.QualName -> Opt.Global
toGlobal (Core.QualName home@(ModuleName.Canonical pkg raw) name)
  | pkg == Pkg.kernel = Opt.toKernelGlobal raw
  | otherwise = Opt.Global home name

-- ENVIRONMENT

data Env = Env
  { _ctors :: Map Core.QualName Ctor,
    -- | The joins that are a function's own entry, and so compile to
    -- @Opt.TailCall@ rather than to a call. See 'tailShape'.
    _tails :: Map Name Tail,
    -- | The module being translated. `Opt.VarDebug` wants the module doing the
    -- referring rather than the one referred to, and Core drops that when it
    -- rewrites a `Debug` reference to the `Debug` module — but the module being
    -- translated is exactly the referrer, so nothing is lost here.
    _home :: ModuleName.Canonical
  }

-- | Where a jump to an entry join goes: the label the JS backend puts on the
-- loop — a function's own name — and the parameters it reassigns.
data Tail = Tail
  { _tailLabel :: !Name,
    _tailParams :: ![Name]
  }

-- | Fresh local names, and the dependencies the /translation/ introduces.
--
-- The names are the same @_v0@, @_v1@ series `Optimize.Names` uses, so that
-- generated code reads the same way it did. The dependency set is there for the
-- same reason `Optimize.Names` has a @Tracker@: some of what a definition
-- depends on is not in the code being translated but in the JavaScript chosen
-- for it — see 'need'.
type Fresh a = State Gen a

data Gen = Gen !Int !(Set Opt.Global)

runFresh :: Fresh a -> (a, Set Opt.Global)
runFresh f =
  let (a, Gen _ needed) = runState f (Gen 0 Set.empty)
   in (a, needed)

fresh :: Fresh Name
fresh = state (\(Gen uid needed) -> (Name.fromVarIndex uid, Gen (uid + 1) needed))

-- | A name the emitted JavaScript will refer to that the Core expression does
-- not mention.
--
-- Two of these, and both are `Generate.JavaScript.Expression`'s choices rather
-- than Core's (§J10):
--
--   * an @Opt.VarBox@ is @Basics.identity@ under @--optimize@, because an
--     unboxed constructor /is/ the identity function there;
--   * an @Opt.Chr@ is a call to @_Utils_chr@ in dev mode.
--
-- Both are registered unconditionally, exactly as `Optimize.Names` registers
-- them, because the graph is built once and the mode is chosen after it.
need :: Opt.Global -> Fresh ()
need global = state (\(Gen uid needed) -> ((), Gen uid (Set.insert global needed)))

-- EXPRESSIONS

expr :: Env -> Core.Expr -> Fresh Opt.Expr
expr env (Core.Expr value _ sp) =
  let r = region sp
   in case value of
        Core.EVar name ->
          pure (Opt.VarLocal r name)
        Core.EGlobal (Core.QualName home@(ModuleName.Canonical pkg raw) name)
          | pkg == Pkg.kernel -> pure (Opt.VarKernel r raw name)
          | home == ModuleName.debug -> pure (Opt.VarDebug r name (_home env) Nothing)
          | otherwise -> pure (Opt.VarGlobal r (Opt.Global home name))
        Core.ELit lit ->
          literal r lit
        Core.ELam binders body ->
          Opt.Function r (map (\b -> A.At r (Core._binderName b)) binders) <$> expr env body
        Core.EApp fn args ->
          Opt.Call r <$> expr env fn <*> traverse (expr env) args
        Core.ELet binds body ->
          lets env r binds =<< expr env body
        Core.ELetRec binds body ->
          lets env r binds =<< expr env body
        Core.EJoin binds body ->
          joins env r binds =<< expr env body
        Core.EJump join args ->
          jump env r join args
        Core.ECase scrutinee alts _fallback ->
          caseOf env r scrutinee alts
        Core.ECtor name tag args ->
          ctor env r name tag args
        Core.ERecord fields ->
          Opt.Record r . Map.fromList <$> traverse (field env r) fields
        Core.EUpdate base fields ->
          Opt.Update r <$> expr env base <*> (Map.fromList <$> traverse (field env r) fields)
        Core.EAccess base name ->
          (\b -> Opt.Access b r name) <$> expr env base
        Core.EArray items ->
          Opt.Array r <$> traverse (expr env) items
        Core.EPrim _ _ ->
          error "Generate.FromCore: EPrim — `core` has no @prim declarations yet (docs/m1a-lowering.md §L4)"
        Core.ECrash _ ->
          error "Generate.FromCore: ECrash — the lowering does not produce one yet (docs/m1a-lowering.md §L4)"
        Core.ETyLam _ _ ->
          error "Generate.FromCore: ETyLam — specialization is M1b (docs/m1a-lowering.md §L2)"
        Core.ETyApp _ _ ->
          error "Generate.FromCore: ETyApp — specialization is M1b (docs/m1a-lowering.md §L2)"
        Core.EWitLam _ _ ->
          error "Generate.FromCore: EWitLam — classes are M1b"
        Core.EWitApp _ _ ->
          error "Generate.FromCore: EWitApp — classes are M1b"

field :: Env -> A.Region -> (Core.Field, Core.Expr) -> Fresh (A.Located Name, Opt.Expr)
field env r (name, value) =
  (,) (A.At r name) <$> expr env value

lets :: Env -> A.Region -> [Core.Bind] -> Opt.Expr -> Fresh Opt.Expr
lets env r binds body =
  foldr wrap (pure body) binds
  where
    wrap (Core.Bind binder value) acc =
      let name = Core._binderName binder
       in case tailShape value of
            Nothing -> Opt.Let . Opt.Def r name <$> expr env value <*> acc
            Just (params, join, loop) ->
              Opt.Let . Opt.TailDef r name [A.At r p | p <- params]
                <$> expr (entering name params join env) loop
                <*> acc

-- JOINS

-- | A join that is not a function's entry becomes a function, and a jump to it
-- a call.
--
-- Not what C15 says a join point is, and it is the backend's limit rather than
-- the IR's: @Opt.Case@ ties its own join points to a case — @Opt.Jump@ exists
-- only inside a decider — so there is no general labelled block to land a
-- general 'Core.EJoin' on. It costs one closure where a labelled block would
-- cost nothing, and it goes away with the @Opt@ hop
-- (@docs/m1a-js-on-core.md@ §J3).
--
-- A join with no parameters takes an ignored one, because @Opt@'s call helpers
-- start at one argument and a call with none generates the function rather than
-- a call to it.
joins :: Env -> A.Region -> [Core.Bind] -> Opt.Expr -> Fresh Opt.Expr
joins env r binds body =
  foldr wrap (pure body) binds
  where
    wrap (Core.Bind binder value) acc =
      do
        translated <- expr env value
        let name = Core._binderName binder
            function =
              case translated of
                Opt.Function {} -> translated
                _ -> Opt.Function r [A.At r ignored] translated
        Opt.Let (Opt.Def r name function) <$> acc

jump :: Env -> A.Region -> Name -> [Core.Expr] -> Fresh Opt.Expr
jump env r join args =
  case Map.lookup join (_tails env) of
    Just (Tail label params) ->
      Opt.TailCall label . zip params <$> traverse (expr env) args
    Nothing ->
      case args of
        [] -> pure (Opt.Call r (Opt.VarLocal r join) [Opt.Record r Map.empty])
        _ -> Opt.Call r (Opt.VarLocal r join) <$> traverse (expr env) args

-- | The parameter a parameterless join takes and never reads.
ignored :: Name
ignored = Name.fromChars "$jarg"

-- LITERALS

literal :: A.Region -> Core.Literal -> Fresh Opt.Expr
literal r lit =
  case lit of
    Core.LIntLegacy n -> pure (Opt.Int r (fromInteger n))
    Core.LInt n -> pure (Opt.Int r (fromIntegral n))
    Core.LInt64 n -> pure (Opt.Int r (fromIntegral n))
    Core.LUInt32 n -> pure (Opt.Int r (fromIntegral n))
    Core.LUInt64 n -> pure (Opt.Int r (fromIntegral n))
    Core.LFloat d -> pure (Opt.Float r (float d))
    Core.LFloat32 f -> pure (Opt.Float r (float (realToFrac f)))
    -- A character is a one-character string wrapped by @_Utils_chr@ in dev mode,
    -- so it depends on the kernel @Utils@ module. `Optimize.Expression` records
    -- the same dependency, with @Names.registerKernel Name.utils@.
    Core.LChar code ->
      do
        need (Opt.toKernelGlobal Name.utils)
        pure (Opt.Chr r (jsLiteral [toEnum (fromIntegral code)]))
    Core.LString text -> pure (Opt.Str r (jsLiteral (Utf8.toChars text)))

-- | A `Gren.Float` is the digits as written, and Core holds a `Double`, so the
-- digits have to be written again. Haskell's `show` produces the shortest
-- decimal that reads back as the same `Double`, and every form it produces —
-- @1.0@, @1.0e-2@, @Infinity@, @NaN@ — is also valid JavaScript.
float :: Double -> EF.Float
float = Utf8.fromChars . show

-- | Text as the body of a JavaScript literal.
--
-- `Generate.JavaScript.Builder` writes a string between __single__ quotes, so
-- that is the quote to escape and the double quote goes out as itself — which is
-- also what `Parse.String` does when it builds one of these from source.
--
-- Core holds characters (C2's `Text`), not the escapes they were written with,
-- so this is where they are escaped again, and it escapes only what has to be:
-- the quote, the backslash, the C0 controls and DEL, and U+2028 and U+2029,
-- which older JavaScript treats as line terminators inside a string. Everything
-- else, astral characters included, goes out as itself, in UTF-8.
--
-- Deliberately __not__ `Gren.String`'s surrogate-pair encoder. That is the
-- function whose boundary was off by one — `docs/upstream/`
-- @compiler-u-ffff-becomes-a-surrogate-pair.md@ — and a literal character needs
-- no arithmetic to go wrong in.
jsLiteral :: [Char] -> ES.String
jsLiteral = Utf8.fromChars . concatMap escape
  where
    escape c =
      case c of
        '\'' -> "\\'"
        '\\' -> "\\\\"
        '\n' -> "\\n"
        '\r' -> "\\r"
        '\t' -> "\\t"
        _
          | code < 0x20 || code == 0x7F || code == 0x2028 || code == 0x2029 ->
              "\\u" ++ pad (showHex code)
          | otherwise -> [c]
      where
        code = fromEnum c

    pad hex = replicate (4 - length hex) '0' ++ hex

    showHex 0 = "0"
    showHex n = go n ""
      where
        go 0 acc = acc
        go m acc = go (m `div` 16) (digit (m `mod` 16) : acc)
        digit d = if d < 10 then toEnum (fromEnum '0' + d) else toEnum (fromEnum 'a' + d - 10)

-- CONSTRUCTORS

-- | A saturated constructor application, which is the only shape Core has: a
-- bare constructor is an `ELam` around one of these.
ctor :: Env -> A.Region -> Core.QualName -> Int -> [Core.Expr] -> Fresh Opt.Expr
ctor env r name@(Core.QualName home short) tag args
  | isBool name = pure (Opt.Bool r (short == Name.true))
  | otherwise =
      do
        let opts = _opts (lookupCtor env name)
        case opts of
          Can.Unbox -> need identity
          _ -> pure ()
        let reference =
              case opts of
                Can.Normal -> Opt.VarGlobal r (Opt.Global home short)
                Can.Enum -> Opt.VarEnum r (Opt.Global home short) (zeroBased tag)
                Can.Unbox -> Opt.VarBox r (Opt.Global home short)
        case args of
          [] -> pure reference
          _ -> Opt.Call r reference <$> traverse (expr env) args

-- | What an @Opt.VarBox@ compiles to under @--optimize@, and so a dependency of
-- every definition that mentions an unboxed constructor. `Optimize.Names`
-- records it at the same place, in @registerCtor@.
identity :: Opt.Global
identity = Opt.Global ModuleName.basics Name.identity

lookupCtor :: Env -> Core.QualName -> Ctor
lookupCtor env name@(Core.QualName _ short) =
  case Map.lookup name (_ctors env) of
    Just c -> c
    Nothing -> error ("Generate.FromCore: no datatype declares " ++ Name.toChars short)

-- | `Data.Index` exports the type and not the constructor, on purpose: an index
-- is meant to be built by walking a list. A constructor tag arrives as a machine
-- integer from Core, so this is the one place that has to count up to it.
zeroBased :: Int -> Index.ZeroBased
zeroBased n = iterate Index.next Index.first !! n

isBool :: Core.QualName -> Bool
isBool (Core.QualName home short) =
  home == ModuleName.basics && (short == Name.true || short == Name.false)

-- CASE

-- | Alternatives tested in order: a right-nested chain of conjunctions.
--
-- The scrutinee is bound to a name first, because a decider tests paths from a
-- root variable rather than from an expression — unless it is already a
-- variable, in which case that one is the root, which is the same shortcut
-- `Optimize.Expression` takes.
caseOf :: Env -> A.Region -> Core.Expr -> [Core.Alt] -> Fresh Opt.Expr
caseOf env r scrutinee alts =
  do
    oscrutinee <- expr env scrutinee
    label <- fresh
    case oscrutinee of
      Opt.VarLocal _ root ->
        do
          decider <- chain env root alts
          pure (Opt.Case label root decider [])
      _ ->
        do
          root <- fresh
          decider <- chain env root alts
          pure (Opt.Let (Opt.Def r root oscrutinee) (Opt.Case label root decider []))

chain :: Env -> Name -> [Core.Alt] -> Fresh (Opt.Decider Opt.Choice)
chain env root alts =
  case alts of
    [] ->
      error "Generate.FromCore: a case with no alternatives"
    [alt] ->
      -- The last alternative is the fallback. Every `ECase` the lowering
      -- produces is exhaustive — `Nitpick.PatternMatches` rejects the ones that
      -- are not, which is why `Core.ECase`'s fallback is `Nothing` — so nothing
      -- is lost by not testing it.
      leaf env root alt
    alt@(Core.Alt pattern _) : rest ->
      let (tests, _) = compile env root DT.Empty pattern
       in if null tests
            then leaf env root alt
            else Opt.Chain tests <$> leaf env root alt <*> chain env root rest

leaf :: Env -> Name -> Core.Alt -> Fresh (Opt.Decider Opt.Choice)
leaf env root (Core.Alt pattern body) =
  do
    obody <- expr env body
    let (_, destructors) = compile env root DT.Empty pattern
    pure (Opt.Leaf (Opt.Inline (foldr Opt.Destruct obody destructors)))

-- | What a pattern tests, and what it binds.
--
-- One walk, two answers, because a naive matcher needs the tests without the
-- bindings (to decide whether to take the branch) and the bindings without the
-- tests (inside it).
compile :: Env -> Name -> DT.Path -> Core.Pattern -> ([(DT.Path, DT.Test)], [Opt.Destructor])
compile env root path pattern =
  case pattern of
    Core.PWild ->
      ([], [])
    Core.PVar binder ->
      ([], [Opt.Destructor (Core._binderName binder) (optPath root path)])
    Core.PAs binder inner ->
      -- The alias binds the same value the sub-pattern matches, so the
      -- sub-pattern keeps the same path and the binding is one more destructor.
      let (tests, ds) = compile env root path inner
       in (tests, Opt.Destructor (Core._binderName binder) (optPath root path) : ds)
    Core.PLit lit ->
      ([(path, litTest lit)], [])
    Core.PCtor name@(Core.QualName home short) tag args ->
      let Ctor opts alts = lookupCtor env name
          subs =
            case opts of
              Can.Unbox -> map (compile env root (DT.Unbox path)) args
              _ -> Index.indexedMap (\i arg -> compile env root (DT.Index i path) arg) args
          below = (concatMap fst subs, concatMap snd subs)
          -- A one-constructor type is irrefutable, and a `Can.Unbox` test would
          -- compare the payload against the constructor's own name. `DecisionTree`
          -- drops those tests for the same reason.
          test =
            if isBool name
              then [(path, DT.IsBool (short == Name.true))]
              else [(path, DT.IsCtor home short (zeroBased tag) alts opts) | alts > 1]
       in (test ++ fst below, snd below)
    Core.PRecord fields ->
      let subs = map (\(f, p) -> compile env root (DT.RecordField f path) p) fields
       in (concatMap fst subs, concatMap snd subs)
    Core.PArray items Nothing ->
      let subs = Index.indexedMap (\i p -> compile env root (DT.ArrayIndex i path) p) items
       in ((path, DT.IsArray (length items)) : concatMap fst subs, concatMap snd subs)
    Core.PArray _ (Just _) ->
      error "Generate.FromCore: an array pattern with a tail — the frontend has no syntax for one"

litTest :: Core.Literal -> DT.Test
litTest lit =
  case lit of
    Core.LIntLegacy n -> DT.IsInt (fromInteger n)
    Core.LInt n -> DT.IsInt (fromIntegral n)
    Core.LInt64 n -> DT.IsInt (fromIntegral n)
    Core.LUInt32 n -> DT.IsInt (fromIntegral n)
    Core.LUInt64 n -> DT.IsInt (fromIntegral n)
    Core.LChar code -> DT.IsChr (jsLiteral [toEnum (fromIntegral code)])
    Core.LString text -> DT.IsStr (jsLiteral (Utf8.toChars text))
    Core.LFloat _ -> error "Generate.FromCore: a float pattern — the frontend rejects one"
    Core.LFloat32 _ -> error "Generate.FromCore: a float pattern — the frontend rejects one"

optPath :: Name -> DT.Path -> Opt.Path
optPath root path =
  case path of
    DT.Empty -> Opt.Root root
    DT.Index index sub -> Opt.Index index (optPath root sub)
    DT.ArrayIndex index sub -> Opt.ArrayIndex index (optPath root sub)
    DT.RecordField name sub -> Opt.Field name (optPath root sub)
    DT.Unbox sub -> Opt.Unbox (optPath root sub)

-- REGIONS

region :: Core.Span -> A.Region
region (Core.Span _ startRow startCol endRow endCol) =
  A.Region
    (A.Position (fromIntegral startRow) (fromIntegral startCol))
    (A.Position (fromIntegral endRow) (fromIntegral endCol))
