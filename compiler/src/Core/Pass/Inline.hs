{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | Small functions inlined across modules, and the cases that leaves known
-- folded away (@docs/m2-beam-toptier.md@ §TT11, D442).
--
-- Every operator in Geng is a function, and after specialization most of them
-- are a short chain of small ones: @n < 2@ at @Int@ is a copy of @Basics.lt@, which
-- calls the @Ord Int@ instance's @compare@, which calls @ltInt@, which is the
-- primitive, and @lt@ then matches the 'Basics.Order' that @compare@ built.
-- A backend that cannot inline across modules — the BEAM cannot — pays every
-- link of it; §TT10.3 measured that as most of @fib@'s time. This pass does
-- what such a compiler's middle end does, and it is Core → Core, so every
-- backend gains:
--
-- > case lt$s… n 2 of …     ⟹     case prim i32_lt n 2 of …
--
-- __What is inlined__: a top-level binding whose value is a lambda, whose body
-- is at most 'sizeLimit' nodes once this pass has run over it (or of any size,
-- when @core@ wrote @\@inline@ on it, D545), that is not
-- part of a recursive group, and whose body is plain data and control — no
-- lambda, no @let rec@, no join, no witness or type node, no task primitive and
-- no reference to an extern. That last set is what keeps the pass out of the
-- places a backend reads a call by name: a boundary row, an extern with a Geng
-- body (D222), a callback. A candidate's body is the /optimized/ body, so a
-- chain collapses from the bottom up; the knot is tied lazily, and it ends
-- because a binding in a recursive group is never looked through.
--
-- __What is folded__, after a call is inlined and anywhere else it applies:
--
--   * a case of a known constructor or literal takes the branch it selects;
--   * a case of a case whose every leaf is known is pushed into the leaves,
--     where the first rule then fires (case-of-case) — only when a branch that
--     would be copied more than once is small;
--   * a @let@ whose body is a case of the name it binds, which nothing else
--     names, is the case of the bound value, evaluated where it was: what
--     inlining @Maybe.withDefault d (get i b)@ leaves, which case-of-case
--     then reaches (geng-lang @m4-visiterm.md@ §VA26, D999);
--   * a case of a @let@ is the @let@ of the case, when the branches name
--     nothing the @let@ binds, so that the two rules above reach the @case@
--     an inlined body such as @Array.get@'s ends in, behind the @let@s it
--     starts with (@m3-bytes-access.md@ §BA12, D544);
--   * a case whose branches are all one nullary constructor or literal, of a
--     scrutinee with no effect, is that constructor;
--   * a case that answers each constructor of its scrutinee with that same
--     constructor is its scrutinee.
--   * a comparison, @Int@ arithmetic or a bitwise primitive of literals is
--     its answer, a shift only by a count in its primitive's @[0, width)@,
--     and a top-level binding that is a literal or a nullary constructor is
--     that, so a constant written as a mask of others is a literal too
--     (geng-lang @m4-visiterm.md@ §VA54, D1023).
--   * a partial application of a global bound by a @let@ and applied at
--     once, with every argument a value, is the one saturated call — what
--     inlining @apR@ leaves of @x |> f a@; and one whose arguments are free
--     of effects, applied once further in, under no lambda or join, which is
--     what inlining a higher-order function leaves of a call that passed one
--     (@Array.Builder.update p (write a b) row@, geng-lang @m4-visiterm.md@
--     §VA16, D982), and one holding a call, which is bound by a @let@ where
--     the partial application was so that the application holds its name
--     (§VA22, D994);
--   * a field of a record written out in place is that field, when the other
--     fields are values — a witness table once specialization has chosen it;
--   * a lambda written out in place and applied at once is its body, the
--     arguments bound as a call's are (m2-beam-toptier.md §TT18).
--
-- Together they turn @lt@'s @compare@-then-match into the one comparison.
--
-- __JavaScript's narrow set__ ('Matched', D792, geng-lang @m3-js-inline.md@):
-- on node the full set slows a real program (D487), and what it is worth
-- there is the constructor a caller matches, §BA4's @Just@ a byte above all.
-- So in this mode a call is opened only
--
--   * where a @case@ matches it, its candidate's every leaf a constructor, a
--     literal or a crash ('answersKnown'), and only when the @case@ is then
--     decided (case-of-case pushes into it, or 'select' takes a branch); or
--   * anywhere, when its candidate is one primitive of its parameters
--     ('onePrim', @core@'s @\@prim@ declarations): the JavaScript backend
--     writes that call as the operator anyway, and as a call it makes a test
--     of it look effectful to 'pure_'.
--
-- and one more fold applies: a @case@ whose branches are all the same
-- expression, nothing bound, of a scrutinee with no effect, is that
-- expression ('sameBranches'), which case-of-case leaves when it copies a
-- branch into two leaves. Every other fold above applies in both modes.
--
-- __Evaluation order is kept__: an argument that is not a variable, literal or
-- nullary constructor is bound by a @let@ where the call was, in order, so it
-- is evaluated exactly when it was before; the only thing ever dropped is a
-- scrutinee 'pure' says has no effect.
--
-- __Names__: every binder in an inlined copy is renamed to a fresh @$nK@, from a
-- counter per definition, so two copies in one function never bind one name.
-- __Spans__ keep saying where the code was written: an inlined node's span
-- names the module it came from, which the target module's file table gains
-- an entry for (C5 anticipated exactly this). __Except where the call was__
-- (D514, geng-lang @m3-native.md@ §NA30): the root of a copy from another file
-- has the call's span, and a case case-of-case rebuilds has the outer case's,
-- so that a debugger, a profiler and a source map find code on the row a
-- person wrote the call or the @when@ on, not only on @core@'s.
--
-- Run after "Core.Pass.Specialize", which makes the chains monomorphic, and
-- before "Core.Pass.Case" and "Core.Pass.TailCall", which then see one
-- program's worth of plain cases.
module Core.Pass.Inline
  ( run,
    runWith,
    Mode (..),

    -- * The pass's account of itself (geng-lang @m4-profile.md@ T3)
    Note (..),
    account,

    -- * For "Core.Pass.FoldSpec" (prototype)
    Space,
    fileSpace,
    toGlobal,
    spaceName,
    spanFiles,
    respan,
    reorder,
  )
where

import Control.Monad.Trans.State.Strict (State, runState, state)
import Core.AST qualified as Core
import Core.Order qualified as Order
import Core.Pass.Specialize qualified as Specialize
import Core.Prim qualified as Prim
import Core.Refs qualified as Refs
import Data.Functor.Identity (Identity (..))
import Data.Graph qualified as Graph
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Monoid (All (..), Sum (..))
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Bits (Bits, complement, shiftL, shiftR, xor, (.&.), (.|.))
import Data.Int (Int32, Int64)
import Data.Word (Word32, Word64)
import Gren.ModuleName qualified as ModuleName

-- KNOBS

-- | The largest body inlined, in nodes. The @Ord Int@ instance's @compare@ is
-- 11 and a specialized @Dict@ comparison a little more; a body this size costs
-- less to copy than the call it replaces costs to make.
sizeLimit :: Int
sizeLimit = 24

-- | The largest branch case-of-case will copy into more than one leaf.
copyLimit :: Int
copyLimit = 8

-- | How many calls one definition may inline, all told. Growth is already
-- bounded by 'sizeLimit' and by the call graph being acyclic where it is looked
-- through; this is the backstop.
fuelPerDefinition :: Int
fuelPerDefinition = 400

-- THE PASS

-- | Which calls are opened: every candidate's ('Full', D442, the BEAM's and
-- native's @inline@), or JavaScript's narrow set ('Matched', D792, its
-- @inlinematch@): see the header.
data Mode = Full | Matched
  deriving (Eq)

run :: Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
run = runWith Full

runWith :: Mode -> Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
runWith mode cores =
  let space = fileSpace cores
      defs =
        Map.fromList
          [ (Core.QualName home (Core._binderName binder), toGlobal space modul value)
          | (home, modul) <- Map.toList cores,
            Core.Bind binder value <- Core._moduleDefs modul
          ]
      externs =
        Set.fromList
          [ Core.QualName home (Core._binderName (Core._externBinder ext))
          | (home, modul) <- Map.toList cores,
            ext <- Core._moduleExterns modul
          ]
      recursive = recursiveNames defs
      marked =
        Set.fromList
          [ q
          | modul <- Map.elems cores,
            q <- Core._moduleInline modul
          ]
      barred q = Set.member q externs || Set.member q recursive

      -- The knot: each definition optimized against the others' optimized
      -- bodies. Lazy, and it ends because 'candidate' refuses a recursive name
      -- before it forces anything.
      optimized = Map.map (optimize mode candidate constant) defs
      classified = Map.mapWithKey classify optimized
      classify q (value, _)
        | barred q = Nothing
        | otherwise =
            case value of
              Core.Expr (Core.ELam params body) tipe _
                | inlinable externs body && (size body <= sizeLimit || Set.member (source q) marked) -> Just (Cand params body tipe)
              _ -> Nothing
      candidate q = Maybe.fromMaybe Nothing (Map.lookup q classified)
      constants = Map.mapWithKey constantOf optimized
      constantOf q (value, _)
        | barred q = Nothing
        | otherwise =
            case Core._exprValue value of
              Core.ELit _ -> Just value
              Core.ECtor _ _ [] -> Just value
              _ -> Nothing
      constant q = Maybe.fromMaybe Nothing (Map.lookup q constants)
   in Map.mapWithKey (rebuild space optimized) cores

-- | The binding a specialized or monomorphic copy was made from: @get$kI4@
-- and @get$s0896c1b6@ are copies of @get@, and what @\@inline@ says of @get@
-- it says of them. A name Geng source can write has no @$@ in it; one that
-- starts with @$@ (an instance's method) is its own.
source :: Core.QualName -> Core.QualName
source q@(Core.QualName home name) =
  case Name.toChars name of
    '$' : _ -> q
    chars -> Core.QualName home (Name.fromChars (takeWhile (/= '$') chars))

data Cand = Cand
  { _candParams :: [Core.Binder],
    _candBody :: Core.Expr,
    _candType :: Core.Type
  }

-- | A body the pass may copy: see the header.
inlinable :: Set Core.QualName -> Core.Expr -> Bool
inlinable externs e =
  ok (Core._exprValue e) && getAll (Specialize.children_ (All . inlinable externs) e)
  where
    ok v =
      case v of
        Core.ELam _ _ -> False
        Core.ELetRec _ _ -> False
        Core.EJoin _ _ -> False
        Core.EJump _ _ -> False
        Core.ETyLam _ _ -> False
        Core.ETyApp _ _ -> False
        Core.EWitLam _ _ -> False
        Core.EWitApp _ _ -> False
        Core.EPrim (Prim.TaskOp _) _ -> False
        Core.EPrim Prim.DebugLog _ -> False
        Core.EGlobal q -> not (Set.member q externs)
        _ -> True

size :: Core.Expr -> Int
size e = 1 + getSum (Specialize.children_ (Sum . size) e)

-- | Every top-level name that can reach itself, through any module.
recursiveNames :: Map Core.QualName Core.Expr -> Set Core.QualName
recursiveNames defs =
  Set.fromList
    [ q
    | Graph.CyclicSCC group <-
        Graph.stronglyConnComp
          [ (q, q, Set.toList (Refs._refGlobals (Refs.refsIn value)))
          | (q, value) <- Map.toList defs
          ],
      q <- group
    ]

-- THE ACCOUNT

-- | A call the pass left a call, where it is and why (geng-lang
-- @m4-profile.md@ T3, D1005): what @geng profile@ joins to a line's cost, so
-- that a costly line says "this @get@ is a call: its body is 27 nodes, the
-- limit is 24", which the surveys read off the C by hand.
data Note = Note
  { _noteHome :: !ModuleName.Canonical,
    _noteRow :: !Word32,
    _noteCol :: !Word32,
    _noteCallee :: !Core.QualName,
    _noteWhy :: !String
  }

-- | Every call to a top-level function in the pass's output, which is the
-- input with every call the pass could open opened, and why each was not: the
-- pass's own rules, asked again of the bodies as the pass left them, which
-- are the optimized bodies it judged. A call to a function the pass would
-- open and did not is one its mode or the call's shape kept: JavaScript's
-- narrow set, a call with more or fewer arguments than the function takes,
-- or the definition's fuel spent.
account :: Mode -> Map ModuleName.Canonical Core.Module -> [Note]
account mode cores =
  let defs =
        Map.fromList
          [ (Core.QualName home (Core._binderName binder), value)
          | (home, modul) <- Map.toList cores,
            Core.Bind binder value <- Core._moduleDefs modul
          ]
      externs =
        Set.fromList
          [ Core.QualName home (Core._binderName (Core._externBinder ext))
          | (home, modul) <- Map.toList cores,
            ext <- Core._moduleExterns modul
          ]
      recursive = recursiveNames defs
      marked = Set.fromList [q | modul <- Map.elems cores, q <- Core._moduleInline modul]
      why q args
        | Set.member q externs = Just "it is an extern"
        | Set.member q recursive = Just "it is recursive, in a group that can reach itself"
        | otherwise =
            case Map.lookup q defs of
              Nothing -> Nothing
              Just (Core.Expr (Core.ELam params body) _ _) ->
                case offence externs body of
                  Just what -> Just ("its body has " ++ what)
                  Nothing
                    | size body > sizeLimit && not (Set.member (source q) marked) ->
                        Just ("its body is " ++ show (size body) ++ " nodes, and the limit is " ++ show sizeLimit)
                    | mode == Matched -> Just "JavaScript's narrow set opens only a call a case is decided by"
                    | length args /= length params ->
                        Just ("it takes " ++ show (length params) ++ " arguments, and it is given " ++ show (length args))
                    | otherwise -> Just "the definition's fuel ran out, or the call is where the pass does not look"
              Just _ -> Just "it is not a function written as one"
      notesIn home modul e =
        let here =
              case Core._exprValue e of
                Core.EApp (Core.Expr (Core.EGlobal q) _ _) args
                  | Just reason <- why q args ->
                      let sp = Core.spanOf e
                          file = Map.findWithDefault home (Core._spanFile sp) (Core._moduleFiles modul)
                       in [Note file (Core._spanStartRow sp) (Core._spanStartCol sp) q reason]
                _ -> []
         in here ++ concat (Specialize.children_ (\c -> [notesIn home modul c]) e)
   in concat
        [ notesIn home modul value
        | (home, modul) <- Map.toList cores,
          Core.Bind _ value <- Core._moduleDefs modul
        ]

-- | What in a body keeps it from being opened, as 'inlinable' judges it: the
-- first node it refuses, said in words.
offence :: Set Core.QualName -> Core.Expr -> Maybe String
offence externs e =
  case own (Core._exprValue e) of
    Just what -> Just what
    Nothing -> Maybe.listToMaybe (concat (Specialize.children_ (\c -> [Maybe.maybeToList (offence externs c)]) e))
  where
    own v =
      case v of
        Core.ELam _ _ -> Just "a lambda"
        Core.ELetRec _ _ -> Just "a recursive let"
        Core.EJoin _ _ -> Just "a join point"
        Core.EJump _ _ -> Just "a jump"
        Core.ETyLam _ _ -> Just "a type abstraction"
        Core.ETyApp _ _ -> Just "a type application"
        Core.EWitLam _ _ -> Just "a witness abstraction"
        Core.EWitApp _ _ -> Just "a witness application"
        Core.EPrim (Prim.TaskOp _) _ -> Just "a task primitive"
        Core.EPrim Prim.DebugLog _ -> Just "a Debug.log"
        Core.EGlobal q | Set.member q externs -> Just "a reference to an extern"
        _ -> Nothing

-- ONE DEFINITION

data St = St
  { _fresh :: !Int,
    _fuel :: !Int,
    _fired :: !Bool
  }

type M a = State St a

-- | A definition optimized, and whether anything in it changed.
-- | What simplifying one expression knows: the candidates, and the locals a
-- @let@ in scope bound to a constructor or a literal, so that a case of one
-- takes its branch as a case of the value itself would. That is the shape an
-- inlined argument leaves (@Encode.unsignedInt8 250@ lets @U8 250@ and then
-- cases on it over every width), and the dead branches it keeps are what
-- @erlc@ and @dialyzer@ warn about.
data Ctx = Ctx
  { _mode :: Mode,
    _candidate :: Core.QualName -> Maybe Cand,
    -- | A top-level binding whose value is a literal or a nullary
    -- constructor, by name: @Ryu.mantissaBits@ is 52, and a guard on it is a
    -- branch @dialyzer@ can see is dead.
    _constant :: Core.QualName -> Maybe Core.Expr,
    _known :: Map Name Core.Expr,
    -- | The locals the definition binds once when its simplifying starts,
    -- other than a name 'fresh' could make: a lambda whose parameters are
    -- all of these can have them bound by @let@s where it stands without
    -- shadowing anything (D780).
    _once :: Set Name
  }

optimize :: Mode -> (Core.QualName -> Maybe Cand) -> (Core.QualName -> Maybe Core.Expr) -> Core.Expr -> (Core.Expr, Bool)
optimize mode candidate constant value =
  let (out, St _ _ changed) = runState (simplify (Ctx mode candidate constant Map.empty (boundOnce value)) value) (St 0 fuelPerDefinition False)
   in (out, changed)

fresh :: M Name
fresh = state (\s -> (Name.fromChars ("$n" ++ show (_fresh s)), s {_fresh = _fresh s + 1}))

markFired :: M ()
markFired = state (\s -> ((), s {_fired = True}))

spend :: M Bool
spend =
  state $ \s ->
    if _fuel s <= 0 then (False, s) else (True, s {_fuel = _fuel s - 1})

-- | Bottom up: the children first, then the node.
simplify :: Ctx -> Core.Expr -> M Core.Expr
simplify ctx e =
  case Core._exprValue e of
    Core.ELet binds body ->
      do
        (binds', ctx') <- letsKnown ctx binds
        body' <- simplify ctx' body
        case unused binds' body' of
          Just [] ->
            do
              markFired
              return body'
          Just kept ->
            do
              markFired
              node ctx' (Core.Expr (Core.ELet kept body') (Core.typeOf e) (Core.spanOf e))
          Nothing ->
            node ctx' (Core.Expr (Core.ELet binds' body') (Core.typeOf e) (Core.spanOf e))
    _ ->
      do
        e' <- Specialize.childrenA (simplify ctx) e
        node ctx e'

-- | A @let@'s bindings without those nothing names any more whose value has no
-- effect, when there are any: a binding left behind is a variable @erlc@ warns
-- is unused, and a record or constructor built for it is "a term is
-- constructed, but never used". Atomic values were the first of these (an
-- atomic value is substituted for its name, and the binding is left); the
-- rest are what a known @case@ leaves when its branch ignores the field it
-- bound, such as the record @Test.Runner.getFailureReason@ answers under a
-- @Just _@ once it is inlined (m2-beam-toptier.md §TT30.5).
--
-- A record or constructor nothing names whose fields are not all free of
-- effects keeps only those fields, in order, each bound to a name made from
-- the binding's: the structure has no effect, and what is computed for it
-- still is, when it was. It is what a case decided by D999's fold leaves of a
-- failure record holding an @inspect@ (geng-lang @m4-visiterm.md@ §VA26).
unused :: [Core.Bind] -> Core.Expr -> Maybe [Core.Bind]
unused binds body =
  let go rest =
        case rest of
          [] -> ([], Refs.freeLocals body, False)
          b@(Core.Bind binder value) : more ->
            -- The names the rest reads are asked for only once a binding
            -- could go: computing them for every binding of a chain of N
            -- is O(N²), which harness/scaling.py's source/let shows.
            let (keptAfter, free, changed) = go more
                named = Set.member (Core._binderName binder) free
                keep = (b : keptAfter, Set.union (Refs.freeLocals value) (Set.delete (Core._binderName binder) free), changed)
             in if pure_ value
                  then if named then keep else (keptAfter, free, True)
                  else case effects binder value of
                    Just parts | not named -> (parts ++ keptAfter, Set.union (Refs.freeLocals value) free, True)
                    _ -> keep
      (kept, _, anyChanged) = go binds
   in if anyChanged then Just kept else Nothing

-- | What of a record or constructor must still be computed: its fields that
-- may have an effect, in order, those that are records or constructors in
-- turn taken apart, each bound to a name made from the binder's.
effects :: Core.Binder -> Core.Expr -> Maybe [Core.Bind]
effects binder value =
  case Core._exprValue value of
    Core.ECtor _ _ args -> Just (concat (zipWith part [0 :: Int ..] args))
    Core.ERecord fields -> Just (concat (zipWith part [0 :: Int ..] (map snd fields)))
    _ -> Nothing
  where
    part i a
      | pure_ a = []
      | otherwise =
          let b = Core.Binder (Name.fromChars (Name.toChars (Core._binderName binder) ++ "$" ++ show i)) (Core.typeOf a) (Core.spanOf a)
           in Maybe.fromMaybe [Core.Bind b a] (effects b a)

-- | A @let@'s bindings in order, each one known to what follows it when its
-- value is a constructor or a literal.
letsKnown :: Ctx -> [Core.Bind] -> M ([Core.Bind], Ctx)
letsKnown ctx binds =
  case binds of
    [] -> return ([], ctx)
    Core.Bind b v : rest ->
      do
        v' <- simplify ctx v
        let ctx1 =
              case knownValue v' of
                Just value -> ctx {_known = Map.insert (Core._binderName b) value (_known ctx)}
                Nothing -> ctx {_known = Map.delete (Core._binderName b) (_known ctx)}
        (rest', ctx2) <- letsKnown ctx1 rest
        return (Core.Bind b v' : rest', ctx2)

node :: Ctx -> Core.Expr -> M Core.Expr
node ctx e@(Core.Expr value tipe sp) =
  case value of
    -- @x |> f a@ and @f a <| x@ are the one call @f a x@, as the JavaScript
    -- backend has always emitted them ('Generate.CoreJS.Expression.apply').
    -- Inlining @apR@'s body instead bound @f a@ to a @let@ and called the
    -- closure it made, which the fold below catches only when every argument
    -- is a value: a curried call and a closure per pipeline step, which cost the
    -- formatter a tenth of its time on node (pre-m3-js.md §JS2, D483). For
    -- @<|@ the order is the same; for @|>@ the moved value is evaluated after
    -- @f@'s arguments, so one of the two sides has to be free of effects.
    Core.EApp (Core.Expr (Core.EGlobal (Core.QualName home name)) _ _) [left, right]
      | home == ModuleName.basics,
        Just (fn, arg, reorders) <- pipe name left right,
        Just call <- appliedTo fn arg,
        not reorders || pure_ arg || all pure_ (earlierOf fn) ->
          do
            markFired
            node ctx (Core.Expr call tipe sp)
    -- A one-primitive wrapper whose primitive takes its parameters in order
    -- is that primitive of the arguments, with no @let@ for an argument that
    -- is not atomic: each argument is still evaluated once, in the order it
    -- was, before the primitive. Bound by a @let@, @total + UInt8.toInt b@
    -- left a block in a tail call's argument, which JavaScript makes and
    -- calls on every iteration (D796, @m3-js-inline.md@ §JI10).
    Core.EApp (Core.Expr (Core.EGlobal q) _ _) args
      | _mode ctx == Matched,
        Just cand@(Cand params (Core.Expr (Core.EPrim op primArgs) _ _) _) <- _candidate ctx q,
        onePrim cand,
        length args == length params,
        [n | Core.Expr (Core.EVar n) _ _ <- primArgs] == map Core._binderName params,
        length primArgs == length params ->
          do
            markFired
            node ctx (Core.Expr (Core.EPrim op args) tipe sp)
    Core.EApp (Core.Expr (Core.EGlobal q) siteType _) args
      | Just cand <- _candidate ctx q,
        _mode ctx == Full || onePrim cand,
        length args == length (_candParams cand) ->
          do
            ok <- spend
            if not ok
              then return e
              else do
                markFired
                inlined <- beta cand siteType args tipe sp
                simplify ctx inlined
    Core.ECase scrut alts fallback ->
      caseOf ctx e scrut alts fallback
    Core.EVar x
      | Just known <- Map.lookup x (_known ctx),
        atomic known,
        Core._exprType known == tipe ->
          do
            markFired
            return (Core.Expr (Core._exprValue known) tipe sp)
    Core.EGlobal q
      | Just (Core.Expr folded _ _) <- _constant ctx q ->
          do
            markFired
            return (Core.Expr folded tipe sp)
    Core.EPrim op args
      | Just folded <- fold op (map Core._exprValue args) ->
          do
            markFired
            return (Core.Expr folded tipe sp)
    -- A partial application bound once and applied at once, which is what
    -- inlining @apR@ leaves of @taskA |> andThen f@: the two argument lists
    -- together are the one call, which a backend makes directly rather than
    -- through the function's curried form (m2-beam-toptier.md §TT14.7).
    -- Every argument is a value, so nothing is evaluated in another order.
    Core.ELet [Core.Bind b bound] (Core.Expr (Core.EApp (Core.Expr (Core.EVar v) _ _) later) _ _)
      | v == Core._binderName b,
        Just (h, earlier) <- partial bound,
        Core.TFun params _ <- Core.typeOf h,
        length earlier + length later == length params,
        not (Set.member v (Set.unions (map Refs.freeLocals later))),
        all evaluated (earlier ++ later) ->
          do
            markFired
            node ctx (Core.Expr (Core.EApp h (earlier ++ later)) tipe sp)
    -- A value bound once and matched at once, which is what inlining
    -- @Maybe.withDefault d (get i b)@ leaves: the case is of the value
    -- itself, evaluated where it was, so that case-of-case reaches the
    -- constructors it is built of (geng-lang @m4-visiterm.md@ §VA26, D999).
    -- Only when the value's type is the name's: a binder may say more than
    -- the value it is bound to does (beta's 'refine'), and a backend reads
    -- a scrutinee's shape from its type, so a case of the value would match
    -- a pointer against an @Int@'s constructors.
    Core.ELet [Core.Bind b bound] (Core.Expr (Core.ECase (Core.Expr (Core.EVar v) vtype _) alts fallback) ctype csp)
      | v == Core._binderName b,
        Core.typeOf bound == Core._binderType b,
        vtype == Core._binderType b,
        not (Set.member v (Set.unions (maybe Set.empty Refs.freeLocals fallback : [Set.difference (Refs.freeLocals body) (Refs.patternBinders p) | Core.Alt p body <- alts]))) ->
          do
            markFired
            node ctx (Core.Expr (Core.ECase bound alts fallback) ctype csp)
    -- The same partial application applied further in: inside the @let@s
    -- and @case@s of the body, but under no lambda, join or recursive group,
    -- so that it runs at most once. It is what inlining a higher-order
    -- function such as @Array.Builder.update@ leaves of @update p (write a b)
    -- row@: the closure bound before the bounds test, and applied in its
    -- branch (geng-lang @m4-visiterm.md@ §VA16, D982). The arguments it holds
    -- are free of effects, so moving them to the call changes nothing but
    -- when they are computed, and nothing on the way binds a name they use.
    Core.ELet [Core.Bind b bound] body
      | Just (h, earlier) <- partial bound,
        Core.TFun params _ <- Core.typeOf h,
        length earlier < length params,
        all pure_ earlier,
        Just body' <- saturateOnce (Core._binderName b) h earlier (length params) body ->
          do
            markFired
            return body'
    -- The same when an argument it holds may have an effect, a call
    -- (@Builder.fill 0 (extentAt y s) blank@): each such argument is bound
    -- by a @let@ where the partial application was, in order, so that it is
    -- computed where and when it was, and the application holds only the
    -- names, which the rule above then moves (geng-lang @m4-visiterm.md@
    -- §VA22, D994). The names are fresh, so nothing on the way binds one.
    Core.ELet [Core.Bind b bound] body
      | Just (h, earlier) <- partial bound,
        Core.TFun params _ <- Core.typeOf h,
        length earlier < length params,
        not (all pure_ earlier) ->
          do
            n0 <- state (\s -> (_fresh s, s))
            let named = snd (List.mapAccumL nameOne n0 earlier)
                nameOne i a
                  | pure_ a = (i, (a, Nothing))
                  | otherwise = (i + 1, (a, Just (Name.fromChars ("$n" ++ show i))))
                args = [maybe a (\x -> Core.Expr (Core.EVar x) (Core.typeOf a) (Core.spanOf a)) mx | (a, mx) <- named]
                bound' = [(x, a) | (a, Just x) <- named]
            case saturateOnce (Core._binderName b) h args (length params) body of
              Nothing -> return e
              Just body' -> do
                state (\s -> ((), s {_fresh = n0 + length bound'}))
                markFired
                return $
                  foldr
                    (\(x, a) acc -> Core.Expr (Core.ELet [Core.Bind (Core.Binder x (Core.typeOf a) (Core.spanOf a)) a] acc) tipe sp)
                    body'
                    bound'
    -- A field of a record written out in place, as a witness table is once
    -- specialization has chosen it: @(record .outbound = f).outbound@ is @f@.
    -- The other fields are values, so dropping them drops nothing but work.
    Core.EAccess (Core.Expr (Core.ERecord fields) _ _) f
      | Just chosen <- lookup f fields,
        all (evaluated . snd) fields ->
          do
            markFired
            return (Core.Expr (Core._exprValue chosen) tipe sp)
    -- The same of a variable a @let@ bound to such a record, when the field is
    -- atomic: an inlined function's record argument (@asciiDelta code { lo =
    -- 65, hi = 90, delta = 32 }@), whose fields then fold as literals do.
    Core.EAccess (Core.Expr (Core.EVar x) _ _) f
      | Just (Core.Expr (Core.ERecord fields) _ _) <- Map.lookup x (_known ctx),
        Just chosen <- lookup f fields,
        atomic chosen,
        Core._exprType chosen == tipe ->
          do
            markFired
            return (Core.Expr (Core._exprValue chosen) tipe sp)
    -- A lambda written out in place and applied at once, as a witness's
    -- method is once the access above has read it: the body, with the
    -- arguments bound as a call's are ('bindAll').
    --
    -- Except a large body no argument can fold anything in (D780): its
    -- parameters are bound by @let@s around it as it is. The body is already
    -- simplified, and renaming and simplifying it again at every level of a
    -- nest of these is n² in its depth (@m3-closeout.md@ §CL19.3). Its names
    -- are kept, so only a lambda whose parameters nothing else in the
    -- definition binds: specialization copies a witness's methods with their
    -- names, and a copy opened inside another would shadow it ('boundOnce').
    Core.EApp (Core.Expr (Core.ELam params body) _ _) args
      | length params == length args ->
          do
            markFired
            if all (\b -> Set.member (Core._binderName b) (_once ctx)) params
              && opensNothing args
              && Core.typeOf body == tipe
              && atLeast openLimit body
              then
                return $
                  foldr
                    (\(binder, arg) acc -> Core.Expr (Core.ELet [Core.Bind (binder {Core._binderType = refine (Core.typeOf arg) (Core._binderType binder)}) arg] acc) tipe sp)
                    body
                    (zip params args)
              else do
                out <- bindAll (zip params args) body tipe sp
                simplify ctx out
    _ -> return e

-- | The size from which a lambda applied at once keeps its body (D780): past
-- 'sizeLimit', so a body the size of anything inlined is simplified again.
openLimit :: Int
openLimit = 64

-- | Arguments that, put in place of a parameter, give no rule anything to
-- fold and that 'bindAll' would bind by a @let@ itself: none is atomic (a
-- variable or a literal, which it substitutes), a constructor, a lambda or a
-- value known itself.
opensNothing :: [Core.Expr] -> Bool
opensNothing =
  all $ \arg ->
    case Core._exprValue arg of
      Core.ELam _ _ -> False
      _ -> not (atomic arg) && Maybe.isNothing (knownValue arg)

-- | The locals bound exactly once in a definition, leaving out the names
-- 'fresh' makes, since one of those could be made again.
boundOnce :: Core.Expr -> Set Name
boundOnce value =
  Map.keysSet (Map.filterWithKey (\n k -> k == (1 :: Int) && not (List.isPrefixOf "$n" (Name.toChars n))) (go Map.empty [value]))
  where
    go counts pending =
      case pending of
        [] -> counts
        x : rest ->
          let counts' = List.foldl' (\m b -> Map.insertWith (+) (Core._binderName b) 1 m) counts (bindersOf (Core._exprValue x))
           in counts' `seq` go counts' (Specialize.children_ (: []) x ++ rest)

-- | Whether an expression has at least @k@ nodes, counting no more than that.
atLeast :: Int -> Core.Expr -> Bool
atLeast k e = count k [e] <= 0
  where
    count n pending =
      case pending of
        [] -> n
        x : rest
          | n <= 0 -> n
          | otherwise -> count (n - 1) (Specialize.children_ (: []) x ++ rest)

-- | Which side of a pipe is the function, which the value, and whether
-- applying one to the other moves the value after the function's arguments.
pipe :: Name -> Core.Expr -> Core.Expr -> Maybe (Core.Expr, Core.Expr, Bool)
pipe name left right
  | name == Name.fromChars "apR" = Just (right, left, True)
  | name == Name.fromChars "apL" = Just (left, right, False)
  | otherwise = Nothing

-- | A function expression given one more argument, when that makes a saturated
-- call: a global given all but its last, a global or a local of one parameter,
-- or a lambda of one, which the fold of a lambda applied at once then opens.
appliedTo :: Core.Expr -> Core.Expr -> Maybe Core.Expr_
appliedTo fn arg =
  case Core._exprValue fn of
    Core.EApp h@(Core.Expr (Core.EGlobal _) _ _) args
      | Core.TFun params _ <- Core.typeOf h,
        length args + 1 == length params ->
          Just (Core.EApp h (args ++ [arg]))
    Core.ELam [_] _ -> Just (Core.EApp fn [arg])
    _
      | Core.TFun [_] _ <- Core.typeOf fn,
        isName (Core._exprValue fn) ->
          Just (Core.EApp fn [arg])
    _ -> Nothing
  where
    isName v = case v of Core.EGlobal _ -> True; Core.EVar _ -> True; _ -> False

-- | @body@ with the one application of @v@ that saturates @h@ given @earlier@
-- made that call ('node''s second partial-application fold). 'Nothing' when
-- @v@ is used any other way, more than once, under a lambda, a join or a
-- recursive group, or below a binder of a name @earlier@ uses.
saturateOnce :: Name -> Core.Expr -> [Core.Expr] -> Int -> Core.Expr -> Maybe Core.Expr
saturateOnce v h earlier arity body =
  case go body of
    Just (1, body') -> Just body'
    _ -> Nothing
  where
    names = Set.unions (map Refs.freeLocals earlier)
    clear bs = clearNames (map Core._binderName bs)
    clearNames ns = not (any (\x -> Set.member x names || x == v) ns)
    many :: [Core.Expr] -> Maybe (Int, [Core.Expr])
    many es = do
      rs <- mapM go es
      Just (sum (map fst rs), map snd rs)
    go :: Core.Expr -> Maybe (Int, Core.Expr)
    go e@(Core.Expr value t sp)
      | not (Set.member v (Refs.freeLocals e)) = Just (0, e)
      | otherwise =
          case value of
            Core.EApp (Core.Expr (Core.EVar x) _ _) later
              | x == v,
                length earlier + length later == arity,
                not (Set.member v (Set.unions (map Refs.freeLocals later))) ->
                  Just (1, Core.Expr (Core.EApp h (earlier ++ later)) t sp)
            Core.EApp f args -> do
              (n, f') <- go f
              (m, args') <- many args
              Just (n + m, Core.Expr (Core.EApp f' args') t sp)
            Core.ELet binds rest
              | clear (map Core._bindBinder binds) -> do
                  (n, vs) <- many (map Core._bindValue binds)
                  (m, rest') <- go rest
                  Just (n + m, Core.Expr (Core.ELet (zipWith (\(Core.Bind bb _) v' -> Core.Bind bb v') binds vs) rest') t sp)
            Core.ECase scrut alts fallback
              | clearNames (concatMap (Set.toList . Refs.patternBinders . Core._altPattern) alts) -> do
                  (n, scrut') <- go scrut
                  (m, bodies) <- many (map Core._altBody alts)
                  (k, fallback') <- case fallback of
                    Nothing -> Just (0, Nothing)
                    Just f -> do
                      (k, f') <- go f
                      Just (k, Just f')
                  Just (n + m + k, Core.Expr (Core.ECase scrut' (zipWith (\(Core.Alt p _) b' -> Core.Alt p b') alts bodies) fallback') t sp)
            Core.ECtor q i args -> do
              (n, args') <- many args
              Just (n, Core.Expr (Core.ECtor q i args') t sp)
            Core.ERecord fields -> do
              (n, vs) <- many (map snd fields)
              Just (n, Core.Expr (Core.ERecord (zip (map fst fields) vs)) t sp)
            Core.EUpdate record fields w -> do
              (n, record') <- go record
              (m, vs) <- many (map snd fields)
              Just (n + m, Core.Expr (Core.EUpdate record' (zip (map fst fields) vs) w) t sp)
            Core.EAccess record f -> do
              (n, record') <- go record
              Just (n, Core.Expr (Core.EAccess record' f) t sp)
            Core.EArray items -> do
              (n, items') <- many items
              Just (n, Core.Expr (Core.EArray items') t sp)
            Core.EPrim op args -> do
              (n, args') <- many args
              Just (n, Core.Expr (Core.EPrim op args') t sp)
            _ -> Nothing

-- | The arguments a function expression already holds.
earlierOf :: Core.Expr -> [Core.Expr]
earlierOf fn =
  case Core._exprValue fn of
    Core.EApp _ args -> args
    _ -> []

-- | A global applied to fewer arguments than it takes, or named alone.
partial :: Core.Expr -> Maybe (Core.Expr, [Core.Expr])
partial e =
  case Core._exprValue e of
    Core.EGlobal _ -> Just (e, [])
    Core.EApp h@(Core.Expr (Core.EGlobal _) _ _) args -> Just (h, args)
    _ -> Nothing

-- | Evaluated already: an atomic expression, a global, a lambda, or a global
-- given fewer arguments than it takes, each of them evaluated, which builds a
-- closure and runs nothing.
evaluated :: Core.Expr -> Bool
evaluated e =
  case Core._exprValue e of
    Core.EGlobal _ -> True
    Core.ELam _ _ -> True
    Core.EApp h@(Core.Expr (Core.EGlobal _) _ _) args
      | Core.TFun params _ <- Core.typeOf h ->
          length args < length params && all evaluated args
    _ -> atomic e

-- | A primitive of literals, computed: what inlining a comparison of two
-- constants leaves (@clamp 0 2147483647 0@ in @Dict.keys@, @negate 3 == 0@), and which a
-- backend's own checker otherwise reports as a branch that cannot be taken —
-- @dialyzer@ does. 'Int32' arithmetic in Haskell wraps as D2's does.
fold :: Prim.PrimOp -> [Core.Expr_] -> Maybe Core.Expr_
fold op args =
  case (op, args) of
    -- A shift's count is an @Int@ at every width (A5), so it comes before
    -- the @i32@ case, whose two arguments are @Int@s too.
    (Prim.IntOp t p, [Core.ELit a, Core.ELit (Core.LInt n)])
      | p == Prim.IShl || p == Prim.IShr || p == Prim.IUshr ->
          case (t, a) of
            (Prim.I32, Core.LInt x) -> shifted Core.LInt 32 (fromIntegral :: Int32 -> Word32) fromIntegral p x n
            (Prim.I64, Core.LInt64 x) -> shifted Core.LInt64 64 (fromIntegral :: Int64 -> Word64) fromIntegral p x n
            (Prim.U32, Core.LUInt32 x) -> shifted Core.LUInt32 32 id id p x n
            (Prim.U64, Core.LUInt64 x) -> shifted Core.LUInt64 64 id id p x n
            _ -> Nothing
    (Prim.IntOp Prim.I32 p, [Core.ELit (Core.LInt a), Core.ELit (Core.LInt b)]) ->
      case p of
        Prim.IAdd -> Just (Core.ELit (Core.LInt (a + b)))
        Prim.ISub -> Just (Core.ELit (Core.LInt (a - b)))
        Prim.IMul -> Just (Core.ELit (Core.LInt (a * b)))
        Prim.IEq -> Just (bool (a == b))
        Prim.ILt -> Just (bool (a < b))
        _ -> logical Core.LInt p a b
    (Prim.IntOp Prim.I64 p, [Core.ELit (Core.LInt64 a), Core.ELit (Core.LInt64 b)]) -> arith Core.LInt64 p a b
    (Prim.IntOp Prim.U32 p, [Core.ELit (Core.LUInt32 a), Core.ELit (Core.LUInt32 b)]) -> arith Core.LUInt32 p a b
    (Prim.IntOp Prim.U64 p, [Core.ELit (Core.LUInt64 a), Core.ELit (Core.LUInt64 b)]) -> arith Core.LUInt64 p a b
    (Prim.StrOp Prim.SEq, [Core.ELit (Core.LString a), Core.ELit (Core.LString b)]) -> Just (bool (a == b))
    (Prim.IntOp Prim.I32 Prim.INeg, [Core.ELit (Core.LInt a)]) -> Just (Core.ELit (Core.LInt (negate a)))
    (Prim.IntOp Prim.I64 Prim.INeg, [Core.ELit (Core.LInt64 a)]) -> Just (Core.ELit (Core.LInt64 (negate a)))
    (Prim.IntOp Prim.I32 Prim.INot, [Core.ELit (Core.LInt a)]) -> Just (Core.ELit (Core.LInt (complement a)))
    (Prim.IntOp Prim.I64 Prim.INot, [Core.ELit (Core.LInt64 a)]) -> Just (Core.ELit (Core.LInt64 (complement a)))
    (Prim.IntOp Prim.U32 Prim.INot, [Core.ELit (Core.LUInt32 a)]) -> Just (Core.ELit (Core.LUInt32 (complement a)))
    (Prim.IntOp Prim.U64 Prim.INot, [Core.ELit (Core.LUInt64 a)]) -> Just (Core.ELit (Core.LUInt64 (complement a)))
    _ -> Nothing
  where
    -- 'Int64', 'Word32' and 'Word64' wrap as the widths they stand for do.
    arith :: (Integral a, Bits a) => (a -> Core.Literal) -> Prim.IntPrim -> a -> a -> Maybe Core.Expr_
    arith lit p a b =
      case p of
        Prim.IAdd -> Just (Core.ELit (lit (a + b)))
        Prim.ISub -> Just (Core.ELit (lit (a - b)))
        Prim.IMul -> Just (Core.ELit (lit (a * b)))
        Prim.IEq -> Just (bool (a == b))
        Prim.ILt -> Just (bool (a < b))
        _ -> logical lit p a b

    -- Two's complement at the literal's own width, as every backend does it.
    logical :: (Bits a) => (a -> Core.Literal) -> Prim.IntPrim -> a -> a -> Maybe Core.Expr_
    logical lit p a b =
      case p of
        Prim.IAnd -> Just (Core.ELit (lit (a .&. b)))
        Prim.IOr -> Just (Core.ELit (lit (a .|. b)))
        Prim.IXor -> Just (Core.ELit (lit (xor a b)))
        _ -> Nothing

    -- The raw primitive's precondition is a count in @[0, width)@ (A4, which
    -- @Bitwise@ clamps to in Geng before it calls one); outside it nothing is
    -- computed. @shr@ is arithmetic on a signed value; @ushr@ shifts the
    -- value's unsigned reading, its bits as they are.
    shifted :: (Bits a, Bits u) => (a -> Core.Literal) -> Int32 -> (a -> u) -> (u -> a) -> Prim.IntPrim -> a -> Int32 -> Maybe Core.Expr_
    shifted lit width toU fromU p a n
      | n < 0 || n >= width = Nothing
      | otherwise =
          let k = fromIntegral n
           in case p of
                Prim.IShl -> Just (Core.ELit (lit (shiftL a k)))
                Prim.IShr -> Just (Core.ELit (lit (shiftR a k)))
                Prim.IUshr -> Just (Core.ELit (lit (fromU (shiftR (toU a) k))))
                _ -> Nothing

    bool b =
      if b
        then Core.ECtor (Core.QualName ModuleName.basics (Name.fromChars "True")) 0 []
        else Core.ECtor (Core.QualName ModuleName.basics (Name.fromChars "False")) 1 []

-- | A candidate applied to its arguments: its body, freshly named, with each
-- parameter replaced by its argument when that is atomic and bound by a @let@
-- where the call was when it is not.
beta :: Cand -> Core.Type -> [Core.Expr] -> Core.Type -> Core.Span -> M Core.Expr
beta (Cand params body declared) siteType args tipe sp =
  let sub = Specialize.matchT (Specialize.unquantified declared) siteType
      fix = if Map.null sub then id else Specialize.substituteT sub
      body' = if Map.null sub then body else Specialize.retype fix body
      params' = [p {Core._binderType = fix (Core._binderType p)} | p <- params]
   in bindAll (zip params' args) body' tipe sp

-- | Bind each binder to its expression around a body, as 'beta' says, and
-- rename the body's own binders fresh.
--
-- __A parameter bound by a @let@, and the result, keep what both types say.__
-- The candidate's types and the call site's are the same for a candidate
-- 'beta' instantiated, and they are not for a copy "Core.Pass.Mono" made,
-- whose types are shapes: @apR$kPP@'s @x@ is @$P@ where its argument is
-- @{ offset : Int, t : Transient }@, and a field read from the variable the
-- inliner bound it to had lost the record it reads. Nor is the call site
-- always the specific side: a lambda inlined at @f x@ inside @Maybe.map$kPP@
-- builds a record whose call is typed @$P@ (@m3-native.md@ §NA21). D498 lays a
-- shape and the type it stands for out alike, so 'refine' keeps the concrete
-- side of every shape it meets.
bindAll :: [(Core.Binder, Core.Expr)] -> Core.Expr -> Core.Type -> Core.Span -> M Core.Expr
bindAll pairs body tipe sp =
  go pairs Map.empty []
  where
    go rest env lets =
      case rest of
        [] ->
          do
            body' <- freshen env body
            let -- D514: a body from another file stands at the call.
                at =
                  if Core._spanFile (Core.spanOf body') == Core._spanFile sp
                    then Core.spanOf body'
                    else sp
                typed = (refineTails tipe body') {Core._exprSpan = at}
            return (foldr (\b acc -> Core.Expr (Core.ELet [b] acc) tipe sp) typed (reverse lets))
        (binder, arg) : more
          | atomic arg || fieldOfLocal arg ->
              go more (Map.insert (Core._binderName binder) arg env) lets
          | lambda arg && uses (Core._binderName binder) body == 1 ->
              -- A lambda is a value, so making it where it is used rather than
              -- where the call was changes nothing, and a candidate's body has no
              -- lambda of its own for the one use to sit under. Bound by a @let@
              -- it would be a closure called through a variable, which the
              -- lambda-applied-at-once fold below cannot see: inlining @<|@ or
              -- @|>@ with a lambda made exactly that (@pre-m3-js.md@ §JS2, D483).
              go more (Map.insert (Core._binderName binder) arg env) lets
          | otherwise ->
              do
                n <- fresh
                let known = refine (Core.typeOf arg) (Core._binderType binder)
                    binder' = binder {Core._binderName = n, Core._binderType = known}
                    var = Core.Expr (Core.EVar n) known (Core._binderSpan binder)
                go more (Map.insert (Core._binderName binder) var env) (Core.Bind binder' arg : lets)

-- | The call's type refined into the inlined body and each of its tails: a
-- @let@'s body, a @case@'s alternatives and fallback, a join's body. A later
-- pass that floats the body's lets out of a scrutinee binds what is left by its
-- own type, and a copy "Core.Pass.Mono" made types it by shape: @Array.get@
-- inlined at a call typed @Maybe Piece@ left its inner @case@ typed
-- @Maybe $P@, the case pass typed @Just@'s field @$P@ from it, and the C
-- backend, not knowing the field was a @Piece@, switched on the pointer
-- (geng-lang @m3-array.md@ §AR13).
refineTails :: Core.Type -> Core.Expr -> Core.Expr
refineTails tipe e =
  let value =
        case Core._exprValue e of
          Core.ELet binds body -> Core.ELet binds (refineTails tipe body)
          Core.ELetRec binds body -> Core.ELetRec binds (refineTails tipe body)
          Core.ECase scrut alts fallback ->
            Core.ECase
              scrut
              [alt {Core._altBody = refineTails tipe (Core._altBody alt)} | alt <- alts]
              (fmap (refineTails tipe) fallback)
          Core.EJoin joins body -> Core.EJoin joins (refineTails tipe body)
          other -> other
   in e {Core._exprValue = value, Core._exprType = refine (Core.typeOf e) tipe}

-- | Two types of one value, as one: where one is a shape type ("Core.Pass.Mono"'s
-- @$P@, @$I4@ and the rest) and the other is not, the other; where both have
-- structure, the structure refined; otherwise the first.
refine :: Core.Type -> Core.Type -> Core.Type
refine a b =
  case (a, b) of
    -- One interned type, compared by its id: what the walk below would
    -- answer, without walking a type as tall as a nest is deep (D780).
    _ | a == b -> a
    _ | isShape a -> b
    _ | isShape b -> a
    (Core.TCon q xs, Core.TCon q' ys)
      | q == q', length xs == length ys -> Core.TCon q (zipWith refine xs ys)
    (Core.TFun xs r, Core.TFun ys r')
      | length xs == length ys -> Core.TFun (zipWith refine xs ys) (refine r r')
    (Core.TRecord fs row, Core.TRecord gs _)
      | map fst fs == map fst gs -> Core.TRecord (zipWith (\(f, x) (_, y) -> (f, refine x y)) fs gs) row
    _ -> a
  where
    isShape t =
      case t of
        Core.TCon (Core.QualName home name) []
          | home == ModuleName.basics -> take 1 (Name.toChars name) == "$"
        _ -> False

-- | A lambda written out.
lambda :: Core.Expr -> Bool
lambda e =
  case Core._exprValue e of
    Core.ELam _ _ -> True
    _ -> False

-- | How many times a local name is read in an expression.
uses :: Name -> Core.Expr -> Int
uses name e =
  case Core._exprValue e of
    Core.EVar n | n == name -> 1
    _ -> getSum (Specialize.children_ (Sum . uses name) e)

-- | Free of effects and cheap enough to copy: a variable, a literal, a
-- constructor with no fields.
atomic :: Core.Expr -> Bool
atomic e =
  case Core._exprValue e of
    Core.EVar _ -> True
    Core.ELit _ -> True
    Core.ECtor _ _ [] -> True
    _ -> False

-- | A field of a local, or of one of its fields: substituted at each use as
-- the local is, rather than bound to a local of its own, which would be a
-- second name for what the field holds (geng-lang @m4-visiterm.md@ §VA52).
fieldOfLocal :: Core.Expr -> Bool
fieldOfLocal e =
  case Core._exprValue e of
    Core.EAccess base _ ->
      case Core._exprValue base of
        Core.EVar _ -> True
        _ -> fieldOfLocal base
    _ -> False

-- | Free of effects: dropping it changes nothing but the time taken.
pure_ :: Core.Expr -> Bool
pure_ e =
  case Core._exprValue e of
    Core.EVar _ -> True
    Core.ELit _ -> True
    Core.EGlobal _ -> True
    Core.ELam _ _ -> True
    Core.ELet binds body -> all (\(Core.Bind _ v) -> pure_ v) binds && pure_ body
    Core.ECtor _ _ args -> all pure_ args
    Core.ERecord fields -> all (pure_ . snd) fields
    Core.EAccess record _ -> pure_ record
    Core.EUpdate record fields _ -> pure_ record && all (pure_ . snd) fields
    Core.EArray items -> all pure_ items
    Core.EPrim op args -> comparison op && all pure_ args
    _ -> False
  where
    comparison op =
      case op of
        Prim.IntOp _ Prim.IEq -> True
        Prim.IntOp _ Prim.ILt -> True
        Prim.FloatOp _ Prim.FEq -> True
        Prim.FloatOp _ Prim.FLt -> True
        Prim.StrOp Prim.SEq -> True
        _ -> False

-- CASES

-- | The branches with every pattern variable their bodies do not name made
-- @_@, and every alias they do not name its own pattern, when that changes
-- any. A variable nothing reads is a value the backend binds for nothing, and
-- on the BEAM more than that: a flat constructor's pattern (D443) that binds
-- its record builds the record back as a map after the match, which @erlc@
-- warns "is constructed, but never used" when the branch ignores it, as
-- @Test.Runner.getFailureReason@'s @Fail _@ does once it is inlined
-- (m2-beam-toptier.md §TT30.5).
thinned :: [Core.Alt] -> Maybe [Core.Alt]
thinned alts =
  let thinAlt alt@(Core.Alt p b) =
        if Set.null (Refs.patternBinders p) then alt else Core.Alt (thin (Refs.freeLocals b) p) b
      alts' = map thinAlt alts
   in if map Core._altPattern alts' /= map Core._altPattern alts then Just alts' else Nothing

thin :: Set Name -> Core.Pattern -> Core.Pattern
thin free p =
  case p of
    Core.PVar b
      | not (Set.member (Core._binderName b) free) -> Core.PWild
    Core.PAs b inner
      | not (Set.member (Core._binderName b) free) -> thin free inner
      | otherwise -> Core.PAs b (thin free inner)
    Core.PCtor q tag args ->
      Core.PCtor q tag (map (thin free) args)
    Core.PRecord fields ->
      Core.PRecord [(field, thin free q) | (field, q) <- fields]
    Core.PArray items tailBinder ->
      Core.PArray (map (thin free) items) tailBinder
    _ -> p

caseOf :: Ctx -> Core.Expr -> Core.Expr -> [Core.Alt] -> Maybe Core.Expr -> M Core.Expr
caseOf ctx e scrut alts fallback =
  case known of
    Nothing
      | _mode ctx == Matched,
        Core.EApp (Core.Expr (Core.EGlobal q) siteType _) args <- Core._exprValue scrut,
        Just cand <- _candidate ctx q,
        length args == length (_candParams cand),
        answersKnown (_candBody cand) ->
          do
            ok <- spend
            if not ok
              then return e
              else do
                inlined <- beta cand siteType args (Core.typeOf scrut) (Core.spanOf scrut)
                scrut' <- simplify ctx inlined
                -- Only when the case is then decided: a body case-of-case
                -- will not push into (a branch too large to copy, a name it
                -- would capture) stays a call, since opened it is the same
                -- constructor built in place of the call, inside a function
                -- JavaScript makes and calls (m3-js-inline.md §JI3).
                if decides scrut'
                  then do
                    markFired
                    node ctx (Core.Expr (Core.ECase scrut' alts fallback) (Core.typeOf e) (Core.spanOf e))
                  else return e
    Nothing
      | _mode ctx == Matched,
        Just same <- sameBranches scrut alts fallback ->
          do
            markFired
            return same
    Just (Chosen binds body) ->
      do
        markFired
        out <- bindAll binds body (Core.typeOf e) (Core.spanOf e)
        simplify ctx out
    Just (Crashes crash) ->
      do
        markFired
        return (Core.Expr crash (Core.typeOf e) (Core.spanOf e))
    -- One branch whose pattern always matches and binds nothing, of a
    -- scrutinee that may have an effect, which D999's fold can leave of a
    -- record matched field by field with wildcards: the scrutinee bound by
    -- a @let@ nothing names, which 'unused' then takes down to what of it
    -- must still be computed (geng-lang @m4-visiterm.md@ §VA26).
    Nothing
      | [Core.Alt p body] <- alts,
        ignores (Refs.freeLocals body) p ->
          do
            markFired
            n <- fresh
            simplify ctx (Core.Expr (Core.ELet [Core.Bind (Core.Binder n (Core.typeOf scrut) (Core.spanOf scrut)) scrut] body) (Core.typeOf e) (Core.spanOf e))
      | Just floated <- letOfCase e scrut alts fallback ->
          do
            markFired
            simplify ctx floated
      | Just pushed <- caseOfCase e scrut alts fallback ->
          do
            markFired
            simplify ctx pushed
      | Just same <- allSame scrut alts fallback ->
          do
            markFired
            return same
      | identity e scrut alts fallback ->
          do
            markFired
            return scrut
      | Just kept <- pruned ->
          do
            markFired
            return (Core.Expr (Core.ECase scrut kept fallback) (Core.typeOf e) (Core.spanOf e))
      | Just thinnedAlts <- thinned alts ->
          do
            markFired
            return (Core.Expr (Core.ECase scrut thinnedAlts fallback) (Core.typeOf e) (Core.spanOf e))
      | otherwise -> return e
  where
    decides s =
      case Core._exprValue s of
        Core.ELet _ inner ->
          Maybe.isJust (letOfCase e s alts fallback) && decides inner
        _ -> Maybe.isJust (select s alts fallback) || Maybe.isJust (caseOfCase e s alts fallback)

    -- A known value whose branch cannot be taken whole (its pattern binds a
    -- field that is not atomic) still rules out every branch of another
    -- constructor, and those are dropped: they are the clauses @erlc@ says
    -- cannot match.
    pruned =
      case Core._exprValue scrut of
        Core.EVar x
          | Just value <- Map.lookup x (_known ctx) ->
              let kept = [alt | alt@(Core.Alt p _) <- alts, not (isNoMatch (matchBound scrut value p))]
               in if length kept < length alts && not (null kept) then Just kept else Nothing
        _ -> Nothing

    isNoMatch m =
      case m of
        NoMatch -> True
        _ -> False

    -- A variable a @let@ bound to a constructor is decided as the
    -- constructor would be, except that a field is not copied unless it is
    -- atomic: it was evaluated where it was bound, and is not again.
    known =
      case Core._exprValue scrut of
        Core.EVar x
          | Just value <- Map.lookup x (_known ctx) ->
              case selectBy (matchBound scrut value) value alts fallback of
                Just (Chosen binds body) -> Just (Chosen binds body)
                _ -> Nothing
        _ -> select scrut alts fallback

-- | A pattern that matches every value of its type and binds nothing the
-- branch reads: a wildcard, a name not among @used@, or a record of them.
ignores :: Set Name -> Core.Pattern -> Bool
ignores used p =
  case p of
    Core.PWild -> True
    Core.PVar b -> not (Set.member (Core._binderName b) used)
    Core.PRecord fields -> all (ignores used . snd) fields
    _ -> False

data Selected
  = Chosen [(Core.Binder, Core.Expr)] Core.Expr
  | Crashes Core.Expr_

data Match
  = Match [(Core.Binder, Core.Expr)]
  | NoMatch
  | Unknown

-- | The branch a known scrutinee takes, if it can be told.
select :: Core.Expr -> [Core.Alt] -> Maybe Core.Expr -> Maybe Selected
select scrut = selectBy (match scrut) scrut

-- | 'select' with the matching rule given, for 'matchBound'.
selectBy :: (Core.Pattern -> Match) -> Core.Expr -> [Core.Alt] -> Maybe Core.Expr -> Maybe Selected
selectBy matching scrut alts fallback =
  case Core._exprValue scrut of
    Core.ECrash kind -> Just (Crashes (Core.ECrash kind))
    Core.ECtor _ _ _ -> walk alts
    Core.ELit _ -> walk alts
    _ -> Nothing
  where
    walk rest =
      case rest of
        [] -> fmap (Chosen []) fallback
        Core.Alt pattern body : more ->
          case matching pattern of
            Match binds -> Just (Chosen binds body)
            NoMatch -> walk more
            Unknown -> Nothing

-- | What a @let@'s value is known to be: a constructor, a literal or a record
-- written out, or a constructor or literal at the end of @let@s. Behind a @let@ the constructor's fields may name what
-- that @let@ bound, which is out of scope at the case, so they are kept only
-- as their types: 'matchBound' binds no field that is not atomic, and an
-- 'Core.Unreachable' crash is not.
knownValue :: Core.Expr -> Maybe Core.Expr
knownValue v =
  case Core._exprValue v of
    Core.ECtor _ _ _ -> Just v
    Core.ELit _ -> Just v
    Core.ERecord _ -> Just v
    Core.ELet _ body ->
      case knownValue body of
        Just (Core.Expr (Core.ECtor q tag args) t sp) ->
          Just (Core.Expr (Core.ECtor q tag [Core.Expr (Core.ECrash Core.Unreachable) (Core.typeOf a) (Core.spanOf a) | a <- args]) t sp)
        -- A record's fields are what its access reads, and behind a @let@ they
        -- may name what the @let@ bound, so such a record is not known.
        Just (Core.Expr (Core.ERecord _) _ _) -> Nothing
        other -> other
    _ -> Nothing

-- | 'match' against the value a variable was bound to: the variable, not the
-- value, is what a pattern binding the whole is bound to, and a field is bound
-- only when it is atomic.
matchBound :: Core.Expr -> Core.Expr -> Core.Pattern -> Match
matchBound var value pattern =
  case (pattern, Core._exprValue value) of
    (Core.PVar b, _) -> Match [(b, var)]
    (Core.PCtor _ tag subs, Core.ECtor _ tag' args)
      | tag /= tag' -> NoMatch
      | length subs /= length args -> Unknown
      | otherwise -> maybe Unknown (Match . concat) (traverse field (zip subs args))
    _ -> match value pattern
  where
    field (sub, arg) =
      case sub of
        Core.PWild -> Just []
        Core.PVar b | atomic arg -> Just [(b, arg)]
        _ -> Nothing

match :: Core.Expr -> Core.Pattern -> Match
match scrut pattern =
  case (pattern, Core._exprValue scrut) of
    (Core.PWild, _) -> Match []
    (Core.PVar b, _) -> Match [(b, scrut)]
    (Core.PCtor _ tag subs, Core.ECtor _ tag' args)
      | tag /= tag' -> NoMatch
      | length subs /= length args -> Unknown
      | otherwise ->
          maybe Unknown (Match . concat) (traverse field (zip subs args))
    (Core.PLit lit, Core.ELit lit')
      | float lit || float lit' -> Unknown
      | lit == lit' -> Match []
      | otherwise -> NoMatch
    _ -> Unknown
  where
    field (sub, arg) =
      case sub of
        Core.PVar b -> Just [(b, arg)]
        -- A field nobody names is still evaluated, as it was before.
        Core.PWild
          | atomic arg -> Just []
          | otherwise -> Just [(Core.Binder "$" (Core.typeOf arg) (Core.spanOf arg), arg)]
        _ -> Nothing
    float lit =
      case lit of
        Core.LFloat _ -> True
        Core.LFloat32 _ -> True
        _ -> False

-- | @case (let bs in e) of alts@ is @let bs in case e of alts@ (D544). The
-- bindings were evaluated before a branch was chosen either way, so nothing
-- moves in time; a name they bind that a branch or the fallback also names
-- from outside would be captured, and then the case is left as it is. Without
-- it an inlined body that starts with a @let@ hides its known leaves from
-- 'caseOfCase': @Array.get@ opened in a loop still built its @Just@ natively,
-- and the loop took 98 ms where it takes 6 with this (§BA12.1).
letOfCase :: Core.Expr -> Core.Expr -> [Core.Alt] -> Maybe Core.Expr -> Maybe Core.Expr
letOfCase outer scrut alts fallback =
  case Core._exprValue scrut of
    Core.ELet binds inner
      | Set.null (Set.intersection bound free) ->
          Just (Core.Expr (Core.ELet binds (Core.Expr (Core.ECase inner alts fallback) tipe sp)) tipe sp)
      where
        bound = Set.fromList (map (Core._binderName . Core._bindBinder) binds)
        free =
          Set.unions $
            maybe Set.empty Refs.freeLocals fallback
              : [Set.difference (Refs.freeLocals b) (Refs.patternBinders p) | Core.Alt p b <- alts]
    _ -> Nothing
  where
    tipe = Core.typeOf outer
    sp = Core.spanOf outer

-- | Case-of-case: when every leaf of the inner case is a known value, the outer
-- case moves into the leaves, where 'select' then decides each.
caseOfCase :: Core.Expr -> Core.Expr -> [Core.Alt] -> Maybe Core.Expr -> Maybe Core.Expr
caseOfCase outer scrut alts fallback =
  case Core._exprValue scrut of
    Core.ECase _ _ _ ->
      let found = leaves scrut
          chosen = map (\(leaf, _) -> choice leaf) found
          bound = Set.unions (map snd found)
          free =
            Set.unions $
              maybe Set.empty Refs.freeLocals fallback
                : [Set.difference (Refs.freeLocals b) (Refs.patternBinders p) | Core.Alt p b <- alts]
          copies = Map.fromListWith (+) [(i, 1 :: Int) | Just (Just i) <- chosen]
          branchSize i = maybe (maybe 0 size fallback) (size . Core._altBody) (index i)
          index i = if i < 0 then Nothing else Just (alts !! i)
       in if all Maybe.isJust chosen
            && Set.null (Set.intersection bound free)
            && and [branchSize i <= copyLimit | (i, n) <- Map.toList copies, n > 1]
            then Just (push scrut)
            else Nothing
    _ -> Nothing
  where
    outerType = Core.typeOf outer
    outerSpan = Core.spanOf outer

    -- Which branch a leaf selects: 'Just' the index, -1 for the fallback.
    choice leaf =
      case Core._exprValue leaf of
        Core.ECrash _ -> Just Nothing
        _ ->
          case select leaf alts fallback of
            Just (Chosen _ _) -> Just (Just (branchIndex leaf))
            Just (Crashes _) -> Just Nothing
            Nothing -> Nothing

    branchIndex leaf =
      Maybe.fromMaybe (-1) (List.findIndex (\(Core.Alt p _) -> case match leaf p of Match _ -> True; _ -> False) alts)

    push e =
      case Core._exprValue e of
        Core.ECase s inner fb ->
          -- D514: the case that decides is the outer one's, where it was written.
          Core.Expr (Core.ECase s [Core.Alt p (push b) | Core.Alt p b <- inner] (fmap push fb)) outerType outerSpan
        Core.ELet binds body ->
          Core.Expr (Core.ELet binds (push body)) outerType (Core.spanOf e)
        _ ->
          Core.Expr (Core.ECase e alts fallback) outerType outerSpan

-- | The leaves of a nest of cases and lets, each with the names bound on the
-- way down to it.
leaves :: Core.Expr -> [(Core.Expr, Set Name)]
leaves e =
  case Core._exprValue e of
    Core.ECase _ alts fb ->
      [ (leaf, Set.union (Refs.patternBinders p) names)
      | Core.Alt p b <- alts,
        (leaf, names) <- leaves b
      ]
        ++ maybe [] leaves fb
    Core.ELet binds body ->
      [ (leaf, Set.union (Set.fromList (map (Core._binderName . Core._bindBinder) binds)) names)
      | (leaf, names) <- leaves body
      ]
    _ -> [(e, Set.empty)]

-- | A body that is one primitive of the parameters and literals, as @core@'s
-- @\@prim@ declarations are: opened anywhere by the narrow inliner too, since
-- the call is what makes a test of it look effectful to 'pure_' (D792).
onePrim :: Cand -> Bool
onePrim (Cand params body _) =
  case Core._exprValue body of
    Core.EPrim _ args -> all isParam args
    _ -> False
  where
    names = Set.fromList (map Core._binderName params)
    isParam a =
      case Core._exprValue a of
        Core.EVar v -> Set.member v names
        Core.ELit _ -> True
        _ -> False

-- | A body every leaf of which is a constructor, a literal or a crash: what
-- the narrow inliner opens where a @case@ matches it (D792).
answersKnown :: Core.Expr -> Bool
answersKnown body =
  all (known . fst) (leaves body)
  where
    known leaf =
      case Core._exprValue leaf of
        Core.ECtor _ _ _ -> True
        Core.ELit _ -> True
        Core.ECrash _ -> True
        _ -> False

-- | Every branch the same expression, nothing bound, of a scrutinee with no
-- effect: case-of-case leaves @case b < a of True -> x; False -> x@ when it
-- copies one branch into two leaves. The narrow inliner's alone (D792); the
-- full one's is registered (D795).
sameBranches :: Core.Expr -> [Core.Alt] -> Maybe Core.Expr -> Maybe Core.Expr
sameBranches scrut alts fallback =
  case map Core._altBody alts ++ maybe [] pure fallback of
    first : rest@(_ : _)
      | pure_ scrut,
        all (Set.null . Refs.patternBinders . Core._altPattern) alts,
        all (== first) rest ->
          Just first
    _ -> Nothing

-- | Every branch the same nullary constructor or literal, and nothing bound.
allSame :: Core.Expr -> [Core.Alt] -> Maybe Core.Expr -> Maybe Core.Expr
allSame scrut alts fallback =
  case map Core._altBody alts ++ maybe [] pure fallback of
    first : rest
      | pure_ scrut,
        all (Set.null . Refs.patternBinders . Core._altPattern) alts,
        Just k <- key first,
        all ((== Just k) . key) rest ->
          Just first
    _ -> Nothing
  where
    key b =
      case Core._exprValue b of
        Core.ECtor q tag [] -> Just (Left (q, tag))
        Core.ELit lit@(Core.LInt _) -> Just (Right lit)
        Core.ELit lit@(Core.LChar _) -> Just (Right lit)
        _ -> Nothing

-- | @case s of A -> A; B -> B@ is @s@: every branch a nullary constructor
-- pattern answered by that constructor, with no fallback, so it is exhaustive.
identity :: Core.Expr -> Core.Expr -> [Core.Alt] -> Maybe Core.Expr -> Bool
identity e scrut alts fallback =
  Core.typeOf scrut == Core.typeOf e
    && Maybe.isNothing fallback
    && not (null alts)
    && all same alts
  where
    same (Core.Alt p b) =
      case (p, Core._exprValue b) of
        (Core.PCtor q tag [], Core.ECtor q' tag' []) -> q == q' && tag == tag'
        _ -> False

-- RENAMING

-- | Rename every binder in an expression to a fresh name, and replace the
-- variables @env@ names.
freshen :: Map Name Core.Expr -> Core.Expr -> M Core.Expr
freshen env e@(Core.Expr value tipe sp) =
  case value of
    -- What a name is replaced by keeps the concrete side of the two types, as
    -- 'bindAll' keeps it for one it binds: @Result.map$kPP@'s @$P@ variable
    -- read where @.text@'s parameter was is the record the field is read from
    -- (m3-native.md §NA32).
    Core.EVar n ->
      return (maybe e (\r -> r {Core._exprType = refine (Core.typeOf r) tipe}) (Map.lookup n env))
    Core.ELam bs body ->
      do
        (bs', env') <- binders env bs
        body' <- freshen env' body
        return (Core.Expr (Core.ELam bs' body') tipe sp)
    Core.EWitLam bs body ->
      do
        (bs', env') <- binders env bs
        body' <- freshen env' body
        return (Core.Expr (Core.EWitLam bs' body') tipe sp)
    Core.ELet binds body ->
      do
        (binds', env') <- sequential env binds
        body' <- freshen env' body
        return (Core.Expr (Core.ELet binds' body') tipe sp)
    Core.ELetRec binds body ->
      do
        (bs', env') <- binders env (map Core._bindBinder binds)
        values <- mapM (freshen env' . Core._bindValue) binds
        body' <- freshen env' body
        return (Core.Expr (Core.ELetRec (zipWith Core.Bind bs' values) body') tipe sp)
    Core.EJoin binds body ->
      do
        (bs', env') <- binders env (map Core._bindBinder binds)
        values <- mapM (freshen env' . Core._bindValue) binds
        body' <- freshen env' body
        return (Core.Expr (Core.EJoin (zipWith Core.Bind bs' values) body') tipe sp)
    Core.EJump j args ->
      do
        args' <- mapM (freshen env) args
        let j' = case fmap Core._exprValue (Map.lookup j env) of
              Just (Core.EVar n) -> n
              _ -> j
        return (Core.Expr (Core.EJump j' args') tipe sp)
    Core.ECase scrut alts fallback ->
      do
        scrut' <- freshen env scrut
        alts' <-
          mapM
            ( \(Core.Alt p b) ->
                do
                  (p', env') <- pattern_ env p
                  Core.Alt p' <$> freshen env' b
            )
            alts
        fallback' <- traverse (freshen env) fallback
        return (Core.Expr (Core.ECase scrut' alts' fallback') tipe sp)
    _ -> Specialize.childrenA (freshen env) e

rename :: Map Name Core.Expr -> Core.Binder -> M (Core.Binder, Map Name Core.Expr)
rename env b =
  do
    n <- fresh
    let b' = b {Core._binderName = n}
    return (b', Map.insert (Core._binderName b) (Core.Expr (Core.EVar n) (Core._binderType b) (Core._binderSpan b)) env)

binders :: Map Name Core.Expr -> [Core.Binder] -> M ([Core.Binder], Map Name Core.Expr)
binders env bs =
  case bs of
    [] -> return ([], env)
    b : rest ->
      do
        (b', env1) <- rename env b
        (rest', env2) <- binders env1 rest
        return (b' : rest', env2)

sequential :: Map Name Core.Expr -> [Core.Bind] -> M ([Core.Bind], Map Name Core.Expr)
sequential env binds =
  case binds of
    [] -> return ([], env)
    Core.Bind b v : rest ->
      do
        v' <- freshen env v
        (b', env1) <- rename env b
        (rest', env2) <- sequential env1 rest
        return (Core.Bind b' v' : rest', env2)

pattern_ :: Map Name Core.Expr -> Core.Pattern -> M (Core.Pattern, Map Name Core.Expr)
pattern_ env p =
  case p of
    Core.PVar b ->
      do
        (b', env') <- rename env b
        return (Core.PVar b', env')
    Core.PAs b inner ->
      do
        (b', env1) <- rename env b
        (inner', env2) <- pattern_ env1 inner
        return (Core.PAs b' inner', env2)
    Core.PCtor q tag subs ->
      do
        (subs', env') <- patterns env subs
        return (Core.PCtor q tag subs', env')
    Core.PRecord fields ->
      do
        (subs', env') <- patterns env (map snd fields)
        return (Core.PRecord (zip (map fst fields) subs'), env')
    Core.PArray items tail_ ->
      do
        (items', env1) <- patterns env items
        case tail_ of
          Nothing -> return (Core.PArray items' Nothing, env1)
          Just b ->
            do
              (b', env2) <- rename env1 b
              return (Core.PArray items' (Just b'), env2)
    Core.PWild -> return (p, env)
    Core.PLit _ -> return (p, env)

patterns :: Map Name Core.Expr -> [Core.Pattern] -> M ([Core.Pattern], Map Name Core.Expr)
patterns env ps =
  case ps of
    [] -> return ([], env)
    p : rest ->
      do
        (p', env1) <- pattern_ env p
        (rest', env2) <- patterns env1 rest
        return (p' : rest', env2)

-- SPANS

-- | One file space for the whole program, so that an inlined node's span can
-- say which module it came from wherever it lands.
data Space = Space
  { _spaceIds :: Map ModuleName.Canonical Int,
    _spaceNames :: Map Int ModuleName.Canonical
  }

fileSpace :: Map ModuleName.Canonical Core.Module -> Space
fileSpace cores =
  let names =
        Set.toAscList $
          Set.unions (Map.keysSet cores : map (Set.fromList . Map.elems . Core._moduleFiles) (Map.elems cores))
      indexed = zip [0 ..] names
   in Space (Map.fromList [(n, i) | (i, n) <- indexed]) (Map.fromList indexed)

spaceName :: Space -> Int -> ModuleName.Canonical
spaceName space i = _spaceNames space Map.! i

toGlobal :: Space -> Core.Module -> Core.Expr -> Core.Expr
toGlobal space modul =
  respan $ \fid@(Core.FileId _) ->
    case Map.lookup fid (Core._moduleFiles modul) of
      Just name -> Core.FileId (_spaceIds space Map.! name)
      Nothing -> error ("Core.Pass.Inline: a span names file " ++ show fid ++ ", which its module's table does not have")

-- | A module's definitions put back, with its file table grown by the modules
-- its inlined code came from, in name order after the entries it had.
rebuild :: Space -> Map Core.QualName (Core.Expr, Bool) -> ModuleName.Canonical -> Core.Module -> Core.Module
rebuild space optimized home modul =
  let results =
        [ (b, Map.lookup (Core.QualName home (Core._binderName b)) optimized)
        | Core.Bind b _ <- Core._moduleDefs modul
        ]
      changed = or [touched | (_, Just (_, touched)) <- results]
   in if not changed
        then modul
        else
          let table = Core._moduleFiles modul
              known = Map.fromList [(name, fid) | (fid, name) <- Map.toList table]
              used =
                Set.unions
                  [ spanFiles value
                  | (_, Just (value, True)) <- results
                  ]
              usedNames = Set.fromList [_spaceNames space Map.! i | Core.FileId i <- Set.toList used]
              next = 1 + maximum ((-1) : [i | Core.FileId i <- Map.keys table])
              added = zip (List.sort [n | n <- Set.toList usedNames, not (Map.member n known)]) (map Core.FileId [next ..])
              local = Map.union known (Map.fromList added)
              back = respan (\(Core.FileId i) -> local Map.! (_spaceNames space Map.! i))
              defs =
                [ Core.Bind b (maybe original (\(value, touched) -> if touched then back value else original) found)
                | (Core.Bind b original, (_, found)) <- zip (Core._moduleDefs modul) results
                ]
              ordered = reorder home defs
           in modul
                { Core._moduleFiles = Map.union table (Map.fromList [(fid, n) | (n, fid) <- added]),
                  Core._moduleDefs = concat ordered,
                  Core._moduleDefsRec =
                    [ map (Core.QualName home . Core._binderName . Core._bindBinder) g
                    | g <- ordered,
                      length g > 1
                    ]
                }

-- | C14's order again, since inlining changes what refers to what — the same
-- rule "Core.Pass.Specialize" reorders by.
reorder :: ModuleName.Canonical -> [Core.Bind] -> [[Core.Bind]]
reorder home defs =
  let byName = Map.fromList [(Core._binderName (Core._bindBinder b), b) | b <- defs]
      deps =
        Map.fromList
          [ ( Core._binderName (Core._bindBinder b),
              Set.fromList
                [ n
                | Core.QualName h n <- Set.toList (Refs._refGlobals (Refs.refsIn (Core._bindValue b))),
                  h == home
                ]
            )
          | b <- defs
          ]
   in [ [byName Map.! n | n <- group]
      | group <- Order.groups (Map.keys byName) deps
      ]

spanFiles :: Core.Expr -> Set Core.FileId
spanFiles e =
  let collect = Specialize.children_ spanFiles e
   in Set.insert (Core._spanFile (Core.spanOf e)) (Set.union collect (binderFiles (Core._exprValue e)))
  where
    binderFiles v =
      Set.fromList (map (Core._spanFile . Core._binderSpan) (bindersOf v))

bindersOf :: Core.Expr_ -> [Core.Binder]
bindersOf v =
  case v of
    Core.ELam bs _ -> bs
    Core.EWitLam bs _ -> bs
    Core.ELet bs _ -> map Core._bindBinder bs
    Core.ELetRec bs _ -> map Core._bindBinder bs
    Core.EJoin bs _ -> map Core._bindBinder bs
    Core.ECase _ alts _ -> concatMap (patternBinderList . Core._altPattern) alts
    _ -> []

patternBinderList :: Core.Pattern -> [Core.Binder]
patternBinderList p =
  case p of
    Core.PVar b -> [b]
    Core.PAs b inner -> b : patternBinderList inner
    Core.PCtor _ _ subs -> concatMap patternBinderList subs
    Core.PRecord fields -> concatMap (patternBinderList . snd) fields
    Core.PArray items tail_ -> concatMap patternBinderList items ++ Maybe.maybeToList tail_
    Core.PWild -> []
    Core.PLit _ -> []

-- | Map every span an expression carries: its nodes' and its binders'.
respan :: (Core.FileId -> Core.FileId) -> Core.Expr -> Core.Expr
respan f = go
  where
    go e =
      let rebuilt = runIdentity (Specialize.childrenA (Identity . go) e)
       in Core.Expr (value (Core._exprValue rebuilt)) (Core.typeOf e) (span_ (Core.spanOf e))

    span_ s = s {Core._spanFile = f (Core._spanFile s)}
    binder_ b = b {Core._binderSpan = span_ (Core._binderSpan b)}
    bind (Core.Bind b v) = Core.Bind (binder_ b) v

    value v =
      case v of
        Core.ELam bs body -> Core.ELam (map binder_ bs) body
        Core.EWitLam bs body -> Core.EWitLam (map binder_ bs) body
        Core.ELet bs body -> Core.ELet (map bind bs) body
        Core.ELetRec bs body -> Core.ELetRec (map bind bs) body
        Core.EJoin bs body -> Core.EJoin (map bind bs) body
        Core.ECase scrut alts fallback -> Core.ECase scrut [Core.Alt (pat p) b | Core.Alt p b <- alts] fallback
        other -> other

    pat p =
      case p of
        Core.PVar b -> Core.PVar (binder_ b)
        Core.PAs b inner -> Core.PAs (binder_ b) (pat inner)
        Core.PCtor q tag subs -> Core.PCtor q tag (map pat subs)
        Core.PRecord fields -> Core.PRecord [(n, pat q) | (n, q) <- fields]
        Core.PArray items tail_ -> Core.PArray (map pat items) (fmap binder_ tail_)
        other -> other
