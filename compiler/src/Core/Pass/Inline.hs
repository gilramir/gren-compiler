{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | Small functions inlined across modules, and the cases that leaves known
-- folded away (@docs/m2-beam-toptier.md@ §TT11, D442).
--
-- Every operator in Geng is a function, and after specialization most of them
-- are a short chain of small ones: @n < 2@ at @Int@ is @Basics.lt$s2@, which
-- calls the @Ord Int@ instance's @compare@, which calls @ltInt@, which is the
-- primitive, and @lt@ then matches the 'Basics.Order' that @compare@ built.
-- A backend that cannot inline across modules — the BEAM cannot — pays every
-- link of it; §TT10.3 measured that as most of @fib@'s time. This pass does
-- what such a compiler's middle end does, and it is Core → Core, so every
-- backend gains:
--
-- > case lt$s2 n 2 of …     ⟹     case prim i32_lt n 2 of …
--
-- __What is inlined__: a top-level binding whose value is a lambda, whose body
-- is at most 'sizeLimit' nodes once this pass has run over it, that is not
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
--   * a case whose branches are all one nullary constructor or literal, of a
--     scrutinee with no effect, is that constructor;
--   * a case that answers each constructor of its scrutinee with that same
--     constructor is its scrutinee.
--   * a comparison or @Int@ arithmetic of two literals is its answer, and a
--     top-level binding that is a literal or a nullary constructor is that.
--
-- Together they turn @lt@'s @compare@-then-match into the one comparison.
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
-- an entry for (C5 anticipated exactly this).
--
-- Run after "Core.Pass.Specialize", which makes the chains monomorphic, and
-- before "Core.Pass.Case" and "Core.Pass.TailCall", which then see one
-- program's worth of plain cases.
module Core.Pass.Inline
  ( run,
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

run :: Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
run cores =
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
      barred q = Set.member q externs || Set.member q recursive

      -- The knot: each definition optimized against the others' optimized
      -- bodies. Lazy, and it ends because 'candidate' refuses a recursive name
      -- before it forces anything.
      optimized = Map.map (optimize candidate constant) defs
      classified = Map.mapWithKey classify optimized
      classify q (value, _)
        | barred q = Nothing
        | otherwise =
            case value of
              Core.Expr (Core.ELam params body) tipe _
                | inlinable externs body && size body <= sizeLimit -> Just (Cand params body tipe)
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
  { _candidate :: Core.QualName -> Maybe Cand,
    -- | A top-level binding whose value is a literal or a nullary
    -- constructor, by name: @Ryu.mantissaBits@ is 52, and a guard on it is a
    -- branch @dialyzer@ can see is dead.
    _constant :: Core.QualName -> Maybe Core.Expr,
    _known :: Map Name Core.Expr
  }

optimize :: (Core.QualName -> Maybe Cand) -> (Core.QualName -> Maybe Core.Expr) -> Core.Expr -> (Core.Expr, Bool)
optimize candidate constant value =
  let (out, St _ _ changed) = runState (simplify (Ctx candidate constant Map.empty) value) (St 0 fuelPerDefinition False)
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

-- | A @let@'s bindings without those an atomic value was substituted for and
-- nothing names any more, when there are any: a binding left behind is a
-- variable @erlc@ warns is unused.
unused :: [Core.Bind] -> Core.Expr -> Maybe [Core.Bind]
unused binds body =
  let go rest =
        case rest of
          [] -> ([], Refs.freeLocals body)
          b@(Core.Bind binder value) : more ->
            let (keptAfter, free) = go more
             in if atomic value && not (Set.member (Core._binderName binder) free)
                  then (keptAfter, free)
                  else (b : keptAfter, Set.union (Refs.freeLocals value) (Set.delete (Core._binderName binder) free))
      (kept, _) = go binds
   in if length kept < length binds then Just kept else Nothing

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
    Core.EApp (Core.Expr (Core.EGlobal q) siteType _) args
      | Just cand <- _candidate ctx q,
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
    _ -> return e

-- | A primitive of literals, computed: what inlining a comparison of two
-- constants leaves (@clamp 0 2147483647 0@ in @Dict.keys@, @negate 3 == 0@), and which a
-- backend's own checker otherwise reports as a branch that cannot be taken —
-- @dialyzer@ does. 'Int32' arithmetic in Haskell wraps as D2's does.
fold :: Prim.PrimOp -> [Core.Expr_] -> Maybe Core.Expr_
fold op args =
  case (op, args) of
    (Prim.IntOp Prim.I32 p, [Core.ELit (Core.LInt a), Core.ELit (Core.LInt b)]) ->
      case p of
        Prim.IAdd -> Just (Core.ELit (Core.LInt (a + b)))
        Prim.ISub -> Just (Core.ELit (Core.LInt (a - b)))
        Prim.IMul -> Just (Core.ELit (Core.LInt (a * b)))
        Prim.IEq -> Just (bool (a == b))
        Prim.ILt -> Just (bool (a < b))
        _ -> Nothing
    (Prim.IntOp Prim.I64 p, [Core.ELit (Core.LInt64 a), Core.ELit (Core.LInt64 b)]) -> arith Core.LInt64 p a b
    (Prim.IntOp Prim.U32 p, [Core.ELit (Core.LUInt32 a), Core.ELit (Core.LUInt32 b)]) -> arith Core.LUInt32 p a b
    (Prim.IntOp Prim.U64 p, [Core.ELit (Core.LUInt64 a), Core.ELit (Core.LUInt64 b)]) -> arith Core.LUInt64 p a b
    (Prim.IntOp Prim.I32 Prim.INeg, [Core.ELit (Core.LInt a)]) -> Just (Core.ELit (Core.LInt (negate a)))
    (Prim.IntOp Prim.I64 Prim.INeg, [Core.ELit (Core.LInt64 a)]) -> Just (Core.ELit (Core.LInt64 (negate a)))
    _ -> Nothing
  where
    -- 'Int64', 'Word32' and 'Word64' wrap as the widths they stand for do.
    arith :: (Integral a) => (a -> Core.Literal) -> Prim.IntPrim -> a -> a -> Maybe Core.Expr_
    arith lit p a b =
      case p of
        Prim.IAdd -> Just (Core.ELit (lit (a + b)))
        Prim.ISub -> Just (Core.ELit (lit (a - b)))
        Prim.IMul -> Just (Core.ELit (lit (a * b)))
        _ -> compared p a b

    compared :: (Ord a) => Prim.IntPrim -> a -> a -> Maybe Core.Expr_
    compared p a b =
      case p of
        Prim.IEq -> Just (bool (a == b))
        Prim.ILt -> Just (bool (a < b))
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
bindAll :: [(Core.Binder, Core.Expr)] -> Core.Expr -> Core.Type -> Core.Span -> M Core.Expr
bindAll pairs body tipe sp =
  go pairs Map.empty []
  where
    go rest env lets =
      case rest of
        [] ->
          do
            body' <- freshen env body
            return (foldr (\b acc -> Core.Expr (Core.ELet [b] acc) tipe sp) body' (reverse lets))
        (binder, arg) : more
          | atomic arg ->
              go more (Map.insert (Core._binderName binder) arg env) lets
          | otherwise ->
              do
                n <- fresh
                let binder' = binder {Core._binderName = n}
                    var = Core.Expr (Core.EVar n) (Core._binderType binder) (Core._binderSpan binder)
                go more (Map.insert (Core._binderName binder) var env) (Core.Bind binder' arg : lets)

-- | Free of effects and cheap enough to copy: a variable, a literal, a
-- constructor with no fields.
atomic :: Core.Expr -> Bool
atomic e =
  case Core._exprValue e of
    Core.EVar _ -> True
    Core.ELit _ -> True
    Core.ECtor _ _ [] -> True
    _ -> False

-- | Free of effects: dropping it changes nothing but the time taken.
pure_ :: Core.Expr -> Bool
pure_ e =
  case Core._exprValue e of
    Core.EVar _ -> True
    Core.ELit _ -> True
    Core.ECtor _ _ args -> all pure_ args
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

caseOf :: Ctx -> Core.Expr -> Core.Expr -> [Core.Alt] -> Maybe Core.Expr -> M Core.Expr
caseOf ctx e scrut alts fallback =
  case known of
    Just (Chosen binds body) ->
      do
        markFired
        out <- bindAll binds body (Core.typeOf e) (Core.spanOf e)
        simplify ctx out
    Just (Crashes crash) ->
      do
        markFired
        return (Core.Expr crash (Core.typeOf e) (Core.spanOf e))
    Nothing
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
      | otherwise -> return e
  where
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

-- | What a @let@'s value is known to be: a constructor or a literal, or one at
-- the end of @let@s. Behind a @let@ the constructor's fields may name what
-- that @let@ bound, which is out of scope at the case, so they are kept only
-- as their types: 'matchBound' binds no field that is not atomic, and an
-- 'Core.Unreachable' crash is not.
knownValue :: Core.Expr -> Maybe Core.Expr
knownValue v =
  case Core._exprValue v of
    Core.ECtor _ _ _ -> Just v
    Core.ELit _ -> Just v
    Core.ELet _ body ->
      case knownValue body of
        Just (Core.Expr (Core.ECtor q tag args) t sp) ->
          Just (Core.Expr (Core.ECtor q tag [Core.Expr (Core.ECrash Core.Unreachable) (Core.typeOf a) (Core.spanOf a) | a <- args]) t sp)
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
          Core.Expr (Core.ECase s [Core.Alt p (push b) | Core.Alt p b <- inner] (fmap push fb)) outerType (Core.spanOf e)
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
    Core.EVar n -> return (Maybe.fromMaybe e (Map.lookup n env))
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
