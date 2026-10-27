{-# OPTIONS_GHC -Wall #-}

-- | An update of an affine record whose old record nothing reads again is
-- written into that record rather than copied (geng-lang @m4-visiterm.md@
-- §VA17, D984–D987). It marks the update 'Core.InPlace'; the C backend and
-- JavaScript write the fields into the record they are given, and the BEAM,
-- whose tuples are values, copies as before.
--
-- __Why a pass, and why the last one__ (D984). §VA16.4's survey put the mark
-- in the ownership checker, which walks every use of a local in order. But
-- the checker does not see a plain field read after its record was moved
-- (D933), and that read is the whole question: @csi … { t | ps = 0 } t.cur@
-- reads @t@ after the update, and so does a caller that hands @t@ to a
-- function and reads @t.cur@ when it returns, which only the program as a
-- whole shows. So the pass sees the program, after every other pass, and no
-- later pass can move a read past a mark. It does not rest on the checker:
-- it proves for itself that nothing reads the record again, and marks only an
-- affine record because that is what D980 asked for.
--
-- __What it proves__. An update may write its record in place when the
-- record is reached only through the update's base: nothing evaluated after
-- the update reads the record, or reaches it through an alias, a snapshot
-- of it, or a value that holds it, and the record came to its base whole.
-- The walk follows Core's order of evaluation: a call's arguments left to
-- right, an update's base and then its fields, a @let@'s value before its
-- body, and into a join from every jump to it. What it tracks:
--
--   * __Places__: every local is a root, or an alias of a place in one (a
--     @let@ of a local's field, a pattern's binder), and a read of a place is
--     a 'Mention' of it. An alias is a snapshot: what it holds was read when
--     it was bound, so a later read of it does not see a write to the record
--     above it. Two sets go down the walk: what is read after an expression
--     is evaluated, which a write inside it may not be read by, and what
--     holds or reads its value once it is handed on.
--   * __Roots that are their own__: a root whose value nothing else holds
--     when it is bound. A record, constructor, array or update just built is
--     one; so is a call's result when the function's is fresh ('_fresh') and
--     its arguments share nothing with one another; a global, a primitive's
--     result, a lambda's parameter and a value a closure captures are not. A
--     function's parameter is one when every call of it hands it a value
--     nothing else holds ('Facts', a fixed point over the program): a root's
--     are not, nor are those of a function used as a value, whose callers
--     are unknown. A join's parameter is one when every jump to it hands one.
--   * __Links__: a root made from others (a call's result and its
--     arguments, a record and its fields' locals) is linked to them, and a
--     read of a linked place after a write counts as a read of the record.
--     A link says no more than that two subtrees may share an object, so the
--     other place stands whole; one to a root nothing reads again is dropped.
--   * __Escapes__: a value handed, while it is still read, to something that
--     may keep it where nothing follows it (an extern, a function value, a
--     closure, a primitive whose result can hold it, a join's parameter, a
--     parameter a function may keep) makes the place it came from shared
--     ('_taint'), and nothing under that place is written in place or handed
--     on as exclusive.
--
-- Before the walk, a lambda's read of a number from an affine record it
-- captures is made when the lambda is ('hoist', D986), since a closure may
-- be called after any write and would otherwise share the record for as
-- long as it lives. @GENG_INPLACE_REPORT@ lists every update of an affine
-- record, in place or why it copies (D987).
--
-- Everything else is copied, as every update was before. A copy is always
-- right; a mark the analysis cannot prove is never made.
module Core.Pass.InPlace
  ( run,
  )
where

import Core.AST qualified as Core
import Core.Pass.FloatIn qualified as FloatIn
import Data.IntMap.Lazy qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set (Set)
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName
import System.Environment qualified as Env
import System.IO.Unsafe (unsafePerformIO)

-- THE PROGRAM

data Prog = Prog
  { -- | The data types declared @\@affine@ or holding one (FloatIn's).
    _affine :: Set Core.QualName,
    -- | The data types whose values can hold an affine record.
    _holders :: Set Core.QualName,
    -- | Every top-level function, by its arity.
    _fns :: Map Core.QualName Int,
    -- | Every data type, by its name.
    _decls :: Map Core.QualName Core.DataDecl,
    -- | The functions whose callers are not all known: a root, or one named
    -- anywhere but at the head of a call of its own arity.
    _open :: Set Core.QualName,
    -- | 'holdsRecAffine' of every type the program's expressions have and
    -- every type inside one, by 'Core.typeId', each made from its children's.
    -- The walk asks it of every node, and a nest n deep has n types up to n
    -- deep, which walked whole each time cost n² (as D780 found of @mono@).
    _typeInfo :: IntMap.IntMap (Bool, Bool)
  }

-- | What the program's walk learns of its functions, to a fixed point.
data Facts = Facts
  { -- | Whether each parameter is handed a value nothing else holds, at every
    -- call. Shrinks from all true.
    _excl :: Map Core.QualName [Bool],
    -- | Whether the result is a value nothing else holds when the arguments
    -- were. Shrinks from true.
    _fresh :: Map Core.QualName Bool,
    -- | Whether each parameter may be kept by something other than the
    -- function's result: handed to an extern, a function value or another
    -- such parameter, or captured. Grows from all false.
    _stash :: Map Core.QualName [Bool]
  }
  deriving (Eq)

-- | The roots are the build's: a @main@, or what a host library exposes.
run :: [Core.QualName] -> Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
run roots cores =
  let prog = program roots (Map.elems cores)
      defs0 = [(Core.QualName (Core._moduleName m) (Core._binderName b), v) | m <- Map.elems cores, Core.Bind b v <- Core._moduleDefs m]
      start =
        Facts
          { _excl = Map.mapWithKey (\q n -> replicate n (not (Set.member q (_open prog)))) (_fns prog),
            _fresh = Map.map (const True) (_fns prog),
            _stash = Map.map (`replicate` False) (_fns prog)
          }
      defs = [(q, hoist prog v) | (q, v) <- defs0]
      (facts, final) = fixFacts prog defs start
      rewrite home (Core.Bind b v) =
        maybe (Core.Bind b v) (Core.Bind b . _defExpr) (Map.lookup (Core.QualName home (Core._binderName b)) final)
      out = Map.map (\m -> m {Core._moduleDefs = map (rewrite (Core._moduleName m)) (Core._moduleDefs m)}) cores
      factLines =
        [ List.intercalate "\t" [Name.toChars (ModuleName._module (Core._qnHome q)), Name.toChars (Core._qnName q), "-", "facts: exclusive " ++ show ex ++ ", fresh " ++ show (Map.findWithDefault False q (_fresh facts)) ++ ", kept " ++ show (Map.findWithDefault [] q (_stash facts)) ++ (if Set.member q (_open prog) then ", open" else "")]
        | (q, ex) <- Map.toList (_excl facts)
        ]
   in if any (hasAffineUpdate prog . snd) defs0
        then report (factLines ++ concatMap (_outLines . _defOut) (Map.elems final)) out
        else cores

-- | Whether the expression updates a record the pass may mark. A program
-- with none is left as it is, unwalked: the pass marks nothing else, and
-- what it hoists out of a lambda is only for such an update's sake.
hasAffineUpdate :: Prog -> Core.Expr -> Bool
hasAffineUpdate prog e =
  case Core._exprValue e of
    Core.EUpdate {} | affineRec prog (Core._exprType e) -> True
    _ -> any (hasAffineUpdate prog) (children e)

-- | The facts every definition's walk gives, until they stop changing, and
-- each definition walked with them. Each fact moves one way, so this ends;
-- a program that has not settled in a hundred rounds is given the facts
-- that mark nothing.
--
-- A walk reads no facts but its own parameters' and those of the functions
-- it names, so a round walks again only the definitions one of those changed
-- for, and keeps the others' walks: the rounds' facts are the ones walking
-- every definition every round would give.
fixFacts :: Prog -> [(Core.QualName, Core.Expr)] -> Facts -> (Facts, Map Core.QualName Def)
fixFacts prog defs start =
  go start (walkAll start) (0 :: Int)
  where
    defMap = Map.fromList defs
    readers = Map.fromListWith Set.union [(c, Set.singleton d) | (d, v) <- defs, c <- Set.toList (globalsOf v)]
    readersOf qs = Set.unions [Map.findWithDefault Set.empty c readers | c <- Set.toList qs]
    walkOne facts q v = (definition prog facts False q v, freshOf facts q v)
    walkAll facts = Map.mapWithKey (walkOne facts) defMap
    freshOf facts q v
      | Map.member q (_fns prog) = _defResult (definition prog facts True q v)
      | otherwise = False
    go facts walked rounds
      | Just stop <- stopAfter, rounds >= stop = (facts, Map.map fst walked)
      | rounds >= 100 = let f = nothingExclusive facts in (f, Map.map fst (walkAll f))
      | next == facts = (facts, Map.map fst walked)
      | otherwise =
          let changed :: (Eq a) => (Facts -> Map Core.QualName a) -> Set Core.QualName
              changed field = Set.fromList [q | (q, a) <- Map.toList (field next), Map.lookup q (field facts) /= Just a]
              byCallee = readersOf (Set.union (changed _fresh) (changed _stash))
              -- The walk that asks for the result's freshness takes every
              -- parameter as exclusive, so reads no '_excl'.
              byParams = changed _excl
              rewalk q v (d, fr)
                | Set.member q byCallee = walkOne next q v
                | Set.member q byParams = (definition prog next False q v, fr)
                | otherwise = (d, fr)
           in go next (Map.intersectionWithKey rewalk defMap walked) (rounds + 1)
      where
        calls = Map.unionsWith (zipWith (&&)) [_outCalls (_defOut d) | (d, _) <- Map.elems walked]
        next =
          Facts
            { _excl = Map.mapWithKey (\q old -> maybe old (zipWith (&&) old) (Map.lookup q calls)) (_excl facts),
              _fresh = Map.mapWithKey (\q old -> old && maybe True snd (Map.lookup q walked)) (_fresh facts),
              _stash = Map.mapWithKey (\q old -> zipWith (||) old (maybe (map (const False) old) (_defStash . fst) (Map.lookup q walked))) (_stash facts)
            }

-- | The globals an expression names.
globalsOf :: Core.Expr -> Set Core.QualName
globalsOf e =
  case Core._exprValue e of
    Core.EGlobal q -> Set.singleton q
    _ -> foldChildren globalsOf e

nothingExclusive :: Facts -> Facts
nothingExclusive facts =
  facts
    { _excl = Map.map (map (const False)) (_excl facts),
      _fresh = Map.map (const False) (_fresh facts),
      _stash = Map.map (map (const True)) (_stash facts)
    }

program :: [Core.QualName] -> [Core.Module] -> Prog
program roots modules =
  let affineSet = FloatIn.affine modules
      decls = concatMap Core._moduleData modules
      holdsIn known decl = any (any (declHolds affineSet known) . Core._ctorFields) (Core._dataCtors decl)
      fixed known =
        let next = Set.fromList [Core._dataName d | d <- decls, holdsIn known d]
         in if next == known then known else fixed next
      defs = [(Core.QualName (Core._moduleName m) (Core._binderName b), v) | m <- modules, Core.Bind b v <- Core._moduleDefs m]
      fns = Map.fromList [(q, length bs) | (q, v) <- defs, Just (bs, _) <- [lambdaOf v]]
      named = Set.unions [valueUses fns v | (_, v) <- defs]
      prog =
        Prog
          { _affine = affineSet,
            _holders = fixed Set.empty,
            _fns = fns,
            _decls = Map.fromList [(Core._dataName d, d) | d <- decls],
            _open = Set.union named (Set.fromList roots),
            _typeInfo = IntMap.fromList [(Core.typeId t, holdsRecAffineNode prog t) | t <- typesIn (concatMap (exprTypes . snd) defs)]
          }
   in prog

-- | The types of an expression's nodes.
exprTypes :: Core.Expr -> [Core.Type]
exprTypes e0 = go e0 []
  where
    -- Onto what follows, so that a deep child is not copied at each level.
    go e rest = Core._exprType e : foldr go rest (children e)

-- | The types, and every type inside one, each once.
typesIn :: [Core.Type] -> [Core.Type]
typesIn = go IntSet.empty
  where
    go _ [] = []
    go seen (t : rest)
      | IntSet.member (Core.typeId t) seen = go seen rest
      | otherwise = t : go (IntSet.insert (Core.typeId t) seen) (typeChildren t ++ rest)

typeChildren :: Core.Type -> [Core.Type]
typeChildren t =
  case t of
    Core.TVar _ -> []
    Core.TFun args result -> result : args
    Core.TCon _ args -> args
    Core.TRecord fields _ -> map snd fields
    Core.TForall _ _ body -> [body]

-- | A data type's field that can hold an affine record, its parameters taken
-- as holding none (a use of the type says what they are).
declHolds :: Set Core.QualName -> Set Core.QualName -> Core.Type -> Bool
declHolds affineSet known t =
  case t of
    Core.TVar _ -> False
    Core.TFun _ _ -> True
    Core.TCon q args -> Set.member q known || any (declHolds affineSet known) args
    Core.TRecord fields _ -> affineRecordOf affineSet t || any (declHolds affineSet known . snd) fields
    Core.TForall _ _ body -> declHolds affineSet known body

-- | Whether a value of the type can hold an affine record, or be one. A type
-- variable, a function and an open record can.
holdsRec :: Prog -> Core.Type -> Bool
holdsRec p = fst . holdsRecAffine p

-- | 'holdsRec', and whether the type holds an affine value
-- ('FloatIn.fieldHoldsAffine'), in one walk of the type: asking the second at
-- each record of a type records nest in deeply would walk it again at each.
holdsRecAffine :: Prog -> Core.Type -> (Bool, Bool)
holdsRecAffine p t =
  Maybe.fromMaybe (holdsRecAffineNode p t) (IntMap.lookup (Core.typeId t) (_typeInfo p))

-- | 'holdsRecAffine' of a type from its children's.
holdsRecAffineNode :: Prog -> Core.Type -> (Bool, Bool)
holdsRecAffineNode p t =
  case t of
    Core.TVar _ -> (True, False)
    Core.TFun _ _ -> (True, False)
    Core.TCon q args ->
      let rs = map (holdsRecAffine p) args
       in (Set.member q (_holders p) || any fst rs, Set.member q (_affine p) || any snd rs)
    Core.TRecord fields row ->
      let rs = map (holdsRecAffine p . snd) fields
          affine = any snd rs
       in (row /= Nothing || affine || any fst rs, affine)
    Core.TForall _ _ body -> holdsRecAffine p body

-- | Whether a value of the first type can hold a value of the second, at
-- any depth. A type variable, a function and an open record can hold
-- anything.
mayContain :: Prog -> Core.Type -> Core.Type -> Bool
mayContain p a b = go Set.empty a
  where
    go seen t
      | t == b = True
      | otherwise =
          case t of
            Core.TVar _ -> True
            Core.TFun _ _ -> True
            Core.TRecord fields row -> row /= Nothing || any (go seen . snd) fields
            Core.TForall _ _ body -> go seen body
            Core.TCon q args
              | Set.member q seen -> any (go seen) args
              | Just decl <- Map.lookup q (_decls p) ->
                  any (go seen) args
                    || any (go (Set.insert q seen) . substitute_ (zip (Core._dataParams decl) args)) (concatMap Core._ctorFields (Core._dataCtors decl))
              | otherwise -> any (go seen) args

-- | A data type's field type with its parameters given.
substitute_ :: [(Name, Core.Type)] -> Core.Type -> Core.Type
substitute_ sub t =
  case t of
    Core.TVar v -> Maybe.fromMaybe t (lookup v sub)
    Core.TFun args result -> Core.TFun (map (substitute_ sub) args) (substitute_ sub result)
    Core.TRecord fields row -> Core.TRecord [(f, substitute_ sub ft) | (f, ft) <- fields] row
    Core.TCon q args -> Core.TCon q (map (substitute_ sub) args)
    Core.TForall vs cs body -> Core.TForall vs cs (substitute_ [(v, x) | (v, x) <- sub, v `notElem` vs] body)

-- | A closed record with a field that is affine or holds one: what the pass
-- marks.
affineRec :: Prog -> Core.Type -> Bool
affineRec p t =
  case t of
    Core.TRecord fields Nothing -> any (snd . holdsRecAffine p . snd) fields
    _ -> False

-- | 'affineRec' before there is a 'Prog', for the data types' fields.
affineRecordOf :: Set Core.QualName -> Core.Type -> Bool
affineRecordOf affineSet t =
  case t of
    Core.TRecord fields Nothing -> any (FloatIn.fieldHoldsAffine affineSet . snd) fields
    _ -> False

lambdaOf :: Core.Expr -> Maybe ([Core.Binder], Core.Expr)
lambdaOf e =
  case Core._exprValue e of
    Core.ELam bs body -> Just (bs, body)
    Core.ETyLam _ inner -> lambdaOf inner
    _ -> Nothing

-- | The functions an expression names other than at the head of a call of
-- their own arity.
valueUses :: Map Core.QualName Int -> Core.Expr -> Set Core.QualName
valueUses fns e =
  case Core._exprValue e of
    Core.EGlobal q -> Set.singleton q
    Core.EApp fn args
      | Core.EGlobal q <- Core._exprValue (peelTyApp fn),
        Map.lookup q fns == Just (length args) ->
          Set.unions (map (valueUses fns) args)
    _ -> foldChildren (valueUses fns) e

peelTyApp :: Core.Expr -> Core.Expr
peelTyApp e =
  case Core._exprValue e of
    Core.ETyApp inner _ -> peelTyApp inner
    _ -> e

foldChildren :: (Core.Expr -> Set Core.QualName) -> Core.Expr -> Set Core.QualName
foldChildren f e =
  Set.unions (map f (children e))

children :: Core.Expr -> [Core.Expr]
children e =
  case Core._exprValue e of
    Core.EVar _ -> []
    Core.EGlobal _ -> []
    Core.ELit _ -> []
    Core.ELam _ body -> [body]
    Core.EApp fn args -> fn : args
    Core.ELet binds body -> map Core._bindValue binds ++ [body]
    Core.ELetRec binds body -> map Core._bindValue binds ++ [body]
    Core.ECase scrut alts fallback -> scrut : map Core._altBody alts ++ Maybe.maybeToList fallback
    Core.ECtor _ _ args -> args
    Core.ERecord fields -> map snd fields
    Core.EUpdate base fields _ -> base : map snd fields
    Core.EAccess base _ -> [base]
    Core.EArray items -> items
    Core.EPrim _ args -> args
    Core.EJoin binds body -> map Core._bindValue binds ++ [body]
    Core.EJump _ args -> args
    Core.ETyLam _ body -> [body]
    Core.ETyApp fn _ -> [fn]
    Core.EWitLam _ body -> [body]
    Core.EWitApp fn args -> fn : args
    Core.ECrash (Core.Todo _ message) -> [message]
    Core.ECrash _ -> []

-- READS A CLOSURE MAKES EARLY

-- | A lambda's read of a field of an affine record it captures, where the
-- field's value holds no affine record (an @Int@, say), is made when the
-- lambda is, and the lambda captures the value (D986):
--
-- > \row -> set t.x c row     ⟹     let $hoisted0 = t.x in \row -> set $hoisted0 c row
--
-- Under copying the two are the same program, since @t@ never changes. What
-- a closure captures is shared for as long as the closure lives, since it
-- may be called after any write, and a record a closure only reads a number
-- from would otherwise never be written in place. A join's body is not a
-- closure and is left as it is.
hoist :: Prog -> Core.Expr -> Core.Expr
hoist prog value =
  case Core._exprValue value of
    Core.ELam bs body -> value {Core._exprValue = Core.ELam bs (fst3 (go body 0))}
    Core.ETyLam vs inner -> value {Core._exprValue = Core.ETyLam vs (hoist prog inner)}
    _ -> fst3 (go value 0)
  where
    fst3 (a, _, _) = a
    -- The expression with each lambda's seen hoisted, the counter that
    -- names what is hoisted, and the seen it makes of a field holding no
    -- affine record, of a local whose value is an affine record and which
    -- no binder inside it binds, by the local's name. A lambda hoists those
    -- whose local it does not bind itself, and they are then made outside
    -- it. Gathered from the children, not by a walk of each lambda's body,
    -- which lambdas nested n deep would make n².
    go :: Core.Expr -> Int -> (Core.Expr, Int, [(Name, Core.Expr)])
    go e n =
      case Core._exprValue e of
        Core.ELam bs body ->
          let inside = binderNames bs
              (body', n1, seen) = go body n
              found = List.nubBy (\a b -> snd a == snd b) (outside inside seen)
              names = [Name.fromChars ("$hoisted" ++ show i) | i <- [n1 .. n1 + length found - 1]]
              lam = e {Core._exprValue = Core.ELam bs (substitute inside (zip (map snd found) names) body')}
              binds = [Core.Bind (Core.Binder nm (Core._exprType r) (Core.spanOf r)) r | ((_, r), nm) <- zip found names]
           in if null found
                then (e {Core._exprValue = Core.ELam bs body'}, n1, [])
                else (e {Core._exprValue = Core.ELet binds lam}, n1 + length found, found)
        Core.EJoin binds body ->
          let (binds', n1, seen) = joinBinds binds n
              (body', n2, seen2) = go body n1
           in (e {Core._exprValue = Core.EJoin binds' body'}, n2, seen ++ seen2)
        -- A recursive group's functions stay lambdas; what they read is not
        -- made early.
        Core.ELetRec binds body ->
          let (binds', n1, seen) = joinBinds binds n
              (body', n2, seen2) = go body n1
              names = binderNames (map Core._bindBinder binds)
           in (e {Core._exprValue = Core.ELetRec binds' body'}, n2, outside names (seen ++ seen2))
        Core.ELet binds body ->
          let (values, n1, seen) = goAll (map Core._bindValue binds) n
              (body', n2, seen2) = go body n1
              names = binderNames (map Core._bindBinder binds)
           in (e {Core._exprValue = Core.ELet (zipWith (\(Core.Bind b _) v -> Core.Bind b v) binds values) body'}, n2, seen ++ outside names seen2)
        Core.ECase scrut alts fallback ->
          let (scrut', n1, seen) = go scrut n
              (bodies, n2, altSeen) = goEach [(binderNames (patternBinders pat), b) | Core.Alt pat b <- alts] n1
              (fallback', n3, seen3) = case fallback of
                Just f -> let (f', k, rs) = go f n2 in (Just f', k, rs)
                Nothing -> (Nothing, n2, [])
           in (e {Core._exprValue = Core.ECase scrut' (zipWith (\(Core.Alt p _) b -> Core.Alt p b) alts bodies) fallback'}, n3, seen ++ altSeen ++ seen3)
        -- A chain is looked into once: its root and record are each access's.
        Core.EAccess _ _ ->
          let (record, levels) = unwind e []
           in case Core._exprValue record of
                Core.EVar x
                  | affineRec prog (Core._exprType record) ->
                      (e, n, take 1 [(x, a) | a <- reverse levels, not (holdsRec prog (Core._exprType a))])
                  | otherwise -> (e, n, [])
                _ ->
                  let (record', n1, seen) = go record n
                   in (List.foldl' rewrap_ record' levels, n1, seen)
        _ ->
          let (kids, n1, seen) = goAll (children e) n
           in (replaceChildren e kids, n1, seen)
    goAll es n = goEach [(Set.empty, c) | c <- es] n
    -- Expressions one after another, each under binders, the seen the
    -- binders bind dropped.
    goEach bodies n =
      let step (acc, k, rss) (names, c) =
            let (c', k', rs) = go c k
             in (c' : acc, k', outside names rs : rss)
          (done, n1, seens) = List.foldl' step ([], n, []) bodies
       in (reverse done, n1, concat (reverse seens))
    -- A join's or a recursive group's lambdas stay lambdas.
    joinBinds binds n =
      let one (Core.Bind b v) =
            case Core._exprValue v of
              Core.ELam ps jbody -> (binderNames ps, jbody, \jbody' -> Core.Bind b v {Core._exprValue = Core.ELam ps jbody'})
              _ -> (Set.empty, v, Core.Bind b)
          parts = map one binds
          (bodies, n1, seen) = goEach [(names, body) | (names, body, _) <- parts] n
       in (zipWith (\(_, _, rebuild) body -> rebuild body) parts bodies, n1, seen)
    outside names = filter (\(root, _) -> not (Set.member root names))
    binderNames bs = Set.fromList (map Core._binderName bs)
    -- The chain's record, and its accesses from the innermost out.
    unwind x acc =
      case Core._exprValue x of
        Core.EAccess base _ -> unwind base (x : acc)
        _ -> (x, acc)
    rewrap_ inner level =
      case Core._exprValue level of
        Core.EAccess _ f -> level {Core._exprValue = Core.EAccess inner f}
        _ -> level

-- | Each read replaced by its name, where its root is not shadowed.
substitute :: Set Name -> [(Core.Expr, Name)] -> Core.Expr -> Core.Expr
substitute shadow pairs e =
  case lookup e pairs of
    Just nm | maybe False (`Set.notMember` shadow) (rootName e) -> e {Core._exprValue = Core.EVar nm}
    _ ->
      case Core._exprValue e of
        Core.ELam bs body -> e {Core._exprValue = Core.ELam bs (substitute (names bs) pairs body)}
        Core.ELet bs body ->
          e {Core._exprValue = Core.ELet [Core.Bind b (substitute shadow pairs v) | Core.Bind b v <- bs] (substitute (binds bs) pairs body)}
        Core.ELetRec bs body ->
          e {Core._exprValue = Core.ELetRec [Core.Bind b (substitute (binds bs) pairs v) | Core.Bind b v <- bs] (substitute (binds bs) pairs body)}
        Core.ECase scrut alts fallback ->
          e
            { Core._exprValue =
                Core.ECase
                  (substitute shadow pairs scrut)
                  [Core.Alt pat (substitute (names (patternBinders pat)) pairs b) | Core.Alt pat b <- alts]
                  (fmap (substitute shadow pairs) fallback)
            }
        Core.EJoin bs body ->
          e {Core._exprValue = Core.EJoin [Core.Bind b (joinValue v) | Core.Bind b v <- bs] (substitute shadow pairs body)}
        _ -> replaceChildren e (map (substitute shadow pairs) (children e))
  where
    names bs = Set.union shadow (Set.fromList (map Core._binderName bs))
    binds bs = names (map Core._bindBinder bs)
    -- A join's parameters bind as a lambda's do.
    joinValue v =
      case Core._exprValue v of
        Core.ELam ps body -> v {Core._exprValue = Core.ELam ps (substitute (names ps) pairs body)}
        _ -> substitute shadow pairs v
    rootName x = case Core._exprValue x of
      Core.EVar n -> Just n
      Core.EAccess b _ -> rootName b
      _ -> Nothing

-- | An expression with its children, in 'children''s order, replaced.
replaceChildren :: Core.Expr -> [Core.Expr] -> Core.Expr
replaceChildren e cs =
  e {Core._exprValue = node (Core._exprValue e)}
  where
    node v =
      case v of
        Core.EVar _ -> v
        Core.EGlobal _ -> v
        Core.ELit _ -> v
        Core.ELam bs _ -> Core.ELam bs (at 0)
        Core.EApp _ args -> Core.EApp (at 0) (take (length args) (drop 1 cs))
        Core.ELet binds _ -> Core.ELet (zipWith (\(Core.Bind b _) c -> Core.Bind b c) binds cs) (at (length binds))
        Core.ELetRec binds _ -> Core.ELetRec (zipWith (\(Core.Bind b _) c -> Core.Bind b c) binds cs) (at (length binds))
        Core.ECase _ alts fallback ->
          Core.ECase (at 0) (zipWith (\(Core.Alt p _) c -> Core.Alt p c) alts (drop 1 cs)) (fmap (const (at (1 + length alts))) fallback)
        Core.ECtor q t args -> Core.ECtor q t (take (length args) cs)
        Core.ERecord fields -> Core.ERecord (zipWith (\(f, _) c -> (f, c)) fields cs)
        Core.EUpdate _ fields w -> Core.EUpdate (at 0) (zipWith (\(f, _) c -> (f, c)) fields (drop 1 cs)) w
        Core.EAccess _ f -> Core.EAccess (at 0) f
        Core.EArray items -> Core.EArray (take (length items) cs)
        Core.EPrim op args -> Core.EPrim op (take (length args) cs)
        Core.EJoin binds _ -> Core.EJoin (zipWith (\(Core.Bind b _) c -> Core.Bind b c) binds cs) (at (length binds))
        Core.EJump j args -> Core.EJump j (take (length args) cs)
        Core.ETyLam vs _ -> Core.ETyLam vs (at 0)
        Core.ETyApp _ ts -> Core.ETyApp (at 0) ts
        Core.EWitLam bs _ -> Core.EWitLam bs (at 0)
        Core.EWitApp _ args -> Core.EWitApp (at 0) (take (length args) (drop 1 cs))
        Core.ECrash (Core.Todo place _) -> Core.ECrash (Core.Todo place (at 0))
        Core.ECrash _ -> v
    at i = case drop i cs of
      c : _ -> c
      [] -> error "Core.Pass.InPlace.replaceChildren: too few children"

-- THE REPORT

-- | @GENG_INPLACE_REPORT=<file>@: a line for each update of an affine
-- record, module, definition, where, and @in place@ or why it copies.
-- Appended, so that a suite that builds more than once writes each build's.
reportPath :: Maybe FilePath
reportPath = unsafePerformIO (Env.lookupEnv "GENG_INPLACE_REPORT")
{-# NOINLINE reportPath #-}

-- | @GENG_INPLACE_ROUNDS=<n>@: the program's facts after @n@ rounds rather
-- than at their fixed point, which is unsound and is for reading the report:
-- the first round's copies are what the rest follow from.
stopAfter :: Maybe Int
stopAfter = unsafePerformIO (fmap read <$> Env.lookupEnv "GENG_INPLACE_ROUNDS")
{-# NOINLINE stopAfter #-}

-- | Whether a report is asked for.
reporting :: Bool
reporting = maybe False (/= "") reportPath

-- | The report's lines, or none when no report is asked for.
say :: [String] -> [String]
say lines_ = if reporting then lines_ else []

report :: [String] -> a -> a
report lines_ out =
  case reportPath of
    Just path | path /= "" -> unsafePerformIO (appendFile path (unlines lines_) >> return out)
    _ -> out

-- PLACES

data Step
  = SField !Name
  | SCtor !Int !Int
  deriving (Eq, Ord, Show)

-- | A root, by its number in the definition's walk, and the steps from it.
data Place = Place
  { _root :: !Int,
    _path :: ![Step]
  }
  deriving (Eq, Ord)

-- | A read of a place. The first '_snap' steps were taken when an alias was
-- bound, so the objects above them are not read now; '_deep' is a value that
-- can hold an affine record, whose whole is handed to whatever reads it.
data Mention = Mention
  { _place :: !Place,
    _snap :: !Int,
    _deep :: !Bool,
    -- | Fields of the object at the place this mention does not read: an
    -- update's base, which replaces them.
    _except :: ![Name]
  }
  deriving (Eq, Ord)

mention :: Place -> Int -> Bool -> Mention
mention p snap deep = Mention p snap deep []

-- | Whether the path is at or under a field the mention does not read.
excepted :: Mention -> [Step] -> Bool
excepted (Mention (Place _ q) _ _ except) r =
  any (\f -> (q ++ [SField f]) `List.isPrefixOf` r) except

type Ms = Set Mention

-- | A write of the fields of the object at the path, in place: a mention
-- reads it when it reads a field of that object now, or hands on a value the
-- object is in.
shallowHits :: [Step] -> Mention -> Bool
shallowHits p m@(Mention (Place _ q) snap deep _) =
  (length p >= snap && length p < length q && p `List.isPrefixOf` q)
    || (deep && q `List.isPrefixOf` p && not (excepted m p))

-- | The object at the path and everything under it handed to something that
-- may write any of it: a mention reads it when it reads a field of an object
-- at or under the path now, or hands on a value that holds one.
deepHits :: [Step] -> Mention -> Bool
deepHits r m@(Mention (Place _ q) snap deep _) =
  (r `List.isPrefixOf` q && length q - 1 >= max snap (length r))
    || (deep && (r `List.isPrefixOf` q || (q `List.isPrefixOf` r && not (excepted m r))))

hitsIn :: ([Step] -> Mention -> Bool) -> Place -> Ms -> Bool
hitsIn hits (Place root path) ms =
  any (hits path) (Set.toList (Set.filter (\m -> _root (_place m) == root) ms))

-- | A shared place under which nothing is written: a write at or under it.
taintedShallow :: Set Place -> Place -> Bool
taintedShallow taint (Place root p) =
  any (\(Place r q) -> r == root && q `List.isPrefixOf` p) (Set.toList taint)

taintedDeep :: Set Place -> Place -> Bool
taintedDeep taint (Place root p) =
  any (\(Place r q) -> r == root && (q `List.isPrefixOf` p || p `List.isPrefixOf` q)) (Set.toList taint)

-- | What a mention of a value already handed on holds: the object at the
-- place, read when it was handed.
held :: Place -> Mention
held p =
  mention p (length (_path p)) True

-- THE WALK

-- | A local: the place it names, and how many of its steps are a snapshot.
data Ref = Ref
  { _refPlace :: !Place,
    _refSnap :: !Int,
    _refTracked :: !Bool
  }

data JoinInfo = JoinInfo
  { -- | The first root number bound inside the join.
    _joinStart :: Int,
    -- | What may be read once the join is entered, of what is bound outside
    -- it: its body's mentions, those of every join it may jump to, and what
    -- follows the 'Core.EJoin' that binds it.
    _joinAfter :: Ms
  }

data Env = Env
  { _prog :: Prog,
    _facts :: Facts,
    _def :: Core.QualName,
    _names :: Map Name Ref,
    -- | Whether a root's value was its own when it was bound: nothing else
    -- held it, but what '_coOf' names.
    _rootExcl :: IntMap.IntMap Bool,
    -- | Where a root's value may share an object with another place's: a
    -- call's result and its arguments, a record and its fields' locals.
    _coOf :: IntMap.IntMap [CoLink],
    -- | What each root is, for the report.
    _rootWhat :: IntMap.IntMap String,
    _next :: Int,
    _joins :: Map Name JoinInfo,
    _taint :: Set Place,
    _joinExcl :: Map Name [Bool]
  }

-- | The object at '_mine', under a root, may be or hold the object at
-- '_other', or the other way round.
data CoLink = CoLink
  { _mine :: [Step],
    _other :: Place
  }

-- Strict, so that a walk's 'Out' holds what it says and not the walk: a
-- lazy field would keep every environment that made it alive.
data Out = Out
  { _outCalls :: !(Map Core.QualName [Bool]),
    _outTaint :: !(Set Place),
    _outJoins :: !(Map Name [Bool]),
    _outStash :: !(Set Int),
    -- | A root and the roots its value was made from.
    _outDerived :: !(Map Int (Set Int)),
    -- | For @GENG_INPLACE_REPORT@: each affine update, and why it copies.
    -- Empty when no report is asked for.
    _outLines :: ![String]
  }

instance Semigroup Out where
  Out a b c d e f <> Out a' b' c' d' e' f' =
    Out (Map.unionWith (zipWith (&&)) a a') (Set.union b b') (Map.unionWith (zipWith (&&)) c c') (Set.union d d') (Map.unionWith Set.union e e') (say (f ++ f'))

instance Monoid Out where
  mempty = Out Map.empty Set.empty Map.empty Set.empty Map.empty []

-- | An expression walked. '_ms', '_flow' and '_co' depend on nothing but the
-- names in scope, so that a sibling's walk can be given them before it is
-- done.
data R = R
  { _expr :: Core.Expr,
    -- | What it reads.
    _ms :: Ms,
    -- | The places whose objects may be in its value.
    _flow :: [Place],
    -- | The places whose objects may be in its value, or share one with it:
    -- '_flow''s and more. The places themselves, not what the links in scope
    -- say they share ('closeCo'): a value made of two disjoint places of a
    -- root that holds nothing twice holds nothing twice.
    _co :: Set Place,
    -- | Its value holds nothing that anything but '_flow' and '_co' holds.
    _ex :: Bool,
    -- | Its value is held by nothing else once it is handed on: '_ex', and
    -- nothing read after it reads '_flow' or '_co'.
    _x :: Bool,
    _out :: Out,
    -- | The joins it jumps to.
    _jumps :: Set Name,
    -- | For the report: why '_x' is false.
    _why :: String
  }

data Def = Def
  { _defExpr :: Core.Expr,
    _defResult :: Bool,
    _defOut :: Out,
    _defStash :: [Bool]
  }

-- | A definition walked, with its own joins' and escapes' facts taken to a
-- fixed point. With @allExclusive@, every parameter is taken as handed a value
-- nothing else holds, which is what the function's '_fresh' asks: whether
-- its result holds nothing but what it made and what it was handed.
definition :: Prog -> Facts -> Bool -> Core.QualName -> Core.Expr -> Def
definition prog facts allExclusive q value =
  go Set.empty Map.empty (0 :: Int)
  where
    (params, body) = Maybe.fromMaybe ([], value) (lambdaOf value)
    n = length params
    paramExcl
      | allExclusive = replicate n True
      | otherwise = Map.findWithDefault (replicate n False) q (_excl facts)
    go taint joinExcl rounds =
      let env =
            Env
              { _prog = prog,
                _facts = facts,
                _def = q,
                _names = Map.fromList [(Core._binderName b, Ref (Place i []) 0 (holdsRec prog (Core._binderType b))) | (i, b) <- zip [0 ..] params],
                _rootExcl = IntMap.fromList (zip [0 ..] paramExcl),
                _coOf = IntMap.empty,
                _rootWhat = IntMap.fromList [(i, "parameter " ++ Name.toChars (Core._binderName b)) | (i, b) <- zip [0 ..] params],
                _next = n,
                _joins = Map.empty,
                _taint = taint,
                _joinExcl = joinExcl
              }
          r = walk env Set.empty Set.empty body
          out = _out r
          taint' = Set.union taint (_outTaint out)
          joinExcl' = Map.unionWith (zipWith (&&)) joinExcl (_outJoins out)
          settled = taint' == taint && joinExcl' == joinExcl
       in if rounds >= 100
            then Def value False (nothingOut out) (replicate n True)
            else
              if settled
                then
                  let stashed = closeStash (_outDerived out) (_outStash out)
                      rebuilt = if null params then _expr r else rewrap value (_expr r)
                      -- The result may be a parameter's value, or hold one:
                      -- fresh is what it holds besides.
                      result = _ex r && all (\p -> _root p < n) (Set.toList (_co r))
                   in Def rebuilt result out [Set.member i stashed | i <- [0 .. n - 1]]
                else go taint' joinExcl' (rounds + 1)
    nothingOut out = out {_outCalls = Map.map (map (const False)) (_outCalls out), _outLines = []}

-- | The definition with its lambda's body replaced.
rewrap :: Core.Expr -> Core.Expr -> Core.Expr
rewrap e body =
  case Core._exprValue e of
    Core.ELam bs _ -> e {Core._exprValue = Core.ELam bs body}
    Core.ETyLam vs inner -> e {Core._exprValue = Core.ETyLam vs (rewrap inner body)}
    _ -> body

closeStash :: Map Int (Set Int) -> Set Int -> Set Int
closeStash derived = grow
  where
    grow seen =
      let next = Set.union seen (Set.unions [Map.findWithDefault Set.empty r derived | r <- Set.toList seen])
       in if next == seen then seen else grow next

isExcl :: Env -> Int -> Bool
isExcl env r = IntMap.findWithDefault False r (_rootExcl env)

-- | The places a value at the place may share an object with, besides it.
shareOf :: Env -> Place -> Set Place
shareOf env (Place r path) =
  Set.fromList
    [ _other l
    | l <- IntMap.findWithDefault [] r (_coOf env),
      _mine l `List.isPrefixOf` path || path `List.isPrefixOf` _mine l
    ]

-- | The places whose objects may be, or hold, the one at the place. A link
-- says no more than that two subtrees may share an object somewhere, so
-- the other place stands whole.
sameAs :: Env -> Place -> [Place]
sameAs env (Place r path) =
  [ _other l
  | l <- IntMap.findWithDefault [] r (_coOf env),
    _mine l `List.isPrefixOf` path
  ]

-- | The objects under the one at the place that may be another place's: the
-- path under the place's root, and the other place.
sharedBelow :: Env -> Place -> [([Step], Place)]
sharedBelow env (Place r path) =
  [ (_mine l, _other l)
  | l <- IntMap.findWithDefault [] r (_coOf env),
    path `List.isPrefixOf` _mine l,
    path /= _mine l
  ]

-- | The places, and every place one of them may share an object with.
closeCo :: Env -> Set Place -> Set Place
closeCo env places = Set.union places (Set.unions [shareOf env p | p <- Set.toList places])

-- | A local's field path, as a place.
placeOf :: Env -> Core.Expr -> Maybe (Ref, [Step])
placeOf env e0 = go e0 []
  where
    go e steps =
      case Core._exprValue e of
        Core.EVar x -> (\ref -> (ref, steps)) <$> Map.lookup x (_names env)
        Core.EAccess base f -> go base (SField f : steps)
        _ -> Nothing

-- | Whether something in @keep@ holds or reads a value made of the places'
-- objects, or sharing one with the roots: one of the places read or handed on
-- (by the paths), or one of the other roots mentioned at all.
heldIn :: [Place] -> Set Place -> Ms -> Bool
heldIn flow co keep =
  any (\p -> hitsIn deepHits p keep) (Set.toList (Set.union (Set.fromList flow) co))

-- | What a value holds or shares, as places.
holdsPlaces :: R -> [Place]
holdsPlaces r =
  Set.toList (Set.union (Set.fromList (_flow r)) (_co r))

-- | The same, and every place the links in scope say they may share with.
holdsClosed :: Env -> R -> [Place]
holdsClosed env r =
  Set.toList (closeCo env (Set.fromList (holdsPlaces r)))

heldAll :: [Place] -> Ms
heldAll = Set.fromList . map held

-- | An expression walked. @live@ is what is read after it is evaluated,
-- which a write inside it may not be read by; @keep@ is what holds or reads
-- its value once the value is handed on, which decides whether the value is
-- held by nothing else.
walk :: Env -> Ms -> Ms -> Core.Expr -> R
walk env live keep e =
  settle env keep e (walkNode env live keep e)

-- | What 'walk' adds to a node's own walk: whether something in @keep@ holds
-- its value.
settle :: Env -> Ms -> Core.Expr -> R -> R
settle env keep e r =
  if holdsRec (_prog env) (Core._exprType e)
    then
      let held_ = heldIn (_flow r) (closeCo env (_co r)) keep
       in r
            { _x = _ex r && not held_,
              _why = if _ex r then (if held_ then "held by what is read after it: " ++ whoHolds env r keep else "") else _why r
            }
    else r {_x = True, _ex = True, _co = Set.empty, _flow = []}

whoHolds :: Env -> R -> Ms -> String
whoHolds env r keep =
  List.intercalate ", " (take 3 [IntMap.findWithDefault "?" (_root (_place m)) (_rootWhat env) ++ show (_path (_place m)) | m <- Set.toList keep, any (\p -> _root p == _root (_place m) && deepHits (_path p) m) (holdsPlaces r)])

leaf :: Core.Expr -> R
leaf e = R e Set.empty [] Set.empty False False mempty Set.empty (constructorOf e)

walkNode :: Env -> Ms -> Ms -> Core.Expr -> R
walkNode env live keep e =
  case placeOf env e of
    Just (ref, steps) ->
      let p = Place (_root (_refPlace ref)) (_path (_refPlace ref) ++ steps)
          deep = holdsRec (_prog env) (Core._exprType e)
          m = mention p (_refSnap ref) deep
          own = isExcl env (_root p) && not (taintedDeep (_taint env) p)
       in if _refTracked ref
            then
              R
                { _expr = e,
                  _ms = Set.singleton m,
                  _flow = [p | deep],
                  _co = Set.singleton p,
                  _ex = own,
                  _x = own,
                  _out = mempty,
                  _jumps = Set.empty,
                  _why =
                    if isExcl env (_root p)
                      then IntMap.findWithDefault "?" (_root p) (_rootWhat env) ++ " was handed on while it was still read"
                      else "not its own: " ++ IntMap.findWithDefault "?" (_root p) (_rootWhat env)
                }
            else (leaf e) {_why = "not tracked"}
    Nothing ->
      case Core._exprValue e of
        Core.EVar _ -> leaf e
        Core.EGlobal _ -> (leaf e) {_ex = isFunction (Core._exprType e), _why = "a global"}
        Core.ELit _ -> (leaf e) {_ex = True}
        Core.ECrash (Core.Todo place message) ->
          let r = walk env live live message
           in r {_expr = e {Core._exprValue = Core.ECrash (Core.Todo place (_expr r))}, _ex = True, _co = Set.empty, _flow = []}
        Core.ECrash _ -> (leaf e) {_ex = True}
        Core.ELam binders body -> lambda env e binders body
        Core.ELetRec binds body -> letRec env live keep e binds body
        Core.ELet binds body -> lets env live keep e binds body
        Core.ECase scrut alts fallback -> caseOf env live keep e scrut alts fallback
        Core.ECtor q tag args ->
          let ks = siblings env live keep args
           in built e ks (Core.ECtor q tag (map (_expr . fst) ks))
        Core.ERecord fields ->
          let ks = siblings env live keep (map snd fields)
           in built e ks (Core.ERecord (zip (map fst fields) (map (_expr . fst) ks)))
        Core.EArray items ->
          let ks = siblings env live keep items
           in built e ks (Core.EArray (map (_expr . fst) ks))
        Core.EUpdate base fields _ -> update env live keep e base fields
        Core.EAccess _ _ -> accessChain env live e
        Core.EApp fn args -> call env live keep e fn args
        Core.EWitApp fn args -> unknownCall env live e fn args Core.EWitApp
        Core.EPrim op args ->
          -- A primitive keeps what it is handed only in its result, and its
          -- result may be what a builder holds.
          let ks = siblings env live live args
              rs = map fst ks
              keeps = holdsRec (_prog env) (Core._exprType e)
           in (combine rs)
                { _expr = e {Core._exprValue = Core.EPrim op (map _expr rs)},
                  _flow = [],
                  _ex = False,
                  _out = foldMap _out rs <> (if keeps then escapes env rs else mempty),
                  _why = "a primitive's result"
                }
        Core.EJoin binds body -> joins env live keep e binds body
        Core.EJump j args -> jump env e j args
        Core.ETyLam vs body ->
          let r = walk env live keep body
           in r {_expr = e {Core._exprValue = Core.ETyLam vs (_expr r)}}
        Core.ETyApp fn tys ->
          let r = walk env live keep fn
           in r {_expr = e {Core._exprValue = Core.ETyApp (_expr r) tys}}
        Core.EWitLam binders body -> lambda env e binders body

-- | An access chain whose record is not a local's, walked from the record
-- out, each access's value settled as 'walk' would: walking each access
-- whole would look for the chain's local again at each, n² for a chain n long.
accessChain :: Env -> Ms -> Core.Expr -> R
accessChain env live e0 =
  let (record, levels) = unwind e0 []
      step (r, left) node =
        let raw = accessed node r
         in (if left == (1 :: Int) then raw else settle env live node raw, left - 1)
   in fst (List.foldl' step (walk env live live record, length levels) levels)
  where
    -- The record, and the accesses from the innermost out.
    unwind e acc =
      case Core._exprValue e of
        Core.EAccess base _ -> unwind base (e : acc)
        _ -> (e, acc)
    accessed node r =
      case Core._exprValue node of
        Core.EAccess _ f ->
          r
            { _expr = node {Core._exprValue = Core.EAccess (_expr r) f},
              _flow = [Place root (path ++ [SField f]) | Place root path <- _flow r],
              _ex = False,
              _why = "a field of something not a local"
            }
        _ -> r

isFunction :: Core.Type -> Bool
isFunction t =
  case t of
    Core.TFun _ _ -> True
    Core.TForall _ _ body -> isFunction body
    _ -> False

-- | Expressions evaluated one after another and handed on together: each is
-- evaluated before what the later ones read, while the values the earlier
-- ones made are held; once handed on, each is held beside all the others'.
-- Each comes with whether it shares nothing with the others.
siblings :: Env -> Ms -> Ms -> [Core.Expr] -> [(R, Bool)]
siblings env live keep kids = zip rs alone
  where
    rs = lazyZip3 (\k after (before, others) -> walk env (Set.unions [live, after, before]) (Set.union keep others) k) kids afters heldBy
    holds r = heldAll (holdsClosed env r)
    afters = drop 1 (scanr (\r acc -> Set.union (_ms r) acc) Set.empty rs)
    befores = scanl (\acc r -> Set.union acc (holds r)) Set.empty rs
    laters = drop 1 (scanr (\r acc -> Set.union (holds r) acc) Set.empty rs)
    heldBy = lazyZip3 (\_ b l -> (b, Set.union b l)) kids befores laters
    alone = lazyZip3 (\r _ (_, others) -> _ex r && not (heldIn (_flow r) (_co r) others)) rs kids heldBy

-- | 'zipWith3' with its spine the first list's alone: the other two are
-- made from what it answers, and are read only when an element is.
lazyZip3 :: (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
lazyZip3 f as bs cs =
  case as of
    [] -> []
    a : rest -> f a (head' bs) (head' cs) : lazyZip3 f rest (drop 1 bs) (drop 1 cs)
  where
    head' xs = case xs of
      x : _ -> x
      [] -> error "Core.Pass.InPlace.lazyZip3: a list shorter than the first"

combine :: [R] -> R
combine rs =
  R
    { _expr = error "Core.Pass.InPlace: combine has no expression",
      _ms = Set.unions (map _ms rs),
      _flow = concatMap _flow rs,
      _co = Set.unions (map _co rs),
      _ex = all _ex rs,
      _x = all _x rs,
      _out = foldMap _out rs,
      _jumps = Set.unions (map _jumps rs),
      _why = firstWhy rs
    }

firstWhy :: [R] -> String
firstWhy rs =
  case [_why r | r <- rs, not (_x r)] of
    w : _ -> w
    [] -> ""

-- | What a value that keeps its parts where nothing follows them does to the
-- parts something else holds too: they are shared from now on.
escapes :: Env -> [R] -> Out
escapes env rs =
  mempty {_outTaint = Set.fromList (concat [holdsClosed env r | r <- rs, not (_x r)])}

-- | A record, constructor or array literal: a new value holding its parts,
-- its own when each part shares nothing with another.
built :: Core.Expr -> [(R, Bool)] -> Core.Expr_ -> R
built e ks node =
  let rs = map fst ks
   in (combine rs)
        { _expr = e {Core._exprValue = node},
          _ex = and (map snd ks),
          _why = "a part is shared: " ++ firstWhy rs
        }

-- | A new root, its value its own or not, sharing with the roots given.
bindRoot :: Env -> String -> Core.Binder -> Bool -> Set Place -> (Env, Int)
bindRoot env what b excl co =
  let i = _next env
   in ( env
          { _names = Map.insert (Core._binderName b) (Ref (Place i []) 0 (holdsRec (_prog env) (Core._binderType b))) (_names env),
            _rootExcl = IntMap.insert i excl (_rootExcl env),
            _coOf =
              foldr
                (\q m -> IntMap.insertWith (++) (_root q) [CoLink (_path q) (Place i [])] m)
                (IntMap.insert i [CoLink [] q | q <- Set.toList co] (_coOf env))
                (Set.toList co),
            _rootWhat = IntMap.insert i (what ++ " " ++ Name.toChars (Core._binderName b)) (_rootWhat env),
            _next = i + 1
          },
        i
      )

-- | A function: what it captures is shared from now on, since the closure
-- may be called at any time, and its parameters are handed values nothing
-- says are exclusive.
lambda :: Env -> Core.Expr -> [Core.Binder] -> Core.Expr -> R
lambda env e binders body =
  let start = _next env
      inner = foldl (\en b -> fst (bindRoot en "a lambda's parameter" b False Set.empty)) env {_joins = Map.empty} binders
      r = walk inner Set.empty Set.empty body
      outer = Set.filter (\m -> _root (_place m) < start) (_ms r)
      -- A number read when an alias was bound is not read again, whatever
      -- is written after.
      capturedPlaces = closeCo env (Set.fromList [Place (_root (_place m)) [] | m <- Set.toList outer, _deep m || _snap m < length (_path (_place m))])
      captured = Set.map _root capturedPlaces
      node = case Core._exprValue e of
        Core.EWitLam bs _ -> Core.EWitLam bs (_expr r)
        _ -> Core.ELam binders (_expr r)
   in R
        { _expr = e {Core._exprValue = node},
          _ms = outer,
          _flow = [],
          _co = Set.empty,
          _ex = True,
          _x = True,
          _out = (_out r) {_outTaint = Set.union (_outTaint (_out r)) capturedPlaces, _outStash = Set.union (_outStash (_out r)) captured, _outLines = say (_outLines (_out r) ++ keptLines env "a closure" captured)},
          _jumps = Set.empty,
          _why = ""
        }

letRec :: Env -> Ms -> Ms -> Core.Expr -> [Core.Bind] -> Core.Expr -> R
letRec env live keep e binds body =
  let inner = foldl (\en (Core.Bind b _) -> fst (bindRoot en "a recursive function" b False Set.empty)) env binds
      values = [walk inner Set.empty Set.empty v | Core.Bind _ v <- binds]
      rb = walk inner live keep body
      all_ = rb : values
   in (combine all_)
        { _expr = e {Core._exprValue = Core.ELetRec [Core.Bind b (_expr r) | (Core.Bind b _, r) <- zip binds values] (_expr rb)},
          _flow = _flow rb,
          _co = _co rb,
          _ex = _ex rb,
          _why = _why rb
        }

lets :: Env -> Ms -> Ms -> Core.Expr -> [Core.Bind] -> Core.Expr -> R
lets env live keep e binds body =
  case binds of
    [] -> walk env live keep body
    Core.Bind b v : rest ->
      let restExpr = case rest of
            [] -> body
            _ -> e {Core._exprValue = Core.ELet rest body}
          rebuild v' inner =
            case Core._exprValue (_expr inner) of
              Core.ELet more body' | not (null rest) -> Core.ELet (Core.Bind b v' : more) body'
              _ -> Core.ELet [Core.Bind b v'] (_expr inner)
       in case placeOf env v of
            Just (ref, steps) ->
              let p = Place (_root (_refPlace ref)) (_path (_refPlace ref) ++ steps)
                  alias = Ref p (length (_path p)) (_refTracked ref)
                  inner = walk env {_names = Map.insert (Core._binderName b) alias (_names env)} live keep restExpr
                  readNow = [mention p (_refSnap ref) False | _refTracked ref]
               in inner
                    { _expr = e {Core._exprValue = rebuild v inner},
                      _ms = Set.union (Set.fromList readNow) (_ms inner)
                    }
            Nothing ->
              let (env', i) = bindRoot env "a let" b (_ex rv) (alive after (closeCo env (_co rv)))
                  inner = walk env' live keep restExpr
                  after = Set.union (_ms inner) live
                  rv = walk env after after v
                  mine m = _root (_place m) == i
                  derived = Set.fromList [_root (_place m) | m <- Set.toList (_ms rv)]
                  flowOut = concat [if _root p == i then _flow rv else [p] | p <- _flow inner]
                  coOut =
                    if any (\q -> _root q == i) (Set.toList (_co inner))
                      then Set.union (Set.filter (\q -> _root q /= i) (_co inner)) (_co rv)
                      else _co inner
               in R
                    { _expr = e {Core._exprValue = rebuild (_expr rv) inner},
                      _ms = Set.union (_ms rv) (Set.filter (not . mine) (_ms inner)),
                      _flow = flowOut,
                      _co = coOut,
                      _ex = _ex inner,
                      _x = _x inner,
                      _out = _out rv <> _out inner <> mempty {_outDerived = Map.singleton i derived},
                      _jumps = Set.union (_jumps rv) (_jumps inner),
                      _why = _why inner ++ (if _ex rv then "" else " (" ++ Name.toChars (Core._binderName b) ++ ": " ++ _why rv ++ ")")
                    }

caseOf :: Env -> Ms -> Ms -> Core.Expr -> Core.Expr -> [Core.Alt] -> Maybe Core.Expr -> R
caseOf env live keep e scrut alts fallback =
  let (scrutR, armEnv, armPlace, armTracked, extraOut) =
        case placeOf env scrut of
          Just (ref, steps) ->
            let p = Place (_root (_refPlace ref)) (_path (_refPlace ref) ++ steps)
                m = [mention p (_refSnap ref) True | _refTracked ref]
             in ((leaf scrut) {_ms = Set.fromList m, _ex = True}, env, p, _refTracked ref, mempty)
          Nothing ->
            let hidden = Core.Binder (hiddenName (_next env)) (Core._exprType scrut) (Core.spanOf scrut)
                (env', i) = bindRoot env "what a case matched," hidden (_ex rs) (alive after (closeCo env (_co rs)))
                after = Set.union armsMs live
                rs = walk env after after scrut
             in ( rs,
                  env',
                  Place i [],
                  True,
                  mempty {_outDerived = Map.singleton i (Set.fromList [_root (_place m) | m <- Set.toList (_ms rs)])}
                )
      arm pat body = walk (bindPattern armEnv armTracked armPlace pat) live keep body
      armRs = [arm pat body | Core.Alt pat body <- alts]
      fallbackR = fmap (walk armEnv live keep) fallback
      armsMs = Set.unions (map _ms armRs ++ maybe [] (pure . _ms) fallbackR)
      every = armRs ++ Maybe.maybeToList fallbackR
      hiddenRoot = case placeOf env scrut of
        Just _ -> Nothing
        Nothing -> Just (_next env)
      scrubCo co = case hiddenRoot of
        Just h | any (\q -> _root q == h) (Set.toList co) -> Set.union (Set.filter (\q -> _root q /= h) co) (_co scrutR)
        _ -> co
   in R
        { _expr = e {Core._exprValue = Core.ECase (_expr scrutR) [Core.Alt pat (_expr r) | (Core.Alt pat _, r) <- zip alts armRs] (fmap _expr fallbackR)},
          _ms = Set.union (_ms scrutR) armsMs,
          _flow = concatMap _flow every,
          _co = scrubCo (Set.unions (map _co every)),
          _ex = all _ex every,
          _x = all _x every,
          _out = _out scrutR <> extraOut <> foldMap _out every,
          _jumps = Set.unions (_jumps scrutR : map _jumps every),
          _why = "a case: " ++ firstWhy every
        }

-- | The places whose roots something reads after a binding: a value may
-- share an object with one nothing reads again, and no read can see it. The
-- places are closed over the links already ('closeCo'), so a root reached
-- through a dead one is still there.
alive :: Ms -> Set Place -> Set Place
alive after co =
  let roots = Set.map (_root . _place) after
   in Set.filter (\q -> Set.member (_root q) roots) co

-- | A name no source can write, for what a case matched when that is not a
-- local.
hiddenName :: Int -> Name
hiddenName i = Name.fromChars ("$scrutinee" ++ show i)

-- | A pattern's binders, each an alias of the place it matched, read when the
-- match was made. An array's elements are not places in it: each is a root
-- of its own that nothing says is exclusive.
bindPattern :: Env -> Bool -> Place -> Core.Pattern -> Env
bindPattern env tracked p pat =
  case pat of
    Core.PVar b -> alias b
    Core.PWild -> env
    Core.PLit _ -> env
    Core.PAs b inner -> bindPattern (alias b) tracked p inner
    Core.PCtor _ tag pats ->
      foldl (\en (i, sub) -> bindPattern en tracked (extend (SCtor tag i)) sub) env (zip [0 ..] pats)
    Core.PRecord fields ->
      foldl (\en (f, sub) -> bindPattern en tracked (extend (SField f)) sub) env fields
    Core.PArray pats rest ->
      foldl (\en b -> fst (bindRoot en "an array pattern's" b False (Set.singleton p))) env (concatMap patternBinders pats ++ Maybe.maybeToList rest)
  where
    alias b = env {_names = Map.insert (Core._binderName b) (Ref p (length (_path p)) tracked) (_names env)}
    extend s = p {_path = _path p ++ [s]}

patternBinders :: Core.Pattern -> [Core.Binder]
patternBinders pat =
  case pat of
    Core.PVar b -> [b]
    Core.PWild -> []
    Core.PLit _ -> []
    Core.PAs b inner -> b : patternBinders inner
    Core.PCtor _ _ pats -> concatMap patternBinders pats
    Core.PRecord fields -> concatMap (patternBinders . snd) fields
    Core.PArray pats rest -> concatMap patternBinders pats ++ Maybe.maybeToList rest

-- | A record update: written in place when the record is the base's alone and
-- nothing reads it after. The base is evaluated first, then the fields, and
-- the record is written once every field's value is made.
update :: Env -> Ms -> Ms -> Core.Expr -> Core.Expr -> [(Core.Field, Core.Expr)] -> R
update env live keep e base fields =
  let replaced = map fst fields
      basePlace = fmap (\(ref, steps) -> (ref, Place (_root (_refPlace ref)) (_path (_refPlace ref) ++ steps))) (placeOf env base)
      -- Where the record is: the base's place, and the places it may share.
      anchors = case basePlace of
        Just (_, p) -> p : sameAs env p
        Nothing -> []
      -- Objects under the record that other places may hold: a field that
      -- the update replaces may take one, and nothing else may.
      below = case basePlace of
        Just (_, p) -> [(mine, other) | (mine, other) <- sharedBelow env p, not (any (\f -> (_path p ++ [SField f]) `List.isPrefixOf` mine) replaced)]
        Nothing -> []
      -- A field may read the base's own fields, and take one it replaces.
      under q = any (\a -> _root a == _root q && any (\f -> (_path a ++ [SField f]) `List.isPrefixOf` _path q) replaced) anchors
      -- The fields the update keeps are held by the new value.
      kept = case Core._exprType base of
        Core.TRecord fs _ | not (null anchors) -> heldAll [Place (_root a) (_path a ++ [SField f]) | a <- anchors, (f, _) <- fs, f `notElem` replaced]
        _ -> heldAll (holdsClosed env baseR)
      fieldRs = lazyZip3 (\(_, v) after (before, others) -> walk env (Set.unions [live, after, before, kept]) (Set.unions [keep, others, kept]) v) fields afters heldBy
      holds r = heldAll (holdsClosed env r)
      afters = drop 1 (scanr (\r acc -> Set.union (_ms r) acc) Set.empty fieldRs)
      befores = scanl (\acc r -> Set.union acc (holds r)) Set.empty fieldRs
      laters = drop 1 (scanr (\r acc -> Set.union (holds r) acc) Set.empty fieldRs)
      heldBy = lazyZip3 (\_ b l -> (b, Set.union b l)) fields befores laters
      fieldAlone = lazyZip3 (\r _ (_, others) -> _ex r && not (heldIn (_flow r) (_co r) (Set.union others kept))) fieldRs fields heldBy
      fieldMs = Set.unions (map _ms fieldRs)
      fieldHolds = concatMap (holdsClosed env) fieldRs
      baseHeldBy = heldAll (filter (not . under) fieldHolds)
      baseR = walk env (Set.union live fieldMs) (Set.union keep baseHeldBy) base
      baseAlone = _ex baseR && not (heldIn (_flow baseR) (_co baseR) baseHeldBy)
      affine = affineRec (_prog env) (Core._exprType e)
      -- No field may put the record, or a part of it the update keeps, into
      -- the record: a write would then be read through it.
      overlaps a q = _root a == _root q && (_path a `List.isPrefixOf` _path q || _path q `List.isPrefixOf` _path a)
      -- Only a field whose type can hold the record's can hold the record:
      -- values make no cycles, so a field made from the record's parts holds
      -- the record only if one of them holds a value of its type.
      canHold r = mayContain (_prog env) (Core._exprType (_expr r)) (Core._exprType e)
      embeds = case basePlace of
        Just _ ->
          any (\r -> canHold r && any (\q -> (not (under q) && any (`overlaps` q) anchors) || any ((`overlaps` q) . snd) below) (holdsClosed env r)) fieldRs
        Nothing -> any (\r -> canHold r && any (\q -> any (`overlaps` q) (holdsClosed env baseR)) (holdsClosed env r)) fieldRs
      coRead = any (\o -> hitsIn shallowHits o live) (drop 1 anchors)
      why = case basePlace of
        Just (ref, p)
          | not (_refTracked ref) -> Just "the base is not tracked"
          | not (isExcl env (_root p)) -> Just ("the record is not the base's alone: " ++ IntMap.findWithDefault "?" (_root p) (_rootWhat env))
          | taintedShallow (_taint env) p -> Just "the record is shared: it was handed on while it was still read"
          | hitsIn shallowHits p live -> Just "the record is read after the update"
          | coRead -> Just "what may share the record is read after the update"
          | embeds -> Just "a field puts the record into itself"
          | otherwise -> Nothing
        Nothing
          | not (_x baseR) -> Just "the base is not a value nothing else holds"
          | embeds -> Just "a field puts the record into itself"
          | otherwise -> Nothing
      inPlace = affine && Maybe.isNothing why
      baseMs = case basePlace of
        Just _ -> Set.map (\m -> m {_except = List.sort replaced}) (_ms baseR)
        Nothing -> _ms baseR
      rs = baseR : fieldRs
      line =
        [ List.intercalate "\t" [Name.toChars (ModuleName._module (Core._qnHome (_def env))), Name.toChars (Core._qnName (_def env)), spanText (Core.spanOf e), maybe "in place" id why]
        | affine
        ]
   in R
        { _expr = e {Core._exprValue = Core.EUpdate (_expr baseR) (zip replaced (map _expr fieldRs)) (if inPlace then Core.InPlace else Core.Copy)},
          _ms = Set.unions (baseMs : map _ms fieldRs),
          _flow = concatMap _flow rs,
          _co = Set.unions (map _co rs),
          _ex = baseAlone && and fieldAlone,
          _x = all _x rs,
          _out = foldMap _out rs <> mempty {_outLines = say line},
          _jumps = Set.unions (map _jumps rs),
          _why = "an update: " ++ firstWhy rs
        }

spanText :: Core.Span -> String
spanText sp =
  show (Core._spanStartRow sp) ++ ":" ++ show (Core._spanStartCol sp)

-- | A call. Its arguments are evaluated in turn, and then the function runs,
-- after which what is read later may read what it wrote.
call :: Env -> Ms -> Ms -> Core.Expr -> Core.Expr -> [Core.Expr] -> R
call env live keep e fn args =
  case Core._exprValue (peelTyApp fn) of
    Core.EGlobal q
      | Just arity <- Map.lookup q (_fns (_prog env)),
        arity == length args ->
          let facts = _facts env
              ks = siblings env live live args
              rs = map fst ks
              stash = Map.findWithDefault (replicate arity True) q (_stash facts)
              shared = Set.fromList (concat [holdsClosed env r | (r, True) <- zip rs stash, not (_x r)])
              stashed = Set.fromList [_root (_place m) | (r, True) <- zip rs stash, m <- Set.toList (_ms r), _deep m]
              fresh = Map.findWithDefault False q (_fresh facts)
              lines_ =
                [ List.intercalate "\t" [Name.toChars (ModuleName._module (Core._qnHome (_def env))), Name.toChars (Core._qnName (_def env)), spanText (Core.spanOf a), "hands " ++ Name.toChars (Core._qnName q) ++ " argument " ++ show i ++ " shared: " ++ _why r]
                | (i, a, r) <- zip3 [0 :: Int ..] args rs,
                  not (_x r),
                  affineRec (_prog env) (Core._exprType a)
                ]
           in R
                { _expr = e {Core._exprValue = Core.EApp fn (map _expr rs)},
                  _ms = Set.unions (map _ms rs),
                  _flow = [],
                  _co = Set.unions (map _co rs),
                  _ex = fresh && and (map snd ks),
                  _x = False,
                  _out = foldMap _out rs <> mempty {_outCalls = Map.singleton q (map _x rs), _outTaint = shared, _outStash = stashed, _outLines = say (lines_ ++ keptLines env ("a call of " ++ Name.toChars (Core._qnName q)) stashed)},
                  _jumps = Set.unions (map _jumps rs),
                  _why =
                    if fresh
                      then "a call of " ++ Name.toChars (Core._qnName q) ++ ", " ++ concat ["argument " ++ show i ++ ": " ++ _why r ++ "; " | (i, (r, alone)) <- zip [0 :: Int ..] ks, not alone]
                      else "a call of " ++ Name.toChars (Core._qnName q) ++ ", whose result is not fresh"
                }
    -- A partial application holds what it is given, as a record does.
    Core.EGlobal q
      | Just arity <- Map.lookup q (_fns (_prog env)),
        arity > length args ->
          let ks = siblings env live keep args
           in (built e ks (Core.EApp fn (map (_expr . fst) ks))) {_why = "a partial application: " ++ firstWhy (map fst ks)}
    _ -> unknownCall env live e fn args Core.EApp

-- | For the report: the roots something may keep, and what keeps them.
keptLines :: Env -> String -> Set Int -> [String]
keptLines env what roots =
  [ List.intercalate "\t" [Name.toChars (ModuleName._module (Core._qnHome (_def env))), Name.toChars (Core._qnName (_def env)), "-", "kept by " ++ what ++ ": " ++ IntMap.findWithDefault "?" r (_rootWhat env)]
  | r <- Set.toList roots
  ]

constructorOf :: Core.Expr -> String
constructorOf a =
  case Core._exprValue a of
    Core.EApp f _ ->
      "a call of " ++ case Core._exprValue (peelTyApp f) of
        Core.EGlobal q -> Name.toChars (Core._qnName q)
        _ -> "a function value"
    Core.EUpdate _ _ _ -> "an update"
    Core.ELet _ _ -> "a let"
    Core.ECase _ _ _ -> "a case"
    Core.EJoin _ _ -> "a join"
    Core.ERecord _ -> "a record"
    Core.EPrim _ _ -> "a primitive"
    Core.EGlobal _ -> "a global"
    _ -> "something else"

-- | A call of something that may keep what it is handed: an extern, a
-- function value or a partial application.
unknownCall :: Env -> Ms -> Core.Expr -> Core.Expr -> [Core.Expr] -> (Core.Expr -> [Core.Expr] -> Core.Expr_) -> R
unknownCall env live e fn args node =
  let rs = map fst (siblings env live live (fn : args))
      stashed = Set.map _root (closeCo env (Set.fromList [Place (_root (_place m)) [] | r <- rs, m <- Set.toList (_ms r), _deep m]))
   in case rs of
        fnR : argRs ->
          (combine rs)
            { _expr = e {Core._exprValue = node (_expr fnR) (map _expr argRs)},
              _flow = [],
              _ex = False,
              _out = foldMap _out rs <> escapes env rs <> mempty {_outStash = stashed, _outLines = say (keptLines env ("a call of " ++ constructorOf e) stashed)},
              _why = "a call of " ++ constructorOf e
            }
        [] -> leaf e

-- | Joins: each one's parameters are roots, exclusive when every jump to it
-- hands a value nothing else holds; what may be read once one is entered is
-- worked out over the group, so that a jump's arguments are checked against
-- it.
joins :: Env -> Ms -> Ms -> Core.Expr -> [Core.Bind] -> Core.Expr -> R
joins env live keep e binds body =
  let start = _next env
      infos = Map.fromList [(Core._binderName b, JoinInfo start (after (Core._binderName b))) | Core.Bind b _ <- binds]
      env' = env {_joins = Map.union infos (_joins env)}
      walkJoin (Core.Bind b v) =
        let name = Core._binderName b
         in case Core._exprValue v of
              Core.ELam params jbody ->
                let excl = Map.findWithDefault (map (const True) params) name (_joinExcl env)
                    inner = foldl (\en (p, x) -> fst (bindRoot en "a join's parameter" p x Set.empty)) env' (zip params (excl ++ repeat False))
                    r = walk inner live keep jbody
                 in (name, r {_expr = v {Core._exprValue = Core.ELam params (_expr r)}, _co = Set.filter (\q -> _root q < start) (_co r)})
              _ -> (name, walk env' live keep v)
      walked = map walkJoin binds
      own = Map.fromList [(name, Set.filter (\m -> _root (_place m) < start) (_ms r)) | (name, r) <- walked]
      targets = Map.fromList [(name, _jumps r) | (name, r) <- walked]
      after name = Set.union live (reach name)
      reach name = Set.unions [Map.findWithDefault (outerAfter t) t own | t <- Set.toList (closure (Set.singleton name))]
      outerAfter t = maybe Set.empty _joinAfter (Map.lookup t (_joins env))
      closure seen =
        let next = Set.union seen (Set.unions [Map.findWithDefault Set.empty t targets | t <- Set.toList seen, Map.member t targets])
         in if next == seen then seen else closure next
      rb = walk env' live keep body
      every = rb : map snd walked
   in R
        { _expr = e {Core._exprValue = Core.EJoin [Core.Bind b (_expr r) | (Core.Bind b _, (_, r)) <- zip binds walked] (_expr rb)},
          _ms = Set.unions (map _ms every),
          _flow = concatMap _flow every,
          _co = Set.unions (map _co every),
          _ex = all _ex every,
          _x = all _x every,
          _out = foldMap _out every,
          _jumps = Set.difference (Set.unions (map _jumps every)) (Map.keysSet infos),
          _why = "a join: " ++ firstWhy every
        }

jump :: Env -> Core.Expr -> Name -> [Core.Expr] -> R
jump env e j args =
  let info = Map.lookup j (_joins env)
      live = maybe Set.empty _joinAfter info
      rs = map fst (siblings env live live args)
      start = maybe 0 _joinStart info
   in R
        { _expr = e {Core._exprValue = Core.EJump j (map _expr rs)},
          _ms = Set.unions (map _ms rs),
          _flow = [],
          _co = Set.empty,
          _ex = True,
          _x = True,
          _out =
            foldMap _out rs
              <> escapes env rs
              <> mempty
                { _outJoins = Map.singleton j (map _x rs),
                  _outLines =
                    say
                      [ List.intercalate "\t" [Name.toChars (ModuleName._module (Core._qnHome (_def env))), Name.toChars (Core._qnName (_def env)), spanText (Core.spanOf a), "jumps to " ++ Name.toChars j ++ " with argument " ++ show i ++ " shared: " ++ _why r]
                      | (i, a, r) <- zip3 [0 :: Int ..] args rs,
                        not (_x r),
                        affineRec (_prog env) (Core._exprType a)
                      ],
                  _outDerived = Map.fromList [(start + i, Set.fromList [_root (_place m) | m <- Set.toList (_ms r)]) | (i, r) <- zip [0 ..] rs]
                },
          _jumps = Set.singleton j,
          _why = ""
        }
