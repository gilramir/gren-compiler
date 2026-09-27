{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | A local group of functions whose calls to one another are all tail calls
-- becomes one self-recursive function, which "Core.Pass.TailCall" then makes a
-- loop (D479, geng-lang @docs/pre-m3-tail.md@ §MT4).
--
-- "Core.Pass.TailCall" loops self-recursion only, so before this pass a local
-- @isEven@/@isOdd@ pair overflowed node's stack between 5,000 and 10,000 deep
-- while the BEAM ran it ten million deep (§MT1). Rewritten, the group is one
-- function on every backend, C included, and it is faster where it already
-- worked: a thousand million calls between members are 3.3 to 10.8 times
-- quicker on node and 1.7 to 10.2 on the BEAM (§MT3).
--
-- __What is a group__: a strongly connected part of an 'Core.ELetRec' of two or
-- more members. The letrec is split into its parts first, since the
-- specializer puts every copy of a constrained local into the one letrec
-- (D357), and copies do not call each other. A part is taken when every member
-- is an 'Core.ELam' and every reference from a member to a member is a
-- saturated call in tail position of the member's body, where tail position
-- runs through @let@, @letrec@, the alternatives and fallback of a case, and
-- both halves of a join, as it does in "Core.Pass.TailCall". A member named as
-- a value, applied partially, or called anywhere else leaves its part as it is.
--
-- __Two forms__, since Core is typed and one function has one list of
-- parameter types. The results always agree: a tail call from one member to
-- another makes their results one type.
--
-- > isEven k = … isOdd (k - 1)        $g0 = \$g0$i $g0$0 ->
-- > isOdd k = … isEven (k - 1)          case $g0$i of
-- >                                       0 -> let k = $g0$0 in … $g0 1 (k - 1)
-- >                                       _ -> let k = $g0$0 in … $g0 0 (k - 1)
-- >                                   isEven = \k -> $g0 0 k
--
-- When every member takes the same parameter types, the function takes a
-- member's index and those parameters. When they differ, the pass declares a
-- data type in the module, one constructor per member carrying its arguments,
-- and the function takes one of those: a constructor built on every call,
-- which is still faster than the group as it was on both backends (§MT3). The
-- type is named @$G@ and a number, which no source can write, and its
-- parameters are the type variables the members' parameters mention.
--
-- __Each member the rest of the program names__ becomes a wrapper that calls
-- the function; one named only inside the group is not written.
--
-- __It runs after inlining and before "Core.Pass.Case" builds its constructor
-- table__, so that it sees the groups after the specializer has taken away
-- every type and witness abstraction, and so that a declaration it makes is in
-- the table the case pass compiles its patterns with.
module Core.Pass.Mutual
  ( run,
  )
where

import Control.Monad.Trans.State.Strict (State, runState, state)
import Core.AST qualified as Core
import Data.Graph qualified as Graph
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set (Set)
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName

-- | What rewriting a module makes: a counter for fresh names, and the data
-- types the second form declares, in the order they were made.
data Made = Made
  { _madeNext :: !Int,
    _madeData :: ![Core.DataDecl]
  }

type Fresh a = State Made a

fresh :: Fresh Int
fresh = state (\(Made n ds) -> (n, Made (n + 1) ds))

declare :: Core.DataDecl -> Fresh ()
declare d = state (\(Made n ds) -> ((), Made n (d : ds)))

run :: Core.Module -> Core.Module
run m =
  let home = Core._moduleName m
      (defs, Made _ made) = runState (traverse (topLevel home) (Core._moduleDefs m)) (Made 0 [])
   in m
        { Core._moduleDefs = defs,
          Core._moduleData = Core._moduleData m ++ reverse made
        }

topLevel :: ModuleName.Canonical -> Core.Bind -> Fresh Core.Bind
topLevel home (Core.Bind binder value) = Core.Bind binder <$> walk home value

-- WALKING

-- | Every letrec in the expression, innermost first, so that a group inside a
-- member's body is already one function when its enclosing group is looked at.
walk :: ModuleName.Canonical -> Core.Expr -> Fresh Core.Expr
walk home expr =
  let node v = Core.Expr v (Core.typeOf expr) (Core.spanOf expr)
      recur = walk home
      bindM (Core.Bind b v) = Core.Bind b <$> recur v
   in case Core._exprValue expr of
        Core.ELetRec binds body ->
          do
            binds' <- traverse bindM binds
            body' <- recur body
            letRec home (Core.typeOf expr) (Core.spanOf expr) binds' body'
        Core.ELet binds body -> node <$> (Core.ELet <$> traverse bindM binds <*> recur body)
        Core.EJoin binds body -> node <$> (Core.EJoin <$> traverse bindM binds <*> recur body)
        Core.EJump j args -> node . Core.EJump j <$> traverse recur args
        Core.ELam binders body -> node . Core.ELam binders <$> recur body
        Core.EApp fn args -> node <$> (Core.EApp <$> recur fn <*> traverse recur args)
        Core.ECase scrutinee alts fallback ->
          node
            <$> ( Core.ECase
                    <$> recur scrutinee
                    <*> traverse (\(Core.Alt p b) -> Core.Alt p <$> recur b) alts
                    <*> traverse recur fallback
                )
        Core.ECtor q tag args -> node . Core.ECtor q tag <$> traverse recur args
        Core.ERecord fields -> node . Core.ERecord <$> traverse (\(f, e) -> (,) f <$> recur e) fields
        Core.EUpdate base fields ->
          node <$> (Core.EUpdate <$> recur base <*> traverse (\(f, e) -> (,) f <$> recur e) fields)
        Core.EAccess base f -> node . (`Core.EAccess` f) <$> recur base
        Core.EArray items -> node . Core.EArray <$> traverse recur items
        Core.EPrim op args -> node . Core.EPrim op <$> traverse recur args
        Core.ETyLam vars body -> node . Core.ETyLam vars <$> recur body
        Core.ETyApp body types -> node . (`Core.ETyApp` types) <$> recur body
        Core.EWitLam binders body -> node . Core.EWitLam binders <$> recur body
        Core.EWitApp body args -> node <$> (Core.EWitApp <$> recur body <*> traverse recur args)
        Core.EVar _ -> pure expr
        Core.EGlobal _ -> pure expr
        Core.ELit _ -> pure expr
        Core.ECrash (Core.Todo place message) -> node . Core.ECrash . Core.Todo place <$> recur message
        Core.ECrash _ -> pure expr

-- LETREC

-- | A letrec with no group the pass takes is returned as it was. One with a
-- group is split into its strongly connected parts, each bound around the
-- ones that use it, and each group among them is rewritten.
letRec :: ModuleName.Canonical -> Core.Type -> Core.Span -> [Core.Bind] -> Core.Expr -> Fresh Core.Expr
letRec home ty sp binds body =
  let names = Set.fromList (map (Core._binderName . Core._bindBinder) binds)
      parts =
        Graph.stronglyConnComp
          [ (b, Core._binderName (Core._bindBinder b), Set.toList (Set.intersection names (free (Core._bindValue b))))
          | b <- binds
          ]
      taken = [ms | Graph.CyclicSCC ms <- parts, length ms >= 2, takes ms]
      node v = Core.Expr v ty sp
   in if null taken
        then pure (node (Core.ELetRec binds body))
        else do
          -- 'Graph.stronglyConnComp' answers a part after every part it uses,
          -- so the first part is bound outermost.
          let used = free body
          foldr (bindPart used) (pure body) (zip parts (map (neededOutside parts) parts))
  where
    bindPart used (part, outside) inner =
      do
        inner' <- inner
        let node v = Core.Expr v ty sp
        case part of
          Graph.AcyclicSCC b -> pure (node (Core.ELet [b] inner'))
          Graph.CyclicSCC ms
            | length ms >= 2 && takes ms ->
                group home ty sp ms (Set.union used outside) inner'
            | otherwise -> pure (node (Core.ELetRec ms inner'))

    -- The names of this part that another part uses.
    neededOutside parts part =
      Set.unions
        [ free (Core._bindValue b)
        | other <- parts,
          otherNames other /= otherNames part,
          b <- Graph.flattenSCC other
        ]

    otherNames = map (Core._binderName . Core._bindBinder) . Graph.flattenSCC

-- | Whether the pass takes a strongly connected part.
takes :: [Core.Bind] -> Bool
takes ms =
  let arities = Map.fromList [(Core._binderName b, n) | Core.Bind b v <- ms, Just n <- [arity v]]
   in Map.size arities == length ms
        && and [onlyTailCalls arities True Set.empty body | Core.Bind _ v <- ms, Just body <- [lamBody v]]

arity :: Core.Expr -> Maybe Int
arity e =
  case Core._exprValue e of
    Core.ELam params _ -> Just (length params)
    _ -> Nothing

lamBody :: Core.Expr -> Maybe Core.Expr
lamBody e =
  case Core._exprValue e of
    Core.ELam _ body -> Just body
    _ -> Nothing

-- | Every reference to a member is a saturated call in tail position. The
-- set is the names bound between the member's body and here, which hide a
-- member of the same name.
onlyTailCalls :: Map.Map Name Int -> Bool -> Set Name -> Core.Expr -> Bool
onlyTailCalls members inTail hidden expr =
  let member n = Map.member n members && not (Set.member n hidden)
      inner = onlyTailCalls members
   in case Core._exprValue expr of
        Core.EVar n -> not (member n)
        Core.EApp fn args
          | Core.EVar n <- Core._exprValue fn,
            member n ->
              inTail && Map.lookup n members == Just (length args) && all (inner False hidden) args
          | otherwise -> inner False hidden fn && all (inner False hidden) args
        Core.ELam params body -> inner False (Set.union hidden (binderNames params)) body
        Core.ELet binds body ->
          all (inner False hidden . Core._bindValue) binds
            && inner inTail (Set.union hidden (bindNames binds)) body
        Core.ELetRec binds body ->
          let hidden' = Set.union hidden (bindNames binds)
           in all (inner False hidden' . Core._bindValue) binds && inner inTail hidden' body
        Core.EJoin binds body ->
          let hidden' = Set.union hidden (bindNames binds)
              joinBody v =
                case Core._exprValue v of
                  Core.ELam params b -> inner inTail (Set.union hidden' (binderNames params)) b
                  _ -> inner False hidden' v
           in all (joinBody . Core._bindValue) binds && inner inTail hidden' body
        Core.ECase scrutinee alts fallback ->
          inner False hidden scrutinee
            && all (\(Core.Alt p b) -> inner inTail (Set.union hidden (patternNames p)) b) alts
            && all (inner inTail hidden) fallback
        _ -> all (inner False hidden) (children expr)

-- REWRITING A GROUP

-- | One part, rewritten: the group's function, and a wrapper for each member
-- named in @outside@, around @inner@.
group :: ModuleName.Canonical -> Core.Type -> Core.Span -> [Core.Bind] -> Set Name -> Core.Expr -> Fresh Core.Expr
group home ty sp ms outside inner =
  do
    n <- fresh
    let members = [(Core._bindBinder b, params, body) | b <- ms, Core.ELam params body <- [Core._exprValue (Core._bindValue b)]]
        signatures = [map Core._binderType params | (_, params, _) <- members]
        result = case members of
          (_, _, body) : _ -> Core.typeOf body
          [] -> ty
        prefix = "$g" ++ show n
        fn = Name.fromChars prefix
        indexOf = Map.fromList (zip [Core._binderName b | (b, _, _) <- members] [0 ..])
        node v t = Core.Expr v t sp
    (params, scrutinee, alts, callOf) <-
      case signatures of
        first : rest | all (== first) rest -> pure (byIndex prefix sp members)
        _ -> bySum home prefix sp members
    let fnType = Core.TFun (map Core._binderType params) result
        call args i = node (Core.EApp (node (Core.EVar fn) fnType) (callOf i args)) result
        alts' = [Core.Alt p (retarget indexOf call Set.empty b) | Core.Alt p b <- alts]
        fnValue = node (Core.ELam params (node (Core.ECase scrutinee alts' Nothing) result)) fnType
        wrappers =
          [ Core.Bind b (node (Core.ELam ps (call [node (Core.EVar (Core._binderName p)) (Core._binderType p) | p <- ps] i)) (Core._binderType b))
          | ((b, ps, _), i) <- zip members [0 :: Int ..],
            Set.member (Core._binderName b) outside
          ]
        withWrappers = if null wrappers then inner else node (Core.ELet wrappers inner) (Core.typeOf inner)
    pure (node (Core.ELetRec [Core.Bind (Core.Binder fn fnType sp) fnValue] withWrappers) (Core.typeOf inner))

-- | The first form: the function takes a member's index and the parameters
-- every member shares, and each alternative binds the member's own names to
-- them.
byIndex :: String -> Core.Span -> [(Core.Binder, [Core.Binder], Core.Expr)] -> ([Core.Binder], Core.Expr, [Core.Alt], Int -> [Core.Expr] -> [Core.Expr])
byIndex prefix sp members =
  let shared = case members of
        (_, params, _) : _ -> map Core._binderType params
        [] -> []
      index = Core.Binder (Name.fromChars (prefix ++ "$i")) intT sp
      slots = [Core.Binder (Name.fromChars (prefix ++ "$" ++ show k)) t sp | (k, t) <- zip [0 :: Int ..] shared]
      var b = Core.Expr (Core.EVar (Core._binderName b)) (Core._binderType b) sp
      alt i (_, params, body) =
        let pat = if i == length members - 1 then Core.PWild else Core.PLit (Core.LInt (fromIntegral i))
            bound = Core.Expr (Core.ELet [Core.Bind p (var s) | (p, s) <- zip params slots] body) (Core.typeOf body) sp
         in Core.Alt pat bound
      callOf i args = Core.Expr (Core.ELit (Core.LInt (fromIntegral i))) intT sp : args
   in (index : slots, var index, zipWith alt [0 ..] members, callOf)

-- | The second form: a data type with a constructor per member, carrying that
-- member's arguments, and a function of one of them.
bySum :: ModuleName.Canonical -> String -> Core.Span -> [(Core.Binder, [Core.Binder], Core.Expr)] -> Fresh ([Core.Binder], Core.Expr, [Core.Alt], Int -> [Core.Expr] -> [Core.Expr])
bySum home prefix sp members =
  do
    let dataName = Core.QualName home (Name.fromChars ("$G" ++ drop 2 prefix))
        vars = List.nub (concatMap (typeVars . Core._binderType) [p | (_, params, _) <- members, p <- params])
        dataType = Core.TCon dataName (map Core.TVar vars)
        ctorName b = Core.QualName home (Name.fromChars ("$G" ++ drop 2 prefix ++ "$" ++ Name.toChars (Core._binderName b)))
        ctors = [Core.Ctor (ctorName b) i (map Core._binderType params) | ((b, params, _), i) <- zip members [0 ..]]
        arg = Core.Binder (Name.fromChars (prefix ++ "$c")) dataType sp
        alt (Core.Ctor q i _) (_, params, body) = Core.Alt (Core.PCtor q i (map Core.PVar params)) body
        callOf i args =
          case drop i ctors of
            Core.Ctor q tag _ : _ -> [Core.Expr (Core.ECtor q tag args) dataType sp]
            [] -> error "Core.Pass.Mutual: a call to a member the group does not have"
    declare
      Core.DataDecl
        { Core._dataName = dataName,
          Core._dataParams = vars,
          Core._dataTransparency = Core.Transparent,
          Core._dataCtors = ctors,
          Core._dataClasses = []
        }
    pure ([arg], Core.Expr (Core.EVar (Core._binderName arg)) dataType sp, zipWith alt ctors members, callOf)

-- | Every call to a member, which 'takes' has found only in tail position,
-- becomes a call to the group's function.
retarget :: Map.Map Name Int -> ([Core.Expr] -> Int -> Core.Expr) -> Set Name -> Core.Expr -> Core.Expr
retarget members call hidden expr =
  let node v = Core.Expr v (Core.typeOf expr) (Core.spanOf expr)
      member n = if Set.member n hidden then Nothing else Map.lookup n members
      recur = retarget members call
   in case Core._exprValue expr of
        Core.EApp fn args
          | Core.EVar n <- Core._exprValue fn,
            Just i <- member n ->
              call args i
        Core.ELet binds body -> node (Core.ELet binds (recur (Set.union hidden (bindNames binds)) body))
        Core.ELetRec binds body -> node (Core.ELetRec binds (recur (Set.union hidden (bindNames binds)) body))
        Core.EJoin binds body ->
          let hidden' = Set.union hidden (bindNames binds)
              joinValue v =
                case Core._exprValue v of
                  Core.ELam params b -> Core.Expr (Core.ELam params (recur (Set.union hidden' (binderNames params)) b)) (Core.typeOf v) (Core.spanOf v)
                  _ -> v
           in node (Core.EJoin [Core.Bind b (joinValue v) | Core.Bind b v <- binds] (recur hidden' body))
        Core.ECase scrutinee alts fallback ->
          node
            ( Core.ECase
                scrutinee
                [Core.Alt p (recur (Set.union hidden (patternNames p)) b) | Core.Alt p b <- alts]
                (fmap (recur hidden) fallback)
            )
        _ -> expr

-- NAMES

-- | The local names an expression uses and does not bind.
free :: Core.Expr -> Set Name
free expr =
  case Core._exprValue expr of
    Core.EVar n -> Set.singleton n
    Core.ELam params body -> Set.difference (free body) (binderNames params)
    Core.EWitLam params body -> Set.difference (free body) (binderNames params)
    Core.ELet binds body ->
      Set.union (Set.unions (map (free . Core._bindValue) binds)) (Set.difference (free body) (bindNames binds))
    Core.ELetRec binds body -> Set.difference (Set.unions (free body : map (free . Core._bindValue) binds)) (bindNames binds)
    Core.EJoin binds body -> Set.difference (Set.unions (free body : map (free . Core._bindValue) binds)) (bindNames binds)
    Core.ECase scrutinee alts fallback ->
      Set.unions
        ( free scrutinee
            : maybe Set.empty free fallback
            : [Set.difference (free b) (patternNames p) | Core.Alt p b <- alts]
        )
    _ -> Set.unions (map free (children expr))

-- | The sub-expressions of a node with no binders of its own.
children :: Core.Expr -> [Core.Expr]
children expr =
  case Core._exprValue expr of
    Core.EVar _ -> []
    Core.EGlobal _ -> []
    Core.ELit _ -> []
    Core.ELam _ body -> [body]
    Core.EApp fn args -> fn : args
    Core.ELet binds body -> body : map Core._bindValue binds
    Core.ELetRec binds body -> body : map Core._bindValue binds
    Core.EJoin binds body -> body : map Core._bindValue binds
    Core.ECase scrutinee alts fallback -> scrutinee : map Core._altBody alts ++ Maybe.maybeToList fallback
    Core.ECtor _ _ args -> args
    Core.ERecord fields -> map snd fields
    Core.EUpdate base fields -> base : map snd fields
    Core.EAccess base _ -> [base]
    Core.EArray items -> items
    Core.EPrim _ args -> args
    Core.EJump _ args -> args
    Core.ETyLam _ body -> [body]
    Core.ETyApp body _ -> [body]
    Core.EWitLam _ body -> [body]
    Core.EWitApp body args -> body : args
    Core.ECrash (Core.Todo _ message) -> [message]
    Core.ECrash _ -> []

binderNames :: [Core.Binder] -> Set Name
binderNames = Set.fromList . map Core._binderName

bindNames :: [Core.Bind] -> Set Name
bindNames = binderNames . map Core._bindBinder

patternNames :: Core.Pattern -> Set Name
patternNames p =
  case p of
    Core.PVar b -> Set.singleton (Core._binderName b)
    Core.PWild -> Set.empty
    Core.PLit _ -> Set.empty
    Core.PCtor _ _ ps -> Set.unions (map patternNames ps)
    Core.PRecord fields -> Set.unions (map (patternNames . snd) fields)
    Core.PArray ps rest -> Set.unions (maybe Set.empty (Set.singleton . Core._binderName) rest : map patternNames ps)
    Core.PAs b inner -> Set.insert (Core._binderName b) (patternNames inner)

-- | The type variables a type mentions and does not quantify, in the order
-- they are first met.
typeVars :: Core.Type -> [Name]
typeVars t =
  case t of
    Core.TVar n -> [n]
    Core.TCon _ args -> concatMap typeVars args
    Core.TFun args res -> concatMap typeVars args ++ typeVars res
    Core.TRecord fields row -> concatMap (typeVars . snd) fields ++ Maybe.maybeToList row
    Core.TForall bound _ body -> filter (`notElem` bound) (typeVars body)

intT :: Core.Type
intT = Core.TCon (Core.QualName ModuleName.basics "Int") []
