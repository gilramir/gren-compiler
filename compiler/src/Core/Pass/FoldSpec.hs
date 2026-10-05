{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | A fold copied for the function it is handed (geng-lang @m3-fold.md@, D579,
-- D581): @core@'s six folds are loops that take a function and hand it back to
-- themselves unchanged, and a call that hands one a lambda or a known function
-- gets a copy of the loop with that function's body in it, so that the loop
-- calls nothing through a pointer.
--
-- > foldlHelp fn acc a i n = … foldlHelp fn (fn (get a i) acc) a (i + 1) n
-- > Array.foldl (\x d -> Dict.set x 1 d) Dict.empty xs
-- >   ⟹ foldlHelp$q1 Dict.empty xs 0 (unsafeLength xs)
-- >      foldlHelp$q1 acc a i n = … foldlHelp$q1 (let x = get a i; d = acc in Dict.set x 1 d) a (i + 1) n
--
-- It saves nothing measurable alone (§FL5): a call through a pointer costs
-- little beside what a loop body does. What it is for is the loop it leaves,
-- which "Core.Pass.Transient" can then see (D579): a fold's accumulator is a
-- loop's parameter only once the fold is a loop of its own.
--
-- __Which loops__: 'folds', @Array@'s four loops and @Dict.foldl@ and
-- @foldr@, the parameter of function type each hands back to itself unchanged
-- (static) and calls. Every other loop that takes a function is left alone
-- until a program shows it pays for its size (D579, §FL3–§FL4).
--
-- __Which wrappers__: a function that does not call itself and hands its own
-- parameter of function type to such a loop's, or to another wrapper's, found
-- to a fixed point: @Array.foldl@ hands @fn@ to @foldlHelp@. __A small wrapper
-- is opened at the call__ (D581): its body is written where the call was, its
-- arguments bound as a call's are, and the loop it calls copied from there, so
-- that no copy of the wrapper is made. Natively the inliner would open it
-- anyway; on JavaScript nothing does (D487), and the wrappers' copies were
-- most of what the JavaScript grew by (§FL4). A larger one is copied, as the
-- loop is.
--
-- __Which arguments__: a lambda written at the call, one a @let@ in scope
-- binds, or a global. What the lambda names and does not bind becomes the
-- copy's first parameters, passed at the call before the others, so that a
-- partial application of the copy is still one. @x |> Array.foldl f d@ is
-- the call @Array.foldl f d x@, as the JavaScript backend writes it, with @x@
-- bound first so that it is still evaluated first.
--
-- __The copy__: the loop's body with the parameter replaced by the function,
-- its binders renamed at each use, every self call pointed at the copy, and a
-- lambda applied at once turned into @let@s. Its type is the loop's with the
-- variables the function fixes substituted. __One copy per caller module and
-- function__, the function compared with its binders renamed and its spans
-- taken out; a copy lives in the caller's module, as the inliner's copies do,
-- and its root has the span of the call that made it, as an inlined body's
-- has (D514): the nodes under it keep the rows of the file they were written
-- in, and a backend places them where their parent is.
--
-- __Where it runs__: after @specialize@, so that what it copies has no
-- witness left to pass, and before @mono@, which copies the copy by shape like
-- any other definition (D491), and before @inline@. A pass is optional (C4):
-- the program answers the same without it.
--
-- With @GENG_FOLDSPEC_CENSUS=<file>@ it appends every call site it looked at,
-- what it was handed and what it did, and every copy it made with its size, to
-- the file (@bench/memory/fold/census.py@ reads it).
module Core.Pass.FoldSpec
  ( run,
  )
where

import Control.Monad (foldM, forM)
import Control.Monad.Trans.State.Strict (State, evalState, get, gets, modify', put, runState)
import Core.AST qualified as Core
import Core.Pass.Inline qualified as Inline
import Core.Pass.Specialize qualified as Specialize
import Core.Refs qualified as Refs
import Data.Functor.Identity (Identity (..))
import Data.Graph qualified as Graph
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Monoid (Any (..), Sum (..))
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set (Set)
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName
import System.Environment qualified as Env
import System.IO.Unsafe (unsafePerformIO)

census :: Maybe FilePath
census = unsafePerformIO (Env.lookupEnv "GENG_FOLDSPEC_CENSUS")
{-# NOINLINE census #-}

-- | D579's six: the loops @Array.foldl@, @foldr@, @indexedFoldl@ and
-- @indexedFoldr@ run, and @Dict.foldl@ and @Dict.foldr@.
folds :: Set Core.QualName
folds =
  Set.fromList $
    [Core.QualName ModuleName.array n | n <- ["foldlHelp", "foldrHelp", "indexedFoldlHelp", "indexedFoldrHelp"]]
      ++ [Core.QualName ModuleName.dict n | n <- ["foldl", "foldr"]]

-- | How deep a copy of a copy, or a wrapper opened in a wrapper, may go.
depthCap :: Int
depthCap = 6

-- | The most nodes a wrapper's body may have to be opened at the call rather
-- than copied: room for a body that is one call, as @Array.foldl@'s is, with a
-- little arithmetic in its arguments.
openCap :: Int
openCap = 24

data Info = Info
  { _params :: [Core.Binder],
    _body :: Core.Expr,
    _type :: Core.Type,
    _self :: Bool
  }

data St = St
  { _fresh :: !Int,
    _copies :: Map (ModuleName.Canonical, String) Core.QualName,
    _made :: [(Core.QualName, Core.Expr, Int)],
    _log :: [(Core.QualName, String)]
  }

type M a = State St a

data Env = Env
  { _useful :: Map Core.QualName [Int],
    _infos :: Map Core.QualName Info
  }

data Ctx = Ctx
  { _home :: ModuleName.Canonical,
    _def :: Core.QualName,
    _depth :: Int,
    _lets :: Map Name Core.Expr,
    _staticHere :: Set Name
  }

run :: Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
run cores =
  let space = Inline.fileSpace cores
      defs =
        Map.fromList
          [ (Core.QualName home (Core._binderName b), (Core._binderType b, Inline.toGlobal space modul v))
          | (home, modul) <- Map.toList cores,
            Core.Bind b v <- Core._moduleDefs modul
          ]
      externs =
        Set.fromList
          [ Core.QualName home (Core._binderName (Core._externBinder e))
          | (home, modul) <- Map.toList cores,
            e <- Core._moduleExterns modul
          ]
      sccs =
        Graph.stronglyConnComp
          [ (q, q, Set.toList (Refs._refGlobals (Refs.refsIn v)))
          | (q, (_, v)) <- Map.toList defs
          ]
      selfRec = Set.fromList [q | Graph.CyclicSCC [q] <- sccs]
      mutual = Set.fromList [q | Graph.CyclicSCC g@(_ : _ : _) <- sccs, q <- g]
      infos =
        Map.fromList
          [ (q, Info ps body (Specialize.unquantified t) (Set.member q selfRec))
          | (q, (t, Core.Expr (Core.ELam ps body) _ _)) <- Map.toList defs,
            not (Set.member q externs),
            not (Set.member q mutual)
          ]
      env = Env (fixpoint infos (Map.mapWithKey staticPositions infos)) infos
      (rewritten, st) =
        runState
          ( forM (Map.toList defs) $ \(q, (_, v)) ->
              do
                v' <- walk env (Ctx (Core._qnHome q) q 0 Map.empty (staticNames env q)) v
                return (q, v')
          )
          (St 0 Map.empty [] [])
      made = reverse (_made st)
      madeTypes = Map.fromList [(q, Core.typeOf v) | (q, v, _) <- made]
      changed = Set.fromList [q | (q, v') <- rewritten, Just (_, v) <- [Map.lookup q defs], v' /= v]
      out =
        Map.mapWithKey
          ( \home modul ->
              let mine = Map.fromList [(Core._qnName q, v) | (q, v) <- rewritten, Core._qnHome q == home, Set.member q changed]
                  added =
                    [ (Core.Binder (Core._qnName q) (madeTypes Map.! q) (Core.spanOf v), v)
                    | (q, v, _) <- made,
                      Core._qnHome q == home
                    ]
               in if Map.null mine && null added then modul else putBack space home modul mine added
          )
          cores
   in case census of
        Nothing -> out
        Just path ->
          unsafePerformIO $ do
            let allDefs = Map.union (Map.fromList rewritten) (Map.fromList [(q, v) | (q, v, _) <- made])
                reached = reach cores allDefs
                reachedTag q = if Set.member q reached then "reached" else "dead"
                siteLines = [l ++ "\t" ++ reachedTag q | (q, l) <- reverse (_log st)]
                copyLines =
                  [ "copy\t" ++ showQ q ++ "\t" ++ show sz ++ "\t" ++ reachedTag q
                  | (q, _, sz) <- made
                  ]
                usefulLines = ["useful\t" ++ showQ q ++ "\t" ++ show is | (q, is) <- Map.toList (_useful env), not (null is)]
            appendFile path (unlines (usefulLines ++ siteLines ++ copyLines))
            return out

showQ :: Core.QualName -> String
showQ (Core.QualName (ModuleName.Canonical _ m) n) = Name.toChars m ++ "\t" ++ Name.toChars n

-- STATIC AND USEFUL PARAMETERS

-- | The positions a function's self calls all pass back unchanged: every
-- position, for a function that does not call itself.
staticPositions :: Core.QualName -> Info -> [Int]
staticPositions q (Info ps body _ self)
  | not self = [0 .. length ps - 1]
  | otherwise =
      case usesOf q body of
        Nothing -> []
        Just calls ->
          [ i
          | (i, p) <- zip [0 ..] ps,
            all (\args -> isVar (Core._binderName p) (args !! i)) calls
          ]

isVar :: Name -> Core.Expr -> Bool
isVar n e = case Core._exprValue e of
  Core.EVar m -> m == n
  _ -> False

-- | Every self call's arguments, or 'Nothing' if the name is used other than
-- as the head of a saturated call.
usesOf :: Core.QualName -> Core.Expr -> Maybe [[Core.Expr]]
usesOf q = go
  where
    go e =
      case Core._exprValue e of
        Core.EGlobal g | g == q -> Nothing
        Core.EApp (Core.Expr (Core.EGlobal g) (Core.TFun ts _) _) args
          | g == q ->
              if length ts == length args
                then fmap ((args :) . concat) (mapM go args)
                else Nothing
        _ -> fmap concat (sequence (Specialize.children_ (\c -> [go c]) e))

isFun :: Core.Type -> Bool
isFun t = case Specialize.unquantified t of
  Core.TFun _ _ -> True
  _ -> False

-- | The useful positions, to a fixed point: a fold's static parameter of
-- function type that its body calls, and a wrapper's that it hands to one.
fixpoint :: Map Core.QualName Info -> Map Core.QualName [Int] -> Map Core.QualName [Int]
fixpoint infos statics = go base
  where
    base = Map.mapWithKey seed infos
    seed q info =
      [ i
      | Set.member q folds,
        _self info,
        i <- Map.findWithDefault [] q statics,
        let p = _params info !! i,
        isFun (Core._binderType p),
        applied (Core._binderName p) (_body info)
      ]
    go cur =
      let next = Map.mapWithKey (step cur) infos
       in if next == cur then cur else go next
    step cur q info =
      List.sort . List.nub $
        Map.findWithDefault [] q cur
          ++ [ i
             | not (_self info),
               i <- Map.findWithDefault [] q statics,
               let p = _params info !! i,
               isFun (Core._binderType p),
               passedOn cur (Core._binderName p) (_body info)
             ]

applied :: Name -> Core.Expr -> Bool
applied n e =
  case Core._exprValue e of
    Core.EApp f _ | isVar n f -> True
    _ -> getAny (Specialize.children_ (Any . applied n) e)

passedOn :: Map Core.QualName [Int] -> Name -> Core.Expr -> Bool
passedOn cur n e =
  case Core._exprValue e of
    Core.EApp (Core.Expr (Core.EGlobal g) _ _) args
      | Just is <- Map.lookup g cur,
        any (\i -> i < length args && isVar n (args !! i)) is ->
          True
    _ -> getAny (Specialize.children_ (Any . passedOn cur n) e)

staticNames :: Env -> Core.QualName -> Set Name
staticNames env q =
  case Map.lookup q (_infos env) of
    Just info -> Set.fromList [Core._binderName (_params info !! i) | i <- Map.findWithDefault [] q (_useful env)]
    Nothing -> Set.empty

-- THE WALK

walk :: Env -> Ctx -> Core.Expr -> M Core.Expr
walk env ctx e =
  case Core._exprValue e of
    Core.ELet binds body ->
      do
        (binds', ctx') <-
          foldM
            ( \(acc, c) (Core.Bind b v) ->
                do
                  v' <- walk env c v
                  let c' = case Core._exprValue v' of
                        Core.ELam _ _ -> c {_lets = Map.insert (Core._binderName b) v' (_lets c)}
                        _ -> c {_lets = Map.delete (Core._binderName b) (_lets c)}
                  return (acc ++ [Core.Bind b v'], c')
            )
            ([], ctx)
            binds
        body' <- walk env ctx' body
        return e {Core._exprValue = Core.ELet binds' body'}
    _ ->
      do
        flat <- flatten env e
        case flat of
          Just e1 -> walk env ctx e1
          Nothing ->
            do
              e' <- Specialize.childrenA (walk env ctx) e
              site env ctx e'

-- | A call to a fold or a wrapper written as more than one application, made
-- one: @x |> f a@ and @f a <| x@ are @f a x@ (with @x@ bound first when it
-- moves after @a@), and @(f a) b@ is @f a b@.
flatten :: Env -> Core.Expr -> M (Maybe Core.Expr)
flatten env e =
  case Core._exprValue e of
    Core.EApp (Core.Expr (Core.EGlobal (Core.QualName home name)) _ _) [left, right]
      | home == ModuleName.basics,
        name == Name.fromChars "apR",
        Just (h, as) <- partialOf right ->
          if value left || all value as
            then return (Just e {Core._exprValue = Core.EApp h (as ++ [left])})
            else do
              n <- freshN
              let b = Core.Binder (Name.fromChars ("$q" ++ show n)) (Core.typeOf left) (Core.spanOf left)
                  x = Core.Expr (Core.EVar (Core._binderName b)) (Core.typeOf left) (Core.spanOf left)
              return (Just e {Core._exprValue = Core.ELet [Core.Bind b left] e {Core._exprValue = Core.EApp h (as ++ [x])}})
      | home == ModuleName.basics,
        name == Name.fromChars "apL",
        Just (h, as) <- partialOf left ->
          return (Just e {Core._exprValue = Core.EApp h (as ++ [right])})
    Core.EApp inner later
      | Just (h, as) <- partialOf inner,
        Core.TFun ps _ <- Core.typeOf h,
        length as + length later <= length ps ->
          return (Just e {Core._exprValue = Core.EApp h (as ++ later)})
    _ -> return Nothing
  where
    partialOf f =
      case Core._exprValue f of
        Core.EApp h@(Core.Expr (Core.EGlobal g) (Core.TFun ps _) _) as
          | Map.member g (_useful env),
            length as < length ps ->
              Just (h, as)
        _ -> Nothing

-- | An expression whose evaluation does nothing: moving it changes nothing.
value :: Core.Expr -> Bool
value a = case Core._exprValue a of
  Core.EVar _ -> True
  Core.ELit _ -> True
  Core.EGlobal _ -> True
  Core.ELam _ _ -> True
  _ -> False

site :: Env -> Ctx -> Core.Expr -> M Core.Expr
site env ctx e =
  case Core._exprValue e of
    Core.EApp fn@(Core.Expr (Core.EGlobal g) _ _) args
      | Just is@(_ : _) <- Map.lookup g (_useful env),
        Just info <- Map.lookup g (_infos env),
        length args <= length (_params info),
        g /= _def ctx ->
          do
            let kinds = [(i, classify ctx (args !! i)) | i <- is, i < length args]
                known = [(i, a) | (i, Right a) <- kinds]
                desc = List.intercalate "," [either id (kindOf (args !! i)) k | (i, k) <- kinds]
            if null kinds
              then return e
              else
                if null known || _depth ctx >= depthCap
                  then do
                    logSite ctx g desc (if null known then "unknown" else "depth")
                    return e
                  else
                    if opens info && length args == length (_params info)
                      then do
                        logSite ctx g desc "opened"
                        open env ctx info fn args e
                      else do
                        r <- specialise env ctx g info known (Core.spanOf e)
                        case r of
                          Nothing -> do
                            logSite ctx g desc "nullary"
                            return e
                          Just (copyQ, caps, fresh) ->
                            do
                              logSite ctx g desc (if fresh then "copied" else "shared")
                              let rest = [a | (j, a) <- zip [0 :: Int ..] args, j `notElem` map fst known]
                                  capArgs = [Core.Expr (Core.EVar n) t (Core.spanOf e) | (n, t) <- caps]
                                  copyT = case Core.typeOf fn of
                                    Core.TFun ts r' -> Core.TFun (map snd caps ++ [t | (j, t) <- zip [0 :: Int ..] ts, j `notElem` map fst known]) r'
                                    other -> other
                              return e {Core._exprValue = Core.EApp (Core.Expr (Core.EGlobal copyQ) copyT (Core.spanOf fn)) (capArgs ++ rest)}
    _ -> return e

-- | A wrapper small enough to be written out at the call (D581).
opens :: Info -> Bool
opens info = not (_self info) && size (_body info) <= openCap

kindOf :: Core.Expr -> Core.Expr -> String
kindOf orig a =
  case Core._exprValue orig of
    Core.ELam _ _ -> if Set.null (freeIn a) then "lambda" else "lambda+" ++ show (Set.size (freeIn a))
    Core.EGlobal _ -> "global"
    Core.EVar _ -> if Set.null (freeIn a) then "let-lambda" else "let-lambda+" ++ show (Set.size (freeIn a))
    _ -> "?"

-- | A known function, or why not.
classify :: Ctx -> Core.Expr -> Either String Core.Expr
classify ctx a =
  case Core._exprValue a of
    Core.ELam _ _ -> Right a
    Core.EGlobal _ -> Right a
    Core.EVar n
      | Just l <- Map.lookup n (_lets ctx) -> Right l
      | Set.member n (_staticHere ctx) -> Left "param-static"
      | otherwise -> Left "var"
    Core.EApp _ _ -> Left "call"
    Core.EAccess _ _ -> Left "field"
    Core.ECase {} -> Left "case"
    Core.ELet _ _ -> Left "let"
    _ -> Left "other"

logSite :: Ctx -> Core.QualName -> String -> String -> M ()
logSite ctx g desc outcome =
  case census of
    Nothing -> return ()
    Just _ ->
      modify' $ \s ->
        s {_log = (_def ctx, "site\t" ++ showQ (_def ctx) ++ "\t" ++ showQ g ++ "\t" ++ desc ++ "\t" ++ outcome ++ "\t" ++ show (_depth ctx)) : _log s}

-- OPENING A WRAPPER

-- | The wrapper's body where the call was: its binders renamed, its types
-- fixed by the call's, each argument that is a value written where the
-- parameter was used, if it is used at most once or is a name, and every
-- other argument bound by a @let@ in order, as a call would have evaluated
-- it; then walked again, which copies the loop it calls.
open :: Env -> Ctx -> Info -> Core.Expr -> [Core.Expr] -> Core.Expr -> M Core.Expr
open env ctx info fn args e =
  do
    n0 <- gets _fresh
    let sp = Core.spanOf (_body info)
        lam = Core.Expr (Core.ELam (_params info) (_body info)) (_type info) sp
        (lam', n1) = runState (renameE (\k -> Name.fromChars ("$q" ++ show k)) Map.empty lam) n0
    modify' (\s -> s {_fresh = n1})
    case Core._exprValue lam' of
      Core.ELam ps body ->
        do
          let sub0 = Specialize.matchT (_type info) (Core.typeOf fn)
              callerVars = Set.unions (tyVars (Core.typeOf e) : map allTyVars args)
              clash = [v | v <- Set.toList (allTyVars body), not (Map.member v sub0), Set.member v callerVars]
          k <- freshN
          let sub = Map.union sub0 (Map.fromList [(v, Core.TVar (Name.fromChars (Name.toChars v ++ "$q" ++ show k))) | v <- clash])
              ty = Specialize.substituteT sub
              body' = Specialize.retype ty body
              uses p = occurrences (Core._binderName p) body'
              inline (p, a) =
                case Core._exprValue a of
                  Core.EVar _ -> True
                  Core.ELit _ -> True
                  Core.EGlobal _ -> True
                  Core.ELam _ _ -> uses p <= 1
                  _ -> False
              pairs = zip ps args
              direct = Map.fromList [(Core._binderName p, a) | (p, a) <- pairs, inline (p, a)]
              binds = [Core.Bind p {Core._binderType = ty (Core._binderType p)} a | (p, a) <- pairs, not (inline (p, a))]
              lets' = foldl (\m (Core.Bind b a) -> if isLam a then Map.insert (Core._binderName b) a m else m) (_lets ctx) binds
          walked <- walk env ctx {_depth = _depth ctx + 1, _lets = lets'} (substVars direct body')
          return $
            if null binds
              then walked {Core._exprType = Core.typeOf e, Core._exprSpan = Core.spanOf e}
              else Core.Expr (Core.ELet binds walked) (Core.typeOf e) (Core.spanOf e)
      _ -> return e
  where
    isLam a = case Core._exprValue a of
      Core.ELam _ _ -> True
      _ -> False

-- | How many times a name is used. Every binder in the expression is fresh, so
-- nothing shadows it.
occurrences :: Name -> Core.Expr -> Int
occurrences n e =
  case Core._exprValue e of
    Core.EVar m | m == n -> 1
    _ -> getSum (Specialize.children_ (Sum . occurrences n) e)

-- | Names replaced by expressions. Every binder in the expression is fresh,
-- so nothing is captured.
substVars :: Map Name Core.Expr -> Core.Expr -> Core.Expr
substVars sub e
  | Map.null sub = e
  | otherwise =
      case Core._exprValue e of
        Core.EVar n | Just a <- Map.lookup n sub -> a
        _ -> runIdentity (Specialize.childrenA (Identity . substVars sub) e)

-- THE COPY

specialise ::
  Env ->
  Ctx ->
  Core.QualName ->
  Info ->
  [(Int, Core.Expr)] ->
  Core.Span ->
  M (Maybe (Core.QualName, [(Name, Core.Type)], Bool))
specialise env ctx g info known sp =
  let capNames = Set.toAscList (Set.unions [freeIn a | (_, a) <- known])
      capTypes = Map.unions [varTypes a | (_, a) <- known]
      caps = [(n, capTypes Map.! n) | n <- capNames]
      remaining = [p | (j, p) <- zip [0 ..] (_params info), j `notElem` map fst known]
      keyArgs =
        evalState
          (mapM (\(i, a) -> fmap ((,) i . strip) (renameE (\k -> Name.fromChars ("$k" ++ show k)) (Map.fromList (zip capNames [Name.fromChars ("$c" ++ show k) | k <- [0 :: Int ..]])) a)) known)
          0
      key = showQ g ++ show keyArgs ++ show [t | (_, t) <- caps]
   in if null remaining && null caps
        then return Nothing
        else do
          existing <- gets (Map.lookup (_home ctx, key) . _copies)
          case existing of
            Just q -> return (Just (q, caps, False))
            Nothing -> do
              n <- freshN
              let q = Core.QualName (_home ctx) (Name.fromChars (Name.toChars (Core._qnName g) ++ "$q" ++ show n))
              modify' (\s -> s {_copies = Map.insert (_home ctx, key) q (_copies s)})
              -- types: the callee's variables fixed by the arguments
              let sub0 = Map.unions [Specialize.matchT (Core._binderType (_params info !! i)) (Core.typeOf a) | (i, a) <- known]
                  calleeVars = tyVars (_type info)
                  callerVars = Set.unions [allTyVars a | (_, a) <- known]
                  clash = [v | v <- Set.toList calleeVars, not (Map.member v sub0), Set.member v callerVars]
                  sub = Map.union sub0 (Map.fromList [(v, Core.TVar (Name.fromChars (Name.toChars v ++ "$q" ++ show n))) | v <- clash])
                  ty = Specialize.substituteT sub
                  body0 = Specialize.retype ty (_body info)
                  params' = [p {Core._binderType = ty (Core._binderType p)} | p <- remaining]
                  result' = ty (resultOf (_type info))
              capBinders <- forM caps $ \(cn, ct) -> do
                k <- freshN
                return (cn, Core.Binder (Name.fromChars ("$q" ++ show k)) ct sp)
              let capRename = Map.fromList [(cn, Core._binderName b) | (cn, b) <- capBinders]
                  subst = Map.fromList [(Core._binderName (_params info !! i), a) | (i, a) <- known]
                  allParams = map snd capBinders ++ params'
                  copyType = Core.TFun (map Core._binderType allParams) result'
                  capVars = [Core.Expr (Core.EVar (Core._binderName b)) (Core._binderType b) sp | (_, b) <- capBinders]
              body1 <- substitute g (_self info) q copyType (map fst known) capVars capRename subst body0
              body2 <- normalise body1
              body3 <- walk env (Ctx (_home ctx) q (_depth ctx + 1) Map.empty Set.empty) body2
              let v = Core.Expr (Core.ELam allParams body3) copyType sp
              modify' (\s -> s {_made = (q, v, size body3) : _made s})
              return (Just (q, caps, True))

resultOf :: Core.Type -> Core.Type
resultOf t = case Specialize.unquantified t of
  Core.TFun _ r -> r
  other -> other

freshN :: M Int
freshN = do
  s <- get
  put s {_fresh = _fresh s + 1}
  return (_fresh s)

-- | Replace the known parameters by their functions, freshly named at each
-- use, and point the self calls at the copy.
substitute ::
  Core.QualName ->
  Bool ->
  Core.QualName ->
  Core.Type ->
  [Int] ->
  [Core.Expr] ->
  Map Name Name ->
  Map Name Core.Expr ->
  Core.Expr ->
  M Core.Expr
substitute g self q copyType knownIs capVars capRename subst = go
  where
    go e =
      case Core._exprValue e of
        Core.EVar n
          | Just a <- Map.lookup n subst ->
              do
                n0 <- gets _fresh
                let (a', n1) = runState (renameE (\k -> Name.fromChars ("$q" ++ show k)) capRename a) n0
                modify' (\s -> s {_fresh = n1})
                return a'
        Core.EApp (Core.Expr (Core.EGlobal h) _ sp) args
          | self && h == g ->
              do
                args' <- mapM go args
                let rest = [a | (j, a) <- zip [0 :: Int ..] args', j `notElem` knownIs]
                return e {Core._exprValue = Core.EApp (Core.Expr (Core.EGlobal q) copyType sp) (capVars ++ rest)}
        _ -> Specialize.childrenA go e

-- | A lambda applied at once becomes its body under @let@s, and a @let@ left
-- as an argument is bound before the call.
normalise :: Core.Expr -> M Core.Expr
normalise e0 =
  do
    e <- Specialize.childrenA normalise e0
    case Core._exprValue e of
      Core.EApp (Core.Expr (Core.ELam ps body) _ _) args
        | length ps == length args ->
            return e {Core._exprValue = Core.ELet (zipWith Core.Bind ps args) body}
      Core.EApp f args | any isLet args -> anf args (\args' -> e {Core._exprValue = Core.EApp f args'})
      Core.EPrim op args | any isLet args -> anf args (\args' -> e {Core._exprValue = Core.EPrim op args'})
      Core.ECtor c t args | any isLet args -> anf args (\args' -> e {Core._exprValue = Core.ECtor c t args'})
      _ -> return e
  where
    isLet a = case Core._exprValue a of
      Core.ELet _ _ -> True
      _ -> False
    anf args k =
      do
        pairs <- forM args $ \a ->
          if value a
            then return ([], a)
            else do
              n <- freshN
              let b = Core.Binder (Name.fromChars ("$q" ++ show n)) (Core.typeOf a) (Core.spanOf a)
              return ([Core.Bind b a], Core.Expr (Core.EVar (Core._binderName b)) (Core.typeOf a) (Core.spanOf a))
        let binds = concatMap fst pairs
            inner = k (map snd pairs)
        return inner {Core._exprValue = Core.ELet binds inner}

-- RENAMING

-- | Every binder renamed, and the free names in the map.
renameE :: (Int -> Name) -> Map Name Name -> Core.Expr -> State Int Core.Expr
renameE mk = go
  where
    fresh b = do
      k <- get
      put (k + 1)
      return b {Core._binderName = mk k}
    extend env bs bs' = Map.union (Map.fromList (zip (map Core._binderName bs) (map Core._binderName bs'))) env
    go env e =
      let re v = return e {Core._exprValue = v}
       in case Core._exprValue e of
            Core.EVar n -> re (Core.EVar (Map.findWithDefault n n env))
            Core.ELam bs body -> do
              bs' <- mapM fresh bs
              body' <- go (extend env bs bs') body
              re (Core.ELam bs' body')
            Core.EWitLam bs body -> do
              bs' <- mapM fresh bs
              body' <- go (extend env bs bs') body
              re (Core.EWitLam bs' body')
            Core.ELet binds body -> do
              (binds', env') <-
                foldM
                  ( \(acc, en) (Core.Bind b v) -> do
                      v' <- go en v
                      b' <- fresh b
                      return (acc ++ [Core.Bind b' v'], extend en [b] [b'])
                  )
                  ([], env)
                  binds
              body' <- go env' body
              re (Core.ELet binds' body')
            Core.ELetRec binds body -> do
              bs' <- mapM (fresh . Core._bindBinder) binds
              let env' = extend env (map Core._bindBinder binds) bs'
              vs <- mapM (go env' . Core._bindValue) binds
              body' <- go env' body
              re (Core.ELetRec (zipWith Core.Bind bs' vs) body')
            Core.EJoin binds body -> do
              bs' <- mapM (fresh . Core._bindBinder) binds
              let env' = extend env (map Core._bindBinder binds) bs'
              vs <- mapM (go env' . Core._bindValue) binds
              body' <- go env' body
              re (Core.EJoin (zipWith Core.Bind bs' vs) body')
            Core.EJump n args -> do
              args' <- mapM (go env) args
              re (Core.EJump (Map.findWithDefault n n env) args')
            Core.ECase scrut alts fallback -> do
              scrut' <- go env scrut
              alts' <- forM alts $ \(Core.Alt p b) -> do
                (p', env') <- pat env p
                b' <- go env' b
                return (Core.Alt p' b')
              fallback' <- traverse (go env) fallback
              re (Core.ECase scrut' alts' fallback')
            _ -> Specialize.childrenA (go env) e
    pat env p =
      case p of
        Core.PVar b -> do
          b' <- fresh b
          return (Core.PVar b', extend env [b] [b'])
        Core.PAs b inner -> do
          b' <- fresh b
          (inner', env') <- pat (extend env [b] [b']) inner
          return (Core.PAs b' inner', env')
        Core.PCtor q t subs -> do
          (subs', env') <- pats env subs
          return (Core.PCtor q t subs', env')
        Core.PRecord fields -> do
          (ps', env') <- pats env (map snd fields)
          return (Core.PRecord (zip (map fst fields) ps'), env')
        Core.PArray items tl -> do
          (items', env1) <- pats env items
          case tl of
            Nothing -> return (Core.PArray items' Nothing, env1)
            Just b -> do
              b' <- fresh b
              return (Core.PArray items' (Just b'), extend env1 [b] [b'])
        other -> return (other, env)
    pats env ps =
      foldM
        ( \(acc, en) p -> do
            (p', en') <- pat en p
            return (acc ++ [p'], en')
        )
        ([], env)
        ps

-- | The names an expression uses and does not bind, exactly: a @let@'s
-- bindings are in scope in the ones after them, which 'Refs.freeLocals'
-- does not take away.
freeIn :: Core.Expr -> Set Name
freeIn e =
  case Core._exprValue e of
    Core.EVar n -> Set.singleton n
    Core.ELam bs body -> without bs (freeIn body)
    Core.EWitLam bs body -> without bs (freeIn body)
    Core.ELet binds body ->
      foldr
        (\(Core.Bind b v) inner -> Set.union (freeIn v) (Set.delete (Core._binderName b) inner))
        (freeIn body)
        binds
    Core.ELetRec binds body -> recursive binds body
    Core.EJoin binds body -> recursive binds body
    Core.ECase scrut alts fallback ->
      Set.unions
        ( freeIn scrut
            : maybe Set.empty freeIn fallback
            : [Set.difference (freeIn b) (Refs.patternBinders p) | Core.Alt p b <- alts]
        )
    _ -> Specialize.children_ freeIn e
  where
    without bs s = foldr (Set.delete . Core._binderName) s bs
    recursive binds body =
      without (map Core._bindBinder binds) (Set.unions (freeIn body : map (freeIn . Core._bindValue) binds))

-- | Spans taken out, for a key.
strip :: Core.Expr -> String
strip e = show (Inline.respan (const (Core.FileId 0)) (zeroSpans e))
  where
    zeroSpans x =
      let rebuilt = runIdentity (Specialize.childrenA (Identity . zeroSpans) x)
       in rebuilt {Core._exprSpan = Core.Span (Core.FileId 0) 0 0 0 0}

varTypes :: Core.Expr -> Map Name Core.Type
varTypes e =
  case Core._exprValue e of
    Core.EVar n -> Map.singleton n (Core.typeOf e)
    _ -> Specialize.children_ varTypes e

tyVars :: Core.Type -> Set Name
tyVars t =
  case t of
    Core.TVar n -> Set.singleton n
    Core.TCon _ as -> Set.unions (map tyVars as)
    Core.TFun as r -> Set.unions (map tyVars (r : as))
    Core.TRecord fs row -> Set.unions (maybe Set.empty Set.singleton row : map (tyVars . snd) fs)
    Core.TForall vs _ b -> foldr Set.delete (tyVars b) vs

allTyVars :: Core.Expr -> Set Name
allTyVars e = Set.union (tyVars (Core.typeOf e)) (Specialize.children_ allTyVars e)

size :: Core.Expr -> Int
size e = 1 + getSum (Specialize.children_ (Sum . size) e)

-- | What the program's @main@s reach, for the census.
reach :: Map ModuleName.Canonical Core.Module -> Map Core.QualName Core.Expr -> Set Core.QualName
reach cores defs =
  let roots = [Core.QualName home "main" | (home, m) <- Map.toList cores, Maybe.isJust (Core._moduleMain m)]
      go seen [] = seen
      go seen (q : rest)
        | Set.member q seen = go seen rest
        | otherwise =
            case Map.lookup q defs of
              Nothing -> go (Set.insert q seen) rest
              Just v -> go (Set.insert q seen) (Set.toList (Refs._refGlobals (Refs.refsIn v)) ++ rest)
   in go Set.empty roots

-- PUTTING IT BACK

-- | A module's changed definitions and its copies, out of the program's file
-- space and back into the module's, its file table grown by the modules the
-- copies came from, as "Core.Pass.Inline" does.
putBack :: Inline.Space -> ModuleName.Canonical -> Core.Module -> Map Name Core.Expr -> [(Core.Binder, Core.Expr)] -> Core.Module
putBack space home modul rewritten added =
  let table = Core._moduleFiles modul
      known = Map.fromList [(name, fid) | (fid, name) <- Map.toList table]
      values = Map.elems rewritten ++ map snd added
      used = Set.unions (map Inline.spanFiles values ++ [Set.fromList [Core._spanFile (Core._binderSpan b)] | (b, _) <- added])
      usedNames = Set.fromList [Inline.spaceName space i | Core.FileId i <- Set.toList used]
      next = 1 + maximum ((-1) : [i | Core.FileId i <- Map.keys table])
      newFiles = zip (List.sort [n | n <- Set.toList usedNames, not (Map.member n known)]) (map Core.FileId [next ..])
      local = Map.union known (Map.fromList newFiles)
      toLocal (Core.FileId i) = local Map.! Inline.spaceName space i
      back = Inline.respan toLocal
      backB b = b {Core._binderSpan = (Core._binderSpan b) {Core._spanFile = toLocal (Core._spanFile (Core._binderSpan b))}}
      defs =
        [ Core.Bind b (maybe v back (Map.lookup (Core._binderName b) rewritten))
        | Core.Bind b v <- Core._moduleDefs modul
        ]
          ++ [Core.Bind (backB b) (back v) | (b, v) <- added]
      ordered = Inline.reorder home defs
   in modul
        { Core._moduleFiles = Map.union table (Map.fromList [(fid, n) | (n, fid) <- newFiles]),
          Core._moduleDefs = concat ordered,
          Core._moduleDefsRec =
            [ map (Core.QualName home . Core._binderName . Core._bindBinder) grp
            | grp <- ordered,
              length grp > 1
            ]
        }
