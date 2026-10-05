{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | A @Dict@ updated in place in a loop that keeps no old version of it
-- (geng-lang @m3-fold.md@ §FL10, D579, D582; @m3-inplace.md@ D518, D576).
--
-- > fill i n d = if i >= n then d else fill (i + 1) n (Dict.set i (i * 2) d)
-- >   ⟹ fill i n d = fill$tr (dict_owner {}) i n d
-- >      fill$tr o i n d = if i >= n then d else fill$tr o (i + 1) n (Dict.setT o i (i * 2) d)
--
-- @core@'s @setT@, @updateT@, @updateWithDefaultT@ and @removeT@ are its
-- @set@, @update@, @updateWithDefault@ and @remove@ over four @dict_@
-- primitives ('Core.Prim.DictPrim'): a node that carries the loop's owner is
-- written, and any other is copied once and carries it from then on. What
-- this pass decides is where that is sound: where the old version of the
-- @Dict@ is never looked at again, so that writing a node this loop made can
-- change nothing anything else holds.
--
-- __Which loops__: a top-level function that calls itself, every use of its
-- own name a saturated call outside any lambda, with a parameter of type
-- @Dict k v@ — the /version/. Where "Core.Pass.FoldSpec" has copied a fold
-- for its lambda, the copy is such a function, and its accumulator such a
-- parameter (D579).
--
-- __The rule__, checked over the function's body: the version, and each name
-- a @let@ binds it to or binds what is made of it to, is
--
--   * __consumed once on every path__: handed to an update as the
--     dictionary, handed back to the loop in the parameter's place, or the
--     result; and an update of it, or the loop's own answer, is a version in
--     turn, which is how @foldl@'s copy, @set k v (foldl acc left)@, reads;
--   * __read only before it is consumed__: as the dictionary of @get@,
--     @member@, @count@ and the other functions of 'readers', whose answers hold
--     no node of it, in a @let@ or a @when@'s subject before the code that
--     consumes it, or in an update's other arguments when the dictionary it is
--     handed is the version itself and no update is evaluated with them;
--   * __never anywhere else__: not in a lambda, a record, a constructor, a
--     field, a pattern, or a call to any other function.
--
-- A loop that passes keeps its name as its entry, which takes a fresh owner
-- and enters the loop's copy, @…$tr@, with it; the copy hands the owner to
-- each of its own calls and to each twin it calls. An owner is never handed
-- out twice, so nodes made by a loop that has finished are any other loop's
-- foreign nodes, and an entry from inside the loop is a loop of its own.
--
-- It runs after "Core.Pass.FoldSpec", whose copies it reads, and before
-- @mono@: it names the twins by the copies "Core.Pass.Specialize" made of them
-- ('Core.Pass.Specialize.twins'), and a call it cannot name a twin for is
-- left alone. A pass is optional (C4): the program answers the same without
-- it, and on the BEAM, where nothing is written in place (D518), it is not
-- among the defaults.
--
-- With @GENG_TRANSIENT_CENSUS=<file>@ it appends a line for every function
-- that calls itself and takes a @Dict@: its module and name, the parameter,
-- and @taken@ or @refused@.
module Core.Pass.Transient
  ( run,
  )
where

import Control.Monad (foldM, forM)
import Core.AST qualified as Core
import Core.Pass.Inline qualified as Inline
import Core.Pass.Specialize qualified as Specialize
import Core.Prim qualified as Prim
import Core.Refs qualified as Refs
import Data.Functor.Identity (Identity (..))
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Monoid (All (..), Any (..))
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set (Set)
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName
import System.Environment qualified as Env
import System.IO.Unsafe (unsafePerformIO)

census :: Maybe FilePath
census = unsafePerformIO (Env.lookupEnv "GENG_TRANSIENT_CENSUS")
{-# NOINLINE census #-}

-- | The updates that have twins, with how many arguments each takes and which
-- is the dictionary.
updates :: Map String (Int, Int)
updates =
  Map.fromList
    [ ("set", (3, 2)),
      ("update", (3, 2)),
      ("updateWithDefault", (4, 3)),
      ("remove", (2, 1))
    ]

-- | @Dict@'s functions whose answer holds no node of the dictionary they read,
-- with which argument that is.
readers :: Map String Int
readers =
  Map.fromList
    [ ("get", 1),
      ("member", 1),
      ("count", 0),
      ("isEmpty", 0),
      ("first", 0),
      ("last", 0),
      ("keys", 0),
      ("values", 0)
    ]

data Ck = Ck
  { _loop :: Core.QualName,
    _arity :: Int,
    _pos :: Int,
    _owner :: Core.Expr,
    _dictDefs :: Set Name
  }

run :: Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
run cores =
  case Map.lookup ModuleName.dict cores of
    Nothing -> cores
    Just dictModule ->
      let dictDefs = Set.fromList [Core._binderName b | Core.Bind b _ <- Core._moduleDefs dictModule]
       in Map.mapWithKey (module_ dictDefs) cores

module_ :: Set Name -> ModuleName.Canonical -> Core.Module -> Core.Module
module_ dictDefs home modul =
  let results = [(b, v, loop dictDefs (Core.QualName home (Core._binderName b)) v) | Core.Bind b v <- Core._moduleDefs modul]
   in logged home modul results $
        if null [() | (_, _, Just _) <- results]
          then modul
          else
            let defs =
                  concat
                    [ case found of
                        Nothing -> [Core.Bind b v]
                        Just (entry, (tb, tv)) -> [Core.Bind b entry, Core.Bind tb tv]
                    | (b, v, found) <- results
                    ]
                ordered = Inline.reorder home defs
             in modul
                  { Core._moduleDefs = concat ordered,
                    Core._moduleDefsRec =
                      [ map (Core.QualName home . Core._binderName . Core._bindBinder) grp
                      | grp <- ordered,
                        length grp > 1
                      ]
                  }

-- | The census line of each loop that takes a @Dict@, when one is asked for.
logged :: ModuleName.Canonical -> Core.Module -> [(Core.Binder, Core.Expr, Maybe a)] -> b -> b
logged home@(ModuleName.Canonical _ m) _ results out =
  case census of
    Nothing -> out
    Just path ->
      unsafePerformIO $ do
        appendFile path $
          unlines
            [ Name.toChars m ++ "\t" ++ Name.toChars (Core._binderName b) ++ "\t" ++ Name.toChars (Core._binderName p) ++ "\t" ++ (if taken then "taken" else "refused")
            | (b, Core.Expr (Core.ELam ps body) _ _, found) <- results,
              calls (Core.QualName home (Core._binderName b)) body,
              p <- ps,
              isDict (Core._binderType p),
              let taken = maybe False (const True) found
            ]
        return out

isDict :: Core.Type -> Bool
isDict t =
  case t of
    Core.TCon dict [_, _] -> dict == dictType
    _ -> False

-- | A loop's entry and its copy that takes the owner, when one of its
-- parameters passes the rule.
loop :: Set Name -> Core.QualName -> Core.Expr -> Maybe (Core.Expr, (Core.Binder, Core.Expr))
loop dictDefs q value =
  case value of
    Core.Expr (Core.ELam ps body) fnType sp
      | selfOnly q (length ps) body,
        calls q body ->
          let ownerB = Core.Binder (Name.fromChars "$owner") tInt sp
              ownerV = Core.Expr (Core.EVar (Core._binderName ownerB)) tInt sp
              qt = Core.QualName (Core._qnHome q) (Name.fromChars (Name.toChars (Core._qnName q) ++ "$tr"))
              try body0 (i, p)
                | isDict (Core._binderType p) =
                    case version (Ck q (length ps) i ownerV dictDefs) (Set.singleton (Core._binderName p)) body0 of
                      Just (body1, _) | body1 /= body0 -> body1
                      _ -> body0
                | otherwise = body0
              rewritten = foldl try body (zip [0 ..] ps)
           in if rewritten == body
                then Nothing
                else
                  let qtType = case fnType of
                        Core.TFun ts r -> Core.TFun (tInt : ts) r
                        other -> other
                      copy = Core.Expr (Core.ELam (ownerB : ps) (retarget q qt qtType ownerV rewritten)) qtType sp
                      unit = Core.Expr (Core.ERecord []) (Core.TRecord [] Nothing) sp
                      fresh = Core.Expr (Core.EPrim (Prim.DictOp Prim.DictOwner) [unit]) tInt sp
                      entry =
                        Core.Expr
                          ( Core.ELam
                              ps
                              ( Core.Expr
                                  (Core.EApp (Core.Expr (Core.EGlobal qt) qtType sp) (fresh : [Core.Expr (Core.EVar (Core._binderName p)) (Core._binderType p) sp | p <- ps]))
                                  (Core.typeOf body)
                                  sp
                              )
                          )
                          fnType
                          sp
                   in Just (entry, (Core.Binder (Core._qnName qt) qtType sp, copy))
    _ -> Nothing

tInt :: Core.Type
tInt = Core.TCon (Core.QualName ModuleName.basics (Name.fromChars "Int")) []

dictType :: Core.QualName
dictType = Core.QualName ModuleName.dict (Name.fromChars "Dict")

-- | Whether the body calls the function.
calls :: Core.QualName -> Core.Expr -> Bool
calls q e =
  case Core._exprValue e of
    Core.EGlobal g -> g == q
    _ -> getAny (Specialize.children_ (Any . calls q) e)

-- | Whether every use of the name is a saturated call, and none is inside a
-- lambda or a local recursive binding, where a closure could call the loop
-- after this time round, or after the loop.
selfOnly :: Core.QualName -> Int -> Core.Expr -> Bool
selfOnly q arity = go
  where
    go e =
      case Core._exprValue e of
        Core.EGlobal g -> g /= q
        Core.EApp (Core.Expr (Core.EGlobal g) _ _) args
          | g == q -> length args == arity && all go args
        Core.ELam _ body -> not (calls q body)
        Core.ELetRec binds body -> not (any (calls q . Core._bindValue) binds) && go body
        _ -> getAll (Specialize.children_ (All . go) e)

-- | Every call to the loop made a call to its copy, with the owner first.
retarget :: Core.QualName -> Core.QualName -> Core.Type -> Core.Expr -> Core.Expr -> Core.Expr
retarget q qt qtType ownerV = go
  where
    go e =
      case Core._exprValue e of
        Core.EApp (Core.Expr (Core.EGlobal g) _ fsp) args
          | g == q -> e {Core._exprValue = Core.EApp (Core.Expr (Core.EGlobal qt) qtType fsp) (ownerV : map go args)}
        _ -> runIdentity (Specialize.childrenA (Identity . go) e)

-- THE RULE

-- | An expression whose value goes on — the result, a @let@'s binding, an
-- update's dictionary or the loop's argument — checked against the names the
-- version goes by, and rewritten: the expression with the version's updates
-- made twins, and whether its value is the version.
version :: Ck -> Set Name -> Core.Expr -> Maybe (Core.Expr, Bool)
version ck v e
  | not (mentions v e) = Just (e, False)
  | otherwise =
      case Core._exprValue e of
        Core.EVar x | Set.member x v -> Just (e, True)
        Core.ELet binds body ->
          do
            (e', c) <- lets ck v binds body
            return (e {Core._exprValue = Core._exprValue e'}, c)
        Core.ECase scrut alts fallback
          | readsOnly ck v scrut ->
              do
                alts' <- forM alts $ \(Core.Alt p b) -> do
                  let v' = Set.difference v (Refs.patternBinders p)
                  (b', c) <- version ck v' b
                  return (Core.Alt p b', c)
                fallback' <- traverse (version ck v) fallback
                return (e {Core._exprValue = Core.ECase scrut (map fst alts') (fmap fst fallback')}, any snd alts' || maybe False snd fallback')
        Core.EApp fn args
          | Just (twin, n, at) <- update ck fn,
            length args == n ->
              do
                (d', c) <- version ck v (args !! at)
                if not c
                  then if readsOnly ck v e then Just (e, False) else Nothing
                  else do
                    let others = [a | (j, a) <- zip [0 ..] args, j /= at]
                    if all (alongside ck v (args !! at)) others
                      then
                        let args' = [if j == at then d' else a | (j, a) <- zip [0 ..] args]
                         in Just (e {Core._exprValue = Core.EApp twin (_owner ck : args')}, True)
                      else Nothing
        Core.EApp fn@(Core.Expr (Core.EGlobal g) _ _) args
          | g == _loop ck,
            length args == _arity ck ->
              do
                (a', _) <- version ck v (args !! _pos ck)
                let others = [a | (j, a) <- zip [0 ..] args, j /= _pos ck]
                if all (alongside ck v (args !! _pos ck)) others
                  then Just (e {Core._exprValue = Core.EApp fn [if j == _pos ck then a' else a | (j, a) <- zip [0 ..] args]}, True)
                  else Nothing
        _
          | readsOnly ck v e -> Just (e, False)
          | otherwise -> Nothing

-- | Another argument of a call one of whose arguments is the version: it may
-- read the version only when that argument is the version itself, since
-- otherwise an update evaluated beside it could come first.
alongside :: Ck -> Set Name -> Core.Expr -> Core.Expr -> Bool
alongside ck v consumed other =
  not (mentions v other)
    || (isVersionName v consumed && readsOnly ck v other)

isVersionName :: Set Name -> Core.Expr -> Bool
isVersionName v e =
  case Core._exprValue e of
    Core.EVar x -> Set.member x v
    _ -> False

-- | A @let@'s bindings in order, then its body: a binding that names the
-- version is a name for it too; one that reads it is evaluated before what
-- follows; one that consumes it makes its own name the version's, and nothing
-- after it may name the old one.
lets :: Ck -> Set Name -> [Core.Bind] -> Core.Expr -> Maybe (Core.Expr, Bool)
lets ck v0 binds0 body0 =
  do
    (binds', v) <- foldM step ([], v0) (zip [0 :: Int ..] binds0)
    (body', c) <- version ck v body0
    return (Core.Expr (Core.ELet (reverse binds') body') (Core.typeOf body0) (Core.spanOf body0), c)
  where
    step (acc, v) (i, Core.Bind b r) =
      let name = Core._binderName b
          rest = map Core._bindValue (drop (i + 1) binds0) ++ [body0]
       in if not (mentions v r)
            then Just (Core.Bind b r : acc, Set.delete name v)
            else
              if isVersionName v r
                then Just (Core.Bind b r : acc, Set.insert name v)
                else
                  if readsOnly ck v r
                    then Just (Core.Bind b r : acc, Set.delete name v)
                    else do
                      (r', c) <- version ck v r
                      if not c
                        then Nothing
                        else
                          let old = Set.delete name v
                           in if any (mentions old) rest
                                then Nothing
                                else Just (Core.Bind b r' : acc, Set.singleton name)

-- | Whether every use of the version in the expression is as the dictionary a
-- function of 'readers' is handed, outside any lambda.
readsOnly :: Ck -> Set Name -> Core.Expr -> Bool
readsOnly ck v e =
  case Core._exprValue e of
    Core.EVar x -> not (Set.member x v)
    Core.ELam _ body -> not (mentions v body)
    Core.ELetRec binds body -> not (any (mentions v . Core._bindValue) binds) && readsOnly ck v body
    Core.EApp fn args
      | Just (n, at) <- readOf ck fn,
        length args == n ->
          all (\(j, a) -> if j == at then isVersionName v a || readsOnly ck v a else readsOnly ck v a) (zip [0 ..] args)
    _ -> getAll (Specialize.children_ (All . readsOnly ck v) e)

-- | A call to one of @Dict@'s 'updates' as "Core.Pass.Specialize" copied it,
-- and the twin to call instead: @set$s…@'s is @setT$s…@, taking the owner
-- first.
update :: Ck -> Core.Expr -> Maybe (Core.Expr, Int, Int)
update ck fn =
  case fn of
    Core.Expr (Core.EGlobal (Core.QualName home name)) fnType sp
      | home == ModuleName.dict,
        (base, suffix) <- splitCopy (Name.toChars name),
        "$s" `List.isPrefixOf` suffix,
        Just (n, at) <- Map.lookup base updates,
        let twin = Name.fromChars (base ++ "T" ++ suffix),
        Set.member twin (_dictDefs ck),
        Core.TFun ts r <- fnType ->
          Just (Core.Expr (Core.EGlobal (Core.QualName home twin)) (Core.TFun (tInt : ts) r) sp, n, at)
    _ -> Nothing

-- | A call to one of @Dict@'s 'readers', copied or not.
readOf :: Ck -> Core.Expr -> Maybe (Int, Int)
readOf _ fn =
  case Core._exprValue fn of
    Core.EGlobal (Core.QualName home name)
      | home == ModuleName.dict,
        (base, _) <- splitCopy (Name.toChars name),
        Just at <- Map.lookup base readers,
        Core.TFun ts _ <- Core.typeOf fn ->
          Just (length ts, at)
    _ -> Nothing

-- | A name and what a pass added after its @$@.
splitCopy :: String -> (String, String)
splitCopy = break (== '$')

-- | Whether the expression names one of the version's names and does not
-- bind it first.
mentions :: Set Name -> Core.Expr -> Bool
mentions v e
  | Set.null v = False
  | otherwise = not (Set.null (Set.intersection v (freeIn e)))

-- | The names an expression uses and does not bind, exactly (a @let@'s
-- bindings are in scope in the ones after them).
freeIn :: Core.Expr -> Set Name
freeIn e =
  case Core._exprValue e of
    Core.EVar n -> Set.singleton n
    Core.ELam bs body -> without bs (freeIn body)
    Core.EWitLam bs body -> without bs (freeIn body)
    Core.ELet binds body ->
      foldr
        (\(Core.Bind b x) inner -> Set.union (freeIn x) (Set.delete (Core._binderName b) inner))
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
