{-# OPTIONS_GHC -Wall #-}

-- | The quadratic shapes report (geng-lang @m4-quadratic.md@, D1070): the
-- shapes a quadratic is written in, over the Core the front end lowered, before
-- any pass, so that every target sees what the author wrote. It changes
-- nothing. @GENG_QUAD_REPORT=<file>@ appends a line for each site,
-- tab-separated: the check, the package, the module, the definition, where,
-- and what it saw. A reading list, not a verdict: most of what it names is a
-- true shape whose n is small, which only a reader can judge (§QD5).
--
-- The checks:
--
--   * @rewalk@: a function that recurses on a part of a parameter (its
--     argument at a recursive call is a field, a pattern variable or a slice of
--     it), and that calls a walk of that parameter, or a part of it, on the
--     way. A walk is a function the table says costs the length of an
--     argument, or one this report finds walking one.
--   * @rewalk-fold@: a walk, inside a fold's function, of the collection the
--     fold is over (@canary/member-scan@'s shape).
--   * @accwalk@: a walk of a loop's accumulator, in its round: a fold's
--     accumulator, or a parameter a recursive call hands back grown.
--   * @forked@: a loop's accumulator grown twice on one path through a round,
--     D708's shape: the second growth copies it.
--
-- No check names an append onto a growing left side: natively, on JavaScript
-- and on the BEAM it is linear (§QD2, D1068).
module Core.Pass.Quad
  ( report,
  )
where

import Core.AST qualified as Core
import Data.ByteString qualified as BS
import Data.ByteString.Builder qualified as BB
import Data.ByteString.Lazy qualified as LBS
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
import System.Environment qualified as Env
import System.IO.Unsafe (unsafePerformIO)

reportPath :: Maybe FilePath
reportPath = unsafePerformIO (Env.lookupEnv "GENG_QUAD_REPORT")
{-# NOINLINE reportPath #-}

-- | The program as it was, the report written on the way when it is asked for.
report :: Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
report cores =
  case reportPath of
    Just path
      | path /= "" ->
          let ls = List.nub (findings cores)
              -- one write, so that builds running at once do not cut into
              -- each other's lines
              bytes = LBS.toStrict (BB.toLazyByteString (BB.stringUtf8 (unlines ls)))
           in BS.length bytes `seq` unsafePerformIO (BS.appendFile path bytes >> return cores)
    _ -> cores

-- NAMES

data Callee
  = G !Core.QualName
  | L !Name
  deriving (Eq, Ord)

type Key = (String, String)

key :: Core.QualName -> Key
key q = (Name.toChars (ModuleName._module (Core._qnHome q)), Name.toChars (Core._qnName q))

-- | What the table says of core's functions: the arguments whose length each
-- costs, from the costs their documentation gives.
seed :: Map Key [Int]
seed =
  Map.fromList $
    [(("Array", f), [1]) | f <- ["map", "indexedMap", "keepIf", "indexedKeepIf", "mapAndKeepJust", "findFirst", "findLast", "member", "any", "all", "mapAndFlatten", "intersperse", "partition", "sortBy", "sortWith"]]
      ++ [(("Array", f), [2]) | f <- ["foldl", "foldr", "indexedFoldl", "indexedFoldr", "set"]]
      ++ [(("Array", f), [0]) | f <- ["reverse", "minimum", "maximum", "flatten", "sort"]]
      ++ [(("Array", "map2"), [1, 2])]
      ++ [(("String", f), [0]) | f <- ["count", "reverse", "words", "lines", "toUpper", "toLower", "toArray", "fromArray", "graphemes", "graphemeLength", "toInt", "toFloat"]]
      ++ [(("String", f), [1]) | f <- ["join", "contains", "firstIndexOf", "lastIndexOf", "indices", "map", "keepIf", "split", "dropFirst", "takeFirst", "dropLast", "takeLast"]]
      ++ [(("String", f), [2]) | f <- ["replace", "slice", "foldl", "foldr", "foldlGraphemes"]]
      ++ [(("Dict", f), [0]) | f <- ["count", "keys", "values", "union", "intersect", "toArray"]]
      ++ [(("Dict", f), [1]) | f <- ["map", "keepIf", "mapAndKeepJust", "partition"]]
      ++ [(("Dict", f), [2]) | f <- ["foldl", "foldr"]]
      ++ [(("Set", f), [0]) | f <- ["count", "union", "intersect", "toArray"]]
      ++ [(("Set", f), [1]) | f <- ["map", "keepIf", "partition"]]
      ++ [(("Set", f), [2]) | f <- ["foldl", "foldr"]]
      ++ [(("Bytes", f), [0]) | f <- ["toString", "flatten", "fromString"]]

-- | Functions that hand a function the elements of a collection: where the
-- function is, where the collection is, which of its parameters are the
-- elements, and which is the accumulator.
data Hof = Hof {_hFn :: !Int, _hColl :: !Int, _hElems :: ![Int], _hAcc :: !(Maybe Int)}

hofs :: Map Key Hof
hofs =
  Map.fromList $
    [(("Array", f), Hof 0 2 [0] (Just 1)) | f <- ["foldl", "foldr"]]
      ++ [(("Array", f), Hof 0 2 [1] (Just 2)) | f <- ["indexedFoldl", "indexedFoldr"]]
      ++ [(("Array", f), Hof 0 1 [0] Nothing) | f <- ["map", "keepIf", "mapAndKeepJust", "any", "all", "findFirst", "findLast", "mapAndFlatten", "partition"]]
      ++ [(("Array", f), Hof 0 1 [1] Nothing) | f <- ["indexedMap", "indexedKeepIf"]]
      ++ [(("Dict", f), Hof 0 2 [0, 1] (Just 2)) | f <- ["foldl", "foldr"]]
      ++ [(("Dict", f), Hof 0 1 [0, 1] Nothing) | f <- ["map", "keepIf", "mapAndKeepJust", "any", "all"]]
      ++ [(("Set", f), Hof 0 2 [0] (Just 1)) | f <- ["foldl", "foldr"]]
      ++ [(("String", f), Hof 0 2 [0] (Just 1)) | f <- ["foldl", "foldr"]]

-- | Functions whose result is a part of an argument.
shrinkers :: Map Key Int
shrinkers =
  Map.fromList $
    [(("Array", f), 0) | f <- ["popFirst", "popLast", "first", "last"]]
      ++ [(("Array", f), 1) | f <- ["dropFirst", "dropLast", "takeFirst", "takeLast", "get"]]
      ++ [(("Array", "slice"), 2)]
      ++ [(("String", f), 0) | f <- ["popFirst", "popLast"]]
      ++ [(("String", f), 1) | f <- ["dropFirst", "dropLast", "takeFirst", "takeLast"]]
      ++ [(("String", "slice"), 2)]
      ++ [(("Dict", "get"), 1)]

-- | An append, and which argument is its left operand: what it grows.
appendLeft :: Key -> Maybe Int
appendLeft (m, f)
  | "$i$Appendable$" `List.isPrefixOf` f && "$append" `List.isSuffixOf` f = Just 0
  | m == "Basics" && f == "append" = Just 0
  | m `elem` ["Array", "String"] && f == "prepend" = Just 0
  | m `elem` ["Array", "String"] && f == "append" = Just 1
  | otherwise = Nothing

-- | A growth of an accumulator: an append's left operand, or a push's.
growthOf :: Key -> Maybe Int
growthOf k@(m, f)
  | Just i <- appendLeft k = Just i
  | m `elem` ["Array", "String"] && f `elem` ["pushLast", "pushFirst"] = Just 1
  | otherwise = Nothing

-- EXPRESSIONS

calleeOf :: Core.Expr -> Maybe Callee
calleeOf e =
  case Core._exprValue e of
    Core.EGlobal q -> Just (G q)
    Core.EVar n -> Just (L n)
    Core.ETyApp f _ -> calleeOf f
    Core.EWitApp f _ -> calleeOf f
    _ -> Nothing

appOf :: Core.Expr -> Maybe (Callee, [Core.Expr])
appOf e =
  case Core._exprValue e of
    Core.EApp f args ->
      case appOf f of
        Just (c, as) -> Just (c, as ++ args)
        Nothing -> (\c -> (c, args)) <$> calleeOf f
    _ -> Nothing

lambdaOf :: Core.Expr -> Maybe ([Core.Binder], Core.Expr)
lambdaOf e =
  case Core._exprValue e of
    Core.ETyLam _ b -> lambdaOf b
    Core.EWitLam _ b -> lambdaOf b
    Core.ELam bs body -> Just (bs, body)
    _ -> Nothing

globalKey :: Callee -> Maybe Key
globalKey c = case c of G q -> Just (key q); L _ -> Nothing

freeNames :: Core.Expr -> Set Name
freeNames e =
  case Core._exprValue e of
    Core.EVar n -> Set.singleton n
    _ -> Set.unions (map freeNames (children e))

-- | Every expression directly inside one.
children :: Core.Expr -> [Core.Expr]
children e =
  case Core._exprValue e of
    Core.EVar _ -> []
    Core.EGlobal _ -> []
    Core.ELit _ -> []
    Core.ELam _ b -> [b]
    Core.EApp f as -> f : as
    Core.ELet bs b -> map Core._bindValue bs ++ [b]
    Core.ELetRec bs b -> map Core._bindValue bs ++ [b]
    Core.ECase s alts fb -> s : map Core._altBody alts ++ Maybe.maybeToList fb
    Core.ECtor _ _ as -> as
    Core.ERecord fs -> map snd fs
    Core.EUpdate b fs _ -> b : map snd fs
    Core.EAccess b _ -> [b]
    Core.EArray as -> as
    Core.EPrim _ as -> as
    Core.EJoin bs b -> map Core._bindValue bs ++ [b]
    Core.EJump _ as -> as
    Core.ETyLam _ b -> [b]
    Core.ETyApp b _ -> [b]
    Core.EWitLam _ b -> [b]
    Core.EWitApp b as -> b : as
    Core.ECrash (Core.Todo _ m) -> [m]
    Core.ECrash _ -> []

patVars :: Bool -> Core.Pattern -> [(Name, Bool)]
patVars strict pat =
  case pat of
    Core.PVar b -> [(Core._binderName b, strict)]
    Core.PWild -> []
    Core.PLit _ -> []
    Core.PCtor _ _ ps -> concatMap (patVars True) ps
    Core.PRecord fs -> concatMap (patVars True . snd) fs
    Core.PArray ps rest -> concatMap (patVars True) ps ++ [(Core._binderName b, True) | Just b <- [rest]]
    Core.PAs b p -> (Core._binderName b, strict) : patVars strict p

-- THE WALK

-- | What the program knows: each function's walked arguments, and the data
-- types, to say what shape a parameter has.
data Ctx = Ctx
  { _walkers :: !(Map Callee [(Int, Kind)]),
    _datas :: !(Map Core.QualName Core.DataDecl)
  }

-- | A walk of the whole of an argument, or of one path down it (a lookup in a
-- tree: its depth, not its size).
--
-- 'Along' is a walk along a collection, the table's functions and what hands
-- one an argument: it costs the collection's length, and goes no deeper into
-- the elements than the function it is handed does, whose own walk is an
-- event of its own.
data Kind = Along | Path | Full
  deriving (Eq, Ord, Show)

-- | Which alternative of which case each event is in, innermost first: two
-- events are on one path when no case puts them in different alternatives.
type Arm = [(Core.Span, Int)]

onePath :: Arm -> Arm -> Bool
onePath a b = and [i == j | (s, i) <- a, (t, j) <- b, s == t]

-- | A value's root: the parameter of the function being walked that it is, or
-- is a part of ('True').
type Root = (Int, Bool)

data Env = Env
  { _roots :: !(Map Name Root),
    -- | Local functions' walked arguments.
    _locals :: !(Map Callee [(Int, Kind)]),
    _self :: !(Set Callee),
    _arm :: !Arm
  }

data Ev
  = SelfCall ![Maybe Root] ![Core.Expr] !Arm
  | SelfElems !Int
  | Walk !Callee !Kind !Core.Expr !Core.Span !(Maybe Root) !Arm
  | Grow !Core.Expr !Core.Span !Arm

-- | A finding: the check, the definition's name, where, and what.
data Finding = Finding !String !String !Core.Span !String

rootOf :: Env -> Core.Expr -> Maybe Root
rootOf env e =
  case Core._exprValue e of
    Core.EVar n -> Map.lookup n (_roots env)
    Core.EAccess b _ -> (\(i, _) -> (i, True)) <$> rootOf env b
    _ ->
      case appOf e of
        Just (G q, args)
          | Just i <- Map.lookup (key q) shrinkers,
            i < length args ->
              (\(r, _) -> (r, True)) <$> rootOf env (args !! i)
        _ -> Nothing

walkersOf :: Ctx -> Env -> Callee -> [(Int, Kind)]
walkersOf ctx env c =
  case Map.lookup c (_locals env) of
    Just ps -> ps
    Nothing ->
      case globalKey c >>= (`Map.lookup` seed) of
        Just ps -> [(p, Along) | p <- ps]
        Nothing -> Map.findWithDefault [] c (_walkers ctx)

-- | The events of one expression, and the findings of the loops and local
-- functions inside it.
walk :: Ctx -> String -> Env -> Core.Expr -> ([Ev], [Finding])
walk ctx def env e =
  case Core._exprValue e of
    Core.ECase scrut alts fb ->
      let r = rootOf env scrut
          bind k alt =
            let armed = env {_arm = (sp, k) : _arm env}
             in case r of
                  Just (i, s) -> armed {_roots = foldr (\(n, st) -> Map.insert n (i, s || st)) (_roots env) (patVars False (Core._altPattern alt))}
                  Nothing -> armed
       in walk ctx def env scrut <> mconcat [walk ctx def (bind k a) (Core._altBody a) | (k, a) <- zip [0 ..] alts] <> foldMap (walk ctx def env {_arm = (sp, -1) : _arm env}) fb
    Core.ELet binds body ->
      let (env', out) = List.foldl' (letBind False) (env, mempty) binds
       in out <> walk ctx def env' body
    Core.ELetRec binds body ->
      let group = Set.fromList [L (Core._binderName (Core._bindBinder b)) | b <- binds]
          (env', out) = localGroup group binds
       in out <> walk ctx def env' body
    _ ->
      case appOf e of
        Just (c, args) -> call c args
        Nothing -> foldMap (walk ctx def env) (children e)
  where
    sp = Core._exprSpan e
    letBind _ (en, out) (Core.Bind b v) =
      let n = Core._binderName b
       in case lambdaOf v of
            Just _ ->
              let (en', o) = localGroup (Set.singleton (L n)) [Core.Bind b v]
               in (en', out <> o)
            Nothing ->
              let en' = case rootOf en v of
                    Just r -> en {_roots = Map.insert n r (_roots en)}
                    Nothing -> en
               in (en', out <> walk ctx def en v)
    -- A local group: each function's walked arguments to a fixed point, and
    -- its findings under the enclosing definition's name.
    -- A local function that calls the one being walked is a step of its
    -- recursion (@sub i e = (shallow (step i path) e).expr@): a call of it is
    -- the recursive call, and it is not walked on its own.
    localGroup group binds =
      let fns = [(L (Core._binderName (Core._bindBinder b)), bs, body) | b <- binds, Just (bs, body) <- [lambdaOf (Core._bindValue b)]]
          wraps = not (Set.null (_self env)) && any (\(_, _, body) -> mentionsAny (_self env) body) fns
          step locals = Map.union (Map.fromList [(c, linear (fnWalk ctx (def ++ "." ++ calleeText c) (env {_locals = locals}) group bs body)) | (c, bs, body) <- fns]) locals
          final = iterate step (_locals env) !! 3
          env'
            | wraps = env {_self = Set.union group (_self env)}
            | otherwise = env {_locals = final}
          outs
            | wraps = []
            | otherwise = mconcat [snd (fnWalk ctx (def ++ "." ++ calleeText c) env' group bs body) | (c, bs, body) <- fns]
       in (env', ([], outs))
    -- a call whose witness is the function itself (a derived instance's
    -- recursion through @Array@'s) is the descent too
    witnessed =
      case Core._exprValue e of
        Core.EApp f _ -> witnessHas f
        _ -> False
    witnessHas f =
      case Core._exprValue f of
        Core.EWitApp g ws -> any (mentionsAny (_self env)) ws || witnessHas g
        Core.ETyApp g _ -> witnessHas g
        Core.EApp g _ -> witnessHas g
        _ -> False
    call c args =
      let k = globalKey c
          selfEv = [SelfCall (map (rootOf env) args) args (_arm env) | Set.member c (_self env)]
          -- a function handed elements whose own function recurses is the
          -- recursion's descent, not a walk beside it
          descentHof = witnessed || case hof of
            Just h | _hFn h < length args, Just (_, body) <- lambdaOf (args !! _hFn h) -> mentionsAny (_self env) body
            Just h | _hFn h < length args, Just f <- calleeOf (args !! _hFn h) -> Set.member f (_self env)
            _ -> False
          walkEvs =
            [ Walk c kind a sp (rootOf env a) (_arm env)
            | not (Set.member c (_self env)),
              not descentHof,
              (i, kind) <- walkersOf ctx env c,
              i < length args,
              let a = args !! i
            ]
          growEvs = [Grow (args !! i) sp (_arm env) | Just kk <- [k], Just i <- [growthOf kk], i < length args]
          hof = k >>= (`Map.lookup` hofs)
          (hofOut, handled) =
            case hof of
              Just h
                | _hFn h < length args,
                  _hColl h < length args ->
                    let coll = args !! _hColl h
                        fn = args !! _hFn h
                        collRoot = rootOf env coll
                     in case lambdaOf fn of
                          Just (bs, body) -> (foldBody h coll collRoot bs body, [_hFn h])
                          Nothing ->
                            case (calleeOf fn, collRoot) of
                              (Just f, Just (i, _)) | Set.member f (_self env) -> (([SelfElems i], []), [])
                              _ -> (mempty, [])
              _ -> (mempty, [])
          rest = foldMap (walk ctx def env) [a | (j, a) <- zip [0 ..] args, j `notElem` handled]
       in (selfEv ++ walkEvs ++ growEvs, []) <> hofOut <> rest
    -- A fold's function: its elements are parts of what the collection is a
    -- part of, and its accumulator is a loop's.
    foldBody h coll collRoot bs body =
      let names = map Core._binderName bs
          elems = [n | (j, n) <- zip [0 ..] names, j `elem` _hElems h]
          acc = [n | Just j <- [_hAcc h], j < length names, let n = names !! j]
          env' = case collRoot of
            Just (i, _) -> env {_roots = foldr (\n -> Map.insert n (i, True)) (_roots env) elems}
            Nothing -> env {_roots = foldr Map.delete (_roots env) names}
          (evs, out) = walk ctx def env' body
          collName = case Core._exprValue coll of Core.EVar n -> Just n; _ -> Nothing
          foldFindings =
            [ Finding "rewalk-fold" def s ("walks the folded " ++ Name.toChars n ++ " by " ++ calleeText w)
            | Just n <- [collName],
              Walk w kind a s _ _ <- evs,
              kind /= Path,
              isName n a
            ]
              ++ [Finding c def s d | Finding c _ s d <- accFindings ctx [(n, t) | b <- bs, let n = Core._binderName b, n `elem` acc, let t = Core._binderType b] evs]
       in (evs, out ++ foldFindings)

mentionsAny :: Set Callee -> Core.Expr -> Bool
mentionsAny cs e =
  case calleeOf e of
    Just c | Set.member c cs -> True
    _ -> any (mentionsAny cs) (children e)

isName :: Name -> Core.Expr -> Bool
isName n e = case Core._exprValue e of Core.EVar m -> m == n; _ -> False

-- | Where a value is read from: a name and the fields under it.
placeOf :: Core.Expr -> Maybe (Name, [Name])
placeOf e =
  case Core._exprValue e of
    Core.EVar m -> Just (m, [])
    Core.EAccess b f -> (\(m, fs) -> (m, fs ++ [f])) <$> placeOf b
    _ -> Nothing

-- | The accumulator itself, or one of its fields.
isAcc :: [Name] -> Core.Expr -> Bool
isAcc acc e =
  case Core._exprValue e of
    Core.EVar m -> m `elem` acc
    Core.EAccess b _ -> isAcc acc b
    _ -> False

-- | A loop's accumulators, with their types: a whole walk of one in a round,
-- or a path down one that is a list's, and one grown twice on one path
-- through a round.
accFindings :: Ctx -> [(Name, Core.Type)] -> [Ev] -> [Finding]
accFindings _ [] _ = []
accFindings ctx accTs evs =
  [ Finding "accwalk" "" s ("walks the accumulator (" ++ shapeOf ctx (Core.typeOf a) ++ ") by " ++ calleeText w ++ kindText kind)
  | Walk w kind a s _ _ <- evs,
    isAcc acc a,
    kind /= Path || shapeOf ctx (Core.typeOf a) `elem` ["list", "array", "string"]
  ]
    ++ [ Finding "forked" "" s ("the accumulator grown twice on one path through a round, at " ++ spanText s ++ " and " ++ spanText s')
       | let grows = [(s', arm, pl) | Grow g s' arm <- evs, isAcc acc g, Just pl <- [placeOf g]],
         ((s, _, _), (s', _, _)) <- take 1 [(x, y) | (j, x@(_, a1, p1)) <- zip [0 :: Int ..] grows, (k, y@(_, a2, p2)) <- zip [0 ..] grows, j < k, p1 == p2, onePath a1 a2]
       ]
  where
    acc = map fst accTs

evArm :: Ev -> Maybe Arm
evArm ev =
  case ev of
    Walk _ _ _ _ _ a -> Just a
    Grow _ _ a -> Just a
    _ -> Nothing

kindText :: Kind -> String
kindText k = case k of Full -> ""; Path -> " (a path)"; Along -> " (along it)"

spanText :: Core.Span -> String
spanText s = show (Core._spanStartRow s) ++ ":" ++ show (Core._spanStartCol s)

calleeText :: Callee -> String
calleeText c =
  case c of
    G q -> let (m, f) = key q in m ++ "." ++ f
    L n -> Name.toChars n

-- | One function: its events and findings, given the group it recurses in.
fnWalk :: Ctx -> String -> Env -> Set Callee -> [Core.Binder] -> Core.Expr -> ([Ev], [Finding])
fnWalk ctx def outer group bs body =
  let names = map Core._binderName bs
      env =
        outer
          { _roots = Map.union (Map.fromList (zip names [(i, False) | i <- [0 ..]])) (Map.map (const (-1, True)) (_roots outer)),
            _self = group,
            _arm = []
          }
      (evs, out) = walk ctx def env body
      descends =
        Set.fromList ([i | SelfCall rs _ _ <- evs, Just (i, True) <- rs, i >= 0] ++ [i | SelfElems i <- evs])
      accs =
        [ n
        | (i, n) <- zip [0 :: Int ..] names,
          or
            [ not (plain a) && Set.member n (freeNames a)
            | SelfCall _ args _ <- evs,
              i < length args,
              let a = args !! i
            ]
        ]
      plain a = case Core._exprValue a of Core.EVar _ -> True; Core.EAccess _ _ -> True; _ -> False
      shape i = if i < length bs then shapeOf ctx (Core._binderType (bs !! i)) else "?"
      rewalks =
        [ Finding "rewalk" def s ("recurses on a part of " ++ Name.toChars (names !! i) ++ " (" ++ shape i ++ ", " ++ descentText i ++ ") and walks " ++ (if strict then "a part of it" else "it") ++ " by " ++ calleeText w ++ kindText kind)
        | Walk w kind a s (Just (i, strict)) arm <- evs,
          Set.member i descends,
          perRound arm,
          i < length bs,
          if kind == Along
            then shape i `elem` ["array", "string", "balanced"] && Core.typeOf a == Core._binderType (bs !! i)
            else typeContains ctx 3 (Core._binderType (bs !! i)) (Core.typeOf a)
        ]
      descentText i = case Map.lookup i kinds of Just Full -> "every part"; _ -> "one part a step"
      kinds = Map.fromList (linear (evs, out))
      -- in a round: on one path with a recursive call, not in the arm that
      -- ends the recursion
      perRound arm = or [onePath arm a | SelfCall _ _ a <- evs] || not (null [() | SelfElems _ <- evs])
      roundEvs = [ev | ev <- evs, maybe True perRound (evArm ev)]
      accs' = [Finding c def s d | Finding c _ s d <- accFindings ctx [(n, Core._binderType b) | b <- bs, let n = Core._binderName b, n `elem` accs] roundEvs]
   in (evs, out ++ rewalks ++ accs')

-- | The arguments a function's events say it walks: those it recurses on a
-- part of, and those it hands a walk.
--
-- A walk of the whole when two recursive calls on one path each take a part,
-- or the recursion goes through a function handed the elements, or it hands
-- the argument to a walk of the whole; a path otherwise.
linear :: ([Ev], [Finding]) -> [(Int, Kind)]
linear (evs, _) =
  Map.toList (Map.fromListWith max (selfs ++ [(i, Full) | SelfElems i <- evs] ++ [(i, k) | Walk _ k _ _ (Just (i, _)) _ <- evs, i >= 0]))
  where
    calls = [(i, arm) | SelfCall rs _ arm <- evs, Just (i, True) <- rs, i >= 0]
    selfs =
      [ (i, if length [() | (j, a') <- calls, j == i, onePath arm a'] >= 2 then Full else Path)
      | (i, arm) <- calls
      ]

-- | Whether a value of the second type may hold one of the first: the type
-- itself, or one that has it as an argument or a field, to a depth.
typeContains :: Ctx -> Int -> Core.Type -> Core.Type -> Bool
typeContains ctx depth t u
  | t == u = True
  | depth <= 0 = False
  | otherwise =
      case u of
        Core.TCon q args ->
          any (typeContains ctx (depth - 1) t) args
            || maybe False (\d -> any (any (typeContains ctx (depth - 1) t) . Core._ctorFields) (Core._dataCtors d)) (Map.lookup q (_datas ctx))
        Core.TRecord fs _ -> any (typeContains ctx (depth - 1) t . snd) fs
        _ -> False

-- | What shape a parameter's type is: a list (one field of its own type), a
-- tree (more), an array, a string, a balanced tree, or something else.
shapeOf :: Ctx -> Core.Type -> String
shapeOf ctx t =
  case t of
    Core.TCon q _ ->
      case key q of
        ("Array", "Array") -> "array"
        ("String", "String") -> "string"
        ("Dict", "Dict") -> "balanced"
        ("Set", "Set") -> "balanced"
        _ ->
          case Map.lookup q (_datas ctx) of
            Just d ->
              let n = maximum (0 : [sum (map (mentions q) (Core._ctorFields c)) | c <- Core._dataCtors d])
               in if n == 0 then "flat" else if n == 1 then "list" else "tree"
            Nothing -> "other"
    Core.TForall _ _ b -> shapeOf ctx b
    _ -> "other"
  where
    -- a field of the type itself counts once, an array of it twice: either
    -- is a tree's children
    mentions q ft =
      case ft of
        Core.TCon r args
          | r == q -> 1
          | key r == ("Array", "Array") && any ((> 0) . mentions q) args -> 2
          | otherwise -> sum (map (mentions q) args)
        Core.TRecord fs _ -> sum (map (mentions q . snd) fs)
        Core.TFun _ _ -> 0
        _ -> 0 :: Int

-- THE PROGRAM

findings :: Map ModuleName.Canonical Core.Module -> [String]
findings cores =
  let mods = Map.elems cores
      datas = Map.fromList [(Core._dataName d, d) | m <- mods, d <- Core._moduleData m]
      groupOf = Map.fromList [(q, Set.fromList (map G g)) | m <- mods, g <- Core._moduleDefsRec m, q <- g]
      defs =
        [ (m, q, bs, body)
        | m <- mods,
          Core.Bind b v <- Core._moduleDefs m,
          let q = Core.QualName (Core._moduleName m) (Core._binderName b),
          Just (bs, body) <- [lambdaOf v]
        ]
      emptyEnv = Env Map.empty Map.empty Set.empty []
      groupFor q = Set.insert (G q) (Map.findWithDefault Set.empty q groupOf)
      round_ ws =
        let ctx = Ctx ws datas
         in Map.fromList [(G q, ps) | (_, q, bs, body) <- defs, let ps = linear (fnWalk ctx (Name.toChars (Core._qnName q)) emptyEnv (groupFor q) bs body), not (null ps)]
      fixed = go (0 :: Int) Map.empty
        where
          go n ws =
            let ws' = Map.unionWith (\a b -> Map.toList (Map.fromListWith max (a ++ b))) (round_ ws) ws
             in if n >= 8 || ws' == ws then ws' else go (n + 1) ws'
      ctxF = Ctx fixed datas
   in [ List.intercalate "\t" [check, Pkg.toChars (ModuleName._package (Core._moduleName m)), Name.toChars (ModuleName._module (Core._moduleName m)), d, show (Core._spanStartRow s) ++ ":" ++ show (Core._spanStartCol s), detail]
      | (m, q, bs, body) <- defs,
        Finding check d s detail <- snd (fnWalk ctxF (Name.toChars (Core._qnName q)) emptyEnv (groupFor q) bs body)
      ]
