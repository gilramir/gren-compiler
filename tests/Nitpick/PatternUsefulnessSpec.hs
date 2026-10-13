module Nitpick.PatternUsefulnessSpec (spec) where

-- The redundancy and exhaustiveness checks against brute force, on random
-- patterns (geng-lang D694). 'checkPatterns' answers which branch is the
-- first redundant one in one walk over the matrix; here every value of the
-- scrutinee's type is enumerated, one value for each distinction the
-- patterns can draw, and a branch is redundant when every value it matches
-- matches a branch before it.

import AST.Canonical qualified as Can
import Data.Index qualified as Index
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Name qualified as N
import Data.Utf8 qualified as Utf8
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Nitpick.PatternMatches (Context (..), Error (..), checkPatterns)
import Reporting.Annotation qualified as A
import Test.Hspec (Spec, describe, it, shouldBe)

data Ty
  = TyBool
  | TyMaybe Ty
  | TyInt
  | TyArray Ty
  | TyRecord [(String, Ty)]

data Value
  = VBool Bool
  | VNothing
  | VJust Value
  | VInt Integer
  | VArray [Value]
  | VRecord (Map.Map String Value)

-- RANDOM

newtype Gen a = Gen (Int -> (a, Int))

instance Functor Gen where
  fmap f (Gen g) = Gen (\s -> let (a, s') = g s in (f a, s'))

instance Applicative Gen where
  pure a = Gen (\s -> (a, s))
  Gen f <*> Gen g = Gen (\s -> let (h, s1) = f s; (a, s2) = g s1 in (h a, s2))

instance Monad Gen where
  Gen g >>= k = Gen (\s -> let (a, s1) = g s; Gen h = k a in h s1)

runGen :: Gen a -> Int -> a
runGen (Gen g) seed = fst (g seed)

-- | A number in [0, n).
below :: Int -> Gen Int
below n =
  Gen
    ( \s ->
        let s' = (s * 1103515245 + 12345) `mod` 2147483648
         in ((s' `div` 65536) `mod` n, s')
    )

oneOf :: [a] -> Gen a
oneOf xs = (xs !!) <$> below (length xs)

genTy :: Int -> Gen Ty
genTy depth =
  do
    k <- below (if depth <= 0 then 2 else 5)
    case k of
      0 -> pure TyBool
      1 -> pure TyInt
      2 -> TyMaybe <$> genTy (depth - 1)
      3 -> TyArray <$> genTy (depth - 2)
      _ ->
        do
          n <- (+ 1) <$> below 3
          TyRecord <$> traverse (\i -> (,) ("f" ++ show i) <$> genTy (depth - 1)) [1 .. n]

genPattern :: Ty -> Gen Can.Pattern
genPattern ty =
  do
    wild <- below 4
    if wild == 0
      then oneOf [at Can.PAnything, at (Can.PVar (N.fromChars "x"))]
      else case ty of
        TyBool -> at . Can.PBool boolUnion <$> oneOf [True, False]
        TyInt -> at . Can.PInt <$> oneOf [0, 1, 2]
        TyMaybe inner ->
          do
            just <- below 2
            if just == 0
              then pure (at (maybeCtor False []))
              else (\p -> at (maybeCtor True [p])) <$> genPattern inner
        TyArray inner ->
          do
            len <- below 3
            at . Can.PArray <$> traverse (const (genPattern inner)) [1 .. len]
        TyRecord fields ->
          do
            keep <- traverse (\f -> (,) f <$> below 2) fields
            let named = case [f | (f, 1) <- keep] of
                  [] -> take 1 fields
                  fs -> fs
            at . Can.PRecord
              <$> traverse
                (\(name, t) -> (\p -> at (Can.PRFieldPattern (N.fromChars name) p)) <$> genPattern t)
                named

at :: a -> A.Located a
at = A.At A.zero

-- VALUES

-- | One value for each class the patterns can tell apart: the literals they
-- name and one more, and the array lengths they name and one more.
values :: Ty -> [Value]
values ty =
  case ty of
    TyBool -> [VBool True, VBool False]
    TyInt -> map VInt [0, 1, 2, 3]
    TyMaybe inner -> VNothing : map VJust (values inner)
    TyArray inner -> [VArray vs | len <- [0 .. 3], vs <- sequence (replicate len (values inner))]
    TyRecord fields ->
      [ VRecord (Map.fromList (zip (map fst fields) vs))
      | vs <- sequence (map (values . snd) fields)
      ]

matches :: Can.Pattern -> Value -> Bool
matches (A.At _ pattern) value =
  case (pattern, value) of
    (Can.PAnything, _) -> True
    (Can.PVar _, _) -> True
    (Can.PAlias inner _, _) -> matches inner value
    (Can.PBool _ b, VBool v) -> b == v
    (Can.PInt n, VInt v) -> n == v
    (Can.PCtor {Can._p_name = name, Can._p_args = args}, _) ->
      case (N.toChars name, args, value) of
        ("Nothing", [], VNothing) -> True
        ("Just", [Can.PatternCtorArg _ _ p], VJust v) -> matches p v
        _ -> False
    (Can.PArray items, VArray vs) -> length items == length vs && and (zipWith matches items vs)
    (Can.PRecord fields, VRecord vs) ->
      and
        [ maybe False (matches p) (Map.lookup (N.toChars name) vs)
        | A.At _ (Can.PRFieldPattern name p) <- fields
        ]
    _ -> False

-- | What brute force says: the first branch every one of whose values an
-- earlier branch matches, or whether some value matches no branch.
data Verdict = RedundantAt Int | Missing | Fine | Skipped
  deriving (Eq, Show)

oracle :: Ty -> [Can.Pattern] -> Verdict
oracle ty patterns =
  let vs = values ty
      redundant i p = all (\v -> not (matches p v) || any (`matches` v) (take i patterns)) vs
   in case [i | (i, p) <- zip [0 ..] patterns, redundant i p] of
        i : _ -> RedundantAt (i + 1)
        [] -> if all (\v -> any (`matches` v) patterns) vs then Fine else Missing

verdict :: [Can.Pattern] -> Verdict
verdict patterns =
  case checkPatterns A.zero BadCase patterns [] of
    [] -> Fine
    [Redundant _ _ i] -> RedundantAt i
    [Incomplete _ _ _] -> Missing
    _ -> error "checkPatterns answered more than one error for one when"

-- TYPES THE PATTERNS NAME

boolUnion :: Can.Union
boolUnion =
  Can.Union
    { Can._u_vars = [],
      Can._u_alts =
        [ Can.Ctor (N.fromChars "True") Index.first 0 [],
          Can.Ctor (N.fromChars "False") (Index.next Index.first) 0 []
        ],
      Can._u_numAlts = 2,
      Can._u_opts = Can.Enum
    }

maybeUnion :: Can.Union
maybeUnion =
  Can.Union
    { Can._u_vars = [N.fromChars "a"],
      Can._u_alts =
        [ Can.Ctor (N.fromChars "Just") Index.first 1 [Can.TVar (N.fromChars "a")],
          Can.Ctor (N.fromChars "Nothing") (Index.next Index.first) 0 []
        ],
      Can._u_numAlts = 2,
      Can._u_opts = Can.Normal
    }

maybeCtor :: Bool -> [Can.Pattern] -> Can.Pattern_
maybeCtor isJust args =
  Can.PCtor
    { Can._p_home = ModuleName.Canonical Pkg.core (Utf8.fromChars "Maybe"),
      Can._p_type = N.fromChars "Maybe",
      Can._p_union = maybeUnion,
      Can._p_name = N.fromChars (if isJust then "Just" else "Nothing"),
      Can._p_index = if isJust then Index.first else Index.next Index.first,
      Can._p_args = [Can.PatternCtorArg Index.first (Can.TVar (N.fromChars "a")) p | p <- args]
    }

-- SPEC

spec :: Spec
spec =
  describe "redundant and missing patterns, against brute force" $
    -- A type of more than 300 values is skipped: brute force is slow there,
    -- not wrong.
    it "agree on 4,000 random whens" $
      let case_ seed =
            runGen
              ( do
                  ty <- genTy 3
                  n <- (+ 1) <$> below 7
                  patterns <- traverse (const (genPattern ty)) [1 .. n]
                  pure $
                    if length (take 301 (values ty)) > 300
                      then (seed, Skipped, Skipped)
                      else (seed, oracle ty patterns, verdict patterns)
              )
              seed
          cases = filter (\(_, want, _) -> want /= Skipped) (map case_ [1 .. 4000])
          disagreements = [(seed, want) | (seed, want, got) <- cases, want /= got]
          verdicts = map (\(_, want, _) -> want) cases
       in do
            take 5 disagreements `shouldBe` []
            -- The cases have to reach all three answers to test anything.
            List.sort (List.nub (map kind verdicts)) `shouldBe` [0, 1, 2 :: Int]
  where
    kind v = case v of
      RedundantAt _ -> 0
      Missing -> 1
      Fine -> 2
      Skipped -> 3
