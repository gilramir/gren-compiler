{-# LANGUAGE OverloadedStrings #-}

module Type.ClassSpec where

import Data.Name qualified as Name
import Test.Hspec (Spec, describe, it, shouldBe)
import Type.Class qualified as Class

-- | The algebra that replaced `SuperType`'s 4×4 meet table
-- (`docs/m1b-classes.md` §G18). Every fact here was a cell in that table, and
-- the point of writing them down is that the table is gone: they now follow
-- from a membership lookup and a set union, so they have to be *checked*
-- rather than read off a case expression.
--
-- __`Ord` left__ (D130, §G29). `core` declares it, so membership is an instance
-- lookup the elaborator does and there is nothing here to ask. What that took
-- out of this file is most of it: every entailment fact was `Num`-entails-`Ord`,
-- every interesting union was the old `CompAppend` pair, and the recursive array
-- obligation is an ordinary recursive instance in `core` now. What is left is
-- `Num` and `Appendable`, and `Appendable` leaves with D13.
spec :: Spec
spec = do
  describe "Reduction" $ do
    it "two classes neither of which implies the other both stay" $
      names (union [Class.Num] [Class.Appendable]) `shouldBe` ["Num", "Appendable"]

    it "union is commutative" $
      names (union [Class.Appendable] [Class.Num])
        `shouldBe` names (union [Class.Num] [Class.Appendable])

    it "a class unioned with itself is itself" $
      names (union [Class.Num] [Class.Num]) `shouldBe` ["Num"]

  describe "Inhabitance" $ do
    it "an Int is a number" $
      inhabited [Class.Num] `shouldBe` True

    it "a String is appendable" $
      inhabited [Class.Appendable] `shouldBe` True

    it "nothing is both a number and appendable" $
      -- The old table had no constructor for this pair and reported the
      -- mismatch on the spot. A set can hold it, so `unifyFlexSuper` asks.
      inhabited [Class.Num, Class.Appendable] `shouldBe` False

  describe "Entailment" $ do
    it "a class satisfies a demand for itself" $
      entailedBy [Class.Num] [Class.Num] `shouldBe` True

    it "and for nothing else" $ do
      -- `Num` entailed `Ord` until `Ord` left the unifier; with two unrelated
      -- classes left, containment is equality. It is still stated separately
      -- from the tables because D2's `Integral` and `Fractional` bring it back.
      entailedBy [Class.Appendable] [Class.Num] `shouldBe` False
      entailedBy [Class.Num] [Class.Appendable] `shouldBe` False

    it "a set satisfies a demand for either half" $ do
      entailedBy [Class.Num, Class.Appendable] [Class.Num] `shouldBe` True
      entailedBy [Class.Num, Class.Appendable] [Class.Appendable] `shouldBe` True

  describe "Arrays" $ do
    it "no array is a number" $
      Class.arrayObligations Class.Num `shouldBe` Nothing

    it "an array is appendable whatever it holds" $
      Class.arrayObligations Class.Appendable `shouldBe` Just []

  describe "Defaulting" $ do
    it "an ambiguous number becomes Int" $
      -- `classes.md` §0's headline, and `same 3 3`'s whole problem.
      defaultsTo [Class.Num] `shouldBe` Just "Int"

    it "an appendable does not default, because no candidate is one" $
      -- §0 lists the defaultable classes; this reads that list off
      -- `admitsAtom` instead of restating it, so `Appendable` is excluded by
      -- the same table the unifier uses. It leaves with D13.
      defaultsTo [Class.Appendable] `shouldBe` Nothing

    it "nor does a pair one candidate satisfies only half of" $
      defaultsTo [Class.Num, Class.Appendable] `shouldBe` Nothing

  describe "The magic names" $ do
    it "reads the two constrained type variables that are left" $ do
      names' (Class.fromName "number") `shouldBe` Just ["Num"]
      names' (Class.fromName "appendable") `shouldBe` Just ["Appendable"]

    it "numbers them the way the parser does" $
      names' (Class.fromName "number2") `shouldBe` Just ["Num"]

    it "comparable and compappend are ordinary variables now" $ do
      -- The other half of D130: `core` says `Ord a =>`, so these two names mean
      -- nothing and a program may use them for anything.
      names' (Class.fromName "comparable") `shouldBe` Nothing
      names' (Class.fromName "compappend") `shouldBe` Nothing

    it "an ordinary variable has no classes" $
      names' (Class.fromName "a") `shouldBe` Nothing

union :: [Class.Class] -> [Class.Class] -> Maybe Class.Classes
union a b =
  case (Class.fromList a, Class.fromList b) of
    (Just x, Just y) -> Just (Class.union x y)
    _ -> Nothing

inhabited :: [Class.Class] -> Bool
inhabited cs =
  maybe False Class.inhabited (Class.fromList cs)

entailedBy :: [Class.Class] -> [Class.Class] -> Bool
entailedBy have want =
  case (Class.fromList have, Class.fromList want) of
    (Just h, Just w) -> Class.entailedBy h w
    _ -> False

defaultsTo :: [Class.Class] -> Maybe String
defaultsTo cs =
  case Class.fromList cs of
    Nothing -> Nothing
    Just classes -> Name.toChars . snd <$> Class.defaultsTo classes

names :: Maybe Class.Classes -> [String]
names =
  maybe [] (map show' . Class.toList)

names' :: Maybe Class.Classes -> Maybe [String]
names' =
  fmap (map show' . Class.toList)

show' :: Class.Class -> String
show' c =
  case c of
    Class.Num -> "Num"
    Class.Appendable -> "Appendable"
