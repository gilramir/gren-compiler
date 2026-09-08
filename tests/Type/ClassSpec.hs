{-# LANGUAGE OverloadedStrings #-}

module Type.ClassSpec where

import Data.Name qualified as Name
import Gren.ModuleName qualified as ModuleName
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

  describe "The declared names" $ do
    it "reads the two classes the unifier still owns" $ do
      -- D135. What used to be here was a table of magic type-variable *names*;
      -- the bridge is a qualified class name now, and `core` declares both.
      Class.fromDeclared ModuleName.basics "Num" `shouldBe` Just Class.Num
      Class.fromDeclared ModuleName.basics "Appendable" `shouldBe` Just Class.Appendable

    it "round-trips through the name core declares" $ do
      Class.toDeclared Class.Num `shouldBe` (ModuleName.basics, "Num")
      Class.toDeclared Class.Appendable `shouldBe` (ModuleName.basics, "Appendable")

    it "an open class is not one, and that is what makes it the elaborator's" $ do
      -- `Eq` and `Ord` are declared in the same module and are not here: their
      -- constraints leave the unifier entirely (D130).
      Class.fromDeclared ModuleName.basics "Eq" `shouldBe` Nothing
      Class.fromDeclared ModuleName.basics "Ord" `shouldBe` Nothing
      Class.isClosed ModuleName.basics "Ord" `shouldBe` False
      Class.isClosed ModuleName.basics "Num" `shouldBe` True

    it "a same-named class from another module is a different class" $ do
      -- The reason the bridge is a *qualified* name. A package declaring its
      -- own `Num` gets an ordinary open class, not the numeric one.
      Class.fromDeclared ModuleName.string "Num" `shouldBe` Nothing

    it "no type-variable name means anything any more" $ do
      -- `number`, `appendable`, `comparable` and `compappend` were all magic
      -- at M1b's start. This is the whole of what is left of that.
      Class.fromDeclared ModuleName.basics "number" `shouldBe` Nothing
      Class.fromDeclared ModuleName.basics "appendable" `shouldBe` Nothing

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
