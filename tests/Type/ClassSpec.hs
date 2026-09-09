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
-- __`Ord` left__ (D130, §G29) and __`Appendable` left__ (D138, §G36). `core`
-- declares both, so membership is an instance lookup the elaborator does and
-- there is nothing here to ask. What that took out of this file is most of it:
-- every entailment fact was `Num`-entails-`Ord`, every interesting union was
-- the old `CompAppend` pair, and the appendable half of every table is an
-- ordinary pair of instances in `core` now.
--
-- __One class is left__, so the set algebra has one interesting case and the
-- facts below are mostly about what the tables *refuse*. That is worth keeping
-- rather than deleting: D2 puts `Integral`, `Fractional` and `Bits` back, each
-- one a row in the same tables, and these are the shapes their arrival has to
-- keep answering.
spec :: Spec
spec = do
  describe "Reduction" $ do
    it "a class unioned with itself is itself" $
      names (union [Class.Num] [Class.Num]) `shouldBe` ["Num"]

    it "union is commutative" $
      names (union [Class.Num] [Class.Num])
        `shouldBe` names (union [Class.Num] [Class.Num])

  describe "Inhabitance" $ do
    it "an Int is a number" $
      inhabited [Class.Num] `shouldBe` True

    it "an empty constraint set is not a constrained variable at all" $
      -- `fromList []` is `Nothing`, which is `FlexVar` rather than a set no
      -- type satisfies. The distinction is why `inhabited` is asked where the
      -- variable is created.
      names' (Class.fromList []) `shouldBe` Nothing

  describe "Entailment" $ do
    it "a class satisfies a demand for itself" $
      entailedBy [Class.Num] [Class.Num] `shouldBe` True

  describe "Arrays" $ do
    it "no array is a number" $
      -- The recursive case that made this interesting was `Ord`, and the
      -- unconditional one was `Appendable`; both are instances in `core` now,
      -- so every answer this table gives is `Nothing`.
      Class.arrayObligations Class.Num `shouldBe` Nothing

  describe "Defaulting" $ do
    it "an ambiguous number becomes Int" $
      -- `classes.md` §0's headline, and `same 3 3`'s whole problem.
      defaultsTo [Class.Num] `shouldBe` Just "Int"

    it "an unconstrained variable has nothing to default" $
      defaultsTo [] `shouldBe` Nothing

  describe "The declared names" $ do
    it "reads the one class the unifier still owns" $ do
      -- D135. What used to be here was a table of magic type-variable *names*;
      -- the bridge is a qualified class name now, and `core` declares it.
      Class.fromDeclared ModuleName.basics "Num" `shouldBe` Just Class.Num

    it "round-trips through the name core declares" $
      Class.toDeclared Class.Num `shouldBe` (ModuleName.basics, "Num")

    it "an open class is not one, and that is what makes it the elaborator's" $ do
      -- `Eq`, `Ord` and `Appendable` are declared in the same module and are
      -- not here: their constraints leave the unifier entirely (D130, D138).
      Class.fromDeclared ModuleName.basics "Eq" `shouldBe` Nothing
      Class.fromDeclared ModuleName.basics "Ord" `shouldBe` Nothing
      Class.fromDeclared ModuleName.basics "Appendable" `shouldBe` Nothing
      Class.isClosed ModuleName.basics "Ord" `shouldBe` False
      Class.isClosed ModuleName.basics "Appendable" `shouldBe` False
      Class.isClosed ModuleName.basics "Num" `shouldBe` True

    it "a same-named class from another module is a different class" $
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
