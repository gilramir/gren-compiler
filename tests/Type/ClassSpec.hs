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
spec :: Spec
spec = do
  describe "Reduction" $ do
    it "a set keeps only what nothing else implies" $
      -- `number` and `comparable` together is `number`, which is what the old
      -- table's `Number`/`Comparable` cell said and what keeps the error
      -- layer's vocabulary intact.
      names (union [Class.Num] [Class.Ord]) `shouldBe` ["Num"]

    it "two classes neither of which implies the other both stay" $
      -- The old `CompAppend` constructor, as an ordinary set.
      names (union [Class.Ord] [Class.Appendable]) `shouldBe` ["Ord", "Appendable"]

    it "union is commutative" $
      names (union [Class.Appendable] [Class.Ord])
        `shouldBe` names (union [Class.Ord] [Class.Appendable])

  describe "Inhabitance" $ do
    it "a number is comparable, so both together are satisfiable" $
      inhabited [Class.Num, Class.Ord] `shouldBe` True

    it "a string is comparable and appendable" $
      inhabited [Class.Ord, Class.Appendable] `shouldBe` True

    it "nothing is both a number and appendable" $
      -- The old table had no constructor for this pair and reported the
      -- mismatch on the spot. A set can hold it, so `unifyFlexSuper` asks.
      inhabited [Class.Num, Class.Appendable] `shouldBe` False

  describe "Entailment" $ do
    it "a rigid number satisfies a demand for comparable" $
      entailedBy [Class.Num] [Class.Ord] `shouldBe` True

    it "a rigid appendable does not satisfy a demand for comparable" $
      -- An `Array` of something uncomparable is appendable, so the
      -- containment does not hold in this direction.
      entailedBy [Class.Appendable] [Class.Ord] `shouldBe` False

    it "a rigid compappend satisfies either half" $ do
      entailedBy [Class.Ord, Class.Appendable] [Class.Ord] `shouldBe` True
      entailedBy [Class.Ord, Class.Appendable] [Class.Appendable] `shouldBe` True

    it "comparable does not satisfy a demand for number" $
      entailedBy [Class.Ord] [Class.Num] `shouldBe` False

  describe "Arrays" $ do
    it "no array is a number" $
      Class.arrayObligations Class.Num `shouldBe` Nothing

    it "an array is comparable when its element is" $
      Class.arrayObligations Class.Ord `shouldBe` Just [Class.Ord]

    it "an array is appendable whatever it holds" $
      Class.arrayObligations Class.Appendable `shouldBe` Just []

  describe "Defaulting" $ do
    it "an ambiguous number becomes Int" $
      -- `classes.md` §0's headline, and `same 3 3`'s whole problem.
      defaultsTo [Class.Num] `shouldBe` Just "Int"

    it "so does an ambiguous comparable, because Int is comparable" $
      -- §0 makes an open class that both candidates derive defaultable rather
      -- than blocking, and the table is what says `Ord` is one.
      defaultsTo [Class.Ord] `shouldBe` Just "Int"

    it "and so does the pair, which reduces to number anyway" $
      defaultsTo [Class.Num, Class.Ord] `shouldBe` Just "Int"

    it "an appendable does not default, because no candidate is one" $
      -- §0 lists the defaultable classes; this reads that list off
      -- `admitsAtom` instead of restating it, so `Appendable` is excluded by
      -- the same table the unifier uses. It leaves with D13.
      defaultsTo [Class.Appendable] `shouldBe` Nothing

    it "nor does a pair one candidate satisfies only half of" $
      defaultsTo [Class.Num, Class.Appendable] `shouldBe` Nothing

    it "the candidates are ordered, so Int wins wherever both fit" $
      -- Which is what makes §0's `Fractional` clause fall out rather than be
      -- written: `Float` is reached only when `Int` is refused.
      defaultsTo [Class.Ord] `shouldBe` Just "Int"

  describe "The magic names" $ do
    it "reads Gren's three constrained type variables" $ do
      names' (Class.fromName "number") `shouldBe` Just ["Num"]
      names' (Class.fromName "comparable") `shouldBe` Just ["Ord"]
      names' (Class.fromName "appendable") `shouldBe` Just ["Appendable"]
      names' (Class.fromName "compappend") `shouldBe` Just ["Ord", "Appendable"]

    it "numbers them the way the parser does" $
      names' (Class.fromName "number2") `shouldBe` Just ["Num"]

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
    Class.Ord -> "Ord"
    Class.Appendable -> "Appendable"
