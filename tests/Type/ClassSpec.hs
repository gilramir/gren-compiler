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
-- __All four closed classes are here__ as of D145 (`docs/m1b-int.md` §I12), so
-- the set algebra has real cases again: `7 // 2 + 1` constrains one variable by
-- `Integral` and `Num` at once and `1 / 2` by `Fractional` and `Num`. The shape
-- to watch is D146 — the union keeps *both*, because a closed class carries a
-- witness now and `Integral` no longer stands in for `Num`.
spec :: Spec
spec = do
  describe "Union" $ do
    it "a class unioned with itself is itself" $
      names (union [Class.Num] [Class.Num]) `shouldBe` ["Num"]

    it "union is commutative" $
      names (union [Class.Num] [Class.Integral])
        `shouldBe` names (union [Class.Integral] [Class.Num])

    it "keeps a class another one's members contain" $
      -- D146, and the test that would have failed under the reduction this
      -- replaced: every `Integral` type is a `Num` type, so a containment rule
      -- would drop `Num` here -- and with it the witness `+` projects its
      -- method out of. `countDown` publishes two constraints and needs two.
      names (union [Class.Num] [Class.Integral]) `shouldBe` ["Num", "Integral"]

  describe "Inhabitance" $ do
    it "an Int is a number" $
      inhabited [Class.Num] `shouldBe` True

    it "an Int is integral and bitwise at once" $
      inhabited [Class.Num, Class.Integral, Class.Bits] `shouldBe` True

    it "nothing is both fractional and integral" $
      -- `classes.md` §0 calls this a type error rather than a defaulting case,
      -- and this is where it is refused: at the variable that asks for both,
      -- not at whatever later use site would have had nothing to default to.
      inhabited [Class.Fractional, Class.Integral] `shouldBe` False

    it "nor both fractional and bitwise" $
      inhabited [Class.Fractional, Class.Bits] `shouldBe` False

    it "an empty constraint set is not a constrained variable at all" $
      -- `fromList []` is `Nothing`, which is `FlexVar` rather than a set no
      -- type satisfies. The distinction is why `inhabited` is asked where the
      -- variable is created.
      names' (Class.fromList []) `shouldBe` Nothing

  describe "Entailment" $ do
    it "a class satisfies a demand for itself" $
      entailedBy [Class.Num] [Class.Num] `shouldBe` True

    it "Integral does not satisfy a demand for Num" $ do
      -- D146, and it reads backwards until you ask what a witness is. Every
      -- `Integral` type is a `Num` type, so `classes.md` §1.2 promised this
      -- for free under "closed classes pay no superclass cost" -- but at a
      -- *rigid* variable there is no type to look up, and a `Num a` demand
      -- needs a `Num` witness that only a written `Num a` brings in. So
      -- `f : Integral a => a -> a` may not say `x + x`.
      entailedBy [Class.Integral] [Class.Num] `shouldBe` False
      entailedBy [Class.Bits] [Class.Num] `shouldBe` False
      entailedBy [Class.Fractional] [Class.Num] `shouldBe` False

    it "both written satisfies either demand" $ do
      -- What a function needing both writes, exactly as §1.3 has
      -- `(Eq a, Ord a) =>`.
      entailedBy [Class.Num, Class.Integral] [Class.Num] `shouldBe` True
      entailedBy [Class.Num, Class.Integral] [Class.Integral] `shouldBe` True
      entailedBy [Class.Num, Class.Integral] [Class.Num, Class.Integral] `shouldBe` True

    it "and membership at a concrete type still costs nothing" $ do
      -- The half of §1.2's sentence D146 leaves standing: `7 // 2 + 1` needs
      -- no entailment rule, because `Int` is in both tables by construction.
      Class.admitsAtom Class.Integral ModuleName.basics "Int" `shouldBe` True
      Class.admitsAtom Class.Num ModuleName.basics "Int" `shouldBe` True

  describe "Arrays" $ do
    it "no array is in any of them" $ do
      -- The recursive case that made this interesting was `Ord`, and the
      -- unconditional one was `Appendable`; both are instances in `core` now,
      -- so every answer this table gives is `Nothing`.
      Class.arrayObligations Class.Num `shouldBe` Nothing
      Class.arrayObligations Class.Integral `shouldBe` Nothing
      Class.arrayObligations Class.Fractional `shouldBe` Nothing
      Class.arrayObligations Class.Bits `shouldBe` Nothing

  describe "Defaulting" $ do
    it "an ambiguous number becomes Int" $
      -- `classes.md` §0's headline, and `same 3 3`'s whole problem.
      defaultsTo [Class.Num] `shouldBe` Just "Int"

    it "an unconstrained variable has nothing to default" $
      defaultsTo [] `shouldBe` Nothing

    it "a fractional one becomes Float, and no clause here says so" $ do
      -- D129's point, now that the class exists to prove it: `defaultsTo` is
      -- the ordered list [Int, Float] filtered by `admitsAtom`, so §0's
      -- `Fractional` clause falls out of the membership table rather than
      -- being written a second time.
      defaultsTo [Class.Fractional] `shouldBe` Just "Float"
      defaultsTo [Class.Num, Class.Fractional] `shouldBe` Just "Float"

    it "an integral or bitwise one becomes Int" $ do
      -- `inspect (7 // 2)` and `inspect (Bitwise.and 1 2)`, which §0 names.
      defaultsTo [Class.Num, Class.Integral] `shouldBe` Just "Int"
      defaultsTo [Class.Num, Class.Bits] `shouldBe` Just "Int"

  describe "Membership" $ do
    it "the list is what `admitsAtom` is a lookup in" $
      -- One list, not two (D144). `core` writes an instance per member and
      -- `Canonicalize.Module` checks that against this, so a width added here
      -- and nowhere else is a compile error in `Basics` rather than a
      -- `NO INSTANCE` at some unlucky call site.
      map (Name.toChars . snd) (Class.members Class.Num) `shouldBe` ["Int", "Float"]

    it "the integer classes hold the integer types and the fractional one does not" $ do
      -- Three of the four hold one type each today, which is D2's whole shape:
      -- `Int64`, `UInt32` and `UInt64` join the integer three at §I8 step 4 and
      -- `Float32` joins `Fractional`.
      map (Name.toChars . snd) (Class.members Class.Integral) `shouldBe` ["Int"]
      map (Name.toChars . snd) (Class.members Class.Bits) `shouldBe` ["Int"]
      map (Name.toChars . snd) (Class.members Class.Fractional) `shouldBe` ["Float"]

    it "no Float is integral and no Int is fractional" $ do
      Class.admitsAtom Class.Integral ModuleName.basics "Float" `shouldBe` False
      Class.admitsAtom Class.Bits ModuleName.basics "Float" `shouldBe` False
      Class.admitsAtom Class.Fractional ModuleName.basics "Int" `shouldBe` False

    it "every member is admitted, and nothing else is" $ do
      all (uncurry (Class.admitsAtom Class.Num)) (Class.members Class.Num) `shouldBe` True
      Class.admitsAtom Class.Num ModuleName.string "String" `shouldBe` False

    it "the four widths are not members until their instances are written" $ do
      -- §I8 step 4. `Canonicalize.Prim` names their types already, which costs
      -- nothing because they are not Gren types yet; putting one here before
      -- `instance Num Int64` exists would make `Basics` stop compiling.
      Class.admitsAtom Class.Num ModuleName.basics "Int64" `shouldBe` False
      Class.admitsAtom Class.Num ModuleName.basics "Float32" `shouldBe` False

  describe "The declared names" $ do
    it "reads the classes the unifier owns" $ do
      -- D135. What used to be here was a table of magic type-variable *names*;
      -- the bridge is a qualified class name now, and `core` declares it.
      Class.fromDeclared ModuleName.basics "Num" `shouldBe` Just Class.Num
      Class.fromDeclared ModuleName.basics "Integral" `shouldBe` Just Class.Integral
      Class.fromDeclared ModuleName.basics "Fractional" `shouldBe` Just Class.Fractional

    it "Bits is Bitwise's, and that is not an arbitrary choice" $ do
      -- D145: a closed class lives where its operators are, and `Bits` has
      -- none -- but its methods are `and`, `or` and `xor`, which are `Basics`'s
      -- names for the `Bool` operations, and §G20 refuses two values of one
      -- name in one module.
      Class.fromDeclared ModuleName.bitwise "Bits" `shouldBe` Just Class.Bits
      Class.fromDeclared ModuleName.basics "Bits" `shouldBe` Nothing
      Class.fromDeclared ModuleName.bitwise "Num" `shouldBe` Nothing

    it "round-trips through the name core declares" $ do
      Class.toDeclared Class.Num `shouldBe` (ModuleName.basics, "Num")
      Class.toDeclared Class.Integral `shouldBe` (ModuleName.basics, "Integral")
      Class.toDeclared Class.Fractional `shouldBe` (ModuleName.basics, "Fractional")
      Class.toDeclared Class.Bits `shouldBe` (ModuleName.bitwise, "Bits")

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
    Class.Integral -> "Integral"
    Class.Fractional -> "Fractional"
    Class.Bits -> "Bits"
