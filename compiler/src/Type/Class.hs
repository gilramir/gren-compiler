{-# OPTIONS_GHC -Wall #-}

-- | The classes the unifier knows by construction, and the tables that say
-- which types belong to them.
--
-- This replaces the `SuperType` enum that used to live inside `Type.Type`'s
-- `Content` (`docs/m1b-classes.md` §G4 verb 2). Two things changed with it and
-- both are the point:
--
-- * __A variable carries a set of classes, not one.__ The old enum had one
--   slot, so a variable that had to be both comparable and appendable needed a
--   fourth constructor, `CompAppend`, naming that pair — and unification had a
--   4×4 table computing the meet. A set makes the pair `{Ord, Appendable}` and
--   the meet an ordinary union, so `CompAppend` deletes here rather than
--   waiting for `++` to go with D13. D112 has it deleting alongside
--   `Appendable`; it turns out to have been a fact about the representation
--   rather than about `++`.
--
-- * __Membership is a table, not a case in the unifier.__ `classes.md` §1.2
--   keeps `Num`, `Integral`, `Fractional` and `Bits` closed precisely so that
--   membership can be looked up, and §2.5 sanctions a privileged list for
--   `Ord` in the interim, which is what `admitsAtom` is.
--
-- `Ord` leaves this module when verb 3 builds an instance environment, and
-- `Appendable` leaves when D13 drops `++`. `Num` stays, and grows D2's other
-- three integer types.
module Type.Class
  ( Class (..),
    Classes,
    singleton,
    union,
    fromName,
    fromList,
    toList,
    entailedBy,
    inhabited,
    admitsAtom,
    arrayObligations,
  )
where

import Data.Name qualified as Name
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName

-- CLASSES

-- | Written `Class.Num`, `Class.Ord`, `Class.Appendable` at every use site,
-- which is why the constructors may share their names with Haskell's classes
-- without either being in doubt.
data Class
  = Num
  | Ord
  | Appendable
  deriving (Eq, Prelude.Ord, Show)

-- | The classes a variable has to satisfy. Never empty: a variable with no
-- class is a `FlexVar`, which is a different `Content` constructor.
newtype Classes = Classes (Set.Set Class)
  deriving (Eq)

singleton :: Class -> Classes
singleton c =
  Classes (Set.singleton c)

toList :: Classes -> [Class]
toList (Classes cs) =
  Set.toList cs

-- | `Nothing` for the empty list: a variable with no class is a `FlexVar`.
fromList :: [Class] -> Maybe Classes
fromList cs =
  case cs of
    [] ->
      Nothing
    _ ->
      Just (reduce (Set.fromList cs))

-- | Everything both sides demand, with anything implied by something else
-- dropped.
--
-- The reduction is what keeps the error layer's vocabulary intact: `Num`
-- entails `Ord`, so a variable that is both is written `number` and not
-- `number and comparable`, exactly as the old meet table wrote it.
union :: Classes -> Classes -> Classes
union (Classes a) (Classes b) =
  reduce (Set.union a b)

reduce :: Set.Set Class -> Classes
reduce cs =
  Classes (Set.filter (\c -> not (any (\other -> other /= c && entails other c) (Set.toList cs))) cs)

-- | A type variable whose name is one of Gren's three magic ones.
--
-- This is the bridge that lets verb 2 land without verb 7: `number` still
-- means `Num` here, so `core`'s 246 magic signatures go on compiling while the
-- representation underneath them changes. It is deleted when `core` is written
-- against real constraints (D115, as amended by D120).
fromName :: Name.Name -> Maybe Classes
fromName name
  | Name.isNumberType name = Just (singleton Num)
  | Name.isComparableType name = Just (singleton Ord)
  | Name.isAppendableType name = Just (singleton Appendable)
  | Name.isCompappendType name = Just (Classes (Set.fromList [Ord, Appendable]))
  | otherwise = Nothing

-- ENTAILMENT

-- | Whether every type in the first class is also in the second.
--
-- Not a superclass relation — `classes.md` §1.3 has none among the open
-- classes — but a containment fact about the tables below: `Num` is `Int` and
-- `Float`, both of which `Ord` admits. It is stated separately from those
-- tables because it has to be re-derived when they change, which D2 is about
-- to do.
entails :: Class -> Class -> Bool
entails a b =
  a == b || (a == Num && b == Ord)

-- | Whether a rigid variable constrained by `have` satisfies a demand for
-- `want`. A rigid `number` meets a demand for `comparable`; a rigid
-- `appendable` does not, because an `Array` of something uncomparable is
-- appendable.
entailedBy :: Classes -> Classes -> Bool
entailedBy have want =
  all (\w -> any (\h -> entails h w) (toList have)) (toList want)

-- | Whether any type at all satisfies every class in the set.
--
-- The old enum answered this by not existing: there was no constructor for
-- `Number` and `Appendable` together, so `unifyFlexSuper` returned a mismatch
-- on the spot. A set can hold the pair, so the check has to be made
-- deliberately, and at the same moment — a variable that can never be
-- satisfied is an error where it is created, not where it is finally used.
--
-- Decidable because the universe is the privileged list: `Int`, `Float`,
-- `String`, `Char` and `Array`.
inhabited :: Classes -> Bool
inhabited classes =
  let cs = toList classes
      atom home name = all (\c -> admitsAtom c home name) cs
   in atom ModuleName.basics Name.int
        || atom ModuleName.basics Name.float
        || atom ModuleName.string Name.string
        || atom ModuleName.char Name.char
        || all (\c -> arrayObligations c /= Nothing) cs

-- MEMBERSHIP

-- | Whether a type with no arguments belongs to a class.
admitsAtom :: Class -> ModuleName.Canonical -> Name.Name -> Bool
admitsAtom c home name =
  case c of
    Num ->
      isInt home name || isFloat home name
    Ord ->
      isInt home name || isFloat home name || isString home name || isChar home name
    Appendable ->
      isString home name

-- | Whether `Array a` belongs to a class, and what that costs its element.
--
-- `Nothing` is "no `Array` is in this class". `Just cs` is "every `Array` is,
-- provided its element satisfies `cs`" — which for `Ord` is `Ord` again, and
-- is the whole of the recursion the old `unifyComparableRecursive` did. The
-- result is a list rather than a `Classes` because "no obligation" is a real
-- answer and `Classes` is never empty.
arrayObligations :: Class -> Maybe [Class]
arrayObligations c =
  case c of
    Num ->
      Nothing
    Ord ->
      Just [Ord]
    Appendable ->
      Just []

isInt :: ModuleName.Canonical -> Name.Name -> Bool
isInt home name =
  home == ModuleName.basics && name == Name.int

isFloat :: ModuleName.Canonical -> Name.Name -> Bool
isFloat home name =
  home == ModuleName.basics && name == Name.float

isString :: ModuleName.Canonical -> Name.Name -> Bool
isString home name =
  home == ModuleName.string && name == Name.string

isChar :: ModuleName.Canonical -> Name.Name -> Bool
isChar home name =
  home == ModuleName.char && name == Name.char
