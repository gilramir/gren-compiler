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
--   membership can be looked up, which is what `admitsAtom` is.
--
-- `Ord` __has left__: `core` declares it and `Basics.compare` is its method, so
-- membership is an instance lookup the elaborator does and not a table here
-- (`docs/m1b-classes.md` §G29). `Appendable` leaves when D13 drops `++`. `Num`
-- stays until `core` declares it too, and grows D2's other three integer types.
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
    defaultsTo,
    admitsAtom,
    arrayObligations,
  )
where

import Data.Name qualified as Name
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName

-- CLASSES

-- | Written `Class.Num`, `Class.Appendable` at every use site,
-- which is why the constructors may share their names with Haskell's classes
-- without either being in doubt.
data Class
  = Num
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
-- The reduction kept the error layer's vocabulary intact while `Num` entailed
-- `Ord`: a variable that was both was written `number` rather than
-- `number and comparable`. Nothing entails anything today; it stays because
-- D2's `Integral` and `Fractional` do.
union :: Classes -> Classes -> Classes
union (Classes a) (Classes b) =
  reduce (Set.union a b)

reduce :: Set.Set Class -> Classes
reduce cs =
  Classes (Set.filter (\c -> not (any (\other -> other /= c && entails other c) (Set.toList cs))) cs)

-- | A type variable whose name is one of Gren's remaining magic ones.
--
-- This is the bridge that let verb 2 land without verb 7 (D115, as amended by
-- D120): a name still means a class here, so a signature nobody has rewritten
-- goes on compiling while the representation underneath it changes. Half of it
-- is gone -- `comparable` and `compappend` are ordinary variable names now that
-- `core` declares `Ord` (§G29) -- and the rest goes with `Num` and D13.
fromName :: Name.Name -> Maybe Classes
fromName name
  | Name.isNumberType name = Just (singleton Num)
  | Name.isAppendableType name = Just (singleton Appendable)
  | otherwise = Nothing

-- ENTAILMENT

-- | Whether every type in the first class is also in the second.
--
-- Not a superclass relation — `classes.md` §1.3 has none among the open
-- classes — but a containment fact about the tables below. It said `Num`
-- entails `Ord` while both were the unifier's; with `Ord` declared in `core`
-- the two live in different mechanisms and there is nothing left to contain,
-- so this is equality until D2 adds `Integral` and `Fractional`.
entails :: Class -> Class -> Bool
entails a b =
  a == b

-- | Whether a rigid variable constrained by `have` satisfies a demand for
-- `want`.
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

-- DEFAULTING

-- | What an /ambiguous/ variable constrained by these classes becomes —
-- `classes.md` §0, the rule that closes a numeric variable nothing else will.
--
-- §0 states it as a case analysis: @Float@ if @Fractional@ is among the
-- constraints, @Int@ otherwise. It is written here as an __ordered candidate
-- list__ checked against 'admitsAtom', which gives the same answers and says
-- something §0's phrasing does not:
--
--   * The defaulting rule and the unifier read __one__ table. "Does the default
--     satisfy the constraints" is not a second statement of what is in each
--     class, so D2's four integer types cannot be added to 'admitsAtom' and
--     forgotten here.
--   * §0's @Fractional@ clause falls out rather than being written. @Int@ is
--     first and @Fractional@ will not admit it, so a @Fractional@ variable
--     lands on @Float@ the day that class exists, with no edit here.
--   * A variable no candidate admits is not defaulted. §0 calls
--     @{Fractional, Integral}@ a type error rather than an ambiguity, and it
--     already is one: 'inhabited' refuses that pair where the variable is
--     created, which is earlier and names a better place.
--
-- @Appendable@ is deliberately not defaultable — no candidate admits it — which
-- is §0's list of defaultable classes read off the table instead of restated.
-- It leaves with D13.
defaultsTo :: Classes -> Maybe (ModuleName.Canonical, Name.Name)
defaultsTo classes =
  let admits (home, name) = all (\c -> admitsAtom c home name) (toList classes)
   in case filter admits candidates of
        candidate : _ -> Just candidate
        [] -> Nothing

-- | The whole of §0's candidate set: fixed by the compiler, in this order, with
-- no user-facing declaration (§0.2).
candidates :: [(ModuleName.Canonical, Name.Name)]
candidates =
  [ (ModuleName.basics, Name.int),
    (ModuleName.basics, Name.float)
  ]

-- MEMBERSHIP

-- | Whether a type with no arguments belongs to a class.
admitsAtom :: Class -> ModuleName.Canonical -> Name.Name -> Bool
admitsAtom c home name =
  case c of
    Num ->
      isInt home name || isFloat home name
    Appendable ->
      isString home name

-- | Whether `Array a` belongs to a class, and what that costs its element.
--
-- `Nothing` is "no `Array` is in this class". `Just cs` is "every `Array` is,
-- provided its element satisfies `cs`". The recursive case that made this
-- interesting was `Ord`, and it is an ordinary recursive instance in `core`
-- now — `instance Ord a => Ord (Array a)`, which is what
-- `unifyComparableRecursive` was a hardcoding of.
arrayObligations :: Class -> Maybe [Class]
arrayObligations c =
  case c of
    Num ->
      Nothing
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
