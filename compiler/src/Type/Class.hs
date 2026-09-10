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
-- (`docs/m1b-classes.md` §G29). What is left is `classes.md` §1.2's __closed__
-- classes, and `core` declares those too now (D135, §G32) — the difference is
-- what the declaration /means/. An open class means its instances; a closed one
-- means the tables below, so `Basics.Num` is a name this module answers to
-- rather than a name the elaborator resolves.
--
-- `Appendable` __has left__ too, the same way and for the same reason: D138
-- promoted it rather than dropping it with `++`, so `Basics.append` is its
-- method and `String` and `Array a` are ordinary instances (§G34, §G35). What is
-- left here is `classes.md` §1.2's four, and all four are in as of D145
-- (`docs/m1b-int.md` §I12). All four grew D2's other four numeric types at §I8
-- step 4, so the membership table below is now the whole of `classes.md` §1.2.
module Type.Class
  ( Class (..),
    Classes,
    singleton,
    union,
    fromDeclared,
    toDeclared,
    isClosed,
    fromList,
    toList,
    entailedBy,
    inhabited,
    defaultsTo,
    admitsAtom,
    members,
    arrayObligations,
  )
where

import Data.Maybe qualified as Maybe
import Data.Name qualified as Name
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName

-- CLASSES

-- | Written `Class.Num` at every use site, which is why a constructor may
-- share its name with Haskell's class without either being in doubt.
--
-- All four of `classes.md` §1.2's, as of D145. The set machinery around them is
-- what it was built for: `7 // 2 + 1` constrains one variable by `Integral` and
-- `Num` at once, and `1 / 2` by `Fractional` and `Num`.
data Class
  = Num
  | Integral
  | Fractional
  | Bits
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
      Just (Classes (Set.fromList cs))

-- | Everything both sides demand.
--
-- __An ordinary union, with nothing dropped from it__ (D146). There used to be
-- a reduction here that deleted a class another one in the set implied, and it
-- kept the error layer's vocabulary intact while `Num` entailed `Ord`: a
-- variable that was both was written `number` rather than
-- `number and comparable`. It survived §G32 on the promise that D2's `Integral`
-- and `Fractional` would need it, and D145 is where that promise comes due and
-- is refused — see 'entailedBy'. A closed class carries methods and therefore a
-- witness now, so dropping `Num` from @{Num, Integral}@ would drop the witness
-- `+` projects its method out of.
union :: Classes -> Classes -> Classes
union (Classes a) (Classes b) =
  Classes (Set.union a b)

-- | The class a declared name is, when the class is one of `classes.md` §1.2's
-- closed ones.
--
-- __This is what replaced `Class.fromName`__ (D135, §G32). Until verb 7 the
-- bridge into the unifier was a type /variable's/ name: `number` meant `Num`
-- and `appendable` meant `Appendable`, which is what let verb 2 change the
-- representation without rewriting `core` (D115, as amended by D120). Now
-- `Basics` declares both classes and a constraint names one, so this reads a
-- qualified name — and no type-variable name means anything to the compiler any
-- more.
--
-- `Nothing` is an /open/ class, which is the elaborator's: a constraint on one
-- is discharged by finding an instance and passing a witness, and the unifier
-- neither knows nor needs to know about it.
fromDeclared :: ModuleName.Canonical -> Name.Name -> Maybe Class
fromDeclared home name
  | home == ModuleName.basics, name == Name.num = Just Num
  | home == ModuleName.basics, name == Name.integral = Just Integral
  | home == ModuleName.basics, name == Name.fractional = Just Fractional
  | home == ModuleName.bitwise, name == Name.bits = Just Bits
  | otherwise = Nothing

-- | The declared name a class is, which is what an annotation the solver
-- produces has to say (`Type.Type.toAnnotation`).
--
-- The inverse of 'fromDeclared', and total in this direction: every class in
-- the enum is one `core` declares, which is the whole of what D135 changed.
toDeclared :: Class -> (ModuleName.Canonical, Name.Name)
toDeclared c =
  case c of
    Num -> (ModuleName.basics, Name.num)
    Integral -> (ModuleName.basics, Name.integral)
    Fractional -> (ModuleName.basics, Name.fractional)
    Bits -> (ModuleName.bitwise, Name.bits)

-- | Whether a constraint is enforced by unification rather than by a witness.
--
-- D130 states the rule this answers: an open class's constraint leaves the
-- unifier and is enforced by witness resolution; a closed class's stays and is
-- enforced by unification. Everything that builds, binds or applies a witness
-- asks this and skips the ones it says yes to — which is why a closed-class
-- constraint costs a definition no parameter and a call site no argument, and
-- so why `Basics.add` keeps the arity kernel JavaScript calls it at (D132).
-- Takes a home and a name rather than a `Can.Class` so that this module stays
-- a leaf: `AST.Canonical` asks it, in `Can.witnessOrder`.
isClosed :: ModuleName.Canonical -> Name.Name -> Bool
isClosed home name =
  Maybe.isJust (fromDeclared home name)

-- ENTAILMENT

-- | Whether a rigid variable constrained by `have` satisfies a demand for
-- `want`.
--
-- __Containment of the written sets, and no more than that__ (D146). Every type
-- in `Integral` is in `Num`, so a containment fact about 'members' would let an
-- `Integral a =>` signature satisfy a demand for `Num a` — and `classes.md`
-- §1.2 promised exactly that, under "closed classes pay no superclass cost".
-- That sentence was a fact about a closed class having no methods, the same one
-- D144 found under "a closed constraint binds no witness": a `Num a` demand at
-- a rigid `a` needs a `Num` witness, and only a written `Num a` brings one in.
-- So `f : Integral a => a -> a` may not say `x + x`, and a function wanting
-- both writes `(Num a, Integral a) =>` exactly as §1.3 has `(Eq a, Ord a) =>`.
--
-- What is still free is the part §1.2 was really about: membership at a
-- /concrete/ type is 'admitsAtom', a lookup, so `7 // 2 + 1` needs no
-- entailment rule to typecheck and no inference to discharge either constraint.
entailedBy :: Classes -> Classes -> Bool
entailedBy (Classes have) (Classes want) =
  want `Set.isSubsetOf` have

-- | Whether any type at all satisfies every class in the set.
--
-- The old enum answered this by not existing: there was no constructor for
-- `Number` and `Appendable` together, so `unifyFlexSuper` returned a mismatch
-- on the spot. A set can hold the pair, so the check has to be made
-- deliberately, and at the same moment — a variable that can never be
-- satisfied is an error where it is created, not where it is finally used.
--
-- Decidable because the universe is the privileged list: `Int`, `Float`,
-- `String`, `Char` and `Array`. D2's four widths are deliberately not in it and
-- need not be: each one's class set is exactly `Int`'s or exactly `Float`'s, so
-- a set of classes that any of them satisfies is a set one of the two listed
-- types satisfies. A future member with a class set that is neither would have
-- to be added here as well as to 'members'.
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

-- | Every type in a class, which is what "closed" means.
--
-- One list, and 'admitsAtom' is a lookup in it. Two lists is what §G43.3 cost a
-- checkpoint — `Type.Resolve.isStructural` and `Canonicalize.Derive` came apart
-- saying the same thing twice — and D144 gives this one a second reader:
-- `core` writes an instance per member now, and `Canonicalize.Module` checks
-- that list against this one. So the membership table, the unifier, §0's
-- defaulting and `core`'s instances all read one list.
--
-- All six numeric types are in as of §I8 step 4. The three integer classes hold
-- exactly the same four types, which is A11 and A5 read together: every integer
-- type divides, takes a remainder and does bitwise arithmetic, so @Integral@ and
-- @Bits@ have one membership list and @Num@ is that list plus the two floats.
members :: Class -> [(ModuleName.Canonical, Name.Name)]
members c =
  case c of
    Num ->
      [ (ModuleName.basics, Name.int),
        (ModuleName.basics, Name.int64),
        (ModuleName.basics, Name.uint32),
        (ModuleName.basics, Name.uint64),
        (ModuleName.basics, Name.float),
        (ModuleName.basics, Name.float32)
      ]
    Integral ->
      [ (ModuleName.basics, Name.int),
        (ModuleName.basics, Name.int64),
        (ModuleName.basics, Name.uint32),
        (ModuleName.basics, Name.uint64)
      ]
    Fractional ->
      [ (ModuleName.basics, Name.float),
        (ModuleName.basics, Name.float32)
      ]
    Bits ->
      [ (ModuleName.basics, Name.int),
        (ModuleName.basics, Name.int64),
        (ModuleName.basics, Name.uint32),
        (ModuleName.basics, Name.uint64)
      ]

-- | Whether a type with no arguments belongs to a class.
admitsAtom :: Class -> ModuleName.Canonical -> Name.Name -> Bool
admitsAtom c home name =
  (home, name) `elem` members c

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
    Num -> Nothing
    Integral -> Nothing
    Fractional -> Nothing
    Bits -> Nothing
