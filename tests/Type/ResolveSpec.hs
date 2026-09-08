{-# LANGUAGE OverloadedStrings #-}

module Type.ResolveSpec where

import AST.Canonical qualified as Can
import Data.Map qualified as Map
import Data.Name qualified as Name
import Data.NonEmptyList qualified as NE
import Gren.ModuleName qualified as ModuleName
import Reporting.Annotation qualified as A
import Reporting.Error.Instance qualified as E
import Test.Hspec
import Type.Resolve qualified as Resolve
import Type.Solve qualified as Solve

-- | Picking an instance at a call site (`docs/m1b-classes.md` §G23).
--
-- The whole of resolution is here, because the solver has already reduced the
-- question to "what did the class parameter come out as": a type constructor
-- is a key, and anything else is one of the two ways there is no answer.
spec :: Spec
spec = do
  describe "Resolution" $ do
    it "a concrete type picks the instance declared for it" $
      resolve (Can.TType ModuleName.basics "Int" [])
        `shouldBe` Right (ModuleName.basics, "$i$Sizey$Int$size")

    it "the instance's arguments do not have to match, because the key is the constructor" $
      -- `instance Sizey (Array a)` answers for `Array Int` and for
      -- `Array String` alike: §G22.1 makes (class, head constructor) the whole
      -- of the index, so resolution is a lookup and never a search.
      resolveIn
        [instanceHead arrayHome "Array" "$i$Sizey$Array"]
        (Can.TType arrayHome "Array" [Can.TType ModuleName.basics "Int" []])
        `shouldBe` Right (ModuleName.basics, "$i$Sizey$Array$size")

    it "an alias resolves as the type it stands for" $
      -- An alias is refused as an instance head (§G22.1), so the instance is
      -- keyed by the constructor underneath and the use site has to be read
      -- the same way.
      resolve
        ( Can.TAlias
            ModuleName.basics
            "Count"
            []
            (Can.Filled (Can.TType ModuleName.basics "Int" []))
        )
        `shouldBe` Right (ModuleName.basics, "$i$Sizey$Int$size")

  describe "No answer" $ do
    it "a type with no instance is a fact about the program" $
      resolve (Can.TType ModuleName.string "String" []) `shouldBe` Left NoInstance

    it "so is a function type, which no head can ever be" $
      resolve (Can.TLambda unitT unitT) `shouldBe` Left NoInstance

    it "a type variable is a fact about this compiler, not about the program" $
      -- The call needs the instance passed in rather than picked here, which
      -- is verb 6's. Reported apart from `NoInstance` because the two are
      -- different questions and only one of them is the program's fault.
      resolve (Can.TVar "a") `shouldBe` Left NotResolved

    it "every unresolvable use is reported, not just the first" $
      let uses =
            Map.fromList
              [ (Can.NodeId 1, use (Can.TVar "a")),
                (Can.NodeId 2, use (Can.TType ModuleName.string "String" [])),
                (Can.NodeId 3, use (Can.TType ModuleName.basics "Int" []))
              ]
       in case Resolve.run environment uses of
            Right _ -> expectationFailure "expected two errors" >> return ()
            Left errors -> length (NE.toList errors) `shouldBe` 2

-- FIXTURES

sizey :: Can.Class
sizey = Can.Class ModuleName.basics "Sizey"

arrayHome :: ModuleName.Canonical
arrayHome = ModuleName.Canonical (ModuleName._package ModuleName.basics) "Array"

unitT :: Can.Type
unitT = Can.TRecord Map.empty Nothing

-- | One instance of `Sizey`, as `Canonicalize.Instance` would leave it.
instanceHead :: ModuleName.Canonical -> Name.Name -> Name.Name -> Can.InstanceHead
instanceHead conHome conName witness =
  Can.InstanceHead
    { Can._ih_home = ModuleName.basics,
      Can._ih_class = sizey,
      Can._ih_con = conHome,
      Can._ih_conName = conName,
      Can._ih_args = [],
      Can._ih_witness = witness,
      Can._ih_context = Map.empty
    }

environment :: Map.Map Can.InstanceKey Can.InstanceHead
environment =
  keyed [instanceHead ModuleName.basics "Int" "$i$Sizey$Int"]

keyed :: [Can.InstanceHead] -> Map.Map Can.InstanceKey Can.InstanceHead
keyed heads =
  Map.fromList [(Can.instanceKey h, h) | h <- heads]

use :: Can.Type -> Solve.MethodUse
use param =
  Solve.MethodUse (A.Region (A.Position 1 1) (A.Position 1 5)) sizey "size" param

-- | Which of the two ways there is no answer, since the error itself carries
-- a region and a type that say nothing this file is asking about.
data Outcome
  = NoInstance
  | NotResolved
  deriving (Eq, Show)

resolve :: Can.Type -> Either Outcome (ModuleName.Canonical, Name.Name)
resolve = resolveWith environment

resolveIn :: [Can.InstanceHead] -> Can.Type -> Either Outcome (ModuleName.Canonical, Name.Name)
resolveIn heads = resolveWith (keyed heads)

resolveWith ::
  Map.Map Can.InstanceKey Can.InstanceHead ->
  Can.Type ->
  Either Outcome (ModuleName.Canonical, Name.Name)
resolveWith instances param =
  case Resolve.run instances (Map.singleton (Can.NodeId 1) (use param)) of
    Left (NE.List (E.NoInstance _ _ _ _) _) -> Left NoInstance
    Left (NE.List (E.NotResolved _ _ _ _) _) -> Left NotResolved
    Right answers ->
      case Map.lookup (Can.NodeId 1) answers of
        Just answer -> Right answer
        Nothing -> error "Type.ResolveSpec: the use was neither resolved nor reported"
