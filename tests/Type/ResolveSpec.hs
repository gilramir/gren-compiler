{-# LANGUAGE OverloadedStrings #-}

module Type.ResolveSpec where

import AST.Canonical qualified as Can
import Data.Map qualified as Map
import Data.Name qualified as Name
import Gren.ModuleName qualified as ModuleName
import Reporting.Annotation qualified as A
import Reporting.Error.Instance qualified as E
import Test.Hspec
import Type.Resolve qualified as Resolve

-- | Building the witness for one constraint (`docs/m1b-classes.md` §G23, §G26).
--
-- The whole of resolution is here. The traversal around it only decides which
-- constraints to ask about; what an answer *is* — an instance, an instance
-- applied to the witnesses its own context needs, or the parameter the
-- enclosing definition was handed — is this function.
spec :: Spec
spec = do
  describe "An instance" $ do
    it "a concrete type picks the instance declared for it" $
      witness (Can.TType ModuleName.basics "Int" [])
        `shouldBe` Right (Instance "$i$Sizey$Int" [])

    it "an alias resolves as the type it stands for" $
      -- An alias is refused as an instance head (§G22.1), so the instance is
      -- keyed by the constructor underneath and the use site is read the same
      -- way.
      witness
        ( Can.TAlias
            ModuleName.basics
            "Count"
            []
            (Can.Filled (Can.TType ModuleName.basics "Int" []))
        )
        `shouldBe` Right (Instance "$i$Sizey$Int" [])

    it "a type with no instance is a fact about the program" $
      witness (Can.TType ModuleName.string "String" []) `shouldBe` Left NoInstance

    it "so is a function type, which no head can ever be" $
      witness (Can.TLambda unitT unitT) `shouldBe` Left NoInstance

  describe "An instance with a context" $ do
    it "is applied to a witness for each constraint it carries" $
      -- @instance Sizey a => Sizey (Array a)@ at @Array Int@ is the recursive
      -- case §G23.6 left open: the witness is the array instance's table
      -- applied to the integer instance's.
      witness (arrayOf (Can.TType ModuleName.basics "Int" []))
        `shouldBe` Right (Instance "$i$Sizey$Array" [Instance "$i$Sizey$Int" []])

    it "nests as deeply as the type does" $
      witness (arrayOf (arrayOf (Can.TType ModuleName.basics "Int" [])))
        `shouldBe` Right
          ( Instance
              "$i$Sizey$Array"
              [Instance "$i$Sizey$Array" [Instance "$i$Sizey$Int" []]]
          )

    it "does not answer for an argument its context cannot be discharged at" $
      -- Measured in §G23.6 as answering anyway, because the key is the head's
      -- constructor and nothing looked at the context. This is what closes it.
      witness (arrayOf (Can.TType ModuleName.string "String" []))
        `shouldBe` Left NoInstance

  describe "A constrained variable" $ do
    it "takes the witness the enclosing definition was handed" $
      witnessWith (Map.singleton (sizey, "a") "$w0") (Can.TVar "a")
        `shouldBe` Right (Param "$w0")

    it "is an error when nothing constrains it" $
      -- Not "this compiler cannot", which is what it meant before verb 6, but
      -- "the signature does not say": the fix is in the source.
      witness (Can.TVar "a") `shouldBe` Left NotConstrained

    it "is matched by class as well as by name" $
      witnessWith (Map.singleton (Can.Class ModuleName.basics "Other", "a") "$w0") (Can.TVar "a")
        `shouldBe` Left NotConstrained

-- FIXTURES

sizey :: Can.Class
sizey = Can.Class ModuleName.basics "Sizey"

arrayHome :: ModuleName.Canonical
arrayHome = ModuleName.Canonical (ModuleName._package ModuleName.basics) "Array"

unitT :: Can.Type
unitT = Can.TRecord Map.empty Nothing

arrayOf :: Can.Type -> Can.Type
arrayOf item = Can.TType arrayHome "Array" [item]

-- | @instance Sizey Int@, as `Canonicalize.Instance` would leave it.
plain :: ModuleName.Canonical -> Name.Name -> Name.Name -> Can.InstanceHead
plain conHome conName name =
  Can.InstanceHead
    { Can._ih_home = ModuleName.basics,
      Can._ih_class = sizey,
      Can._ih_con = conHome,
      Can._ih_conName = conName,
      Can._ih_args = [],
      Can._ih_witness = name,
      Can._ih_context = Map.empty,
      Can._ih_methods = Map.singleton "size" (Can.TType ModuleName.basics "Int" [])
    }

-- | @instance Sizey a => Sizey (Array a)@.
recursive :: Can.InstanceHead
recursive =
  (plain arrayHome "Array" "$i$Sizey$Array")
    { Can._ih_args = [Can.TVar "a"],
      Can._ih_context = Map.singleton "a" [sizey]
    }

environment :: Resolve.Env
environment =
  Resolve.Env
    (Map.fromList [(Can.instanceKey h, h) | h <- [plain ModuleName.basics "Int" "$i$Sizey$Int", recursive]])
    Map.empty
    Map.empty

-- | A witness, with only what this file is asking about: an instance's name and
-- what it was applied to, or a parameter's name. The types and modules on the
-- real thing are the lowering's business.
data Shape
  = Instance Name.Name [Shape]
  | Param Name.Name
  deriving (Eq, Show)

-- | Which of the two ways there is no answer, since the error itself carries a
-- region and a type that say nothing this file is asking about.
data Outcome
  = NoInstance
  | NotConstrained
  deriving (Eq, Show)

witness :: Can.Type -> Either Outcome Shape
witness = witnessWith Map.empty

witnessWith :: Resolve.Bound -> Can.Type -> Either Outcome Shape
witnessWith bound tipe =
  case Resolve.witnessFor environment bound region (E.ForMethod "size") [] sizey tipe of
    Right w -> Right (shapeOf w)
    Left (E.NoInstance {}) -> Left NoInstance
    Left (E.NotConstrained {}) -> Left NotConstrained
    Left (E.MethodContext {}) -> Left NotConstrained

shapeOf :: Resolve.Witness -> Shape
shapeOf w =
  case w of
    Resolve.FromParam name _ -> Param name
    Resolve.FromInstance _ name args _ -> Instance name (map shapeOf args)

region :: A.Region
region = A.Region (A.Position 1 1) (A.Position 1 5)
