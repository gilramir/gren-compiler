{-# LANGUAGE OverloadedStrings #-}

-- | Lowering canonical types to Core (@docs/core.md@ §C2, §C3).
--
-- Three properties, each of which a backend or a golden test depends on:
-- functions are n-ary and maximally collapsed, aliases are gone, and record
-- fields are alphabetical regardless of how they were written.
module Core.LowerTypeSpec where

import AST.Canonical qualified as Can
import Core.AST qualified as Core
import Core.Lower.Type (lowerAnnotation, lowerClass, lowerType, lowerUnion)
import Data.Index qualified as Index
import Data.Map qualified as Map
import Data.Name qualified as Name
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Test.Hspec

spec :: Spec
spec = do
  describe "functions" $ do
    it "collapses an arrow chain into one argument list" $
      lowerType (Can.TLambda intT (Can.TLambda floatT stringT))
        `shouldBe` Core.TFun [core intT, core floatT] (core stringT)

    it "never leaves a function as a function's result" $
      -- The collapse has to be maximal, not one level deep: a `TFun` whose
      -- result is another `TFun` would mean two Core types for one Gren type,
      -- and equality on the nose is what the golden test and cross-frontend
      -- agreement rest on.
      let chain = Can.TLambda intT (Can.TLambda floatT (Can.TLambda stringT intT))
       in case lowerType chain of
            Core.TFun args result -> do
              length args `shouldBe` 3
              result `shouldBe` Core.TCon (qual "Int") []
            other -> expectationFailure ("expected a function, got " ++ show other)

    it "keeps a function argument grouped" $
      -- The one grouping that *is* writable, and it must survive: the argument
      -- is a function, not two more parameters.
      lowerType (Can.TLambda (Can.TLambda intT floatT) stringT)
        `shouldBe` Core.TFun [Core.TFun [core intT] (core floatT)] (core stringT)

    it "leaves a non-function alone" $
      lowerType intT `shouldBe` Core.TCon (qual "Int") []

  describe "aliases" $ do
    it "expands a filled alias" $
      lowerType (Can.TAlias home "Meters" [] (Can.Filled intT))
        `shouldBe` core intT

    it "expands a holey alias, substituting its arguments" $
      lowerType
        (Can.TAlias home "Pair" [("a", intT)] (Can.Holey (Can.TLambda (Can.TVar "a") (Can.TVar "a"))))
        `shouldBe` Core.TFun [core intT] (core intT)

    it "expands an alias nested inside another type" $
      lowerType (Can.TType home "Array" [Can.TAlias home "Meters" [] (Can.Filled intT)])
        `shouldBe` Core.TCon (qual "Array") [core intT]

  describe "records" $ do
    it "orders fields alphabetically, not by source order" $
      -- The `Word16` Canonical carries is the order the fields were written in.
      -- Two modules writing the same record type in a different order have the
      -- same type, so they must lower to the same Core.
      let written = Can.TRecord (Map.fromList [("b", field 0 intT), ("a", field 1 stringT)]) Nothing
       in lowerType written
            `shouldBe` Core.TRecord [("a", core stringT), ("b", core intT)] Nothing

    it "keeps a row variable" $
      lowerType (Can.TRecord (Map.fromList [("x", field 0 intT)]) (Just "r"))
        `shouldBe` Core.TRecord [("x", core intT)] (Just "r")

    it "lowers an empty record" $
      lowerType (Can.TRecord Map.empty Nothing)
        `shouldBe` Core.TRecord [] Nothing

  describe "annotations" $ do
    it "wraps a polymorphic type in a forall" $
      lowerAnnotation (Can.Forall (Map.fromList [("a", [])]) (Can.TVar "a"))
        `shouldBe` Core.TForall ["a"] [] (Core.TVar "a")

    it "leaves a monomorphic type unwrapped" $
      -- A `forall` with nothing to quantify is noise in a dump and a wasted
      -- node in the wire format.
      lowerAnnotation (Can.Forall Map.empty intT) `shouldBe` core intT

    it "records no constraint for a magic type variable" $
      -- `number` still arrives here as a type variable whose name happens to
      -- be special. `Type.Class.fromName` is what reads it, and it goes on
      -- doing so until `core` declares the classes; turning the name into a
      -- class constraint here would be inventing a reference to something
      -- nothing declares.
      lowerAnnotation (Can.Forall (Map.fromList [("number", [])]) (Can.TVar "number"))
        `shouldBe` Core.TForall ["number"] [] (Core.TVar "number")

    it "carries a constraint the annotation was given" $
      -- The shape D111 asks for, exercised ahead of anything that produces
      -- one: the payload is the constraint list, and `TForall` already had
      -- somewhere to put it.
      lowerAnnotation
        ( Can.Forall
            (Map.fromList [("a", [Can.Class ModuleName.basics "Eq"])])
            (Can.TVar "a")
        )
        `shouldBe` Core.TForall
          ["a"]
          [Core.CClass (Core.QualName ModuleName.basics "Eq") (Core.TVar "a")]
          (Core.TVar "a")

    it "orders constraints by variable, then by how they were written" $
      -- Two compilations of the same source have to emit the same bytes
      -- (`docs/core.md` C2), and a `Map` is only ascending if it is asked to
      -- be.
      lowerAnnotation
        ( Can.Forall
            ( Map.fromList
                [ ("b", [Can.Class ModuleName.basics "Ord"]),
                  ("a", [Can.Class ModuleName.basics "Eq", Can.Class ModuleName.basics "Inspect"])
                ]
            )
            (Can.TLambda (Can.TVar "a") (Can.TVar "b"))
        )
        `shouldBe` Core.TForall
          ["a", "b"]
          [ Core.CClass (Core.QualName ModuleName.basics "Eq") (Core.TVar "a"),
            Core.CClass (Core.QualName ModuleName.basics "Inspect") (Core.TVar "a"),
            Core.CClass (Core.QualName ModuleName.basics "Ord") (Core.TVar "b")
          ]
          (Core.TFun [Core.TVar "a"] (Core.TVar "b"))

  describe "classes" $ do
    it "publishes each method with the class's own constraint on it" $
      -- §G19.1: `class Sizey a where size : a -> Int` publishes
      -- `size : Sizey a => a -> Int`, and the class that constraint names is
      -- the one being declared. `Canonicalize.Environment.Local` is what puts
      -- it on; this is the shape it has to arrive in.
      lowerClass
        home
        "Sizey"
        ( Can.ClassDecl
            "a"
            (Map.fromList [("size", sizey "a" (Can.TLambda (Can.TVar "a") intT))])
        )
        `shouldBe` Core.ClassDecl
          { Core._classNameC = qual "Sizey",
            Core._classParam = "a",
            Core._classOpenness = Core.Open,
            Core._classMethods =
              [ ( "size",
                  Core.TForall
                    ["a"]
                    [Core.CClass (qual "Sizey") (Core.TVar "a")]
                    (Core.TFun [Core.TVar "a"] (core intT))
                )
              ]
          }

    it "orders the methods alphabetically, not by how they were written" $
      -- C2's determinism, met the way record fields meet it: `Can.ClassDecl`
      -- keeps a `Map`, so two frontends agree without agreeing on a traversal.
      map
        fst
        ( Core._classMethods
            ( lowerClass
                home
                "Sizey"
                ( Can.ClassDecl
                    "a"
                    ( Map.fromList
                        [ ("size", sizey "a" (Can.TLambda (Can.TVar "a") intT)),
                          ("isEmpty", sizey "a" (Can.TLambda (Can.TVar "a") intT))
                        ]
                    )
                )
            )
        )
        `shouldBe` ["isEmpty", "size"]

  describe "custom types" $ do
    it "carries the constructor tags" $
      let union =
            Can.Union
              ["a"]
              [ Can.Ctor "Nothing" Index.first 0 [],
                Can.Ctor "Just" Index.second 1 [Can.TVar "a"]
              ]
              2
              Can.Normal
       in lowerUnion home "Maybe" union
            `shouldBe` Core.DataDecl
              { Core._dataName = qual "Maybe",
                Core._dataParams = ["a"],
                Core._dataTransparency = Core.Transparent,
                Core._dataCtors =
                  [ Core.Ctor (qual "Nothing") 0 [],
                    Core.Ctor (qual "Just") 1 [Core.TVar "a"]
                  ],
                Core._dataClasses = []
              }

-- FIXTURES

home :: ModuleName.Canonical
home = ModuleName.Canonical Pkg.core "Maybe"

qual :: Name.Name -> Core.QualName
qual = Core.QualName home

intT :: Can.Type
intT = Can.TType home "Int" []

floatT :: Can.Type
floatT = Can.TType home "Float" []

stringT :: Can.Type
stringT = Can.TType home "String" []

field :: Int -> Can.Type -> Can.FieldType
field i t = Can.FieldType (fromIntegral i) t

core :: Can.Type -> Core.Type
core = lowerType

-- | A method's published signature: the class parameter constrained by
-- `Sizey`, which is what a class declaration puts on each of its methods.
sizey :: Name.Name -> Can.Type -> Can.Annotation
sizey param tipe =
  Can.Forall (Map.fromList [(param, [Can.Class home "Sizey"])]) tipe
