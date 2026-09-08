{-# LANGUAGE OverloadedStrings #-}

module Canonicalize.DeriveSpec where

import AST.Canonical qualified as Can
import Data.Map qualified as Map
import Data.Name qualified as Name
import Reporting.Annotation qualified as A
import Test.Hspec

-- | Which types `@derive` is for (`classes.md` §2.5).
--
-- Abstractness is a fact about the export list and nothing else, which is why
-- §G16.1 could not make this judgement before the exports were canonicalized
-- and why it can now.
spec :: Spec
spec = do
  describe "Abstractness" $ do
    it "a type exposed without its constructors is abstract" $
      Can.isAbstract (exports [("UserId", Can.ExportUnionClosed)]) "UserId" `shouldBe` True

    it "a type exposed with its constructors is transparent" $
      Can.isAbstract (exports [("UserId", Can.ExportUnionOpen)]) "UserId" `shouldBe` False

    it "a type the module does not expose at all is transparent" $
      -- Structure is the meaning when structure is public, and a private
      -- type's structure is public to everyone who can name it — which is the
      -- module that declares it and nobody else. So there is nothing for
      -- `@derive` to add and asking is the redundancy §8.1 calls it.
      Can.isAbstract (exports [("Other", Can.ExportUnionClosed)]) "UserId" `shouldBe` False

    it "`exposing (..)` exposes the constructors too, so nothing is abstract" $
      Can.isAbstract (Can.ExportEverything here) "UserId" `shouldBe` False

exports :: [(Name.Name, Can.Export)] -> Can.Exports
exports entries =
  Can.Export (Map.fromList [(name, A.At here export) | (name, export) <- entries])

here :: A.Region
here =
  A.Region (A.Position 1 1) (A.Position 1 2)
