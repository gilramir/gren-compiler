{-# LANGUAGE OverloadedStrings #-}

module Gren.DetailsSpec (spec) where

import Data.ByteString.Char8 qualified as BS
import Data.Map qualified as Map
import Data.Name qualified as Name
import Gren.Constraint qualified as Con
import Gren.Details qualified as Details
import Gren.Licenses qualified as Licenses
import Gren.Outline qualified as Outline
import Gren.Package qualified as Pkg
import Gren.Platform qualified as P
import Gren.Version qualified as V
import Json.String qualified as Json
import Test.Hspec (Spec, describe, it, shouldBe, shouldNotBe)

spec :: Spec
spec = do
  describe "A package's artifact fingerprint (D101, D911)" $ do
    let fingerprint exposed platform =
          let outline = Outline.Pkg (Outline.PkgOutline Pkg.core (Json.fromChars "s") Licenses.bsd3 V.one exposed Map.empty Con.defaultGren platform Nothing)
              sources = Map.fromList [(Name.fromChars "A", BS.pack "module A"), (Name.fromChars "B", BS.pack "module B")]
           in Details.packageFingerprints (Map.singleton Pkg.core (Details.Dependency outline sources)) Map.! Pkg.core
        a = Name.fromChars "A"
        b = Name.fromChars "B"

    it "moves when a module is exposed and its sources do not" $
      fingerprint (Outline.ExposedList [a]) P.Common
        `shouldNotBe` fingerprint (Outline.ExposedList [a, b]) P.Common

    it "moves with the platform" $
      fingerprint (Outline.ExposedList [a]) P.Common
        `shouldNotBe` fingerprint (Outline.ExposedList [a]) P.Node

    it "does not move with the exposed modules' order or grouping" $
      fingerprint (Outline.ExposedList [a, b]) P.Common
        `shouldBe` fingerprint (Outline.ExposedDict [(Json.fromChars "Two", [b]), (Json.fromChars "One", [a])]) P.Common
