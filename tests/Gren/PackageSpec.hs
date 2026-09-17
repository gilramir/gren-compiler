{-# LANGUAGE OverloadedStrings #-}

module Gren.PackageSpec (spec) where

import Data.ByteString.Builder qualified as B
import Data.ByteString.Lazy.Char8 qualified as LBS
import Data.Utf8 qualified as Utf8
import Generate.JavaScript.Name qualified as JsName
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Json.Decode qualified as D
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec = do
  describe "Package identifiers (packaging.md K7, D295)" $ do
    it "accepts core and URL paths" $
      map Pkg.isValid
        [ "core",
          "github.com/geng-language/node",
          "github.com/geng-language/platforms/browser",
          "gitlab.com/acme/tooling/argparse",
          "git.corp.example/team/pkg.git/sub",
          "example.com/Acme/Widget_2"
        ]
        `shouldBe` replicate 6 True

    it "refuses Gren's author/project, a bare host and malformed paths" $
      map Pkg.isValid
        [ "gren-lang/core",
          "app",
          "kernel",
          "github.com",
          "github.com/",
          "github.com/x/",
          "github.com//x",
          "github.com/./x",
          "github.com/../x",
          "GitHub.com/x",
          "https://github.com/x",
          "github.com/x~y",
          ".github.com/x",
          ""
        ]
        `shouldBe` replicate 14 False

    it "decodes an identifier from JSON and refuses a two-part name" $ do
      fmap Pkg.toChars (D.fromByteString Pkg.decoder "\"github.com/gilramir/gren-toml\"")
        `shouldBeRight` "github.com/gilramir/gren-toml"
      either (const True) (const False) (D.fromByteString Pkg.decoder "\"gren-lang/core\"")
        `shouldBe` True

  describe "Generated names (D296)" $ do
    it "escapes each path element" $
      Pkg.escapedSegments (named "github.com/geng-language/my_pkg")
        `shouldBe` ["github_dcom", "geng_hlanguage", "my_upkg"]

    it "writes core and a hosted package the way D296 shows" $ do
      js "core" "Basics" "add" `shouldBe` "$core$$Basics$add"
      js "github.com/x/y-z" "Basics" "add" `shouldBe` "$github_dcom$x$y_hz$$Basics$add"

    it "does not let a package path element pass for a module part" $
      js "example.com/x/Y" "Basics" "f"
        `shouldNotEqual` js "example.com/x" "Y.Basics" "f"
  where
    named chars =
      case D.fromByteString Pkg.decoder (LBS.toStrict (LBS.pack (show chars))) of
        Right name -> name
        Left _ -> error ("not an identifier: " ++ chars)

    js package modul name =
      LBS.unpack $
        B.toLazyByteString $
          JsName.toBuilder $
            JsName.fromGlobal (ModuleName.Canonical (named package) (Utf8.fromChars modul)) (Utf8.fromChars name)

    shouldBeRight result expected =
      case result of
        Right got -> got `shouldBe` expected
        Left _ -> error "expected the identifier to decode"

    shouldNotEqual a b =
      (a == b) `shouldBe` False
