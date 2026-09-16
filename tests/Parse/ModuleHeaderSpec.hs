{-# LANGUAGE OverloadedStrings #-}

module Parse.ModuleHeaderSpec where

import AST.Source qualified as Src
import Data.ByteString.UTF8 qualified as Utf8
import Data.Name qualified as Name
import Parse.Module qualified as Module
import Reporting.Annotation qualified as A
import Reporting.Error.Syntax qualified as E
import Test.Hspec (Spec, describe, it, shouldBe)

-- | `port module` and `effect module` are refused where the header begins, and
-- `port` is an ordinary name (D279, D280, `m1b-source.md` §SO20). The corpus
-- holds the reports; what it cannot hold is the other half, that a program
-- naming something `port` parses, since no case has a reason to.
spec :: Spec
spec = do
  describe "a removed header" $ do
    it "`port module` is refused at its first word" $
      parse "port module Main exposing (main)\n\nmain =\n    1\n"
        `shouldBe` Refused "PortModuleHeader 1 1"

    it "`effect module` is refused at its first word, before its `where` is read" $
      parse "effect module Task where { command = MyCmd } exposing (Task)\n"
        `shouldBe` Refused "EffectModuleHeader 1 1"

    it "is refused across a line break between the two words" $
      parse "port\nmodule Main exposing (main)\n"
        `shouldBe` Refused "PortModuleHeader 1 1"

  describe "`port` as a name" $ do
    it "is a value a module declares and exposes" $
      parse "module Main exposing (port)\n\nport : Int\nport =\n    8080\n"
        `shouldBe` Parsed ["port"]

    it "is the first declaration of a file with no header" $
      parse "port =\n    8080\n"
        `shouldBe` Parsed ["port"]

    it "is a record field" $
      parse "module Main exposing (main)\n\nmain =\n    { host = \"localhost\", port = 8080 }.port\n"
        `shouldBe` Parsed ["main"]

    it "does not make `ports` or `effects` a header" $
      parse "ports =\n    1\n\neffects =\n    2\n"
        `shouldBe` Parsed ["effects", "ports"]

data Outcome
  = Parsed [String]
  | Refused String
  | Other String
  deriving (Eq, Show)

parse :: String -> Outcome
parse source =
  case Module.fromByteString Module.Application (Utf8.fromString source) of
    Right modul ->
      Parsed (sortedNames [name | (_, A.At _ (Src.Value (A.At _ name) _ _ _ _)) <- Src._values modul])
    Left (E.ParseError err@(E.PortModuleHeader _ _)) ->
      Refused (show err)
    Left (E.ParseError err@(E.EffectModuleHeader _ _)) ->
      Refused (show err)
    Left err ->
      Other (show err)
  where
    sortedNames = foldr insert [] . map Name.toChars
    insert x [] = [x]
    insert x (y : ys) = if x <= y then x : y : ys else y : insert x ys
