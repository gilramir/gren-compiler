{-# LANGUAGE OverloadedStrings #-}

module Parse.PrimSpec where

import AST.Source qualified as Src
import Data.ByteString.UTF8 qualified as Utf8
import Data.Name qualified as Name
import Helpers.Instances ()
import Parse.Declaration (Decl (..), declaration)
import Parse.Primitives qualified as P
import Reporting.Annotation qualified as A
import Test.Hspec (Spec, describe, it, shouldBe)

-- | @\@prim("i32_add")@, the second attribute the language has (`core.md` C13).
--
-- The corpus can hold only one half of this. `@prim` is refused outside
-- `gren/core` and every corpus case is third-party, so `reject/prim-outside-core`
-- is the only case that can name one — which leaves the /shape/ of a primitive
-- declaration with nowhere else to be tested.
spec :: Spec
spec = do
  describe "@prim" $ do
    it "an annotation with no equation is a value" $
      declKind "@prim(\"i32_add\")\naddInt : Int -> Int -> Int\n"
        `shouldBe` Right (APrim "addInt" "i32_add")

    it "the name is whatever the string says; the table checks it later" $
      declKind "@prim(\"nonsense\")\nx : Int\n"
        `shouldBe` Right (APrim "x" "nonsense")

    it "a doc comment goes above the attribute" $
      declKind "{-| Add.\n-}\n@prim(\"i32_add\")\naddInt : Int -> Int -> Int\n"
        `shouldBe` Right (APrim "addInt" "i32_add")

    it "spaces inside the parentheses are allowed, as `@derive` allows them" $
      declKind "@prim( \"i32_add\" )\naddInt : Int -> Int -> Int\n"
        `shouldBe` Right (APrim "addInt" "i32_add")

    it "a bare word is not a primitive name" $
      isError (declKind "@prim(i32_add)\naddInt : Int -> Int\n") `shouldBe` True

    it "the declaration must start a fresh line" $
      isError (declKind "@prim(\"i32_add\") addInt : Int -> Int\n") `shouldBe` True

    it "an equation under it is not a primitive declaration" $
      isError (declKind "@prim(\"i32_add\")\naddInt : Int -> Int\naddInt =\n    1\n")
        `shouldBe` True

    it "a constraint is not something a primitive can carry" $
      -- Not a type error found later: `Type.expression` is what reads the
      -- annotation, so a context is not a sentence the grammar has here.
      isError (declKind "@prim(\"i32_add\")\nadd : Num a => a -> a -> a\n") `shouldBe` True

    it "on a custom type is refused, the way `@derive` on a value is" $
      isError (declKind "@prim(\"i32_add\")\ntype UserId\n    = UserId Int\n") `shouldBe` True

    it "`@derive` still parses beside it" $
      declKind "@derive(Eq)\ntype UserId\n    = UserId Int\n"
        `shouldBe` Right (AUnion "UserId" ["Eq"])

    it "a third attribute name is still unknown" $
      isError (declKind "@extern\nx : Int\n") `shouldBe` True

data Kind
  = APrim String String
  | AUnion String [String]
  | AValue String
  | Other
  deriving (Show, Eq)

isError :: Either e a -> Bool
isError result =
  case result of
    Left _ -> True
    Right _ -> False

declKind :: String -> Either (P.Row, P.Col) Kind
declKind str =
  case P.fromByteString
    (P.specialize (\_ row col -> (row, col)) declaration)
    (\row col -> (row, col))
    (Utf8.fromString str) of
    Left err ->
      Left err
    Right ((decl, _), _) ->
      Right $
        case decl of
          Value _ (A.At _ (Src.Value (A.At _ name) [] (A.At _ (Src.Prim primName)) _ _)) ->
            APrim (Name.toChars name) (located primName)
          Value _ (A.At _ (Src.Value (A.At _ name) _ _ _ _)) ->
            AValue (Name.toChars name)
          Union _ (A.At _ (Src.Union (A.At _ name) _ _ derives _)) ->
            AUnion (Name.toChars name) (map located derives)
          _ ->
            Other

located :: A.Located Name.Name -> String
located (A.At _ name) =
  Name.toChars name
