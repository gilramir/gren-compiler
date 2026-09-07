{-# LANGUAGE OverloadedStrings #-}

module Parse.ClassSpec where

import AST.Source qualified as Src
import Data.ByteString.UTF8 qualified as Utf8
import Data.Name qualified as Name
import Helpers.Instances ()
import Parse.Declaration (Decl (..), declaration)
import Parse.Primitives qualified as P
import Reporting.Annotation qualified as A
import Test.Hspec (Spec, describe, it, shouldBe)

-- | `class Eq a where` — and, just as much, the `class` that is still an
-- ordinary identifier. D117 makes it a contextual keyword, so every one of
-- these has to keep parsing as what it was.
spec :: Spec
spec = do
  describe "Class declarations" $ do
    it "one method" $
      declKind
        "class Inspect a where\n\
        \    inspect : a -> String\n"
        `shouldBe` Right (AClass "Inspect" "a" ["inspect"])

    it "several methods, aligned" $
      declKind
        "class Eq a where\n\
        \    eq : a -> a -> Bool\n\
        \    ne : a -> a -> Bool\n"
        `shouldBe` Right (AClass "Eq" "a" ["eq", "ne"])

    it "a method whose own annotation carries a context" $
      declKind
        "class Sortable a where\n\
        \    sortBy : Ord b => (a -> b) -> a -> a\n"
        `shouldBe` Right (AClass "Sortable" "a" ["sortBy"])

  describe "`class` is still an identifier (D117)" $ do
    it "a value named class" $
      declKind "class : String -> String\nclass name =\n    name\n"
        `shouldBe` Right (AValue "class")

    it "a value named class with no annotation" $
      declKind "class =\n    1\n" `shouldBe` Right (AValue "class")

    it "a value named instance" $
      declKind "instance =\n    1\n" `shouldBe` Right (AValue "instance")

    it "a type whose field is named class" $
      declKind "type alias Attr =\n    { class : String }\n"
        `shouldBe` Right (AnAlias "Attr")

data Kind
  = AClass String String [String]
  | AValue String
  | AnAlias String
  | Other
  deriving (Show, Eq)

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
          Class _ (A.At _ (Src.Class (A.At _ name) (A.At _ var) methods _)) ->
            AClass (Name.toChars name) (Name.toChars var) (map methodName methods)
          Value _ (A.At _ (Src.Value (A.At _ name) _ _ _ _)) ->
            AValue (Name.toChars name)
          Alias _ (A.At _ (Src.Alias (A.At _ name) _ _)) ->
            AnAlias (Name.toChars name)
          _ ->
            Other

methodName :: Src.ClassMethod -> String
methodName (_, A.At _ name, _) =
  Name.toChars name
