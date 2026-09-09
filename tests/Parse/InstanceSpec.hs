{-# LANGUAGE OverloadedStrings #-}

module Parse.InstanceSpec where

import AST.Source qualified as Src
import Data.ByteString.UTF8 qualified as Utf8
import Data.Name qualified as Name
import Helpers.Instances ()
import Parse.Declaration (Decl (..), declaration)
import Parse.Primitives qualified as P
import Reporting.Annotation qualified as A
import Test.Hspec (Spec, describe, it, shouldBe)

-- | `instance Ord Path where` and `@derive(Eq, Ord)` — the other two syntactic
-- additions of verb 1, and where each of them may not go.
spec :: Spec
spec = do
  describe "Instance declarations" $ do
    it "one method" $
      declKind
        "instance Inspect Path where\n\
        \    inspect path =\n\
        \        \"a path\"\n"
        `shouldBe` Right (AnInstance 0 ["inspect"])

    it "a context and several methods" $
      declKind
        "instance Eq a => Eq (Array a) where\n\
        \    eq p q =\n\
        \        True\n\
        \\n\
        \    ne p q =\n\
        \        False\n"
        `shouldBe` Right (AnInstance 1 ["eq", "ne"])

    it "a context of two constraints, which begins with a parenthesis" $
      declKind
        "instance (Eq k, Eq v) => Eq (Dict k v) where\n\
        \    eq p q =\n\
        \        True\n"
        `shouldBe` Right (AnInstance 2 ["eq"])

    it "`instance` is still an identifier (D117)" $
      declKind "instance =\n    1\n" `shouldBe` Right (AValue "instance")

    it "`instance` is still an identifier before a parenthesis too" $
      declKind "instance (Just x) =\n    x\n" `shouldBe` Right (AValue "instance")

  describe "@derive" $ do
    it "on a custom type" $
      declKind "@derive(Eq, Ord, Inspect)\ntype UserId\n    = UserId Int\n"
        `shouldBe` Right (AUnion "UserId" ["Eq", "Ord", "Inspect"])

    it "a custom type without it derives nothing here" $
      declKind "type UserId\n    = UserId Int\n"
        `shouldBe` Right (AUnion "UserId" [])

    it "on a type alias is refused" $
      isError (declKind "@derive(Eq)\ntype alias Attr =\n    { class : String }\n")
        `shouldBe` True

    it "on a value is refused" $
      isError (declKind "@derive(Eq)\nx : Int\nx =\n    1\n") `shouldBe` True

    it "an attribute that is not `derive` is refused" $
      isError (declKind "@extern\ntype UserId\n    = UserId Int\n") `shouldBe` True

data Kind
  = AnInstance Int [String]
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
          Instance _ (A.At _ (Src.Instance maybeContext _ methods _)) ->
            AnInstance (constraintCount maybeContext) (map instanceMethodName methods)
          Union _ (A.At _ (Src.Union (A.At _ name) _ _ derives _)) ->
            AUnion (Name.toChars name) (map located derives)
          Value _ (A.At _ (Src.Value (A.At _ name) _ _ _ _)) ->
            AValue (Name.toChars name)
          _ ->
            Other

-- | How many constraints the head carries, rather than merely whether it has
-- any: a context of two is what `instanceDeclAhead` could not see until it
-- learned to read a whole `Type.context` (`m1b-classes.md` §G41.2), and a
-- count is what says the second one survived the parse.
constraintCount :: Maybe Src.Context -> Int
constraintCount maybeContext =
  case maybeContext of
    Just (Src.Context entries _) -> length entries
    Nothing -> 0

instanceMethodName :: Src.InstanceMethod -> String
instanceMethodName (_, A.At _ (Src.Value name _ _ _ _)) =
  located name

located :: A.Located Name.Name -> String
located (A.At _ name) =
  Name.toChars name
