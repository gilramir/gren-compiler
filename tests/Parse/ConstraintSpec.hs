{-# LANGUAGE OverloadedStrings #-}

module Parse.ConstraintSpec where

import AST.Source qualified as Src
import Data.ByteString qualified as BS
import Data.ByteString.UTF8 qualified as Utf8
import Data.Name qualified as Name
import Helpers.Instances ()
import Parse.Declaration (declaration)
import Parse.Primitives qualified as P
import Parse.Type qualified as Type
import Reporting.Annotation qualified as A
import Reporting.Error.Syntax qualified as E
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

-- | The constraint context on an annotation — D111, and the layouts D116
-- settled. A context is told apart from the type it qualifies only by the
-- `=>` several tokens in, so most of what is worth testing here is what must
-- *not* be read as a context.
spec :: Spec
spec = do
  describe "Constraint contexts" $ do
    it "one constraint" $
      contextOf "Eq a => a -> a -> Bool" `shouldBe` [("Eq", "a")]

    it "several constraints, parenthesized" $
      contextOf "(Eq a, Ord b) => a -> b -> Bool" `shouldBe` [("Eq", "a"), ("Ord", "b")]

    it "a qualified class name" $
      contextOf "Basics.Eq a => a -> Bool" `shouldBe` [("Basics.Eq", "a")]

    it "redundant parentheses around one constraint are not recorded" $
      -- D116: the formatter decides the parentheses rather than preserving
      -- them, so `(Eq a) =>` and `Eq a =>` parse to the same thing.
      contextOf "(Eq a) => a -> Bool" `shouldBe` contextOf "Eq a => a -> Bool"

  describe "Things that are not contexts" $ do
    it "a type that happens to look like a constraint" $
      contextOf "Eq a" `shouldBe` []

    it "a constraint-shaped argument to a function type" $
      contextOf "Eq a -> Bool" `shouldBe` []

    it "a parenthesized function type" $
      contextOf "(a -> b) -> a -> b" `shouldBe` []

    it "a record type" $
      contextOf "{ n : Int } -> Int" `shouldBe` []

  describe "Layout" $ do
    it "an expanded context, with => in the column -> uses" $
      parsesAsDeclaration
        "f :\n\
        \    ( Eq a\n\
        \    , Ord b\n\
        \    )\n\
        \    => a\n\
        \    -> b\n\
        \    -> Bool\n\
        \f _ _ =\n\
        \    True\n"

    it "an expanded context with one constraint and no parentheses" $
      parsesAsDeclaration
        "f :\n\
        \    Eq a\n\
        \    => a\n\
        \    -> Bool\n\
        \f _ =\n\
        \    True\n"

-- | The context an annotation parses to, flattened to class and variable
-- names. `[]` is "no context", which is the only thing an empty list can
-- mean: `() =>` does not parse.
contextOf :: BS.ByteString -> [(String, String)]
contextOf str =
  case P.fromByteString Type.annotation E.TStart str of
    Left _ ->
      error ("did not parse: " ++ show str)
    Right ((Nothing, _, _), _) ->
      []
    Right ((Just (Src.Context entries _), _, _), _) ->
      map (flatten . fst) entries

flatten :: Src.Constraint -> (String, String)
flatten (A.At _ constraint) =
  case constraint of
    Src.Constraint _ name (A.At _ var) ->
      (Name.toChars name, Name.toChars var)
    Src.ConstraintQual _ home name (A.At _ var) ->
      (Name.toChars home ++ "." ++ Name.toChars name, Name.toChars var)

parsesAsDeclaration :: String -> IO ()
parsesAsDeclaration str =
  P.fromByteString
    (P.specialize (\_ row col -> (row, col)) declaration)
    (\row col -> (row, col))
    (Utf8.fromString str)
    `shouldSatisfy` isRight

isRight :: Either x y -> Bool
isRight result =
  case result of
    Right _ -> True
    Left _ -> False
