{-# LANGUAGE OverloadedStrings #-}

module Parse.MultilineStringSpec where

import AST.Source qualified as Src
import Data.ByteString qualified as BS
import Data.Utf8 qualified as Utf8
import Helpers.Instances ()
import Helpers.Parse qualified as Helpers
import Parse.Expression qualified as Expression
import Parse.Pattern qualified as Pattern
import Reporting.Error.Syntax (Expr (ExpressionBadEnd))
import Reporting.Error.Syntax qualified as Error.Syntax
import Test.Hspec (Spec, describe, it)

spec :: Spec
spec = do
  describe "Multiline String" $ do
    -- Each source starts at column 1, so its indentation is none: a line's
    -- leading spaces are part of the string (geng-lang D603).
    -- `corpus/accept/multiline-string-indentation` holds the column rule.
    it "regression test" $
      parse
        "normal string"
        "\"\"\"\nnormal string\n\"\"\""

    it "crlf regression test" $ do
      parse
        "normal string"
        "\"\"\"\r\nnormal string\r\n\"\"\""

    it "the line break before the closing quotes ends the string" $ do
      parse
        "this is \\na test \\nfor newlines"
        "\"\"\"\nthis is \na test \nfor newlines\n\"\"\""

    it "crlfs work" $ do
      parse
        "   this is\\n   a test"
        "\"\"\"\r\n   this is\r\n   a test\r\n\"\"\""

    it "mixing quotes work" $ do
      parse
        "string with \" in it"
        "\"\"\"\nstring with \" in it\n\"\"\""

    it "single quotes don't eat spaces" $ do
      parse
        "  quote followed by spaces: \\'    "
        "\"\"\"\n  quote followed by spaces: \'    \n\"\"\""

    it "escapes don't eat spaces" $ do
      parse
        "  quote followed by spaces: \\'    "
        "\"\"\"\n  quote followed by spaces: \\'    \n\"\"\""

    it "unicode escapes don't eat spaces" $ do
      parse
        "  quote followed by spaces: \\u0020    "
        "\"\"\"\n  quote followed by spaces: \\u{0020}    \n\"\"\""

    it "a trailing blank line is kept" $ do
      parse
        "one  \\n"
        "\"\"\"\none  \n\n\"\"\""

    it "an empty string" $ do
      parse
        ""
        "\"\"\"\n\"\"\""

    it "does not allow closing quotes after content" $ do
      let isCorrectError ((Error.Syntax.String Error.Syntax.StringMultilineMisaligned _ _)) = True
          isCorrectError _ = False
      Helpers.checkParseError Expression.expression ExpressionBadEnd isCorrectError "\"\"\"\nnormal string\"\"\""

    it "does not allow closing quotes right of the opening ones" $ do
      let isCorrectError ((Error.Syntax.String Error.Syntax.StringMultilineMisaligned _ _)) = True
          isCorrectError _ = False
      Helpers.checkParseError Expression.expression ExpressionBadEnd isCorrectError "\"\"\"\nnormal string\n  \"\"\""

    it "does not allow non-newline characters on the first line" $ do
      let isCorrectError ((Error.Syntax.String Error.Syntax.StringMultilineWithoutLeadingNewline _ _)) = True
          isCorrectError _ = False
      Helpers.checkParseError Expression.expression ExpressionBadEnd isCorrectError "\"\"\"this is not allowed\"\"\""

    it "does not allow CR without LF on the first line" $ do
      let isCorrectError ((Error.Syntax.String Error.Syntax.StringInvalidNewline _ _)) = True
          isCorrectError _ = False
      Helpers.checkParseError Expression.expression ExpressionBadEnd isCorrectError "\"\"\"\rthis is not allowed\"\"\""

    it "does not allow CR without LF on the other lines" $ do
      let isCorrectError ((Error.Syntax.String Error.Syntax.StringInvalidNewline _ _)) = True
          isCorrectError _ = False
      Helpers.checkParseError Expression.expression ExpressionBadEnd isCorrectError "\"\"\"\nthis\ris not allowed\"\"\""

parse :: String -> BS.ByteString -> IO ()
parse expectedStr =
  let isExpectedString :: Src.Pattern_ -> Bool
      isExpectedString pattern =
        case pattern of
          Src.PStr str ->
            expectedStr == Utf8.toChars str
          _ ->
            False
   in Helpers.checkSuccessfulParse (fmap (\((pat, _), loc) -> (pat, loc)) Pattern.expression) Error.Syntax.PStart isExpectedString
