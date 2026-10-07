{-# LANGUAGE OverloadedStrings #-}

module Parse.BidiControlSpec where

import Helpers.Instances ()
import Helpers.Parse qualified as Helpers
import Parse.Expression qualified as Expression
import Reporting.Error.Syntax (Expr (ExpressionBadEnd))
import Reporting.Error.Syntax qualified as Error.Syntax
import Test.Hspec (Spec, describe, it)

-- A direction control written as itself in a literal is refused, and its
-- escape is not (geng-lang D604). The sources are UTF-8 bytes: U+202E is
-- E2 80 AE and U+2066 is E2 81 A6.
spec :: Spec
spec = do
  describe "Direction controls" $ do
    it "a raw U+202E in a string is refused" $
      Helpers.checkParseError Expression.expression ExpressionBadEnd (isString 0x202E) "\"user\226\128\174 x\""

    it "a raw U+2066 in a multi-line string is refused" $
      Helpers.checkParseError Expression.expression ExpressionBadEnd (isString 0x2066) "\"\"\"\na\226\129\166b\n\"\"\""

    it "a raw U+202E in a character is refused" $
      Helpers.checkParseError Expression.expression ExpressionBadEnd isChar "'\226\128\174'"

    it "the escape is accepted" $
      Helpers.checkParse Expression.expression ExpressionBadEnd isRight "\"a\\u{202E}b\""

    it "a right-to-left mark, which reorders nothing, is accepted" $
      Helpers.checkParse Expression.expression ExpressionBadEnd isRight "\"a\226\128\143b\""
  where
    isString code err =
      case err of
        Error.Syntax.String (Error.Syntax.StringBidiControl c) _ _ -> c == code
        _ -> False
    isChar err =
      case err of
        Error.Syntax.Char (Error.Syntax.CharBidiControl 0x202E) _ _ -> True
        _ -> False
    isRight result =
      case result of
        Right _ -> True
        Left _ -> False
