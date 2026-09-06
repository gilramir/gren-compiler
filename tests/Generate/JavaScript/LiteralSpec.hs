{-# LANGUAGE OverloadedStrings #-}

-- | Core characters as JavaScript source (@docs/m1a-js-on-core.md@ §J4).
--
-- The encoder exists at all because C2 made Core's 'Core.AST.Text' real
-- characters rather than the source they were written as, so something has to
-- write a literal again — and §J4 asked for that something to be written from
-- the specification rather than ported from `Gren.String`, whose surrogate-pair
-- arithmetic is upstream's @compiler#384@. These are the cases that say it was.
module Generate.JavaScript.LiteralSpec where

import Data.Utf8 qualified as Utf8
import Generate.JavaScript.Literal qualified as Literal
import Test.Hspec

spec :: Spec
spec = do
  describe "string" $ do
    it "leaves ordinary text alone" $
      enc "hello, world" `shouldBe` "hello, world"

    it "escapes the quote the builder writes and not the other one" $
      -- `Generate.JavaScript.Builder` puts a string between single quotes.
      enc "it's \"quoted\"" `shouldBe` "it\\'s \"quoted\""

    it "escapes a backslash" $
      enc "a\\b" `shouldBe` "a\\\\b"

    it "escapes the three whitespace controls by name" $
      enc "a\nb\rc\td" `shouldBe` "a\\nb\\rc\\td"

    it "escapes the other C0 controls and DEL by codepoint" $
      enc "\x00\x01\x1F\x7F" `shouldBe` "\\u0000\\u0001\\u001f\\u007f"

    it "escapes U+2028 and U+2029" $
      -- JavaScript before ES2019 treats them as line terminators inside a
      -- string literal, which ends the literal in the middle of itself.
      enc "\x2028\x2029" `shouldBe` "\\u2028\\u2029"

    it "leaves U+0080 through U+009F alone" $
      -- They are C1 controls, and nothing in a JavaScript string literal cares.
      enc "\x80\x9F" `shouldBe` "\x80\x9F"

    it "writes U+FFFF as itself" $
      -- The bug §J4 is about: `Gren.String` tests `code < 0xFFFF` where it means
      -- `<= 0xFFFF`, and emits U+FFFF as the pair '퟿\uDFFF' — two
      -- characters, neither of them the one written, and the first not even a
      -- surrogate. There is no arithmetic here to be off by one.
      enc "\xFFFF" `shouldBe` "\xFFFF"

    it "writes the characters either side of that boundary as themselves" $
      enc "\xFFFD\xFFFE\xFFFF" `shouldBe` "\xFFFD\xFFFE\xFFFF"

    it "writes an astral character as itself" $
      -- One character, not a surrogate pair: the output is a UTF-8 file, and a
      -- JavaScript string literal may hold any character but the escaped ones.
      enc "\x10000\x10FFFF" `shouldBe` "\x10000\x10FFFF"

    it "is empty for the empty string" $
      enc "" `shouldBe` ""

  describe "float" $ do
    it "writes a whole number so that JavaScript reads it back as a float" $
      flt 1 `shouldBe` "1.0"

    it "writes the shortest decimal that reads back as the same double" $
      flt 0.1 `shouldBe` "0.1"

    it "writes an exponent JavaScript accepts" $
      flt 1.0e-2 `shouldBe` "1.0e-2"

    it "writes the two non-finite values as JavaScript spells them" $
      map flt [1 / 0, -1 / 0, 0 / 0] `shouldBe` ["Infinity", "-Infinity", "NaN"]

enc :: [Char] -> [Char]
enc = Utf8.toChars . Literal.string

flt :: Double -> [Char]
flt = Utf8.toChars . Literal.float
