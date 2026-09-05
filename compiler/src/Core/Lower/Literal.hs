{-# OPTIONS_GHC -Wall #-}

-- | Lower a literal to Core.
--
-- Three of the four kinds need real work, because @Canonical@ does not hold
-- values for them — it holds the source text they were written as.
--
--   * __Strings and characters are JavaScript source__, not text.
--     "Gren.String" keeps a literal in the form the JS backend pastes into its
--     output: raw bytes where the source had raw bytes, and a backslash-u
--     escape where the source had one, with an astral code point stored as a
--     surrogate /pair/ of them. So @"A"@ and @"\\u{41}"@ are two different
--     values standing for one string. Core's 'Core.AST.LString' is UTF-8 (C2)
--     and its 'Core.AST.LChar' is a code point (C8), so both are decoded here.
--     This is the reason 'Core.AST.Text' is a separate type from
--     'Gren.String'.
--
--   * __Floats are source text too.__ "Gren.Float" is the digits as written,
--     and Core's 'Core.AST.LFloat' is a `Double`, so the literal is converted
--     here. `unicode.md` U5 makes correct rounding the specification and names
--     the frontend as the implementation that has to meet it for literals;
--     GHC's `Read Double` goes through an exact `Rational` and `fromRat`, which
--     is round-to-nearest-even, so it meets it.
--
--   * __Integers are already values__, and stay 'Core.AST.LIntLegacy' until D2
--     lands at M1b. See 'Core.AST.LIntLegacy' for why that is its own
--     constructor rather than a widened `LInt64`.
module Core.Lower.Literal
  ( str,
    chr,
    float,
    int,
    decode,
  )
where

import Core.AST qualified as Core
import Data.Char qualified as Char
import Data.Int (Int32)
import Data.Utf8 qualified as Utf8
import Gren.Float qualified as EF
import Gren.String qualified as ES
import Text.Read (readMaybe)

str :: ES.String -> Core.Literal
str = Core.LString . Utf8.fromChars . decode

-- | A character literal.
--
-- Exactly one code point, which the parser guarantees: a `Char` literal is one
-- character or one escape, and an escape is one code point once the surrogate
-- pair an astral one is stored as has been put back together.
chr :: ES.String -> Core.Literal
chr text =
  case decode text of
    [c] -> Core.LChar (fromIntegral (Char.ord c) :: Int32)
    decoded ->
      error $
        "Core.Lower.Literal.chr: a character literal decoded to "
          ++ show (length decoded)
          ++ " code points: "
          ++ show decoded

float :: EF.Float -> Core.Literal
float number =
  let written = Utf8.toChars number
   in case readMaybe written :: Maybe Double of
        Just value -> Core.LFloat value
        Nothing ->
          -- The parser's grammar for a float — digits, an optional fraction, an
          -- optional exponent, at least one of the two — is a subset of
          -- Haskell's, so this is unreachable rather than merely unlikely.
          error ("Core.Lower.Literal.float: cannot read " ++ show written)

int :: Int -> Core.Literal
int = Core.LIntLegacy . toInteger

-- | Resolve a literal's escapes, and put surrogate pairs back together.
--
-- The escapes "Parse.String" can leave behind are exactly the six it calls
-- @EscapeNormal@ — @\\n@, @\\r@, @\\t@, @\\"@, @\\'@ and @\\\\@ — plus the
-- four-hex-digit @\\uXXXX@ that "Gren.String" writes a @\\u{...}@ as. Anything
-- else in the bytes is a character, already UTF-8, and passes through.
decode :: ES.String -> [Char]
decode = resolve . ES.toChars

resolve :: [Char] -> [Char]
resolve chars =
  case chars of
    [] -> []
    '\\' : rest -> escape rest
    c : rest -> c : resolve rest

escape :: [Char] -> [Char]
escape chars =
  case chars of
    'n' : rest -> '\n' : resolve rest
    'r' : rest -> '\r' : resolve rest
    't' : rest -> '\t' : resolve rest
    '"' : rest -> '"' : resolve rest
    '\'' : rest -> '\'' : resolve rest
    '\\' : rest -> '\\' : resolve rest
    'u' : a : b : c : d : rest -> unicode (hex a b c d) rest
    _ -> error ("Core.Lower.Literal: unknown escape in a literal: " ++ show (take 8 chars))

-- | One @\\uXXXX@, plus the one that follows it when the two are a surrogate
-- pair.
--
-- "Gren.String" stores an astral code point as a pair because its output is a
-- JavaScript literal and JavaScript strings are UTF-16. Core is neither, so the
-- pair is joined back into the code point it stands for.
--
-- An unpaired surrogate is passed through as itself. C8 says a surrogate is not
-- a valid `Char`, but the parser accepts @"\\u{D800}"@ today and rejecting it
-- is a language decision rather than something for the lowering to invent.
unicode :: Int -> [Char] -> [Char]
unicode code rest
  | isHigh code,
    '\\' : 'u' : a : b : c : d : more <- rest,
    let low = hex a b c d,
    isLow low =
      Char.chr (0x10000 + (code - 0xD800) * 0x400 + (low - 0xDC00)) : resolve more
  | otherwise =
      Char.chr code : resolve rest

isHigh :: Int -> Bool
isHigh code = 0xD800 <= code && code <= 0xDBFF

isLow :: Int -> Bool
isLow code = 0xDC00 <= code && code <= 0xDFFF

hex :: Char -> Char -> Char -> Char -> Int
hex a b c d =
  Char.digitToInt a * 0x1000
    + Char.digitToInt b * 0x100
    + Char.digitToInt c * 0x10
    + Char.digitToInt d
