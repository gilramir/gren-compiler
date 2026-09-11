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
--   * __Integers are already values__, and the only work is choosing the
--     constructor for the width the type gives them.
--
-- __A literal takes its width from its type__ (D149, @docs/m1b-int.md@ §I13).
-- Both integer and float literals are lowered against the type the solver gave
-- the node, because since §I8 step 4 the type decides what the value /is/: a
-- @1@ at an @Int64@ is the JavaScript @1n@ and a @1@ at an @Int@ is the
-- JavaScript @1@, and those are not the same value. Suffixed literals
-- (@syntax.md@ S5, §I8 step 5) are the way to /pin/ a width; this is what makes
-- an unsuffixed one mean the right thing at a width it was inferred to have,
-- which is most of the arithmetic in @Basics@.
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
import Data.Name qualified as Name
import Data.Utf8 qualified as Utf8
import Gren.Float qualified as EF
import Gren.ModuleName qualified as ModuleName
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

-- | A float literal at the width its type says.
--
-- @Float32@ narrows here rather than at run time: 'realToFrac' from the exactly
-- read `Double` to a `Float` is the round-to-nearest the backend's
-- @Math.fround@ would do, done once at compile time. So @0.1 : Float32@ is the
-- single-precision value and not the double 0.1 sitting in a @Float32@, which
-- is the one width bug in this family that would be silent rather than loud.
float :: Core.Type -> EF.Float -> Core.Literal
float tipe number =
  let written = Utf8.toChars number
   in case readMaybe written :: Maybe Double of
        Just value ->
          if numericType tipe == Just Name.float32
            then Core.LFloat32 (realToFrac value)
            else Core.LFloat value
        Nothing ->
          -- The parser's grammar for a float — digits, an optional fraction, an
          -- optional exponent, at least one of the two — is a subset of
          -- Haskell's, so this is unreachable rather than merely unlikely.
          error ("Core.Lower.Literal.float: cannot read " ++ show written)

-- | An integer literal at the width its type says.
--
-- A literal whose type is still a /variable/ — the body of a
-- @f : Num a => a -> a@ that says @x + 1@ — has no width to read, and takes the
-- @Int@ case. That is `docs/open-items.md`\'s registered hole and not a
-- decision made here: `classes.md` §0 closes an /ambiguous/ numeric variable
-- and a rigid one is not ambiguous, so nothing closes it and @Num@ has no
-- @fromInt@ method for a witness to carry. D63's range check makes the same
-- assumption, and the two have to agree (@docs\/m1b-int.md@ §I20).
--
-- __An integer literal at a float type is a float__, which is what @2 : Float@
-- has always meant and what @42f32@ now says outright. Before §I18 both fell
-- through to the transitional @LIntLegacy@, so a @Float32@ written without a
-- decimal point was a legacy @Int@ in the IR — invisible on JavaScript, where
-- both are a double, and not invisible anywhere else.
--
-- __The value is narrowed rather than checked here.__ @fromInteger@ at an
-- 'Int32' wraps, and nothing out of range reaches this point: D63's check
-- refuses such a literal in `Compile` (§I20), which is the phase that can
-- report an error against a source region.
int :: Core.Type -> Integer -> Core.Literal
int tipe n =
  case numericType tipe of
    Just name
      | name == Name.int64 -> Core.LInt64 (fromIntegral n)
      | name == Name.uint32 -> Core.LUInt32 (fromIntegral n)
      | name == Name.uint64 -> Core.LUInt64 (fromIntegral n)
      | name == Name.float -> Core.LFloat (fromInteger n)
      | name == Name.float32 -> Core.LFloat32 (fromInteger n)
    _ -> Core.LInt (fromInteger n)

-- | The name of the @Basics@ type this literal has, when it has one.
--
-- All six numeric types are declared in @Basics@ (D148), so one match answers
-- for every width. 'Nothing' is a type variable, which is the case above.
numericType :: Core.Type -> Maybe Name.Name
numericType tipe =
  case tipe of
    Core.TCon (Core.QualName home name) []
      | home == ModuleName.basics -> Just name
    _ -> Nothing

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
