{-# LANGUAGE OverloadedStrings #-}

module Parse.NumberSpec where

import Data.ByteString.UTF8 qualified as Utf8
import Data.Utf8 qualified as DUtf8
import Gren.Int qualified as GI
import Gren.Number qualified as GN
import Parse.Number qualified as Number
import Parse.Primitives qualified as P
import Reporting.Error.Syntax qualified as E
import Test.Hspec (Spec, describe, it, shouldBe)

-- | What a numeric literal is carried as.
--
-- The corpus cannot hold this. A literal's /value/ is observable only once it
-- has a type and a backend, and the two numbers this is about — `2^63 - 1` and
-- every `UInt64` above it — were unwritable in a corpus source until the
-- widening these tests pin (`docs/m1b-int.md` §I16). So the parser is tested
-- where the parser is, which is the same argument `Parse.InstanceSpec` makes.
spec :: Spec
spec = do
  describe "an integer literal" $ do
    it "is exact at the largest machine Int, which is where the old carrier stopped" $
      lit "9223372036854775807" `shouldBe` Right (I 9223372036854775807 GI.DecimalInt)

    it "is exact one past it, which the old carrier could not represent at all" $
      lit "9223372036854775808" `shouldBe` Right (I 9223372036854775808 GI.DecimalInt)

    it "reaches UInt64.maxValue" $
      lit "18446744073709551615" `shouldBe` Right (I 18446744073709551615 GI.DecimalInt)

    it "does not stop there, because the range check is the frontend's job and not the parser's" $
      lit "99999999999999999999999999" `shouldBe` Right (I 99999999999999999999999999 GI.DecimalInt)

    it "is still exact at the small values everything else is made of" $
      lit "42" `shouldBe` Right (I 42 GI.DecimalInt)

    it "is zero when it is zero" $
      lit "0" `shouldBe` Right (I 0 GI.DecimalInt)

  describe "a hex literal" $ do
    it "reaches UInt64.maxValue, which is 16 digits of f" $
      lit "0xFFFFFFFFFFFFFFFF" `shouldBe` Right (I 18446744073709551615 GI.HexInt)

    it "is exact at 2^63, the value a signed 64-bit accumulator overflows on" $
      lit "0x8000000000000000" `shouldBe` Right (I 9223372036854775808 GI.HexInt)

    it "reads the same number from either case of digit" $
      lit "0xabcdef" `shouldBe` lit "0xABCDEF"

  describe "a float literal" $ do
    it "is carried as its text, which is why no widening was needed on this side" $
      lit "9223372036854775808.0" `shouldBe` Right (F "9223372036854775808.0")

    it "keeps an exponent as written" $
      lit "1.5e300" `shouldBe` Right (F "1.5e300")

  -- D359 retired the suffix for `(42 : Int64)` (docs/expr-annotation.md
  -- §EA12). The parser still recognizes one, so the error can name the
  -- annotation to write instead, and these pin which problem it reports.
  describe "a retired suffix" $ do
    it "is refused, naming the digits written in front of it" $
      lit "42i64" `shouldBe` Left (Suffix GN.I64 "42")

    it "is refused at each of the eight widths" $
      map (fmap (const ()) . lit) ["42u32", "42u64", "1.5f32", "42i8", "42u8", "42i16", "42u16"]
        `shouldBe` map Left [Suffix GN.U32 "42", Suffix GN.U64 "42", Suffix GN.F32 "1.5", Suffix GN.I8 "42", Suffix GN.U8 "42", Suffix GN.I16 "42", Suffix GN.U16 "42"]

    it "is refused on a hex literal, quoting the hex digits" $
      lit "0xFFu32" `shouldBe` Left (Suffix GN.U32 "0xFF")

    it "is refused after an exponent, which used to be read as an application" $
      lit "1.5e10f32" `shouldBe` Left (Suffix GN.F32 "1.5e10")

    it "is only the weird number when something follows it, since that was never a suffix" $
      lit "42i640" `shouldBe` Left Weird

    it "was never `f32` on a hex literal, because f, 3 and 2 are hex digits" $
      lit "0xFFf32" `shouldBe` lit "0xFFF32"

  describe "what is not a number" $ do
    it "rejects a trailing dot" $
      isError (lit "1.") `shouldBe` True

    it "rejects a leading zero" $
      isError (lit "01") `shouldBe` True

    it "rejects a suffix that was never one of the eight" $
      lit "42i32" `shouldBe` Left Weird

    it "rejects a letter after an exponent, which it did not before" $
      isError (lit "1.5e10x") `shouldBe` True

-- | A literal, in a form that can be compared.
--
-- 'Number.Number' has no `Eq`, and the value half of it is what these tests are
-- about, so it is unpacked here rather than given an orphan instance.
data Lit
  = I Integer GI.IntFormat
  | F String
  deriving (Show)

instance Eq Lit where
  I a fa == I b fb = a == b && sameFormat fa fb
  F a == F b = a == b
  _ == _ = False

-- | Which problem a refused literal reported: the retired suffix, with the
-- digits the hint quotes, or anything else.
data Refusal
  = Suffix GN.Suffix String
  | Weird
  | Other
  deriving (Eq, Show)

refusal :: E.Number -> Refusal
refusal problem =
  case problem of
    E.NumberSuffix suffix written -> Suffix suffix written
    E.NumberEnd -> Weird
    _ -> Other

sameFormat :: GI.IntFormat -> GI.IntFormat -> Bool
sameFormat a b = show a == show b

isError :: Either Refusal a -> Bool
isError result =
  case result of
    Left _ -> True
    Right _ -> False

lit :: String -> Either Refusal Lit
lit str =
  case P.fromByteString
    (Number.number (\_ _ -> Other) (\problem _ _ -> refusal problem))
    (\_ _ -> Other)
    (Utf8.fromString str) of
    Left err ->
      Left err
    Right number ->
      Right $
        case number of
          Number.Int value format -> I value format
          Number.Float text -> F (DUtf8.toChars text)
