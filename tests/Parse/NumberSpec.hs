{-# LANGUAGE OverloadedStrings #-}

module Parse.NumberSpec where

import Data.ByteString.UTF8 qualified as Utf8
import Data.Utf8 qualified as DUtf8
import Gren.Int qualified as GI
import Gren.Number qualified as GN
import Parse.Number qualified as Number
import Parse.Primitives qualified as P
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
      lit "9223372036854775807" `shouldBe` Right (I 9223372036854775807 GI.DecimalInt Nothing)

    it "is exact one past it, which the old carrier could not represent at all" $
      lit "9223372036854775808" `shouldBe` Right (I 9223372036854775808 GI.DecimalInt Nothing)

    it "reaches UInt64.maxValue" $
      lit "18446744073709551615" `shouldBe` Right (I 18446744073709551615 GI.DecimalInt Nothing)

    it "does not stop there, because the range check is the frontend's job and not the parser's" $
      lit "99999999999999999999999999" `shouldBe` Right (I 99999999999999999999999999 GI.DecimalInt Nothing)

    it "is still exact at the small values everything else is made of" $
      lit "42" `shouldBe` Right (I 42 GI.DecimalInt Nothing)

    it "is zero when it is zero" $
      lit "0" `shouldBe` Right (I 0 GI.DecimalInt Nothing)

  describe "a hex literal" $ do
    it "reaches UInt64.maxValue, which is 16 digits of f" $
      lit "0xFFFFFFFFFFFFFFFF" `shouldBe` Right (I 18446744073709551615 GI.HexInt Nothing)

    it "is exact at 2^63, the value a signed 64-bit accumulator overflows on" $
      lit "0x8000000000000000" `shouldBe` Right (I 9223372036854775808 GI.HexInt Nothing)

    it "reads the same number from either case of digit" $
      lit "0xabcdef" `shouldBe` lit "0xABCDEF"

  describe "a float literal" $ do
    it "is carried as its text, which is why no widening was needed on this side" $
      lit "9223372036854775808.0" `shouldBe` Right (F "9223372036854775808.0" Nothing)

    it "keeps an exponent as written" $
      lit "1.5e300" `shouldBe` Right (F "1.5e300" Nothing)

  describe "a suffix" $ do
    it "pins a decimal integer's width" $
      lit "42i64" `shouldBe` Right (I 42 GI.DecimalInt (Just GN.I64))

    it "is read at each of the three integer widths" $ do
      lit "42u32" `shouldBe` Right (I 42 GI.DecimalInt (Just GN.U32))
      lit "42u64" `shouldBe` Right (I 42 GI.DecimalInt (Just GN.U64))

    it "attaches to a hex literal, because a hex literal is a bit pattern" $
      lit "0xFFu32" `shouldBe` Right (I 255 GI.HexInt (Just GN.U32))

    it "attaches to a zero" $
      lit "0u64" `shouldBe` Right (I 0 GI.DecimalInt (Just GN.U64))

    it "attaches to a float and is kept out of its digits" $
      lit "1.5f32" `shouldBe` Right (F "1.5" (Just GN.F32))

    it "attaches to an integer literal, which is how `42 : Float` has always typed" $
      lit "42f32" `shouldBe` Right (I 42 GI.DecimalInt (Just GN.F32))

    it "does not have to agree with the literal's shape, because the type checker says that" $
      lit "1.5i64" `shouldBe` Right (F "1.5" (Just GN.I64))

    -- The row §I17.1 measured: `chompExponentHelp` was the one exit with no
    -- end-of-number check, so this used to be `1.5e10` applied to a variable
    -- named `f32` while the second parser refused the file (D86).
    it "attaches after an exponent, which used to be read as an application" $
      lit "1.5e10f32" `shouldBe` Right (F "1.5e10" (Just GN.F32))

    it "is not `f32` on a hex literal, because f, 3 and 2 are hex digits" $
      lit "0xFFf32" `shouldBe` lit "0xFFF32"

  describe "what is not a number" $ do
    it "rejects a trailing dot" $
      isError (lit "1.") `shouldBe` True

    it "rejects a leading zero" $
      isError (lit "01") `shouldBe` True

    it "rejects a suffix that is not one of the four" $
      isError (lit "42i32") `shouldBe` True

    it "rejects anything after a suffix" $
      isError (lit "42i64x") `shouldBe` True

    it "rejects a letter after an exponent, which it did not before" $
      isError (lit "1.5e10x") `shouldBe` True

-- | A literal, in a form that can be compared.
--
-- 'Number.Number' has no `Eq`, and the value half of it is what these tests are
-- about, so it is unpacked here rather than given an orphan instance.
data Lit
  = I Integer GI.IntFormat (Maybe GN.Suffix)
  | F String (Maybe GN.Suffix)
  deriving (Show)

instance Eq Lit where
  I a fa sa == I b fb sb = a == b && sameFormat fa fb && sa == sb
  F a sa == F b sb = a == b && sa == sb
  _ == _ = False

sameFormat :: GI.IntFormat -> GI.IntFormat -> Bool
sameFormat a b = show a == show b

isError :: Either e a -> Bool
isError result =
  case result of
    Left _ -> True
    Right _ -> False

lit :: String -> Either (P.Row, P.Col) Lit
lit str =
  case P.fromByteString
    (Number.number (\row col -> (row, col)) (\_ row col -> (row, col)))
    (\row col -> (row, col))
    (Utf8.fromString str) of
    Left err ->
      Left err
    Right number ->
      Right $
        case number of
          Number.Int value format suffix -> I value format suffix
          Number.Float text suffix -> F (DUtf8.toChars text) suffix
