{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -Wall #-}

module Parse.Number
  ( Number (..),
    number,
    Outcome (..),
    chompInt,
    chompHex,
    precedence,
  )
where

import AST.Utils.Binop qualified as Binop
import Data.Word (Word8)
import Foreign.Ptr (Ptr, minusPtr, plusPtr)
import Gren.Float qualified as EF
import Gren.Int qualified as GI
import Gren.Number qualified as GN
import Parse.Primitives (Col, Parser, Row)
import Parse.Primitives qualified as P
import Parse.Variable qualified as Var
import Reporting.Error.Syntax qualified as E

-- HELPERS

isDirtyEnd :: Ptr Word8 -> Ptr Word8 -> Word8 -> Bool
isDirtyEnd pos end word =
  Var.getInnerWidthHelp pos end word > 0

isDecimalDigit :: Word8 -> Bool
isDecimalDigit word =
  word <= 0x39 {-9-} && word >= 0x30 {-0-}

-- RETIRED SUFFIXES

-- | Insist the literal ends cleanly, and name the annotation when what ends it
-- is one of the retired suffixes.
--
-- A number takes its type from context or from @(42 : Int64)@ (D358), and the
-- suffix that did the same job is gone (D359, @docs\/expr-annotation.md@
-- §EA12). A letter after the digits was always refused by 'isDirtyEnd', so
-- @42i64@ needs no rule to be an error; it is recognized here only so that the
-- error can say what to write instead. Anything after the suffix, as in
-- @42i640@, is the ordinary weird number, since that was never a suffix.
-- Every exit from a number goes through here (§I17.1, D86).
endOfNumber :: Ptr Word8 -> Ptr Word8 -> (Ptr Word8 -> Outcome) -> Outcome
endOfNumber pos end ok =
  case chompSuffix pos end of
    Just (suffix, suffixEnd)
      | not (dirty suffixEnd) -> Suffixed pos suffix
      | otherwise -> Err suffixEnd E.NumberEnd
    Nothing
      | dirty pos -> Err pos E.NumberEnd
      | otherwise -> ok pos
  where
    dirty p =
      p < end && isDirtyEnd p end (P.unsafeIndex p)

-- | The eight retired suffixes: D2's four and D342's @i16@ and @u16@ three
-- bytes wide, and D342's @i8@ and @u8@ two.
--
-- No suffix is a prefix of another, so the order the two widths are tried in
-- decides nothing (@docs\/m1b-narrow-int.md@ §NI2.5).
chompSuffix :: Ptr Word8 -> Ptr Word8 -> Maybe (GN.Suffix, Ptr Word8)
chompSuffix pos end =
  case chompSuffix3 pos end of
    Just found -> Just found
    Nothing -> chompSuffix2 pos end

chompSuffix3 :: Ptr Word8 -> Ptr Word8 -> Maybe (GN.Suffix, Ptr Word8)
chompSuffix3 pos end =
  if plusPtr pos 3 > end
    then Nothing
    else
      let !a = P.unsafeIndex pos
          !b = P.unsafeIndex (plusPtr pos 1)
          !c = P.unsafeIndex (plusPtr pos 2)
          !after = plusPtr pos 3
       in case (a, b, c) of
            (0x69 {-i-}, 0x36 {-6-}, 0x34 {-4-}) -> Just (GN.I64, after)
            (0x75 {-u-}, 0x33 {-3-}, 0x32 {-2-}) -> Just (GN.U32, after)
            (0x75 {-u-}, 0x36 {-6-}, 0x34 {-4-}) -> Just (GN.U64, after)
            (0x66 {-f-}, 0x33 {-3-}, 0x32 {-2-}) -> Just (GN.F32, after)
            (0x69 {-i-}, 0x31 {-1-}, 0x36 {-6-}) -> Just (GN.I16, after)
            (0x75 {-u-}, 0x31 {-1-}, 0x36 {-6-}) -> Just (GN.U16, after)
            _ -> Nothing

chompSuffix2 :: Ptr Word8 -> Ptr Word8 -> Maybe (GN.Suffix, Ptr Word8)
chompSuffix2 pos end =
  if plusPtr pos 2 > end
    then Nothing
    else
      let !a = P.unsafeIndex pos
          !b = P.unsafeIndex (plusPtr pos 1)
          !after = plusPtr pos 2
       in case (a, b) of
            (0x69 {-i-}, 0x38 {-8-}) -> Just (GN.I8, after)
            (0x75 {-u-}, 0x38 {-8-}) -> Just (GN.U8, after)
            _ -> Nothing

-- | Whether a hex literal's digits are followed by a retired suffix, so that
-- @0xFFu8@ is refused by naming @(0xFF : UInt8)@ rather than as a bad digit.
--
-- All but one, because __@f32@ was never a hex suffix__: @f@, @3@ and @2@
-- are all hex digits, so @0xFFf32@ is the number @0xFFF32@.
isHexSuffix :: Ptr Word8 -> Ptr Word8 -> Bool
isHexSuffix pos end =
  case chompSuffix pos end of
    Just (GN.F32, _) -> False
    Just _ -> True
    Nothing -> False

-- NUMBERS

data Number
  = Int Integer GI.IntFormat
  | Float EF.Float

number :: (Row -> Col -> x) -> (E.Number -> Row -> Col -> x) -> Parser x Number
number toExpectation toError =
  P.Parser $ \(P.State src pos end indent row col) cok _ cerr eerr ->
    if pos >= end
      then eerr row col toExpectation
      else
        let !word = P.unsafeIndex pos
         in if not (isDecimalDigit word)
              then eerr row col toExpectation
              else
                let outcome =
                      if word == 0x30 {-0-}
                        then chompZero (plusPtr pos 1) end
                        else chompInt (plusPtr pos 1) end (fromIntegral (word - 0x30 {-0-}))
                 in case outcome of
                      Err newPos problem ->
                        let !newCol = col + fromIntegral (minusPtr newPos pos)
                         in cerr row newCol (toError problem)
                      Suffixed suffixPos suffix ->
                        let !newCol = col + fromIntegral (minusPtr suffixPos pos)
                            !written = map (toEnum . fromIntegral . P.unsafeIndex . plusPtr pos) [0 .. minusPtr suffixPos pos - 1]
                         in cerr row newCol (toError (E.NumberSuffix suffix written))
                      OkInt newPos intFormat n ->
                        let !newCol = col + fromIntegral (minusPtr newPos pos)
                            !integer = Int n intFormat
                            !newState = P.State src newPos end indent row newCol
                         in cok integer newState
                      OkFloat newPos ->
                        let !newCol = col + fromIntegral (minusPtr newPos pos)
                            !copy = EF.fromPtr pos newPos
                            !float = Float copy
                            !newState = P.State src newPos end indent row newCol
                         in cok float newState

-- CHOMP OUTCOME

-- first Int is newPos
--

-- | @Suffixed@ is a refusal, like @Err@, that carries where the suffix starts
-- rather than a finished problem: the problem quotes the digits in front of
-- the suffix, and only 'number' knows where they began.
data Outcome
  = Err (Ptr Word8) E.Number
  | Suffixed (Ptr Word8) GN.Suffix
  | OkInt (Ptr Word8) GI.IntFormat Integer
  | OkFloat (Ptr Word8)

-- CHOMP INT

chompInt :: Ptr Word8 -> Ptr Word8 -> Integer -> Outcome
chompInt !pos end !n =
  if pos >= end
    then OkInt pos GI.DecimalInt n
    else
      let !word = P.unsafeIndex pos
       in if isDecimalDigit word
            then chompInt (plusPtr pos 1) end (10 * n + fromIntegral (word - 0x30 {-0-}))
            else
              if word == 0x2E {-.-}
                then chompFraction pos end n
                else
                  if word == 0x65 {-e-} || word == 0x45 {-E-}
                    then chompExponent (plusPtr pos 1) end
                    else endOfNumber pos end (\newPos -> OkInt newPos GI.DecimalInt n)

-- CHOMP FRACTION

chompFraction :: Ptr Word8 -> Ptr Word8 -> Integer -> Outcome
chompFraction pos end n =
  let !pos1 = plusPtr pos 1
   in if pos1 >= end
        then Err pos (E.NumberDot n)
        else
          if isDecimalDigit (P.unsafeIndex pos1)
            then chompFractionHelp (plusPtr pos1 1) end
            else Err pos (E.NumberDot n)

chompFractionHelp :: Ptr Word8 -> Ptr Word8 -> Outcome
chompFractionHelp pos end =
  if pos >= end
    then OkFloat pos
    else
      let !word = P.unsafeIndex pos
       in if isDecimalDigit word
            then chompFractionHelp (plusPtr pos 1) end
            else
              if word == 0x65 {-e-} || word == 0x45 {-E-}
                then chompExponent (plusPtr pos 1) end
                else endOfNumber pos end OkFloat

-- CHOMP EXPONENT

chompExponent :: Ptr Word8 -> Ptr Word8 -> Outcome
chompExponent pos end =
  if pos >= end
    then Err pos E.NumberEnd
    else
      let !word = P.unsafeIndex pos
       in if isDecimalDigit word
            then chompExponentHelp (plusPtr pos 1) end
            else
              if word == 0x2B {-+-} || word == 0x2D {---}
                then
                  let !pos1 = plusPtr pos 1
                   in if pos1 < end && isDecimalDigit (P.unsafeIndex pos1)
                        then chompExponentHelp (plusPtr pos 2) end
                        else Err pos E.NumberEnd
                else Err pos E.NumberEnd

chompExponentHelp :: Ptr Word8 -> Ptr Word8 -> Outcome
chompExponentHelp pos end =
  if pos >= end
    then OkFloat pos
    else
      if isDecimalDigit (P.unsafeIndex pos)
        then chompExponentHelp (plusPtr pos 1) end
        else endOfNumber pos end OkFloat

-- CHOMP ZERO

chompZero :: Ptr Word8 -> Ptr Word8 -> Outcome
chompZero pos end =
  if pos >= end
    then OkInt pos GI.DecimalInt 0
    else
      let !word = P.unsafeIndex pos
       in if word == 0x78 {-x-}
            then chompHexInt (plusPtr pos 1) end
            else
              if word == 0x2E {-.-}
                then chompFraction pos end 0
                else
                  if isDecimalDigit word
                    then Err pos E.NumberNoLeadingZero
                    else endOfNumber pos end (\newPos -> OkInt newPos GI.DecimalInt 0)

chompHexInt :: Ptr Word8 -> Ptr Word8 -> Outcome
chompHexInt pos end =
  let (# newPos, answer #) = chompHex pos end
   in if answer < 0
        then Err newPos E.NumberHexDigit
        else endOfNumber newPos end (\afterDigits -> OkInt afterDigits GI.HexInt answer)

-- CHOMP HEX

-- Return -1 if it has NO digits
-- Return -2 if it has BAD digits

chompHex :: Ptr Word8 -> Ptr Word8 -> (# Ptr Word8, Integer #)
chompHex pos end =
  chompHexHelp pos end (-1) 0

chompHexHelp :: Ptr Word8 -> Ptr Word8 -> Integer -> Integer -> (# Ptr Word8, Integer #)
chompHexHelp pos end answer accumulator =
  if pos >= end
    then (# pos, answer #)
    else
      let !newAnswer =
            stepHex pos end (P.unsafeIndex pos) accumulator
       in if newAnswer < 0
            then (# pos, if newAnswer == -1 then answer else -2 #)
            else chompHexHelp (plusPtr pos 1) end newAnswer newAnswer

stepHex :: Ptr Word8 -> Ptr Word8 -> Word8 -> Integer -> Integer
stepHex pos end word acc
  | 0x30 {-0-} <= word && word <= 0x39 {-9-} = 16 * acc + fromIntegral (word - 0x30 {-0-})
  | 0x61 {-a-} <= word && word <= 0x66 {-f-} = 16 * acc + 10 + fromIntegral (word - 0x61 {-a-})
  | 0x41 {-A-} <= word && word <= 0x46 {-F-} = 16 * acc + 10 + fromIntegral (word - 0x41 {-A-})
  | isHexSuffix pos end = -1
  | isDirtyEnd pos end word = -2
  | True = -1

-- PRECEDENCE

precedence :: (Row -> Col -> x) -> Parser x Binop.Precedence
precedence toExpectation =
  P.Parser $ \(P.State src pos end indent row col) cok _ _ eerr ->
    if pos >= end
      then eerr row col toExpectation
      else
        let !word = P.unsafeIndex pos
         in if isDecimalDigit word
              then
                cok
                  (Binop.Precedence (fromIntegral (word - 0x30 {-0-})))
                  (P.State src (plusPtr pos 1) end indent row (col + 1))
              else eerr row col toExpectation
