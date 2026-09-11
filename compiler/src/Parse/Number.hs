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

-- SUFFIXES

-- | Read an optional suffix, and then insist the literal ends cleanly.
--
-- The suffix is the only place letters may appear inside a numeric literal, so
-- this is where 'isDirtyEnd' asks its question: after @i64@, @u32@, @u64@ or
-- @f32@ when one is there, and at the character that ended the digits when it
-- is not. Every exit from a number goes through here, which is what makes
-- @1.5e10f32@ one token — 'chompExponentHelp' used to be the one exit with no
-- end check at all, so the Haskell parser read it as an application and the
-- second parser refused the file (@docs\/m1b-int.md@ §I17.1, D86).
endOfNumber :: Ptr Word8 -> Ptr Word8 -> (Ptr Word8 -> Maybe GN.Suffix -> Outcome) -> Outcome
endOfNumber pos end ok =
  case chompSuffix pos end of
    Just (suffix, suffixEnd) -> cleanly suffixEnd (Just suffix)
    Nothing -> cleanly pos Nothing
  where
    cleanly newPos suffix =
      if newPos < end && isDirtyEnd newPos end (P.unsafeIndex newPos)
        then Err newPos E.NumberEnd
        else ok newPos suffix

-- | The four suffixes, each three bytes wide.
chompSuffix :: Ptr Word8 -> Ptr Word8 -> Maybe (GN.Suffix, Ptr Word8)
chompSuffix pos end =
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
            _ -> Nothing

-- | Whether a hex literal's digits are followed by a suffix.
--
-- Three of the four, because __@f32@ is not a hex suffix__: @f@, @3@ and @2@
-- are all hex digits, so @0xFFf32@ is the number @0xFFF32@ and there is no
-- spelling that could mean otherwise. A @Float32@ built from a bit pattern is
-- @f32_from_bits@\'s job (C13), not a literal\'s.
isHexSuffix :: Ptr Word8 -> Ptr Word8 -> Bool
isHexSuffix pos end =
  case chompSuffix pos end of
    Just (GN.F32, _) -> False
    Just _ -> True
    Nothing -> False

-- NUMBERS

data Number
  = Int Integer GI.IntFormat (Maybe GN.Suffix)
  | Float EF.Float (Maybe GN.Suffix)

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
                      OkInt newPos intFormat suffix n ->
                        let !newCol = col + fromIntegral (minusPtr newPos pos)
                            !integer = Int n intFormat suffix
                            !newState = P.State src newPos end indent row newCol
                         in cok integer newState
                      OkFloat newPos digitsEnd suffix ->
                        let !newCol = col + fromIntegral (minusPtr newPos pos)
                            !copy = EF.fromPtr pos digitsEnd
                            !float = Float copy suffix
                            !newState = P.State src newPos end indent row newCol
                         in cok float newState

-- CHOMP OUTCOME

-- first Int is newPos
--

-- | @OkFloat@ carries two positions: where the /digits/ stopped and where the
-- literal did. "Gren.Float" holds the digits as written and must not see the
-- suffix, so @1.5f32@ answers the text @1.5@ and 'GN.F32'.
data Outcome
  = Err (Ptr Word8) E.Number
  | OkInt (Ptr Word8) GI.IntFormat (Maybe GN.Suffix) Integer
  | OkFloat (Ptr Word8) (Ptr Word8) (Maybe GN.Suffix)

-- CHOMP INT

chompInt :: Ptr Word8 -> Ptr Word8 -> Integer -> Outcome
chompInt !pos end !n =
  if pos >= end
    then OkInt pos GI.DecimalInt Nothing n
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
                    else endOfNumber pos end (\newPos suffix -> OkInt newPos GI.DecimalInt suffix n)

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
    then OkFloat pos pos Nothing
    else
      let !word = P.unsafeIndex pos
       in if isDecimalDigit word
            then chompFractionHelp (plusPtr pos 1) end
            else
              if word == 0x65 {-e-} || word == 0x45 {-E-}
                then chompExponent (plusPtr pos 1) end
                else endOfNumber pos end (\newPos suffix -> OkFloat newPos pos suffix)

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
    then OkFloat pos pos Nothing
    else
      if isDecimalDigit (P.unsafeIndex pos)
        then chompExponentHelp (plusPtr pos 1) end
        else endOfNumber pos end (\newPos suffix -> OkFloat newPos pos suffix)

-- CHOMP ZERO

chompZero :: Ptr Word8 -> Ptr Word8 -> Outcome
chompZero pos end =
  if pos >= end
    then OkInt pos GI.DecimalInt Nothing 0
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
                    else endOfNumber pos end (\newPos suffix -> OkInt newPos GI.DecimalInt suffix 0)

chompHexInt :: Ptr Word8 -> Ptr Word8 -> Outcome
chompHexInt pos end =
  let (# newPos, answer #) = chompHex pos end
   in if answer < 0
        then Err newPos E.NumberHexDigit
        else endOfNumber newPos end (\afterSuffix suffix -> OkInt afterSuffix GI.HexInt suffix answer)

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
