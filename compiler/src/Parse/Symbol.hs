{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module Parse.Symbol
  ( operator,
    hasTypeEnds,
    refuseHasType,
    BadOperator (..),
    binopCharSet,
  )
where

import Data.Char qualified as Char
import Data.IntSet qualified as IntSet
import Data.Name qualified as Name
import Data.Vector qualified as Vector
import Foreign.Ptr (Ptr, minusPtr, plusPtr)
import GHC.Word (Word8)
import Parse.Primitives (Col, Parser, Row)
import Parse.Primitives qualified as P

-- OPERATOR

data BadOperator
  = BadDot
  | BadPipe
  | BadArrow
  | BadEquals
  | BadHasType
  deriving (Show)

operator :: (Row -> Col -> x) -> (BadOperator -> Row -> Col -> x) -> Parser x Name.Name
operator toExpectation toError =
  P.Parser $ \(P.State src pos end indent row col) cok _ cerr eerr ->
    let !newPos = chompOps pos end
     in if pos == newPos
          then eerr row col toExpectation
          else case Name.fromPtr pos newPos of
            "." -> eerr row col (toError BadDot)
            "|" -> cerr row col (toError BadPipe)
            "->" -> cerr row col (toError BadArrow)
            "=" -> cerr row col (toError BadEquals)
            ":" -> cerr row col (toError BadHasType)
            op ->
              let !newCol = col + fromIntegral (minusPtr newPos pos)
                  !newState = P.State src newPos end indent row newCol
               in cok op newState

-- HAS TYPE

-- | Whether a lone @:@ is next: the colon, and no operator character after it.
--
-- @:@ is not an operator (`operator` refuses it), and where it can be read
-- depends on where the expression is. Inside parentheses it starts an
-- annotation, @(e : T)@ (D358, @docs\/expr-annotation.md@ §EA8); anywhere else
-- it is a mistake, usually a signature indented into the definition above it.
isHasType :: Ptr Word8 -> Ptr Word8 -> Bool
isHasType pos end =
  pos < end
    && P.unsafeIndex pos == 0x3A {-:-}
    && not (plusPtr pos 1 < end && isBinopCharHelp (P.unsafeIndex (plusPtr pos 1)))

-- | Fail without consuming anything if a lone @:@ is next, so that an
-- expression ends in front of it; succeed without consuming otherwise.
--
-- This is what 'Parse.Expression'\'s operator branch asks before it reads an
-- operator. `operator`'s committed 'BadHasType' would stop the parse there, and
-- the parentheses around the expression, which are the one place a @:@ may
-- follow one, would never see it.
hasTypeEnds :: (Row -> Col -> x) -> Parser x ()
hasTypeEnds toExpectation =
  P.Parser $ \state@(P.State _ pos end _ row col) _ eok _ eerr ->
    if isHasType pos end
      then eerr row col toExpectation
      else eok () state

-- | Refuse a lone @:@ where an expression has ended and no annotation can
-- follow, with the error `operator` gave for it before D358: the colon is
-- reported where it is, in the context of the definition being parsed.
refuseHasType :: (BadOperator -> Row -> Col -> x) -> Parser x ()
refuseHasType toError =
  P.Parser $ \state@(P.State _ pos end _ row col) _ eok cerr _ ->
    if isHasType pos end
      then cerr row col (toError BadHasType)
      else eok () state

chompOps :: Ptr Word8 -> Ptr Word8 -> Ptr Word8
chompOps pos end =
  if pos < end && isBinopCharHelp (P.unsafeIndex pos)
    then chompOps (plusPtr pos 1) end
    else pos

isBinopCharHelp :: Word8 -> Bool
isBinopCharHelp word =
  word < 128 && Vector.unsafeIndex binopCharVector (fromIntegral word)

binopCharVector :: Vector.Vector Bool
binopCharVector =
  Vector.generate 128 (\i -> IntSet.member i binopCharSet)

binopCharSet :: IntSet.IntSet
binopCharSet =
  IntSet.fromList (map Char.ord "+-/*=.<>:&|^?%!")
