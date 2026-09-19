{-# OPTIONS_GHC -Wall #-}

-- | The suffixes a numeric literal used to carry, which the parser now
-- recognizes only to refuse (D359, @docs\/expr-annotation.md@ §EA12).
--
-- @42i64@, @42u32@, @42u64@ and @1.5f32@ were D2's four spellings, and
-- @42i8@, @42u8@, @42i16@ and @42u16@ D342's. Each was a type ascription
-- written on the literal (D154), and @(42 : Int64)@ (D358) says the same thing
-- anywhere, so what is left of them is the error that names the annotation.
module Gren.Number
  ( Suffix (..),
    toChars,
    typeName,
  )
where

import Data.Name qualified as Name

data Suffix
  = I64
  | U32
  | U64
  | F32
  | -- | D342's four (@docs\/m1b-narrow-int.md@ §NI2.5).
    I8
  | U8
  | I16
  | U16
  deriving (Eq, Show)

-- | The suffix as it is written, without the number in front of it.
toChars :: Suffix -> [Char]
toChars suffix =
  case suffix of
    I64 -> "i64"
    U32 -> "u32"
    U64 -> "u64"
    F32 -> "f32"
    I8 -> "i8"
    U8 -> "u8"
    I16 -> "i16"
    U16 -> "u16"

-- | The @Basics@ type the suffix names (D148 puts all six numeric types there).
typeName :: Suffix -> Name.Name
typeName suffix =
  case suffix of
    I64 -> Name.int64
    U32 -> Name.uint32
    U64 -> Name.uint64
    F32 -> Name.float32
    I8 -> Name.int8
    U8 -> Name.uint8
    I16 -> Name.int16
    U16 -> Name.uint16
