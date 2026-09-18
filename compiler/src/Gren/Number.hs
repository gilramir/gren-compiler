{-# OPTIONS_GHC -Wall #-}

-- | The suffix a numeric literal may carry (@syntax.md@ S5, D63).
--
-- @42i64@, @42u32@, @42u64@ and @1.5f32@ are D2's four spellings, and
-- @42i8@, @42u8@, @42i16@ and @42u16@ are D342's. The suffix is
-- a __type ascription written on the literal__ (D154): it says which of D2's
-- types the literal has, and it is accepted wherever the corresponding
-- annotation would be. So @42f32@ is a @Float32@ for the same reason
-- @42 : Float@ has always typed, and @1.5i64@ parses and is then the ordinary
-- TYPE MISMATCH that @1.5 : Int64@ is — the /grammar/ does not distinguish
-- them, which is what keeps D86's two parsers describing one language.
--
-- @Int@ and @Float@ have no suffix: S5 says their literals stay bare, so there
-- is no @i32@ and no @f64@.
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
