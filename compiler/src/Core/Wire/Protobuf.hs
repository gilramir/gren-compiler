{-# OPTIONS_GHC -Wall #-}

-- | The protobuf wire primitives, and nothing about Core.
--
-- @schema/geng/core/v1.proto@ in the @geng-lang@ repository is the schema this
-- serves and @docs/m1a-wire.md@ is the brief. D88 is why these are here at all
-- rather than being a library's: C10's canonical profile makes an unknown field
-- a __hard error on read__, and preserving unknown fields is required proto3
-- behaviour — so no conforming library can implement the profile, because doing
-- so would mean violating its own specification.
--
-- What this module holds is the part both directions agree about: the wire
-- types, how a tag is packed with one, zigzag, and the size of a varint.
module Core.Wire.Protobuf
  ( -- * Wire types
    WireType (..),
    wireCode,
    wireFromCode,

    -- * Tags
    tagKey,
    keyTag,
    keyWire,

    -- * Numbers
    zigzag32,
    zigzag64,
    unzigzag32,
    unzigzag64,
    varintSize,

    -- * Errors
    Error (..),
    renderError,
  )
where

import Data.Bits (shiftL, shiftR, xor, (.&.), (.|.))
import Data.Int (Int32, Int64)
import Data.List qualified as List
import Data.Word (Word32, Word64)

-- WIRE TYPES

-- | The three of protobuf's six this schema uses. Groups are gone from proto3,
-- and nothing here is 32-bit-fixed except a @float@ — which is 'WFixed32'.
data WireType
  = WVarint
  | WFixed64
  | WBytes
  | WFixed32
  deriving (Eq, Show)

wireCode :: WireType -> Word32
wireCode w =
  case w of
    WVarint -> 0
    WFixed64 -> 1
    WBytes -> 2
    WFixed32 -> 5

wireFromCode :: Word32 -> Maybe WireType
wireFromCode c =
  case c of
    0 -> Just WVarint
    1 -> Just WFixed64
    2 -> Just WBytes
    5 -> Just WFixed32
    _ -> Nothing

-- TAGS

-- | A field's key: the tag shifted left three, with the wire type underneath.
tagKey :: Word32 -> WireType -> Word64
tagKey tag wire =
  fromIntegral (tag `shiftL` 3) .|. fromIntegral (wireCode wire)

keyTag :: Word64 -> Word32
keyTag key = fromIntegral (key `shiftR` 3)

keyWire :: Word64 -> Maybe WireType
keyWire key = wireFromCode (fromIntegral (key .&. 7))

-- NUMBERS

-- | @sint32@ and @sint64@ are zigzag: a small negative number costs one byte
-- rather than ten. Every signed field in the schema is one of those, because
-- Core's negative numbers — an @LInt@, a negative @LIntLegacy@ — are ordinary
-- rather than exceptional.
zigzag32 :: Int32 -> Word64
zigzag32 n = fromIntegral (fromIntegral ((n `shiftL` 1) `xor` (n `shiftR` 31)) :: Word32)

zigzag64 :: Int64 -> Word64
zigzag64 n = fromIntegral ((n `shiftL` 1) `xor` (n `shiftR` 63))

unzigzag32 :: Word64 -> Int32
unzigzag32 w =
  let n = fromIntegral w :: Word32
   in fromIntegral (n `shiftR` 1) `xor` negate (fromIntegral (n .&. 1))

unzigzag64 :: Word64 -> Int64
unzigzag64 w =
  fromIntegral (w `shiftR` 1) `xor` negate (fromIntegral (w .&. 1))

-- | How many bytes the __minimal__ encoding of a varint takes. Rule 2 says
-- there is only one encoding, so this is a function and not an estimate, and
-- the encoder uses it to size a message without building it twice.
varintSize :: Word64 -> Int
varintSize n
  | n < 0x80 = 1
  | n < 0x4000 = 2
  | n < 0x200000 = 3
  | n < 0x10000000 = 4
  | n < 0x800000000 = 5
  | n < 0x40000000000 = 6
  | n < 0x2000000000000 = 7
  | n < 0x100000000000000 = 8
  | n < 0x8000000000000000 = 9
  | otherwise = 10

-- ERRORS

-- | What a reader refuses, and where.
--
-- The path is the field names from the outside in — @Module.defs.value.lit@ —
-- because a byte offset alone in a 600 KB file identifies nothing a person can
-- act on, and the profile's violations are all *about* a particular field.
-- The offset is carried too, since a corrupt file has no meaningful path.
data Error = Error
  { _errOffset :: !Int,
    _errPath :: ![String],
    _errMessage :: !String
  }
  deriving (Eq, Show)

renderError :: Error -> String
renderError (Error offset path message) =
  let at = if null path then "" else " at " ++ List.intercalate "." (reverse path)
   in "byte " ++ show offset ++ at ++ ": " ++ message
