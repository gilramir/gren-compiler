{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | The Core wire format: the file, and the two directions.
--
-- @schema/geng/core/v1.proto@ in the @geng-lang@ repository is the schema of
-- record (D88) and @docs/m1a-wire.md@ is the brief. C10 is the decision this
-- implements and @DESIGN.md@ §8's "byte-identical Core" is what it is for: the
-- only machine-checkable oracle M4's self-hosting port has is that two
-- independently written frontends produce the same bytes for the same program.
--
-- __A @.corepb@ is not a bare message.__
--
-- @
-- \"GENGCORE\"   8 bytes
-- \<varint\>     the schema version
-- \<bytes\>      one Module, to the end of the file
-- @
--
-- The magic is why a wrong file is diagnosable rather than a varint parse error
-- at offset 0, which is the failure @.greni@ has today: a corrupted cache file
-- reports @Byte Offset: 1 / Message: not enough bytes@ and nothing else.
--
-- The version is the __schema's__, bumped by hand for any change that is not a
-- pure addition at an unused tag. Not the compiler's, not a build hash, not a
-- timestamp: byte-identical Core is the gate, and a stamp that varied between
-- two builds of one compiler would break it before the second frontend existed.
module Core.Wire
  ( -- * The format
    magic,
    schemaVersion,

    -- * Encoding
    encode,
    encodeLazy,

    -- * Decoding
    decode,
    Protobuf.Error (..),
    Protobuf.renderError,
  )
where

import Core.AST qualified as Core
import Core.Wire.Decode qualified as Decode
import Core.Wire.Encode qualified as Encode
import Core.Wire.Protobuf qualified as Protobuf
import Data.ByteString qualified as BS
import Data.ByteString.Builder qualified as B
import Data.ByteString.Char8 qualified as BS8
import Data.ByteString.Lazy qualified as LBS
import Data.Word (Word64)

-- THE FILE

magic :: BS.ByteString
magic = BS8.pack "GENGCORE"

-- | Version 1. See the header of @schema/geng/core/v1.proto@ for what bumping
-- it means.
schemaVersion :: Word64
schemaVersion = 1

-- ENCODING

-- | A module's bytes, or the reasons there are none.
--
-- The failure list is D91's and nothing else: 'Core.AST.LIntLegacy' carries an
-- unbounded 'Integer' and the wire format carries a @sint64@. Every other
-- constructor in Core has a total encoding.
encode :: Core.Module -> Either [String] BS.ByteString
encode = fmap LBS.toStrict . encodeLazy

encodeLazy :: Core.Module -> Either [String] LBS.ByteString
encodeLazy m =
  case Encode.run (Encode.moduleEnc m) of
    Left problems -> Left problems
    Right body ->
      Right $
        B.toLazyByteString $
          B.byteString magic
            <> varintB schemaVersion
            <> body

varintB :: Word64 -> B.Builder
varintB n =
  if n < 0x80
    then B.word8 (fromIntegral n)
    else B.word8 (fromIntegral (n `mod` 0x80) + 0x80) <> varintB (n `div` 0x80)

-- DECODING

-- | A module, or the first thing wrong with the file.
--
-- The reader enforces the whole canonical profile (§B7), so "this decoded" and
-- "this was in canonical form" are the same statement. That is what lets the
-- gate assert @encode . decode . encode == encode@ and mean something by it.
decode :: BS.ByteString -> Either Protobuf.Error Core.Module
decode input
  | not (magic `BS.isPrefixOf` input) =
      Left (Protobuf.Error 0 [] "not a Core file: it does not start with GENGCORE")
  | otherwise =
      let rest = BS.drop (BS.length magic) input
       in case readVarint rest (BS.length magic) of
            Left err -> Left err
            Right (version, body, at)
              | version /= schemaVersion ->
                  Left
                    ( Protobuf.Error
                        (BS.length magic)
                        []
                        ( "this Core file is schema version "
                            ++ show version
                            ++ " and this compiler reads version "
                            ++ show schemaVersion
                        )
                    )
              | otherwise -> Decode.runP Decode.moduleP body at

-- | The version stamp, read before the message so that a version mismatch is
-- reported as one rather than as an unknown field.
--
-- __It is held to rule 2 like every other varint__, which it was not until
-- @harness/wire.py@ said so. The version is outside the @Module@ message and
-- so outside "Core.Wire.Decode", and a hand-written second reader is a place
-- for a rule to be forgotten — which is the argument for having one.
readVarint :: BS.ByteString -> Int -> Either Protobuf.Error (Word64, BS.ByteString, Int)
readVarint = go 0 0
  where
    go !shift !acc bs at =
      case BS.uncons bs of
        Nothing -> Left (Protobuf.Error at [] "the file ends before its schema version")
        Just (w, rest) ->
          let acc' = acc + (fromIntegral (w `mod` 0x80) * (2 ^ shift))
           in if w >= 0x80
                then go (shift + 7 :: Int) acc' rest (at + 1)
                else
                  if shift > (0 :: Int) && w == 0
                    then Left (Protobuf.Error at [] "the schema version's varint is not minimally encoded")
                    else Right (acc', rest, at + 1)
