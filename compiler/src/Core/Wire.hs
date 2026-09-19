{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | The Core wire format: the file, and the two directions.
--
-- @schema/geng/core/v7.proto@ in the @geng-lang@ repository is the schema of
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
-- \<varint\>     which message follows: 0 a Module, 1 a Program
-- \<bytes\>      that message, to the end of the file
-- @
--
-- The kind varint is version 7's (D379). Until then the file held one
-- 'Core.AST.Module' and the message was the format; a second top-level message
-- means a reader has to be told which it is holding rather than infer it from
-- a file name or from which tags happen to parse.
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
    Kind (..),

    -- * Encoding
    encode,
    encodeLazy,
    encodeProgram,

    -- * Decoding
    decode,
    decodeProgram,
    kindOfFile,
    Protobuf.Error (..),
    Protobuf.renderError,
  )
where

import Core.AST qualified as Core
import Core.Whole qualified as Whole
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

-- | Version 7. See the header of @schema/geng/core/v7.proto@ for what bumping
-- it means. D92 made strings indices into a table the module carries, D93 did
-- the same for qualified names and D94 for types; D95 is the one that is not a
-- table, because 86.7% of spans are distinct and interning them costs more than
-- writing them out. Each time because the measurement said that was where the
-- bytes had moved to. D336 is the one that is a stamp and nothing else: version
-- 5 had absorbed deleted and added tags without a bump while this binary was
-- the only reader, and M2's reader is the first that is not. D378 and D379 are
-- version 7: the 'Whole.Program' message, and the kind varint that says which
-- message the file holds. It is a bump because the /header/ changed — a
-- version-6 file read as a version-7 one would take the @Module@'s first key
-- byte for the kind.
schemaVersion :: Word64
schemaVersion = 7

-- | Which message a file holds. The codes are the schema's.
data Kind
  = KindModule
  | KindProgram
  deriving (Eq, Show)

kindCode :: Kind -> Word64
kindCode KindModule = 0
kindCode KindProgram = 1

kindOf :: Word64 -> Maybe Kind
kindOf 0 = Just KindModule
kindOf 1 = Just KindProgram
kindOf _ = Nothing

kindName :: Kind -> String
kindName KindModule = "a module"
kindName KindProgram = "a program"

-- ENCODING

-- | A module's bytes, or the reasons there are none.
--
-- __The failure list is now only ever an internal invariant.__ It was D91's and
-- nothing else — the transitional @LIntLegacy@ carried an unbounded 'Integer'
-- and the wire format carries a @sint64@ — and D2's flag day deleted that
-- constructor (@docs\/m1b-int.md@ §I20). Every constructor in Core has a total
-- encoding now; what is left to report is a name or a type missing from its
-- table, which is a bug in this module rather than in a program.
encode :: Core.Module -> Either [String] BS.ByteString
encode = fmap LBS.toStrict . encodeLazy

encodeLazy :: Core.Module -> Either [String] LBS.ByteString
encodeLazy = framed KindModule . Encode.moduleEnc

-- | A program's bytes (D378): the same file, with the kind varint saying so.
encodeProgram :: Whole.Program -> Either [String] BS.ByteString
encodeProgram = fmap LBS.toStrict . framed KindProgram . Encode.programEnc

framed :: Kind -> Encode.Enc -> Either [String] LBS.ByteString
framed kind enc =
  case Encode.run enc of
    Left problems -> Left problems
    Right body ->
      Right $
        B.toLazyByteString $
          B.byteString magic
            <> varintB schemaVersion
            <> varintB (kindCode kind)
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
decode = entered KindModule Decode.moduleP

-- | A program, or the first thing wrong with the file (D378).
decodeProgram :: BS.ByteString -> Either Protobuf.Error Whole.Program
decodeProgram = entered KindProgram Decode.programP

-- | The header, and then the message the caller came for. A file of the other
-- kind is refused by name: it is a Core file, and saying only that a field is
-- unknown would be the report of a corrupt one.
entered :: Kind -> Decode.P a -> BS.ByteString -> Either Protobuf.Error a
entered wanted parser input =
  case header input of
    Left err -> Left err
    Right (kind, body, at)
      | kind /= wanted ->
          Left
            ( Protobuf.Error
                (BS.length magic)
                []
                ( "this Core file holds "
                    ++ kindName kind
                    ++ " and this reader wants "
                    ++ kindName wanted
                )
            )
      | otherwise -> Decode.runP parser body at

-- | Which message a file says it holds, for a caller that reads either one.
kindOfFile :: BS.ByteString -> Either Protobuf.Error Kind
kindOfFile input = (\(kind, _, _) -> kind) <$> header input

-- | The magic, the version and the kind, each checked in that order so that a
-- wrong file, an old file and an unknown kind are three different reports.
header :: BS.ByteString -> Either Protobuf.Error (Kind, BS.ByteString, Int)
header input
  | not (magic `BS.isPrefixOf` input) =
      Left (Protobuf.Error 0 [] "not a Core file: it does not start with GENGCORE")
  | otherwise =
      let rest = BS.drop (BS.length magic) input
       in case readVarint "schema version" rest (BS.length magic) of
            Left err -> Left err
            Right (version, afterVersion, at)
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
              | otherwise ->
                  case readVarint "kind" afterVersion at of
                    Left err -> Left err
                    Right (code, body, at') ->
                      case kindOf code of
                        Nothing ->
                          Left
                            ( Protobuf.Error
                                at
                                []
                                ( "this Core file says its kind is "
                                    ++ show code
                                    ++ ", and this compiler knows 0 (a module) and 1 (a program)"
                                )
                            )
                        Just kind -> Right (kind, body, at')

-- | The version stamp, read before the message so that a version mismatch is
-- reported as one rather than as an unknown field.
--
-- __It is held to rule 2 like every other varint__, which it was not until
-- @harness/wire.py@ said so. The version is outside the @Module@ message and
-- so outside "Core.Wire.Decode", and a hand-written second reader is a place
-- for a rule to be forgotten — which is the argument for having one.
--
-- __And it was forgotten once more__, the ten-byte limit this time
-- (@m1b-protobuf.md@ §Q19.2 in geng-lang). @2 ^ shift@ is 0 in 'Word64' from bit
-- 64 on, so an eleventh byte, or a tenth holding more than bit 63, added
-- nothing and the version still read as 5: two more encodings of one header.
-- The two checks are 'Core.Wire.Decode.varint'\'s, with its words.
readVarint :: String -> BS.ByteString -> Int -> Either Protobuf.Error (Word64, BS.ByteString, Int)
readVarint what input start = go 0 0 input start
  where
    go !shift !acc bs at =
      case BS.uncons bs of
        Nothing -> Left (Protobuf.Error at [] ("the file ends before its " ++ what))
        Just (w, rest) ->
          let acc' = acc + (fromIntegral (w `mod` 0x80) * (2 ^ shift))
           in if w >= 0x80
                then
                  if shift >= (63 :: Int)
                    then Left (Protobuf.Error start [] ("the " ++ what ++ "'s varint is longer than ten bytes"))
                    else go (shift + 7) acc' rest (at + 1)
                else
                  if shift > 0 && w == 0
                    then Left (Protobuf.Error at [] ("the " ++ what ++ "'s varint is not minimally encoded"))
                    else
                      if shift == 63 && w > 1
                        then Left (Protobuf.Error start [] ("the " ++ what ++ "'s varint overflows 64 bits"))
                        else Right (acc', rest, at + 1)
