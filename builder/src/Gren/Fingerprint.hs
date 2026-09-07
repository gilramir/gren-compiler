{-# OPTIONS_GHC -Wall #-}

-- | What a build was made from, as a number.
--
-- __The artifact cache is keyed on content and not on time__ (D96), and this is
-- what "content" is. Stock keys its cache on the modification time of
-- @gren.json@ and on the modification time of each source file, because stock
-- reads those files itself and a time is the cheapest thing it has. This fork
-- does not read them: the frontend hands the builder every byte it will
-- compile — the project's sources and every dependency's — before the build
-- starts (@Gren.Details.Dependency@, @Build.Sources@). So the question "is this
-- the same source I compiled last time" can be asked of the bytes, which is
-- the same discipline C6 and C10 apply to the wire format: state the thing over
-- the content, never over a property the content happens to have had.
--
-- What that buys, in both directions:
--
--   * @touch@ing a file, or a @git checkout@ that restores it unchanged, does
--     not invalidate anything. A time-keyed cache recompiles.
--   * two edits inside one filesystem timestamp tick both invalidate. A
--     time-keyed cache misses the second, and the coarser the filesystem's
--     timestamps the wider that window is.
--
-- __This is a count and a 64-bit FNV-1a, and it is not a cryptographic hash__
-- (D97). Two different sources with the same length and the same hash would be
-- reported as the same source, and the compiler would reuse an artifact it
-- should have rebuilt. Nothing here defends against someone constructing that
-- pair on purpose; what it defends against is the ordinary case, where the
-- chance is the 2^-64 of the hash narrowed further by the length having to
-- agree. It is strictly stronger than the modification time it replaces, which
-- collides whenever a filesystem's clock is coarser than a person's editing,
-- and the cost of being wrong is bounded the same way it is for a stale
-- artifact of any kind: @rm -rf .gren@, and every rebuild of the compiler gets
-- a fresh 'Directories.artifactKey' anyway.
module Gren.Fingerprint
  ( Fingerprint,
    empty,
    bytes,
    chars,
    word64,
    ofBytes,
    toHex,
  )
where

import Data.Binary (Binary, get, put)
import Data.Bits (shiftR, xor, (.&.))
import Data.ByteString qualified as BS
import Data.ByteString.UTF8 qualified as BS_UTF8
import Data.List qualified as List
import Data.Word (Word64, Word8)
import Numeric qualified

-- | How many bytes went in, and FNV-1a over them.
--
-- The count is not redundant with the hash. It is free — the fold is already
-- walking the bytes — and it takes the failure above from "these two byte
-- strings collide" to "these two byte strings collide /and/ are the same
-- length".
data Fingerprint
  = Fingerprint !Word64 !Word64
  deriving (Eq, Ord, Show)

-- | Nothing fed in yet: no bytes, and FNV-1a's offset basis.
empty :: Fingerprint
empty =
  Fingerprint 0 0xcbf29ce484222325

-- | Feed a run of bytes, __length first__.
--
-- The length prefix is what makes the fold injective over a sequence of runs.
-- Without it a module named @Ab@ holding @c@ and one named @A@ holding @bc@
-- feed the same bytes in the same order, and a fingerprint of a whole
-- dependency set is exactly such a sequence — package names, module names and
-- sources, one after another. It is D94's length-prefixed sort key again, in a
-- different place and for the same reason.
bytes :: BS.ByteString -> Fingerprint -> Fingerprint
bytes bs fp =
  BS.foldl' step (word64 (fromIntegral (BS.length bs)) fp) bs

-- | Feed text, as its UTF-8 bytes and length first. Module and package names
-- reach this as 'String's.
chars :: String -> Fingerprint -> Fingerprint
chars =
  bytes . BS_UTF8.fromString

-- | Feed a number, as eight bytes, least significant first.
word64 :: Word64 -> Fingerprint -> Fingerprint
word64 n fp =
  List.foldl' step fp [fromIntegral ((n `shiftR` (8 * i)) .&. 0xff) | i <- [0 .. 7 :: Int]]

step :: Fingerprint -> Word8 -> Fingerprint
step (Fingerprint count hash) w =
  Fingerprint (count + 1) ((hash `xor` fromIntegral w) * 0x100000001b3)

-- | One run of bytes and nothing else.
ofBytes :: BS.ByteString -> Fingerprint
ofBytes bs =
  bytes bs empty

-- | The hash alone, as sixteen hex digits, for somewhere a name is wanted
-- rather than a comparison — 'Directories.artifactKey' is the one caller.
toHex :: Fingerprint -> String
toHex (Fingerprint _ hash) =
  let hex = Numeric.showHex hash ""
   in replicate (16 - length hex) '0' ++ hex

instance Binary Fingerprint where
  put (Fingerprint a b) = put a >> put b
  get = Fingerprint <$> get <*> get
