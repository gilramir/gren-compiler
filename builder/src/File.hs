module File
  ( Time,
    zeroTime,
    writeBinary,
    writeBinaryAtomic,
    readBinary,
    writeBytes,
    readBytes,
    writeUtf8,
    readUtf8,
    writeBuilder,
    exists,
    remove,
    removeDir,
  )
where

import Control.Exception (catch, onException)
import Data.Binary qualified as Binary
import Data.ByteString qualified as BS
import Data.ByteString.Builder qualified as B
import Data.ByteString.Internal qualified as BS
import Data.ByteString.Lazy qualified as BSL
import Data.Fixed qualified as Fixed
import Foreign.ForeignPtr qualified as FPtr
import GHC.IO.Exception (IOErrorType (InvalidArgument), IOException)
import System.Directory qualified as Dir
import System.FilePath ()
import System.FilePath qualified as FP
import System.IO qualified as IO
import System.IO.Error (annotateIOError, ioeGetErrorType, modifyIOError)

-- TIME

newtype Time = Time Fixed.Pico
  deriving (Eq, Ord)

zeroTime :: Time
zeroTime =
  Time 0

instance Binary.Binary Time where
  put (Time time) = Binary.put time
  get = Time <$> Binary.get

-- BINARY

writeBinary :: (Binary.Binary a) => FilePath -> a -> IO ()
writeBinary path value =
  do
    let dir = FP.dropFileName path
    Dir.createDirectoryIfMissing True dir
    Binary.encodeFile path value

-- | Write to a temporary file in the same directory and rename it into place.
--
-- __For the shared artifact cache, and only for it__ (D101). Everything under
-- @<project>\/.gren\/@ belongs to one project, and two builds of one project at
-- once were already a race that nothing here pretends to settle. The package
-- cache is different: it is one directory that every project on the machine
-- writes, so two unrelated builds compiling the same package version at the
-- same moment is ordinary rather than a mistake, and the loser of that race
-- must leave a whole file behind rather than a truncated one. @rename@ within a
-- directory is atomic on every filesystem this compiler runs on, and both
-- writers are writing the same bytes anyway — the file name is the fingerprint
-- of what went into it.
writeBinaryAtomic :: (Binary.Binary a) => FilePath -> a -> IO ()
writeBinaryAtomic path value =
  do
    let dir = FP.dropFileName path
    Dir.createDirectoryIfMissing True dir
    (temp, handle) <- IO.openBinaryTempFile dir (FP.takeFileName path ++ ".tmp")
    onException
      ( do
          BSL.hPut handle (Binary.encode value)
          IO.hClose handle
          Dir.renameFile temp path
      )
      (IO.hClose handle >> remove temp)

-- | A cached artifact, or 'Nothing' if it is not there or will not decode.
--
-- __A file that will not decode is a recoverable condition and says so.__ It
-- used to print eight lines ending in "Please report this to
-- https:\/\/github.com\/gren-lang\/compiler\/issues", which was wrong on both
-- counts: every caller of this function reads the artifact cache, and every one
-- of them recompiles what it could not read, so the build is correct and
-- complete whatever happened here. A truncated file is what a killed build, a
-- full disk or a copied tree leaves behind, and asking the user to open an
-- issue about it is
-- @docs\/upstream\/compiler-artifact-cache-is-write-only.md@'s second
-- consequence. It was harmless while nothing read the cache back; this is the
-- change that makes it reachable, so it is the change that fixes it.
--
-- One line, still on stderr, because an artifact going bad under a key that
-- names this exact compiler build ('Directories.artifactKey') is worth
-- noticing even though nothing depends on it.
readBinary :: (Binary.Binary a) => FilePath -> IO (Maybe a)
readBinary path =
  do
    pathExists <- Dir.doesFileExist path
    if pathExists
      then do
        result <- Binary.decodeFileOrFail path
        case result of
          Right a ->
            return (Just a)
          Left (offset, message) ->
            do
              IO.hPutStrLn IO.stderr $
                "Ignoring an unreadable build artifact and recompiling: "
                  ++ path
                  ++ " (byte "
                  ++ show offset
                  ++ ": "
                  ++ message
                  ++ ")"
              return Nothing
      else return Nothing

-- RAW BYTES

-- | A file that is neither @Data.Binary@ nor text.
--
-- @.grenc@ is the only one: C10's wire format, which has a schema, two codecs
-- and a gate of its own, and which must reach the disk exactly as
-- 'Core.Wire.encode' produced it. Going through 'writeUtf8' would work by
-- accident — it is 'BS.hPut' under a handle whose encoding does not apply to
-- it — and would be a lie about the file.
writeBytes :: FilePath -> BS.ByteString -> IO ()
writeBytes path content =
  do
    Dir.createDirectoryIfMissing True (FP.dropFileName path)
    BS.writeFile path content

-- | Nothing if the file is not there. A file that is there and unreadable
-- throws, as it does everywhere else in this module.
readBytes :: FilePath -> IO (Maybe BS.ByteString)
readBytes path =
  do
    there <- Dir.doesFileExist path
    if there
      then Just <$> BS.readFile path
      else return Nothing

-- WRITE UTF-8

writeUtf8 :: FilePath -> BS.ByteString -> IO ()
writeUtf8 path content =
  withUtf8 path IO.WriteMode $ \handle ->
    BS.hPut handle content

withUtf8 :: FilePath -> IO.IOMode -> (IO.Handle -> IO a) -> IO a
withUtf8 path mode callback =
  IO.withFile path mode $ \handle ->
    do
      IO.hSetEncoding handle IO.utf8
      callback handle

-- READ UTF-8

readUtf8 :: FilePath -> IO BS.ByteString
readUtf8 path =
  withUtf8 path IO.ReadMode $ \handle ->
    modifyIOError (encodingError path) $
      do
        fileSize <- catch (IO.hFileSize handle) useZeroIfNotRegularFile
        let readSize = max 0 (fromIntegral fileSize) + 1
        hGetContentsSizeHint handle readSize (max 255 readSize)

useZeroIfNotRegularFile :: IOException -> IO Integer
useZeroIfNotRegularFile _ =
  return 0

hGetContentsSizeHint :: IO.Handle -> Int -> Int -> IO BS.ByteString
hGetContentsSizeHint handle =
  readChunks []
  where
    readChunks chunks readSize incrementSize =
      do
        fp <- BS.mallocByteString readSize
        readCount <- FPtr.withForeignPtr fp $ \buf -> IO.hGetBuf handle buf readSize
        let chunk = BS.PS fp 0 readCount
        if readCount < readSize && readSize > 0
          then return $! BS.concat (reverse (chunk : chunks))
          else readChunks (chunk : chunks) incrementSize (min 32752 (readSize + incrementSize))

encodingError :: FilePath -> IOError -> IOError
encodingError path ioErr =
  case ioeGetErrorType ioErr of
    InvalidArgument ->
      annotateIOError
        (userError "Bad encoding; the file must be valid UTF-8")
        ""
        Nothing
        (Just path)
    _ ->
      ioErr

-- WRITE BUILDER

writeBuilder :: FilePath -> B.Builder -> IO ()
writeBuilder path builder =
  IO.withBinaryFile path IO.WriteMode $ \handle ->
    do
      IO.hSetBuffering handle (IO.BlockBuffering Nothing)
      B.hPutBuilder handle builder

-- EXISTS

exists :: FilePath -> IO Bool
exists path =
  Dir.doesFileExist path

-- REMOVE FILES

remove :: FilePath -> IO ()
remove path =
  do
    exists_ <- Dir.doesFileExist path
    if exists_
      then Dir.removeFile path
      else return ()

removeDir :: FilePath -> IO ()
removeDir path =
  do
    exists_ <- Dir.doesDirectoryExist path
    if exists_
      then Dir.removeDirectoryRecursive path
      else return ()
