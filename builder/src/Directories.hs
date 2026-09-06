module Directories
  ( details,
    interfaces,
    greni,
    artifactKey,
    findRoot,
    PackageCache,
    getPackageCache,
    package,
    getReplCache,
    getGrenHome,
  )
where

import Data.Bits (xor)
import Data.List qualified as List
import Data.Word (Word64)
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Gren.Version qualified as V
import Numeric qualified
import System.Directory qualified as Dir
import System.Environment qualified as Env
import System.FilePath ((<.>), (</>))
import System.FilePath qualified as FP
import System.IO.Unsafe (unsafePerformIO)

-- PATHS

projectCache :: FilePath -> FilePath
projectCache root =
  root </> ".gren" </> artifactKey

details :: FilePath -> FilePath
details root =
  projectCache root </> "d.dat"

interfaces :: FilePath -> FilePath
interfaces root =
  projectCache root </> "i.dat"

compilerVersion :: FilePath
compilerVersion =
  V.toChars V.compiler

-- ARTIFACT KEY

-- | Names the compiler *build* that wrote the artifacts under `.gren/<key>/`.
--
-- Stock keys that directory on the language version, which is the version a
-- project's `gren-version` is checked against. Those are two different
-- questions, and this fork is exactly the case that separates them: it answers
-- the language question the same way stock does on purpose, so that every
-- existing project and every corpus case still compiles, while writing
-- artifacts stock would not have written. Sharing a directory with stock on the
-- strength of a version they agree on by design is how a stale artifact becomes
-- a wrong answer with nothing on screen to say so.
--
-- So the key is the language version, the fork's name, and a fingerprint of the
-- backend executable: its canonical path, its size and its modification time.
-- Every rebuild of the fork therefore gets a fresh key. That is the point: the
-- alternative is a revision number bumped by hand whenever an artifact changes
-- shape, and the failure mode of forgetting to bump it is a silently wrong
-- build. Throwing the artifacts away costs nothing worth counting -- see
-- `docs/upstream/compiler-artifact-cache-is-write-only.md`, which measures a
-- cold build and a warm one at the same speed because today nothing reads them
-- back at all.
{-# NOINLINE artifactKey #-}
artifactKey :: FilePath
artifactKey =
  unsafePerformIO $
    do
      exe <- Dir.canonicalizePath =<< Env.getExecutablePath
      size <- Dir.getFileSize exe
      time <- Dir.getModificationTime exe
      let identity = List.intercalate "\0" [exe, show size, show time]
      return (compilerVersion ++ "-geng." ++ fingerprint identity)

-- | FNV-1a, 64-bit, as sixteen hex digits. Not a cryptographic hash and it does
-- not need to be: it names an executable the compiler just stat'ed, and the
-- only thing it has to do is differ when the executable does.
fingerprint :: String -> String
fingerprint =
  pad . flip Numeric.showHex "" . List.foldl' step 0xcbf29ce484222325
  where
    step :: Word64 -> Char -> Word64
    step hash char =
      (hash `xor` fromIntegral (fromEnum char)) * 0x100000001b3

    pad :: String -> String
    pad hex =
      replicate (16 - length hex) '0' ++ hex

-- GRENI

-- | A module's interface. There was a @.greno@ beside it holding that module's
-- @Opt.LocalGraph@, and an @o.dat@ holding the dependencies' folded into one
-- graph; both went with the pipeline that read them. Neither was ever read back
-- (@docs\/upstream\/compiler-artifact-cache-is-write-only.md@), so nothing that
-- worked stops working — but the day the cache is restored, what a module needs
-- beside its interface is its Core, which is C10's wire format and has its own
-- gate.
greni :: FilePath -> ModuleName.Raw -> FilePath
greni root name =
  toArtifactPath root name "greni"

toArtifactPath :: FilePath -> ModuleName.Raw -> String -> FilePath
toArtifactPath root name ext =
  projectCache root </> ModuleName.toHyphenPath name <.> ext

-- ROOT

findRoot :: IO (Maybe FilePath)
findRoot =
  do
    dir <- Dir.getCurrentDirectory
    findRootHelp (FP.splitDirectories dir)

findRootHelp :: [String] -> IO (Maybe FilePath)
findRootHelp dirs =
  case dirs of
    [] ->
      return Nothing
    _ : _ ->
      do
        exists <- Dir.doesFileExist (FP.joinPath dirs </> "gren.json")
        if exists
          then return (Just (FP.joinPath dirs))
          else findRootHelp (init dirs)

-- PACKAGE CACHES

newtype PackageCache = PackageCache FilePath

getPackageCache :: IO PackageCache
getPackageCache =
  PackageCache <$> getCacheDir "packages"

package :: PackageCache -> Pkg.Name -> V.Version -> FilePath
package (PackageCache dir) name version =
  dir </> Pkg.toFilePath name </> V.toChars version

-- CACHE

getReplCache :: IO FilePath
getReplCache =
  getCacheDir "repl"

getCacheDir :: FilePath -> IO FilePath
getCacheDir projectName =
  do
    home <- getGrenHome
    let root = home </> compilerVersion </> projectName
    Dir.createDirectoryIfMissing True root
    return root

getGrenHome :: IO FilePath
getGrenHome =
  do
    maybeCustomHome <- Env.lookupEnv "GREN_HOME"
    case maybeCustomHome of
      Just customHome -> return customHome
      Nothing -> Dir.getXdgDirectory Dir.XdgCache "gren"
