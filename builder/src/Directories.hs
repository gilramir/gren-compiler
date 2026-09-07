module Directories
  ( details,
    interfaces,
    cores,
    kernels,
    greni,
    grenc,
    artifactKey,
    findRoot,
    PackageCache,
    getPackageCache,
    package,
    getReplCache,
    getGrenHome,
  )
where

import Data.List qualified as List
import Gren.Fingerprint qualified as Fingerprint
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Gren.Version qualified as V
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

-- | The dependencies' interfaces, their Core and their kernel JavaScript.
--
-- One file each, all three written by 'Gren.Details.verifyDependencies' and all
-- three required before @d.dat@ may be believed (D98). @i.dat@ had a reader and
-- no writer until this landed; @c.dat@ and @k.dat@ are new, because Core and
-- the kernel chunks did not travel this way before M1a re-targeted the backend.
interfaces :: FilePath -> FilePath
interfaces root =
  projectCache root </> "i.dat"

cores :: FilePath -> FilePath
cores root =
  projectCache root </> "c.dat"

kernels :: FilePath -> FilePath
kernels root =
  projectCache root </> "k.dat"

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
fingerprint identity =
  Fingerprint.toHex (Fingerprint.chars identity Fingerprint.empty)

-- GRENI AND GRENC

-- | A module's interface, and its Core beside it.
--
-- There was a @.greno@ here holding the module's @Opt.LocalGraph@, and an
-- @o.dat@ holding the dependencies' folded into one graph; both went with the
-- pipeline that read them. What a module needs beside its interface now is its
-- __Core__, and @.grenc@ is that file: C10's wire format, byte for byte the
-- same thing @GENG_DUMP_WIRE@ writes and @harness/wire.py@ decodes (D98). The
-- cache is the first thing in the compiler that reads the wire format back in
-- anger, which is what D90 wanted for it.
greni :: FilePath -> ModuleName.Raw -> FilePath
greni root name =
  toArtifactPath root name "greni"

grenc :: FilePath -> ModuleName.Raw -> FilePath
grenc root name =
  toArtifactPath root name "grenc"

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
