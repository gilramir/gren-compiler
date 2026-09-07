module Directories
  ( details,
    greni,
    grenc,
    artifactKey,
    findRoot,
    PackageCache,
    getPackageCache,
    package,
    ArtifactCache,
    getArtifactCache,
    packageArtifacts,
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

-- | What the last build of __this project__ knew: its module list, each
-- module's imports and fingerprint, and the build numbers (D99).
--
-- It is the only file left in the project's cache that is not about one of the
-- project's own modules. @i.dat@, @c.dat@ and @k.dat@ were here too and are not
-- any more — the dependencies' artifacts do not depend on the project and are
-- shared between every project that compiles the same packages (D101,
-- 'packageArtifacts').
details :: FilePath -> FilePath
details root =
  projectCache root </> "d.dat"

compilerVersion :: FilePath
compilerVersion =
  V.toChars V.compiler

-- ARTIFACT KEY

-- | Names the compiler *build* that wrote an artifact -- both the project's,
-- under @<project>/.gren/<key>/@, and the dependencies', under
-- @~/.cache/gren/<key>/artifacts/@.
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
      return (compilerVersion ++ "-geng." ++ hashOf identity)

-- | FNV-1a, 64-bit, as sixteen hex digits. Not a cryptographic hash and it does
-- not need to be: it names an executable the compiler just stat'ed, and the
-- only thing it has to do is differ when the executable does.
hashOf :: String -> String
hashOf identity =
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

-- ARTIFACT CACHE

-- | Where a compiled dependency goes, and it is not in the project (D101).
--
-- Compiling @gren-lang\/core@ produces the same interfaces, the same Core and
-- the same kernel chunks for every project that compiles it against the same
-- versions of the same packages with the same compiler. Writing that into
-- @<project>\/.gren\/@ made every project and every fresh checkout pay for it
-- again — 175 ms, essentially all of it encoding Core to C10
-- (@docs\/m1a-cache.md@ §A6), and the reason §A9 said the files were in the
-- wrong place.
--
-- This is roughly where stock kept the same thing, as @artifacts.dat@ beside
-- the downloaded sources, before the half of the cache that read it was
-- removed. It is beside them rather than among them: 'PackageCache' holds what
-- was fetched from the registry and is the same for every compiler, and one
-- directory should not hold both that and this compiler build's output.
newtype ArtifactCache = ArtifactCache FilePath

-- | Under 'artifactKey' rather than under the language version, which is the
-- whole reason that key exists: these are artifacts stock would never have
-- written, and a directory shared with stock on the strength of a version
-- number they agree on by design is how a stale artifact becomes a wrong answer
-- with nothing on screen to say so. @~\/.cache\/gren\/0.6.3-geng.<hex>\/@ sits
-- beside @~\/.cache\/gren\/0.6.3\/@ and says which build wrote it.
getArtifactCache :: IO ArtifactCache
getArtifactCache =
  do
    home <- getGrenHome
    let root = home </> artifactKey </> "artifacts"
    Dir.createDirectoryIfMissing True root
    return (ArtifactCache root)

-- | One package version's artifacts, named by the fingerprint of everything
-- that went into them.
--
-- The fingerprint is 'Gren.Details.packageFingerprints': the package's name and
-- version, every byte of its sources, and the fingerprints of the packages it
-- was compiled against. The name and version are in the path as well as in the
-- fingerprint, so that the directory can be read by a person; the fingerprint
-- is what makes the file correct. Nothing overwrites anything — a package built
-- against a different solution gets a different name, which is why two projects
-- with different dependency sets do not evict each other and why a local-path
-- dependency needs no special case at all.
packageArtifacts :: ArtifactCache -> Pkg.Name -> V.Version -> Fingerprint.Fingerprint -> FilePath
packageArtifacts (ArtifactCache dir) name version fingerprint =
  dir </> Pkg.toFilePath name </> V.toChars version </> Fingerprint.toName fingerprint <.> "dat"

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
