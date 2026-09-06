{-# OPTIONS_GHC -Wall #-}

-- | Writing Core out for a human, and the two places that do it.
--
-- Nothing in the compiler consumes Core yet, so a dump is what forces the
-- lowering and therefore what tests it. There are two of them, and the point of
-- having both is that they are different questions:
--
--   * @GENG_DUMP_CORE@ is written by "Compile", one file per module, as each
--     module is compiled. It says what the frontend produced.
--   * @GENG_DUMP_PROGRAM_CORE@ is written by @Generate@, one file per module,
--     for every module of a whole program at once — the project's and its
--     dependencies'. It says what reached the backend.
--
-- The file names are the same in both, so the two directories can be compared
-- directly, and equal directories are the property M1a's plumbing has to have:
-- the Core the backend is handed is the Core the frontend lowered, for every
-- module, with nothing dropped on the way. @harness/core-golden.py@ checks it.
module Core.Dump
  ( fileName,
    writeModule,
    moduleDir,
    programDir,
    linkFile,
  )
where

import Data.ByteString.Builder qualified as B
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import System.Directory qualified as Dir
import System.Environment qualified as Env
import System.FilePath ((<.>), (</>))
import System.IO.Unsafe (unsafePerformIO)

-- | One flat directory, one file per module, named so that two packages with
-- the same module name do not collide. A package name has a slash in it, which
-- a file name cannot, so it becomes a dash.
fileName :: ModuleName.Canonical -> FilePath
fileName (ModuleName.Canonical pkg raw) =
  let package = map (\c -> if c == '/' then '-' else c) (Pkg.toChars pkg)
   in package ++ "." ++ ModuleName.toChars raw <.> "core"

writeModule :: FilePath -> ModuleName.Canonical -> B.Builder -> IO ()
writeModule dir home builder =
  do
    Dir.createDirectoryIfMissing True dir
    B.writeFile (dir </> fileName home) builder

-- | @GENG_DUMP_CORE@: where "Compile" writes each module as it is compiled.
moduleDir :: Maybe FilePath
moduleDir =
  unsafePerformIO (dirFromEnv "GENG_DUMP_CORE")
{-# NOINLINE moduleDir #-}

-- | @GENG_DUMP_PROGRAM_CORE@: where @Generate@ writes the whole program's.
programDir :: Maybe FilePath
programDir =
  unsafePerformIO (dirFromEnv "GENG_DUMP_PROGRAM_CORE")
{-# NOINLINE programDir #-}

-- | @GENG_DUMP_LINK@: a file, not a directory — one linked program per build, and
-- @Core.Program.render@ writes a summary rather than the program itself.
linkFile :: Maybe FilePath
linkFile =
  unsafePerformIO (Env.lookupEnv "GENG_DUMP_LINK")
{-# NOINLINE linkFile #-}

-- | An empty value means the current directory, so that @VAR=@ is not silently
-- the same as unset.
dirFromEnv :: String -> IO (Maybe FilePath)
dirFromEnv name =
  fmap (\dir -> if null dir then "." else dir) <$> Env.lookupEnv name
