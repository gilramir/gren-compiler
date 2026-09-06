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
    linkEveryExport,
    corePasses,
    spikeFile,
    spikeRoot,
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

-- | @GENG_LINK_ROOTS=exports@: link from every module's exports rather than from
-- the program's @main@.
--
-- A measurement rather than a mode. What a program reaches depends on the
-- program; what @core@ and @node@ reach between them is a property of those
-- packages, and it is the number the kernel decision needs
-- (@docs/m1a-js-on-core.md@ §J3 item 3). Nothing but a dump reads it.
linkEveryExport :: Bool
linkEveryExport =
  unsafePerformIO ((== Just "exports") <$> Env.lookupEnv "GENG_LINK_ROOTS")
{-# NOINLINE linkEveryExport #-}

-- | @GENG_CORE_PASSES=case,tailcall@: which Core→Core passes to run before the
-- backend reads the program.
--
-- Off by default, because C11 gives M1a's pipeline no passes and C4 says the
-- decision-tree pass is optional in the first place. A switch is also what lets
-- the corpus run the same programs with and without them, which is the
-- obligation C12 attaches to @accept\/pattern-shapes@.
corePasses :: [String]
corePasses =
  unsafePerformIO (maybe [] (splitOn ',') <$> Env.lookupEnv "GENG_CORE_PASSES")
{-# NOINLINE corePasses #-}

-- | @GENG_SPIKE_C@: where the Core → C spike writes its C, if it is asked at
-- all. Unset — which is every build but a spike run — and nothing happens.
--
-- A file and an environment variable rather than a @geng make --output=x.c@,
-- because @docs/m1a-c-spike.md@ §X10 is explicit that the spike is __not a
-- backend__: it has no CLI surface, no target in @harness/run.py@ and no
-- corpus. This is the same shape 'linkFile' has and for the same reason —
-- a measurement hung off a build, not a mode of one.
spikeFile :: Maybe FilePath
spikeFile =
  unsafePerformIO (Env.lookupEnv "GENG_SPIKE_C")
{-# NOINLINE spikeFile #-}

-- | @GENG_SPIKE_ROOT=Spike.IntArith.answer@: the binding the spike links from.
--
-- §X3, and it is the whole reason the spike is affordable. Rooting at @main@
-- links 56 bindings and 26 kernel JavaScript functions before the program says
-- anything — a @Program@, and therefore @Task@, @Platform@, @Scheduler@,
-- @Json@ and @Process@ — and hand-writing those in C is a runtime rather than a
-- spike. Rooting at a scalar binding links the arithmetic and its six kernel
-- names. 'Core.Program.link' takes its roots as a plain list, so this is an
-- argument and not a mechanism.
--
-- The module is everything before the last dot and the binding is what follows
-- it; the package is the application's, which only the caller knows.
spikeRoot :: Maybe (String, String)
spikeRoot =
  fmap splitLast (unsafePerformIO (Env.lookupEnv "GENG_SPIKE_ROOT"))
{-# NOINLINE spikeRoot #-}

-- | @"Spike.IntArith.answer"@ to @("Spike.IntArith", "answer")@.
splitLast :: String -> (String, String)
splitLast s =
  case break (== '.') (reverse s) of
    (name, _ : home) -> (reverse home, reverse name)
    (name, []) -> ("", reverse name)

splitOn :: Char -> String -> [String]
splitOn sep s =
  case break (== sep) s of
    (word, []) -> [word | not (null word)]
    (word, _ : rest) -> [word | not (null word)] ++ splitOn sep rest

-- | An empty value means the current directory, so that @VAR=@ is not silently
-- the same as unset.
dirFromEnv :: String -> IO (Maybe FilePath)
dirFromEnv name =
  fmap (\dir -> if null dir then "." else dir) <$> Env.lookupEnv name
