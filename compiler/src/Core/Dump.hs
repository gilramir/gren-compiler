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
    jsFromCore,
    jsNative,
    corePasses,
    depsGap,
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

-- | @GENG_JS_FROM_CORE=1@: build the JS backend's input from Core.
--
-- A switch rather than a mode, for now: both paths are in the binary and the
-- differential harness runs the corpus through each (`docs/m1a-js-on-core.md`
-- §J3 items 6 and 7). It stops being a switch when the Core path answers
-- everything the old one does.
jsFromCore :: Bool
jsFromCore =
  unsafePerformIO ((== Just "1") <$> Env.lookupEnv "GENG_JS_FROM_CORE")
{-# NOINLINE jsFromCore #-}

-- | @GENG_JS_NATIVE=1@: generate JavaScript from the linked Core program,
-- with no @Opt.GlobalGraph@ anywhere in the path.
--
-- The end of §J3 item 6, where @GENG_JS_FROM_CORE@ is the middle of it: that one
-- builds the old backend's input out of Core and lets it walk the graph, this
-- one is "Generate.CoreJS" reading `Core.Program.link`'s output directly. A
-- switch for the same reason and with the same exit: both are in the binary so
-- that the differential harness can run the corpus through each, and it stops
-- being a switch when this path answers everything the old one does.
--
-- It implies @GENG_JS_FROM_CORE@ in the sense that it needs the program's Core,
-- but not in the sense that it needs the graph built from it: nothing in this
-- path reads a node.
jsNative :: Bool
jsNative =
  unsafePerformIO ((== Just "1") <$> Env.lookupEnv "GENG_JS_NATIVE")
{-# NOINLINE jsNative #-}

-- | @GENG_DEPS_GAP@: a file to write the dependency-set measurement to.
--
-- The Core path and @Optimize.*@ each decide what every definition refers to,
-- and they should agree; a passing corpus does not say that they do. This asks
-- for the difference instead, and it does not need @GENG_JS_FROM_CORE@: the
-- measurement compares two dependency sets and changes neither, so it can be
-- taken on a build that generates the old way (@docs\/m1a-js-on-core.md@ §J10,
-- §J14).
depsGap :: Maybe FilePath
depsGap =
  unsafePerformIO (Env.lookupEnv "GENG_DEPS_GAP")
{-# NOINLINE depsGap #-}

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
