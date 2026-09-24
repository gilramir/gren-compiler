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
--   * @GENG_DUMP_PASSED@ is written by @Generate@ too, after "Core.Pass" has
--     run: the Core a backend actually reads, printed and encoded side by side
--     (X19). The first two are pre-pass Core by C11; this is the one a Geng
--     port of the passes is held to.
--
-- The file names are the same in both, so the two directories can be compared
-- directly, and equal directories are the property M1a's plumbing has to have:
-- the Core the backend is handed is the Core the frontend lowered, for every
-- module, with nothing dropped on the way. @harness/core-golden.py@ checks it.
module Core.Dump
  ( fileName,
    wireFileName,
    writeModule,
    writeWire,
    moduleDir,
    programDir,
    linkFile,
    primsFile,
    wireRoundTrip,
    wireDir,
    passedDir,
    linkEveryExport,
    corePasses,
    specializeStrict,
    specializeReport,
    externBodies,
    spikeFile,
    spikeRoot,
  )
where

import Data.ByteString.Builder qualified as B
import Data.List qualified as List
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import System.Directory qualified as Dir
import System.Environment qualified as Env
import System.FilePath ((<.>), (</>))
import System.IO.Unsafe (unsafePerformIO)

-- | One flat directory, one file per module, named so that two packages with
-- the same module name do not collide. A package identifier has slashes in it,
-- which a file name cannot, so its path elements are escaped as a JavaScript
-- name's are (D296) and joined by dashes: @core.Basics.core@, and
-- @github_dcom-geng_hlanguage-node.FileSystem.core@. An escaped element has no
-- dot and no dash, so the first dot ends the package.
fileName :: ModuleName.Canonical -> FilePath
fileName home = baseName home <.> "core"

baseName :: ModuleName.Canonical -> FilePath
baseName (ModuleName.Canonical pkg raw) =
  let package = List.intercalate "-" (Pkg.escapedSegments pkg)
   in package ++ "." ++ ModuleName.toChars raw

-- | The same name with the wire format's extension, so that a dump directory
-- holds @Pkg.Module.core@ and @Pkg.Module.corepb@ side by side and the two
-- forms of one module sort together.
wireFileName :: ModuleName.Canonical -> FilePath
wireFileName home = baseName home <.> "corepb"

writeModule :: FilePath -> ModuleName.Canonical -> B.Builder -> IO ()
writeModule dir home builder =
  do
    Dir.createDirectoryIfMissing True dir
    B.writeFile (dir </> fileName home) builder

writeWire :: FilePath -> ModuleName.Canonical -> B.Builder -> IO ()
writeWire dir home builder =
  do
    Dir.createDirectoryIfMissing True dir
    B.writeFile (dir </> wireFileName home) builder

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

-- | @GENG_DUMP_PRIMS@: a file, like @GENG_DUMP_LINK@'s, listing which of the
-- live primitives the linked program reaches and which it does not (D337).
primsFile :: Maybe FilePath
primsFile =
  unsafePerformIO (Env.lookupEnv "GENG_DUMP_PRIMS")
{-# NOINLINE primsFile #-}

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

-- | @GENG_SPECIALIZE_STRICT=1@: refuse to emit a program that still carries a
-- witness node (§G27.4, D127).
--
-- The specializer is allowed to give up on a site — the witness path it erases
-- is a correct one — so this is not on by an ordinary build. It is on for
-- @harness/run.py@'s @geng-hs-spec@ target, which turns "the pass is complete
-- on every program the corpus has" from a thing measured once into a thing that
-- goes red when it stops being true, and names the binding when it does.
specializeStrict :: Bool
specializeStrict =
  unsafePerformIO ((== Just "1") <$> Env.lookupEnv "GENG_SPECIALIZE_STRICT")
{-# NOINLINE specializeStrict #-}

-- | @GENG_SPECIALIZE_REPORT@: a file, like @GENG_DUMP_LINK@'s, where @Generate@
-- writes the reachable bindings that still carry a witness or type-abstraction
-- node, one per line and sorted, and then builds as usual.
--
-- It is 'specializeStrict' as a measurement rather than a refusal, for a
-- program that has to run whatever the answer is: @harness/suites.py@ holds
-- each suite's list to the one recorded for it (§G54.6, D356), where strict
-- mode would refuse a suite the pass gives up on for a registered reason.
specializeReport :: Maybe FilePath
specializeReport =
  unsafePerformIO (Env.lookupEnv "GENG_SPECIALIZE_REPORT")
{-# NOINLINE specializeReport #-}

-- | @GENG_EXTERN_BODIES=1@: every extern with a Geng body is compiled as its
-- body, even where the backend has an implementation for it (D225,
-- @m1b-json.md@ §O17).
--
-- Off by default, since the implementation is why the extern has a row. On for
-- @harness/run.py@'s @geng-hs-bodies@ target, which is how the corpus holds an
-- implementation and its body to the same answers.
externBodies :: Bool
externBodies =
  unsafePerformIO ((== Just "1") <$> Env.lookupEnv "GENG_EXTERN_BODIES")
{-# NOINLINE externBodies #-}

-- | @GENG_CORE_PASSES@: which Core→Core passes run before the backend reads
-- the program.
--
-- __All three by default__ (@docs/m1b-classes.md@ §G47.7, D169). Without
-- @specialize@ every class method is a witness projection at run time, which
-- §G47.5 measured at 5.5× stock for a loop of @<@ and 2.4× for a @Dict@, and
-- §G47.6 found specialization costs no bundle size. M1a's pipeline had none
-- (C11) and this was off until M1b's classes made "off" the slow program.
--
-- The switch stays, because C4 says the passes are optional and C12 asks that
-- the same programs answer the same with and without them:
--
-- > GENG_CORE_PASSES=none          -- no passes (the harness's geng-hs-nopasses)
-- > GENG_CORE_PASSES=specialize    -- one of them
-- > GENG_CORE_PASSES=case,tailcall -- any list
corePasses :: [String]
corePasses =
  unsafePerformIO (fromSetting <$> Env.lookupEnv "GENG_CORE_PASSES")
  where
    fromSetting setting =
      case setting of
        Nothing -> ["specialize", "inline", "case", "tailcall"]
        Just "none" -> []
        Just "" -> []
        Just list -> splitOn ',' list
{-# NOINLINE corePasses #-}

-- | @GENG_WIRE=1@: put every module through the wire format before the backend
-- sees it — encode it, decode the bytes back, and hand the backend what came
-- out.
--
-- D90, and the reason it is a switch on an ordinary build rather than a test:
-- a codec that nothing calls is a codec whose bugs are found at M2. With this
-- on, @harness/run.py@'s @geng-hs-wire@ target runs the whole corpus through
-- the bytes and fails on a program that computes a different answer, which no
-- round-trip assertion can do.
--
-- Twice per build since X19: once as the frontend's Core is assembled, and
-- once after "Core.Pass", so that what a backend reads has been through the
-- bytes too.
wireRoundTrip :: Bool
wireRoundTrip =
  unsafePerformIO ((== Just "1") <$> Env.lookupEnv "GENG_WIRE")
{-# NOINLINE wireRoundTrip #-}

-- | @GENG_DUMP_WIRE@: where the encoded modules are written, if anywhere.
--
-- 'programDir' with different bytes: one file per module of the whole program,
-- named so that it sorts beside the text dump. @harness/wire.py@ reads these
-- with a decoder built from the schema alone.
wireDir :: Maybe FilePath
wireDir =
  unsafePerformIO (dirFromEnv "GENG_DUMP_WIRE")
{-# NOINLINE wireDir #-}

-- | @GENG_DUMP_PASSED@: where the program's Core is written after the passes,
-- each module twice, as @Pkg.Module.core@ and @Pkg.Module.corepb@.
--
-- The other dumps are pre-pass Core, because they are written where the
-- frontend's output is assembled and C11 pins that. But the passes are what a
-- backend reads, and C11 moves them to a Geng program at M2 whose output has to
-- be byte-identical to "Core.Pass"'s; nothing held that output until this
-- (@warts.md@ X19). Both forms, because @harness/core-golden.py@ pins the
-- printed one and @harness/wire.py@ counts the nodes in the encoded one — the
-- join points and jumps no pre-pass dump can contain.
passedDir :: Maybe FilePath
passedDir =
  unsafePerformIO (dirFromEnv "GENG_DUMP_PASSED")
{-# NOINLINE passedDir #-}

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
