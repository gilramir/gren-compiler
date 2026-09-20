{-# OPTIONS_GHC -Wall #-}

-- | A build stopped after a stage, and a build started from one
-- (@m2-seam.md@ §DS5 item 4).
--
-- §DS3's seam is __Haskell frontend, wire, pass program, wire, backend__, and
-- until now nothing could cut it: the whole pipeline ran in one process, and
-- the wire was a round trip inside it rather than a file another program could
-- be handed. These two switches are the cut.
--
-- @
-- GENG_STAGE_WRITE=front:dir    -- run to the front end's Core, write it, stop
-- GENG_STAGE_READ=front:dir     -- take the front end's Core from there instead
-- GENG_STAGE_WRITE=passed:dir   -- run the passes, write the result, stop
-- GENG_STAGE_READ=passed:dir    -- hand the backend that instead
-- @
--
-- A directory holds one @.corepb@ per module, named as 'Core.Dump.wireFileName'
-- names them so that a stage directory and a @GENG_DUMP_WIRE@ one compare file
-- by file, and a @program.corepb@ beside them: the 'Core.Whole.Program' D378
-- put on the wire, which is what a stage needs and a module does not carry.
--
-- __Environment variables rather than flags on @geng make@__, for the reason
-- @m1a-c-spike.md@ §X10 gives the C spike: this is not a CLI surface the
-- language commits to. It is how @harness/run.py@'s staged target drives a
-- build that is three processes, and how the BEAM backend's own pipeline will
-- start. A stopped build writes no output file.
--
-- __A stage runs its dumps only in the process that runs it.__ A build resumed
-- from @front:dir@ did not assemble the front end's Core, so
-- @GENG_DUMP_PROGRAM_CORE@ writes nothing there; it does run the passes, so
-- @GENG_DUMP_PASSED@ writes as usual.
module Core.Stage
  ( Stage (..),
    stageName,
    readFrom,
    writeTo,
    checkPlan,
    write,
    read,
  )
where

import Core.AST qualified as Core
import Core.Dump qualified as Dump
import Core.Whole qualified as Whole
import Core.Wire qualified as Wire
import Data.ByteString qualified as BS
import Data.ByteString.Builder qualified as B
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Gren.ModuleName qualified as ModuleName
import System.Directory qualified as Dir
import System.Environment qualified as Env
import System.FilePath ((</>))
import System.FilePath qualified as FilePath
import System.IO.Unsafe (unsafePerformIO)
import Prelude hiding (read)

-- | Where a build can be cut. These are the two points §DS3 names, and the
-- two the Core on either side of is already pinned: 'Front' is what
-- @core-golden.py@ holds under @program/@ and 'Passed' what it holds under
-- @passed/@.
data Stage
  = Front
  | Passed
  deriving (Eq, Ord, Show)

stageName :: Stage -> String
stageName Front = "front"
stageName Passed = "passed"

stageFrom :: String -> Maybe Stage
stageFrom "front" = Just Front
stageFrom "passed" = Just Passed
stageFrom _ = Nothing

-- | @program.corepb@ cannot collide with a module's file name:
-- 'Core.Dump.wireFileName' is an escaped package, a dot and a module name, and
-- a module name is capitalized.
programFileName :: FilePath
programFileName = "program.corepb"

-- | @GENG_STAGE_READ=front:dir@: the stage this build starts at, and where its
-- Core is.
readFrom :: Maybe (Stage, FilePath)
readFrom = unsafePerformIO (fromEnv "GENG_STAGE_READ")
{-# NOINLINE readFrom #-}

-- | @GENG_STAGE_WRITE=passed:dir@: the stage this build stops after, and where
-- to write it.
writeTo :: Maybe (Stage, FilePath)
writeTo = unsafePerformIO (fromEnv "GENG_STAGE_WRITE")
{-# NOINLINE writeTo #-}

-- | A malformed value is fatal rather than ignored. A switch that silently did
-- nothing on a typo would be one whose staged build quietly ran unstaged and
-- passed, which is the failure this is here to make impossible.
fromEnv :: String -> IO (Maybe (Stage, FilePath))
fromEnv name =
  do
    value <- Env.lookupEnv name
    case value of
      Nothing -> return Nothing
      Just text ->
        case break (== ':') text of
          (word, ':' : dir)
            | Just stage <- stageFrom word,
              not (null dir) ->
                return (Just (stage, dir))
          _ ->
            error $
              name
                ++ "="
                ++ text
                ++ ": expected <stage>:<directory>, where <stage> is "
                ++ List.intercalate " or " (map stageName [Front, Passed])

-- | The two switches against each other. A build cannot stop at a stage it
-- started at or before: there would be nothing between the read and the write,
-- and the directory it wrote would be a copy of the one it read.
checkPlan :: IO ()
checkPlan =
  case (readFrom, writeTo) of
    (Just (start, _), Just (stop, _))
      | stop <= start ->
          error $
            "GENG_STAGE_READ="
              ++ stageName start
              ++ " and GENG_STAGE_WRITE="
              ++ stageName stop
              ++ ": a build cannot stop at a stage it started at or before"
    _ -> return ()

-- | A stage's Core and the program it belongs to.
--
-- __Stale files are removed first.__ The directory is named by the caller and
-- may hold an earlier build's modules; a module left behind from a program with
-- another set of roots would enter this one's link and be reported as
-- unreachable rather than as a mistake. Only @.corepb@ files go, so a directory
-- that is not a stage directory loses nothing it did not put there.
write :: FilePath -> Whole.Program -> Map ModuleName.Canonical Core.Module -> IO ()
write dir program modules =
  do
    Dir.createDirectoryIfMissing True dir
    stale <- corepbFiles dir
    mapM_ (Dir.removeFile . (dir </>)) stale
    case Wire.encodeProgram program of
      Left problems ->
        error (unlines ("Core.Stage: the program does not encode:" : problems))
      Right bytes ->
        BS.writeFile (dir </> programFileName) bytes
    mapM_ oneModule (Map.toAscList modules)
  where
    oneModule (home, core) =
      case Wire.encode core of
        Left problems ->
          error
            ( unlines
                ( ("Core.Stage: " ++ ModuleName.toChars (ModuleName._module home) ++ " does not encode:")
                    : problems
                )
            )
        Right bytes ->
          Dump.writeWire dir home (B.byteString bytes)

-- | Back again. The modules are keyed by the name each one carries
-- ('Core.AST._moduleName') rather than by its file name, so the directory's
-- naming scheme is a convenience for a reader and not a fact the format
-- depends on.
read :: FilePath -> IO (Whole.Program, Map ModuleName.Canonical Core.Module)
read dir =
  do
    there <- Dir.doesDirectoryExist dir
    if not there
      then error ("Core.Stage: there is no stage directory at " ++ dir)
      else return ()
    programBytes <- readFile' (dir </> programFileName)
    program <-
      case Wire.decodeProgram programBytes of
        Left err -> error ("Core.Stage: " ++ dir </> programFileName ++ ": " ++ Wire.renderError err)
        Right program -> return program
    names <- corepbFiles dir
    modules <- mapM (oneModule . (dir </>)) (List.sort (filter (/= programFileName) names))
    return (program, Map.fromListWith duplicate modules)
  where
    oneModule file =
      do
        bytes <- readFile' file
        case Wire.decode bytes of
          Left err -> error ("Core.Stage: " ++ file ++ ": " ++ Wire.renderError err)
          Right core -> return (Core._moduleName core, core)

    duplicate _ _ =
      error ("Core.Stage: " ++ dir ++ " holds two files for one module")

readFile' :: FilePath -> IO BS.ByteString
readFile' file =
  do
    there <- Dir.doesFileExist file
    if there
      then BS.readFile file
      else error ("Core.Stage: there is no " ++ file)

corepbFiles :: FilePath -> IO [FilePath]
corepbFiles dir =
  filter ((== ".corepb") . FilePath.takeExtension) <$> Dir.listDirectory dir
