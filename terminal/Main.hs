module Main
  ( main,
  )
where

import Command qualified
import Core.Pretty qualified as Pretty
import Core.Wire qualified as Wire
import Data.ByteString qualified
import Data.ByteString.Builder qualified as B
import Data.ByteString.Char8 qualified
import Docs qualified
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Json.Decode qualified as Json
import Make qualified
import Package.Bump qualified as Bump
import Package.Diff qualified as Diff
import Package.Validate qualified as Validate
import Repl qualified
import System.Environment qualified as Env
import System.Exit qualified as Exit
import System.IO qualified as IO

-- MAIN

main :: IO ()
main =
  do
    setLocaleEncoding utf8
    readWireFile
    argStrings <- Env.getArgs
    case argStrings of
      [] -> do
        json <- Data.ByteString.Char8.getLine
        case Json.fromByteString Command.commandDecoder json of
          Left err ->
            error (show err)
          Right (Command.Repl (Command.ReplFlags interpreter root outline rootSources deps)) ->
            Repl.run $ Repl.Flags interpreter root outline rootSources deps
          Right (Command.Make (Command.MakeFlags optimize sourcemaps output report paths projectPath outline rootSources deps)) ->
            Make.run $ Make.Flags optimize sourcemaps output report paths projectPath outline rootSources deps
          Right (Command.Docs (Command.DocsFlags output report projectPath outline rootSources deps)) ->
            Docs.run $ Docs.Flags output report projectPath outline rootSources deps
          Right (Command.PackageValidate (Command.ValidateFlags projectPath knownVersions currentVersion maybePreviousVersion)) ->
            Validate.run $ Validate.Flags projectPath knownVersions currentVersion maybePreviousVersion
          Right (Command.PackageBump (Command.BumpFlags interactive projectPath knownVersions currentVersion publishedVersion)) ->
            Bump.run $ Bump.Flags interactive projectPath knownVersions currentVersion publishedVersion
          Right (Command.PackageDiff (Command.DiffFlags interactive projectPath firstPackage secondPackage)) ->
            Diff.run $ Diff.Flags interactive projectPath firstPackage secondPackage
      _ ->
        do
          putStrLn "Expected exactly 0 arguments."
          putStrLn ""
          putStrLn
            "It looks like you are trying to run Gren's internal backend directly.\
            \ To properly install Gren, see https://gren-lang.org/install"

-- | @GENG_WIRE_READ=path.corepb@: read one Core file and say what happened.
--
-- A debug hook in the shape @GENG_DUMP_LINK@ and @GENG_SPIKE_C@ already have —
-- a measurement hung off the binary, not a mode of it and not a subcommand.
-- What it is for is @harness/wire.py@'s third check: the reader has to refuse a
-- file that is not in canonical form (@docs/m1a-wire.md@ §B7), and a corpus of
-- authored malformed files needs something to feed them to. It prints the
-- module's text form on success and the error on failure, and it exits before
-- anything else runs, because it needs no project.
readWireFile :: IO ()
readWireFile =
  do
    maybePath <- Env.lookupEnv "GENG_WIRE_READ"
    case maybePath of
      Nothing -> return ()
      Just path ->
        do
          input <- Data.ByteString.readFile path
          case Wire.decode input of
            Left err ->
              do
                IO.hPutStrLn IO.stderr (Wire.renderError err)
                Exit.exitWith (Exit.ExitFailure 1)
            Right core ->
              do
                B.hPutBuilder IO.stdout (Pretty.moduleToBuilder Pretty.defaultOptions core)
                Exit.exitSuccess
