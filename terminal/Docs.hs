{-# LANGUAGE OverloadedStrings #-}

module Docs
  ( Flags (..),
    Output (..),
    run,
  )
where

import Build qualified
import Data.ByteString.Builder qualified as B
import Data.Map (Map)
import Data.NonEmptyList qualified as NE
import Generate qualified
import Gren.Details qualified as Details
import Gren.Docs qualified as Docs
import Gren.ModuleName qualified as ModuleName
import Gren.Outline (Outline)
import Gren.Package qualified as Package
import Json.Encode qualified as Json
import Reporting qualified
import Reporting.Exit qualified as Exit
import Reporting.Task qualified as Task
import System.Directory qualified as Dir
import System.Environment qualified as Env
import System.FilePath ((</>))
import System.IO qualified as IO

-- FLAGS

data Flags = Flags
  { _output :: Maybe Output,
    _report :: Bool,
    _project_root :: FilePath,
    _outline :: Outline,
    _root_sources :: Build.Sources,
    _dependencies :: Map Package.Name Details.Dependency
  }

data Output
  = JSON FilePath
  | DevNull
  | DevStdOut
  deriving (Show)

-- RUN

type Task a = Task.Task Exit.Docs a

run :: Flags -> IO ()
run flags@(Flags _ report _ _ _ _) =
  do
    style <- getStyle report
    Reporting.attemptWithStyle style Exit.docsToReport $
      runHelp style flags

-- | The documentation, with each exposed value's ownership facts (geng-lang
-- @m4-own.md@ §OW33, D970–D973), in two runs as a checked build is: the CLI's
-- first asks with @GENG_OWN_STAGE=dir@, and the package is built quietly and
-- staged for the ownership checker under @dir/new@ with every dependency's Core
-- ('Generate.packageOwnStage'), and nothing is written. The CLI checks it and
-- asks again with @GENG_OWN_FACTS@ naming a directory holding @new.tsv@, the
-- checker's @I@ lines, which this run gives the values before it writes them.
-- With neither, the binary run by itself, the documentation has no facts.
runHelp :: Reporting.Style -> Flags -> IO (Either Exit.Docs ())
runHelp style (Flags maybeOutput _ root outline sources dependencies) =
  Task.run $
    do
      details <- Task.eio Exit.DocsBadDetails (Details.load root outline dependencies)
      exposed <- getExposed details
      stage <- Task.io (nonEmpty "GENG_OWN_STAGE")
      facts <- Task.io (nonEmpty "GENG_OWN_FACTS")
      case stage of
        Just dir ->
          do
            (_, cores) <- buildExposed Reporting.silent root details sources Build.KeepDocsAndCore exposed
            Task.io (Generate.packageOwnStage details cores (dir </> "new"))
        Nothing ->
          let build buildStyle =
                do
                  docs <- buildExposed buildStyle root details sources Build.KeepDocs exposed
                  Task.io (factsFrom facts details docs)
           in case maybeOutput of
                Just DevNull ->
                  do
                    _ <- build style
                    return ()
                Just DevStdOut ->
                  do
                    docs <- build Reporting.silent
                    let builder = Json.encodeUgly $ Docs.encode docs
                    Task.io $ B.hPutBuilder IO.stdout builder
                Nothing ->
                  build style >>= Task.io . Json.writeUgly "docs.json" . Docs.encode
                Just (JSON target) ->
                  build style >>= Task.io . Json.writeUgly target . Docs.encode

nonEmpty :: String -> IO (Maybe String)
nonEmpty name =
  do
    value <- Env.lookupEnv name
    return $ case value of
      Just v | v /= "" -> Just v
      _ -> Nothing

factsFrom :: Maybe FilePath -> Details.Details -> Docs.Documentation -> IO Docs.Documentation
factsFrom facts details docs =
  case (facts, Details._outline details) of
    (Just dir, Details.ValidPkg _ pkg _ _) ->
      do
        let path = dir </> "new.tsv"
        present <- Dir.doesFileExist path
        if present
          then (\text -> Docs.withFacts (Package.toChars pkg) (lines text) docs) <$> readFile path
          else return docs
    _ ->
      return docs

-- GET INFORMATION

getStyle :: Bool -> IO Reporting.Style
getStyle report =
  if report then return Reporting.json else Reporting.terminal

getExposed :: Details.Details -> Task (NE.List ModuleName.Raw)
getExposed (Details.Details _ validOutline _ _ _ _) =
  case validOutline of
    Details.ValidApp _ _ ->
      Task.throw Exit.DocsApplication
    Details.ValidPkg _ _ exposed _ ->
      case exposed of
        [] -> Task.throw Exit.DocsNoExposed
        m : ms -> return (NE.List m ms)

-- BUILD PROJECTS

buildExposed :: Reporting.Style -> FilePath -> Details.Details -> Build.Sources -> Build.DocsGoal a -> NE.List ModuleName.Raw -> Task a
buildExposed style root details sources docsGoal exposed =
  Task.eio Exit.DocsBadBuild $
    Build.fromExposed style root details sources docsGoal exposed
