{-# LANGUAGE OverloadedStrings #-}

module Package.Validate
  ( Flags (..),
    run,
  )
where

import Build qualified
import Control.Monad (when)
import Command qualified
import Core.AST qualified as Core
import Data.List qualified as List
import Data.Map (Map)
import Data.NonEmptyList qualified as NE
import Deps.Diff qualified as Diff
import Deps.Refinements qualified as Refinements
import Deps.Package qualified as Pkg
import Generate qualified
import Gren.Details qualified as Details
import Gren.Docs qualified as Docs
import Gren.Magnitude qualified as M
import Gren.Outline qualified as Outline
import Gren.Package qualified as Pkg
import Gren.Version qualified as V
import Reporting qualified
import Reporting.Exit qualified as Exit
import Reporting.Task qualified as Task

data Flags = Flags
  { _project_path :: String,
    _known_versions :: [V.Version],
    _current_version :: Command.ProjectInfo,
    _previous_version :: Maybe Command.ProjectInfo
  }
  deriving (Show)

run :: Flags -> IO ()
run flags =
  Reporting.attempt Exit.validateToReport $
    Task.run $
      validate flags

validate :: Flags -> Task.Task Exit.Validate ()
validate (Flags root knownVersions (Command.ProjectInfo currentOutline currentSources currentDeps) maybePreviousVersion) =
  case (currentOutline, maybePreviousVersion) of
    (Outline.App _, _) ->
      Task.throw Exit.ValidateApplication
    (Outline.Pkg currentPkgOutline@(Outline.PkgOutline _ _ _ _ _ _ _ _ _), Nothing) ->
      do
        (_, goesOn) <- buildChecked root currentPkgOutline currentSources currentDeps
        when goesOn $ Task.io $ putStrLn "Everything looks good!"
    (Outline.Pkg (Outline.PkgOutline _ _ _ _ _ _ _ _ _), Just (Command.ProjectInfo (Outline.App _) _ _)) ->
      error "Previous version is app"
    (Outline.Pkg currentPkgOutline@(Outline.PkgOutline _ _ _ vsn _ _ _ _ _), Just (Command.ProjectInfo (Outline.Pkg previousOutline) previousSources previousDeps)) ->
      do
        (current, goesOn) <- buildChecked root currentPkgOutline currentSources currentDeps
        previous <- buildProject root previousOutline previousSources previousDeps

        -- A first run that stopped for the package's own goals stops for the
        -- comparison too, so that the CLI does both between the same two runs.
        outcome <- Task.io $ Refinements.decide (not goesOn) previous current
        case outcome of
          Refinements.Stopped ->
            return ()
          Refinements.Decided verdicts previousDocs currentDocs ->
            do
              _ <- Task.eio id $ verifyBump verdicts vsn currentDocs previousDocs knownVersions
              Task.io $ putStrLn "Everything looks good!"

-- | The version being published, built, and its own goals owed to the
-- refinement checker (geng-lang @m4-refine.md@ §RF30, D858): its Core goes to
-- @own@ under @GENG_REFINE_STAGE@, the first run stops, and the CLI checks it
-- and refuses the version on a goal not proved. 'False' is that stop. The
-- previous version is not checked; it is already published.
buildChecked :: FilePath -> Outline.PkgOutline -> Build.Sources -> Map Pkg.Name Details.Dependency -> Task.Task Exit.Validate (Refinements.Version, Bool)
buildChecked root pkgOutline sources solution =
  do
    (details, (docs, cores)) <- buildWith root pkgOutline sources solution
    goesOn <- Task.mapError Exit.ValidateBadGenerate (Generate.packageCut "own" details cores)
    return (Refinements.Version docs cores details, goesOn)

buildProject :: FilePath -> Outline.PkgOutline -> Build.Sources -> Map Pkg.Name Details.Dependency -> Task.Task Exit.Validate Refinements.Version
buildProject root pkgOutline sources solution =
  (\(details, (docs, cores)) -> Refinements.Version docs cores details) <$> buildWith root pkgOutline sources solution

buildWith :: FilePath -> Outline.PkgOutline -> Build.Sources -> Map Pkg.Name Details.Dependency -> Task.Task Exit.Validate (Details.Details, (Docs.Documentation, [Core.Module]))
buildWith root pkgOutline@(Outline.PkgOutline _ _ _ _ _ _ _ _ _) sources solution =
  do
    details@(Details.Details _ outline _ _ _ _) <-
      Task.eio Exit.ValidateBadDetails $
        Details.load root (Outline.Pkg pkgOutline) solution

    exposed <-
      case outline of
        Details.ValidApp _ _ -> Task.throw Exit.ValidateApplication
        Details.ValidPkg _ _ [] _ -> Task.throw Exit.ValidateNoExposed
        Details.ValidPkg _ _ (e : es) _ -> return (NE.List e es)

    (,) details
      <$> Task.eio Exit.ValidateBuildProblem (Build.fromExposed Reporting.silent root details sources Build.KeepDocsAndCore exposed)

data GoodVersion
  = GoodBump V.Version M.Magnitude

verifyBump :: Diff.Verdicts -> V.Version -> Docs.Documentation -> Docs.Documentation -> [V.Version] -> IO (Either Exit.Validate GoodVersion)
verifyBump verdicts vsn newDocs oldDocs knownVersions =
  case reverse knownVersions of
    [] ->
      error "Known versions field was empty"
    latest : previous ->
      case List.find (\(_, new, _) -> vsn == new) (Pkg.bumpPossibilities (latest, previous)) of
        Nothing ->
          case List.find (\known -> vsn == known) (latest : previous) of
            Just _ ->
              return $ Right $ GoodBump vsn M.PATCH
            Nothing ->
              return $
                Left $
                  Exit.ValidateInvalidBump vsn latest
        Just (old, new, magnitude) ->
          let changes = Diff.diff verdicts oldDocs newDocs
              realNew = Diff.bump changes old
           in if new == realNew
                then return $ Right $ GoodBump old magnitude
                else
                  return $
                    Left $
                      Exit.ValidateBadBump old new magnitude realNew (Diff.toMagnitude changes)
