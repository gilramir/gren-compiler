module Generate
  ( dev,
    prod,
    repl,
  )
where

import AST.Optimized qualified as Opt
import Build qualified
import Control.Concurrent (MVar, forkIO, newEmptyMVar, newMVar, putMVar, readMVar)
import Control.Monad (liftM2)
import Core.AST qualified as Core
import Core.Dump qualified as Dump
import Core.Pretty qualified as Pretty
import Core.Program qualified as Program
import Data.ByteString.Builder qualified as B
import Data.Map ((!))
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name qualified as N
import Data.NonEmptyList qualified as NE
import Directories qualified as Dirs
import File qualified
import Generate.JavaScript qualified as JS
import Generate.Mode qualified as Mode
import Gren.Details qualified as Details
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Nitpick.Debug qualified as Nitpick
import Reporting.Exit qualified as Exit
import Reporting.Task qualified as Task
import Prelude hiding (cycle, print)

-- GENERATORS

type Task a =
  Task.Task Exit.Generate a

dev :: FilePath -> Details.Details -> Build.Artifacts -> Task JS.GeneratedResult
dev root details artifacts@(Build.Artifacts pkg _ roots modules) =
  do
    objects <- finalizeObjects =<< loadObjects root details modules
    let mode = Mode.Dev
    let graph = objectsToGlobalGraph objects
    let mains = gatherMains pkg objects roots
    dumpCore details artifacts mains
    return $ JS.generate mode graph mains

prod :: FilePath -> Details.Details -> Build.Artifacts -> Task JS.GeneratedResult
prod root details artifacts@(Build.Artifacts pkg _ roots modules) =
  do
    objects <- finalizeObjects =<< loadObjects root details modules
    checkForDebugUses objects
    let graph = objectsToGlobalGraph objects
    let mode = Mode.Prod (Mode.shortenFieldNames graph)
    let mains = gatherMains pkg objects roots
    dumpCore details artifacts mains
    return $ JS.generate mode graph mains

-- PROGRAM CORE

-- | Every module of the program, in Core (M1a).
--
-- The backend is handed a program rather than a module at a time, so Core has to
-- arrive the same way the objects do: the dependencies' from 'Details', the
-- project's own from the 'Build.Artifacts'. This is the plumbing the JS backend
-- will read; nothing generates code from it yet.
--
-- A 'Build.Cached' module contributes nothing, because @.greni@/@.greno@ hold an
-- interface and an 'Opt.LocalGraph' and no Core. That branch cannot be reached
-- today — nothing reads @d.dat@ back, so every module is fresh
-- (@docs/upstream/compiler-artifact-cache-is-write-only.md@) — and the day the
-- cache is restored, Core needs a file beside those two and this function needs
-- to load it. Until then a missing entry would be a silently smaller program, so
-- 'dumpProgramCore' reports the count and @harness/core-golden.py@ compares the
-- module set against the frontend's own dump.
programCore :: Details.Details -> Build.Artifacts -> IO (Map.Map ModuleName.Canonical Core.Module)
programCore details (Build.Artifacts pkg _ roots modules) =
  do
    maybeDeps <- readMVar =<< Details.loadCores details
    let deps = Maybe.fromMaybe Map.empty maybeDeps
    let own = Map.fromList (Maybe.mapMaybe moduleCore modules ++ Maybe.mapMaybe rootCore (NE.toList roots))
    return (Map.union own deps)
  where
    moduleCore modul =
      case modul of
        Build.Fresh name _ _ core -> Just (ModuleName.Canonical pkg name, core)
        Build.Cached _ _ _ -> Nothing

    rootCore root =
      case root of
        Build.Inside _ -> Nothing
        Build.Outside name _ _ core -> Just (ModuleName.Canonical pkg name, core)

-- | The program's roots, as Core names.
--
-- The JS backend's roots are the @main@ of each root module, which is where
-- 'gatherMains' stops; in Core each one is an ordinary top-level binding called
-- @main@ in that module.
coreRoots :: Map.Map ModuleName.Canonical Opt.Main -> [Core.QualName]
coreRoots mains =
  [Core.QualName home (N.fromChars "main") | home <- Map.keys mains]

-- | Write what @GENG_DUMP_PROGRAM_CORE@ and @GENG_DUMP_LINK@ ask for, if either
-- names a place to put it.
--
-- The first is the program's Core, module by module, with the same file names as
-- "Compile"'s per-module dump so that the two are comparable as directories. The
-- second is 'Core.Program.link''s summary: what the roots reach, in what order,
-- and what they refer to that Core cannot supply yet.
dumpCore :: Details.Details -> Build.Artifacts -> Map.Map ModuleName.Canonical Opt.Main -> Task ()
dumpCore details artifacts mains =
  case (Dump.programDir, Dump.linkFile) of
    (Nothing, Nothing) -> return ()
    (maybeDir, maybeFile) ->
      Task.io $
        do
          cores <- programCore details artifacts
          case maybeDir of
            Nothing -> return ()
            Just dir ->
              mapM_
                (\(home, core) -> Dump.writeModule dir home (Pretty.moduleToBuilder Pretty.defaultOptions core))
                (Map.toAscList cores)
          case maybeFile of
            Nothing -> return ()
            Just file ->
              B.writeFile file (Program.render (Program.link cores (coreRoots mains)))

repl :: FilePath -> Details.Details -> Bool -> Build.ReplArtifacts -> N.Name -> Task B.Builder
repl root details ansi (Build.ReplArtifacts home modules localizer annotations) name =
  do
    objects <- finalizeObjects =<< loadObjects root details modules
    let graph = objectsToGlobalGraph objects
    return $ JS.generateForRepl ansi localizer graph home name (annotations ! name)

-- CHECK FOR DEBUG

checkForDebugUses :: Objects -> Task ()
checkForDebugUses (Objects _ locals) =
  case Map.keys (Map.filter Nitpick.hasDebugUses locals) of
    [] -> return ()
    m : ms -> Task.throw (Exit.GenerateCannotOptimizeDebugValues m ms)

-- GATHER MAINS

gatherMains :: Pkg.Name -> Objects -> NE.List Build.Root -> Map.Map ModuleName.Canonical Opt.Main
gatherMains pkg (Objects _ locals) roots =
  Map.fromList $ Maybe.mapMaybe (lookupMain pkg locals) (NE.toList roots)

lookupMain :: Pkg.Name -> Map.Map ModuleName.Raw Opt.LocalGraph -> Build.Root -> Maybe (ModuleName.Canonical, Opt.Main)
lookupMain pkg locals root =
  let toPair name (Opt.LocalGraph maybeMain _ _) =
        (,) (ModuleName.Canonical pkg name) <$> maybeMain
   in case root of
        Build.Inside name -> toPair name =<< Map.lookup name locals
        Build.Outside name _ g _ -> toPair name g

-- LOADING OBJECTS

data LoadingObjects = LoadingObjects
  { _foreign_mvar :: MVar (Maybe Opt.GlobalGraph),
    _local_mvars :: Map.Map ModuleName.Raw (MVar (Maybe Opt.LocalGraph))
  }

loadObjects :: FilePath -> Details.Details -> [Build.Module] -> Task LoadingObjects
loadObjects root details modules =
  Task.io $
    do
      mvar <- Details.loadObjects root details
      mvars <- traverse (loadObject root) modules
      return $ LoadingObjects mvar (Map.fromList mvars)

loadObject :: FilePath -> Build.Module -> IO (ModuleName.Raw, MVar (Maybe Opt.LocalGraph))
loadObject root modul =
  case modul of
    Build.Fresh name _ graph _ ->
      do
        mvar <- newMVar (Just graph)
        return (name, mvar)
    Build.Cached name _ _ ->
      do
        mvar <- newEmptyMVar
        _ <- forkIO $ putMVar mvar =<< File.readBinary (Dirs.greno root name)
        return (name, mvar)

-- FINALIZE OBJECTS

data Objects = Objects
  { _foreign :: Opt.GlobalGraph,
    _locals :: Map.Map ModuleName.Raw Opt.LocalGraph
  }

finalizeObjects :: LoadingObjects -> Task Objects
finalizeObjects (LoadingObjects mvar mvars) =
  Task.eio id $
    do
      result <- readMVar mvar
      results <- traverse readMVar mvars
      case liftM2 Objects result (sequence results) of
        Just loaded -> return (Right loaded)
        Nothing -> return (Left Exit.GenerateCannotLoadArtifacts)

objectsToGlobalGraph :: Objects -> Opt.GlobalGraph
objectsToGlobalGraph (Objects globals locals) =
  foldr Opt.addLocalGraph globals locals
