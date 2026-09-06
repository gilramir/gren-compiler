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
import Core.Pass qualified as Pass
import Core.Pretty qualified as Pretty
import Core.Program qualified as Program
import Core.Refs qualified as Refs
import Data.ByteString.Builder qualified as B
import Data.Map ((!))
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name qualified as N
import Data.NonEmptyList qualified as NE
import Data.Set qualified as Set
import Directories qualified as Dirs
import File qualified
import Generate.CoreJS qualified as CoreJS
import Generate.FromCore qualified as FromCore
import Generate.JavaScript qualified as JS
import Generate.Mode qualified as Mode
import Gren.Details qualified as Details
import Gren.Kernel qualified as K
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
    kernels <- kernelChunks details
    dumpCore details artifacts kernels
    native <- linkCore details artifacts kernels
    case native of
      Just program -> return $ CoreJS.generate Mode.Dev program kernels
      Nothing ->
        do
          objects <- finalizeObjects =<< loadObjects root details modules
          let objectGraph = objectsToGlobalGraph objects
          graph <- fromCore details artifacts objectGraph
          return $ JS.generate Mode.Dev graph (gatherMains pkg objects roots)

prod :: FilePath -> Details.Details -> Build.Artifacts -> Task JS.GeneratedResult
prod root details artifacts@(Build.Artifacts pkg _ roots modules) =
  do
    checkForDebugUses artifacts
    kernels <- kernelChunks details
    dumpCore details artifacts kernels
    native <- linkCore details artifacts kernels
    case native of
      Just program ->
        let mode = Mode.Prod (CoreJS.shortenFieldNames (Program._progFields program))
         in return $ CoreJS.generate mode program kernels
      Nothing ->
        do
          objects <- finalizeObjects =<< loadObjects root details modules
          let objectGraph = objectsToGlobalGraph objects
          graph <- fromCore details artifacts objectGraph
          let mode = Mode.Prod (Mode.shortenFieldNames graph)
          return $ JS.generate mode graph (gatherMains pkg objects roots)

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
programCore details artifacts@(Build.Artifacts pkg _ _ _) =
  do
    maybeDeps <- readMVar =<< Details.loadCores details
    let deps = Maybe.fromMaybe Map.empty maybeDeps
    let own = Map.mapKeys (ModuleName.Canonical pkg) (ownCore artifacts)
    return (Map.union own deps)

-- | The Core of the modules being built, by raw name.
--
-- 'programCore' is this plus the dependencies', keyed canonically. It is
-- separate because 'checkForDebugUses' wants exactly this half — @--optimize@
-- rejects a @Debug@ use in the project and not in a package it depends on — and
-- wants the raw name, which is what the error prints.
--
-- A 'Build.Cached' module contributes nothing, for the reason 'programCore'
-- gives and with a second consequence: a cached module's @Debug@ use would go
-- unreported, where reading its @.greno@ would have found it. That branch is
-- unreachable today — @d.dat@ is never read back, so @Details._locals@ is empty
-- and every module is 'Build.Fresh'
-- (@docs/upstream/compiler-artifact-cache-is-write-only.md@) — and restoring the
-- cache means giving Core a file beside @.greni@ and @.greno@, which is the same
-- work 'programCore' is waiting on.
ownCore :: Build.Artifacts -> Map.Map ModuleName.Raw Core.Module
ownCore (Build.Artifacts _ _ roots modules) =
  Map.fromList (Maybe.mapMaybe moduleCore modules ++ Maybe.mapMaybe rootCore (NE.toList roots))
  where
    moduleCore modul =
      case modul of
        Build.Fresh name _ _ core -> Just (name, core)
        Build.Cached _ _ _ -> Nothing

    rootCore root =
      case root of
        Build.Inside _ -> Nothing
        Build.Outside name _ _ core -> Just (name, core)

-- | The backend's input, with every value definition rebuilt from Core if
-- @GENG_JS_FROM_CORE=1@ asks for it.
--
-- `Generate.FromCore` says what it does and does not rebuild. Off by default:
-- both paths are in the binary so that the differential harness can run the
-- corpus through each (`docs/m1a-js-on-core.md` §J3 items 6 and 7).
--
-- @GENG_DEPS_GAP@ asks for the other thing this function is in a position to
-- know: how far `Generate.FromCore.keepDeps`'s union moves the dependency sets
-- (§J10). It reads both the Core and the graph the old pipeline built, so it is
-- measured here and it does not need the switch on.
fromCore :: Details.Details -> Build.Artifacts -> Opt.GlobalGraph -> Task Opt.GlobalGraph
fromCore details artifacts graph =
  case (Dump.jsFromCore, Dump.depsGap) of
    (False, Nothing) -> return graph
    (usingCore, maybeGapFile) ->
      Task.io $
        do
          cores <- Pass.run <$> programCore details artifacts
          case maybeGapFile of
            Nothing -> return ()
            Just file -> B.writeFile file (FromCore.renderGap (FromCore.gap cores graph))
          return (if usingCore then FromCore.redefine cores graph else graph)

-- | What the kernel JavaScript refers to, read off the chunks the builder
-- already holds (C16, @docs\/m1a-js-on-core.md@ §J7's two caveats).
--
-- "Core.Program" needs it for two reasons and neither is optional. Kernel
-- JavaScript calls back into Gren, so a linker that does not know those edges
-- drops code the kernel calls; and it names record fields, which @--optimize@
-- has to shorten together with the ones Gren code names. The chunks stay here —
-- C16's whole point is that they never enter the IR — and only the names cross.
--
-- The graph's own field census is not the answer to the second half: it is the
-- whole program's, kernel and Gren at once, where the linker wants each kernel
-- module's share attributed to it so that an unreached one contributes nothing.
backendFor :: Map.Map N.Name [K.Chunk] -> Map.Map ModuleName.Canonical Core.Module -> Program.Backend
backendFor kernels cores =
  Program.Backend
    { Program._backendKernels = Map.map kernelInfo kernels,
      Program._backendEdges = runtimeEdges cores
    }

kernelInfo :: [K.Chunk] -> Program.Kernel
kernelInfo chunks =
  Program.Kernel
    { Program._kernelGren = Set.fromList [Core.QualName home name | K.GrenVar home name <- chunks],
      Program._kernelKernels = Set.fromList [short | K.JsVar short _ <- chunks],
      Program._kernelFields = Map.keysSet (K.countFields chunks)
    }

-- | The kernel module each declaration's runtime call lands in.
--
-- A @port@'s constructor is in the kernel @Platform@ module and registers the
-- port in a @var@ that module declares, so the chunk has to come first; a
-- @main : String@ is printed by kernel @Node@ and a @main : Html msg@ is handed
-- to kernel @VirtualDom@. None of those names is in Core and none should be —
-- C16 keeps kernel JavaScript in the build system, C18 and C19 keep the runtime
-- call out of the declaration — so the JS backend supplies them here, where the
-- backend is already chosen.
--
-- @compiler#387@ is the bug this prevents, and it is why these are edges rather
-- than roots: stock 0.6.6 emits a port's @var@ above the kernel @var@ it
-- registers itself in, because @Optimize.Module.addPort@ records the converter's
-- dependencies and not the module the generated call lands in.
runtimeEdges :: Map.Map ModuleName.Canonical Core.Module -> Map.Map Core.QualName Refs.Refs
runtimeEdges cores =
  Map.fromList $
    concat
      [ [ (Core.QualName home (Core._binderName (Core._portBinder p)), kernel N.platform)
        | p <- Core._modulePorts modul
        ]
          ++ [ (Core.QualName home N._main, kernel short)
             | Just m <- [Core._moduleMain modul],
               Just short <- [staticHome m]
             ]
      | (home, modul) <- Map.toList cores
      ]
  where
    kernel = Refs.global . Program.kernelName
    staticHome m =
      case m of
        Core.MainString -> Just N.node
        Core.MainHtml -> Just N.virtualDom
        Core.MainProgram _ -> Nothing

-- | The linked Core program, when @GENG_JS_NATIVE=1@ asks for one (§J15).
--
-- This is the whole of what the Core-native emitter is handed besides the kernel
-- chunks: one call to `Core.Program.link`, with the roots 'coreRoots' names and
-- the kernel information 'kernelInfo' reads off those same chunks. Nothing on
-- this path looks at an `AST.Optimized.GlobalGraph` at all — 'Generate.dev' and
-- 'Generate.prod' do not even load one (§J16).
linkCore :: Details.Details -> Build.Artifacts -> Map.Map N.Name [K.Chunk] -> Task (Maybe Program.Program)
linkCore details artifacts kernels
  | not Dump.jsNative = return Nothing
  | otherwise =
      Task.io $
        do
          cores <- Pass.run <$> programCore details artifacts
          return (Just (Program.link (backendFor kernels cores) cores (coreRoots artifacts cores)))

-- | The kernel modules' JavaScript, which C16 keeps in the build system.
--
-- 'Gren.Details' parses it and holds it; both consumers here read it from there.
-- 'kernelInfo' takes the /names/ out of a module's chunks for the linker and
-- 'Generate.CoreJS' splices the chunks themselves — two readings of one thing,
-- and neither of them is a reading of an 'AST.Optimized.GlobalGraph' any more.
kernelChunks :: Details.Details -> Task (Map.Map N.Name [K.Chunk])
kernelChunks details =
  Task.io (Maybe.fromMaybe Map.empty <$> (readMVar =<< Details.loadKernels details))

-- | The program's roots, as Core names.
--
-- A root module's @main@, when it has one. That question used to be put to the
-- old pipeline — 'gatherMains' reads the 'AST.Optimized.Main' that
-- @Optimize.Module@ attached — and C19 records the same fact in Core beside the
-- binding, so it is put to Core here. The two classifications are one
-- classification on purpose: 'Core.Lower.Module.mainOf' is
-- @Optimize.Module.addDefHelp@'s, case for case, and a disagreement between
-- them would be a compiler bug rather than a missing entry.
--
-- The order is by module name, which is what 'gatherMains''s @Map.keys@ gave
-- and what C6 wants; the order the roots were named on the command line is not
-- a property of the program.
--
-- The kernel modules a runtime enters through are /not/ here. They were, and it
-- was wrong: a root makes a kernel module reachable and says nothing about when
-- it is emitted, so a port's @var@ could still land above the chunk it
-- registers itself in. They are edges instead — 'runtimeEdges'.
coreRoots :: Build.Artifacts -> Map.Map ModuleName.Canonical Core.Module -> [Core.QualName]
coreRoots (Build.Artifacts pkg _ roots _) cores =
  [ Core.QualName home N._main
  | home <- Set.toAscList (Set.fromList (map (ModuleName.Canonical pkg . rootName) (NE.toList roots))),
    Just modul <- [Map.lookup home cores],
    Maybe.isJust (Core._moduleMain modul)
  ]
  where
    rootName root =
      case root of
        Build.Inside name -> name
        Build.Outside name _ _ _ -> name

-- | Write what @GENG_DUMP_PROGRAM_CORE@ and @GENG_DUMP_LINK@ ask for, if either
-- names a place to put it.
--
-- The first is the program's Core, module by module, with the same file names as
-- "Compile"'s per-module dump so that the two are comparable as directories. The
-- second is 'Core.Program.link''s summary: what the roots reach, in what order,
-- and what they refer to that Core cannot supply yet.
dumpCore :: Details.Details -> Build.Artifacts -> Map.Map N.Name [K.Chunk] -> Task ()
dumpCore details artifacts kernels =
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
              let roots =
                    if Dump.linkEveryExport
                      then concatMap Core._moduleExports (Map.elems cores)
                      else coreRoots artifacts cores
               in B.writeFile file (Program.render (Program.link (backendFor kernels cores) cores roots))

repl :: FilePath -> Details.Details -> Bool -> Build.ReplArtifacts -> N.Name -> Task B.Builder
repl root details ansi (Build.ReplArtifacts home modules localizer annotations) name =
  do
    objects <- finalizeObjects =<< loadObjects root details modules
    let graph = objectsToGlobalGraph objects
    return $ JS.generateForRepl ansi localizer graph home name (annotations ! name)

-- CHECK FOR DEBUG

-- | @--optimize@ rejects a program that still calls @Debug@ (@Nitpick.Debug@).
--
-- Asked of Core rather than of the old pipeline's graph, because the answer is
-- in Core: canonicalization turns every reference to a value in the @Debug@
-- module into @Can.VarDebug@, and "Core.Lower.Expression" lowers that to an
-- @EGlobal@ whose home is 'ModuleName.debug'. One walk over the module's
-- bindings finds them.
checkForDebugUses :: Build.Artifacts -> Task ()
checkForDebugUses artifacts =
  case Map.keys (Map.filter Nitpick.hasDebugUses (ownCore artifacts)) of
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
