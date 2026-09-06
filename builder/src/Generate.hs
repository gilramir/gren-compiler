module Generate
  ( dev,
    prod,
    repl,
  )
where

import Build qualified
import Control.Concurrent (readMVar)
import Core.AST qualified as Core
import Core.Dump qualified as Dump
import Core.Low qualified as Low
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
import Generate.CoreJS qualified as CoreJS
import Generate.LowC qualified as LowC
import Generate.Mode qualified as Mode
import Gren.Details qualified as Details
import Gren.Kernel qualified as K
import Gren.ModuleName qualified as ModuleName
import Nitpick.Debug qualified as Nitpick
import Reporting.Exit qualified as Exit
import Reporting.Task qualified as Task
import System.FilePath ((</>))
import System.FilePath qualified as FilePath
import Prelude hiding (cycle, print)

-- GENERATORS

type Task a =
  Task.Task Exit.Generate a

-- | A development build: the linked Core program, emitted by
-- "Generate.CoreJS".
--
-- There is one backend. Until §J18 there were two, and this chose between them
-- on @GENG_JS_NATIVE@ — the switch that let the corpus run every case through
-- each, which is what made the Core path a measured claim rather than a stated
-- one (@docs\/m1a-js-on-core.md@ §J3 items 6 and 7). It stopped being useful
-- when the old path stopped being an independent answer.
dev :: Details.Details -> Build.Artifacts -> Task CoreJS.GeneratedResult
dev details artifacts =
  do
    kernels <- kernelChunks details
    dumpCore details artifacts kernels
    spikeC details artifacts
    program <- linkCore details artifacts kernels
    return $ CoreJS.generate Mode.Dev program kernels

-- | An @--optimize@ build: 'dev', with the field table filled in and @Debug@
-- refused.
prod :: Details.Details -> Build.Artifacts -> Task CoreJS.GeneratedResult
prod details artifacts =
  do
    checkForDebugUses artifacts
    kernels <- kernelChunks details
    dumpCore details artifacts kernels
    program <- linkCore details artifacts kernels
    let mode = Mode.Prod (CoreJS.shortenFieldNames (Program._progFields program))
    return $ CoreJS.generate mode program kernels

-- PROGRAM CORE

-- | Every module of the program, in Core (M1a).
--
-- The backend is handed a program rather than a module at a time, so Core has to
-- arrive the same way the objects do: the dependencies' from 'Details', the
-- project's own from the 'Build.Artifacts'. This is the plumbing the JS backend
-- will read; nothing generates code from it yet.
--
-- A 'Build.Cached' module contributes nothing, because @.greni@ holds an
-- interface and no Core. That branch cannot be reached
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
-- unreported, where reading its Core would have found it. That branch is
-- unreachable today — @d.dat@ is never read back, so @Details._locals@ is empty
-- and every module is 'Build.Fresh'
-- (@docs/upstream/compiler-artifact-cache-is-write-only.md@) — and restoring the
-- cache means giving Core a file beside @.greni@, which is the same
-- work 'programCore' is waiting on.
ownCore :: Build.Artifacts -> Map.Map ModuleName.Raw Core.Module
ownCore (Build.Artifacts _ _ roots modules) =
  Map.fromList (Maybe.mapMaybe moduleCore modules ++ Maybe.mapMaybe rootCore (NE.toList roots))
  where
    moduleCore modul =
      case modul of
        Build.Fresh name _ core -> Just (name, core)
        Build.Cached _ _ _ -> Nothing

    rootCore root =
      case root of
        Build.Inside _ -> Nothing
        Build.Outside name _ core -> Just (name, core)

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

-- | The linked Core program (§J15).
--
-- This is the whole of what the emitter is handed besides the kernel chunks: one
-- call to `Core.Program.link`, with the roots 'coreRoots' names and the kernel
-- information 'kernelInfo' reads off those same chunks.
linkCore :: Details.Details -> Build.Artifacts -> Map.Map N.Name [K.Chunk] -> Task Program.Program
linkCore details artifacts kernels =
  Task.io $
    do
      cores <- Pass.run <$> programCore details artifacts
      return (Program.link (backendFor kernels cores) cores (coreRoots artifacts cores))

-- | The kernel modules' JavaScript, which C16 keeps in the build system.
--
-- 'Gren.Details' parses it and holds it; both consumers here read it from there.
-- 'kernelInfo' takes the /names/ out of a module's chunks for the linker and
-- 'Generate.CoreJS' splices the chunks themselves — two readings of one thing,
-- and neither of them is a reading of a graph. They were, until §J13: a chunk
-- travelled inside an @Opt.Kernel@ node because the graph was the only thing
-- that reached the backend.
kernelChunks :: Details.Details -> Task (Map.Map N.Name [K.Chunk])
kernelChunks details =
  Task.io (Maybe.fromMaybe Map.empty <$> (readMVar =<< Details.loadKernels details))

-- | The program's roots, as Core names.
--
-- A root module's @main@, when it has one. That question used to be put to the
-- old pipeline — @gatherMains@ read the @Opt.Main@ that @Optimize.Module@
-- attached — and C19 records the same fact in Core beside the binding, so it is
-- put to Core here. There were two classifications of @main@ and now there is
-- one: 'Core.Lower.Module.mainOf' was @Optimize.Module.addDefHelp@'s case for
-- case, agreeing by inspection, and `Nitpick.Main` reads the surviving one.
--
-- The order is by module name, which is what @gatherMains@' @Map.keys@ gave
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
        Build.Outside name _ _ -> name

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

-- | The Core → C spike (@docs/m1a-c-spike.md@), when @GENG_SPIKE_C@ asks for it.
--
-- Hung off a build rather than given a CLI surface, because §X10 is explicit
-- that the spike is __not a backend__: no @geng make --output=x.c@, no target
-- in @harness/run.py@, no corpus. When it is over, "Generate.CoreJS" is still
-- the only backend and deleting this function deletes the spike.
--
-- __The roots are the whole trick__ (§X3). This links from the one scalar
-- binding @GENG_SPIKE_ROOT@ names, not from the program\'s @main@ — measured
-- 2026-09-06, @main = "x"@ links 56 bindings and 26 kernel JavaScript
-- functions, among them @Platform.leaf@ and @Scheduler.spawn@, and the language
-- itself costs five of them. 'Program.link' takes its roots as a plain list, so
-- this is an argument at a call site and not a mechanism.
--
-- Two files: the C, and the finding. §X9 makes the spike\'s criterion a written
-- list of everything @Low@ had to compute that Core does not carry, and
-- "Core.Low" produces it as it goes rather than leaving it to be remembered.
spikeC :: Details.Details -> Build.Artifacts -> Task ()
spikeC details artifacts@(Build.Artifacts pkg _ _ _) =
  case (Dump.spikeFile, Dump.spikeRoot) of
    (Just file, Just (home, name)) ->
      Task.io $
        do
          cores <- Pass.run <$> programCore details artifacts
          let root =
                Core.QualName
                  (ModuleName.Canonical pkg (N.fromChars home))
                  (N.fromChars name)
          let program = Program.link spikeBackend cores [root]
          case Low.lower program root of
            Left err -> B.writeFile file (B.stringUtf8 ("/* " ++ err ++ " */\n"))
            Right low ->
              do
                B.writeFile file (LowC.generate low)
                B.writeFile (file ++ ".notes") (Low.renderNotes (Low._lowNotes low))
                -- The spike's own link, and not the program's. @GENG_DUMP_LINK@
                -- writes the link rooted at @main@, which is the 87-binding one
                -- §X2 measured; §X5's budget is about what the /spike's/ root
                -- reaches, and checking the C kernel against the wrong list
                -- would pass anything.
                B.writeFile (file ++ ".link") (Program.render program)
                B.writeFile (FilePath.takeDirectory file </> "geng_tags.h") (LowC.renderTags low)
    _ -> return ()

-- | The linker's view of a backend that has no JavaScript in it.
--
-- __Both fields empty, and that is the whole of §X5's budget.__ A kernel
-- module is a node in the JS link because its chunks are spliced and its
-- JavaScript calls back into Gren — so reaching @Basics.add@ reaches the whole
-- @Basics@ chunk list, which references @Utils@, which references @Dict@,
-- @Set@ and @Array@. Measured on the first spike run: linking @Case.answer@
-- with the JavaScript backend's kernel map dragged in @Dict@, @Set@ and
-- @Array.splice1@, none of which the arithmetic wants.
--
-- For C there is no JavaScript to splice. So a kernel name is not defined, the
-- graph stops there, and the reference comes out in 'Program._progMissing'
-- instead — which is exactly the list §X5 makes the C kernel's budget. The
-- transitive closure disappears because the edge that created it was a fact
-- about JavaScript.
--
-- 'Program._backendEdges' is empty for the same kind of reason: its edges are a
-- @port@'s runtime constructor and a static @main@'s entry point, and §X3's
-- root has neither.
spikeBackend :: Program.Backend
spikeBackend =
  Program.Backend
    { Program._backendKernels = Map.empty,
      Program._backendEdges = Map.empty
    }

-- | One REPL entry, generated the way @dev@ is (§J17).
repl :: Details.Details -> Bool -> Build.ReplArtifacts -> N.Name -> Task B.Builder
repl details ansi artifacts@(Build.ReplArtifacts home _ localizer annotations) name =
  do
    kernels <- kernelChunks details
    program <- linkReplCore details artifacts name kernels
    return $ CoreJS.generateForRepl ansi localizer program kernels home name (annotations ! name)

-- | 'linkCore' for a REPL entry, which differs from a program in its roots.
--
-- The modules are the REPL\'s own — the generated @Gren_Repl@ module and
-- whatever it imports out of the project — plus the dependencies\' Core, exactly
-- as 'programCore' assembles them for a build. A 'Build.Cached' module
-- contributes nothing here for the reason 'programCore' gives.
linkReplCore :: Details.Details -> Build.ReplArtifacts -> N.Name -> Map.Map N.Name [K.Chunk] -> Task Program.Program
linkReplCore details (Build.ReplArtifacts home modules _ _) name kernels =
  Task.io $
    do
      maybeDeps <- readMVar =<< Details.loadCores details
      let deps = Maybe.fromMaybe Map.empty maybeDeps
      let own =
            Map.fromList
              [ (ModuleName.Canonical (ModuleName._package home) raw, core)
              | Build.Fresh raw _ core <- modules
              ]
      let cores = Pass.run (Map.union own deps)
      return (Program.link (backendFor kernels cores) cores (replRoots home name))

-- | What a REPL entry reaches: the value being printed, and @Debug.toString@.
--
-- The second is @Generate.JavaScript.generateForRepl@\'s, kept name for name.
-- Nothing generated calls @Debug.toString@ — the printer calls kernel @Debug@\'s
-- @_Debug_toAnsiString@ straight — so what the root is for is the kernel module
-- that function is in, which that binding refers to and nothing else does.
--
-- It is a Gren binding rather than the kernel module itself on purpose. §J13\'s
-- rule is that a kernel module a /runtime/ enters through is an edge and not a
-- root, because a root says a thing is reachable and says nothing about when;
-- here the printer is appended after every linked item, so no order could be
-- wrong. Keeping the same root as the old path is worth more: it is what makes
-- the two REPLs reach the same set, and so makes comparing their output a test
-- of the emitter rather than of two different programs.
replRoots :: ModuleName.Canonical -> N.Name -> [Core.QualName]
replRoots home name =
  [ Core.QualName ModuleName.debug (N.fromChars "toString"),
    Core.QualName home name
  ]

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
