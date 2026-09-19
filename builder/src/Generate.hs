module Generate
  ( dev,
    prod,
    repl,
    ExtSources,
    extSources,
  )
where

import Build qualified
import Core.AST qualified as Core
import Core.Dump qualified as Dump
import Core.Low qualified as Low
import Core.Pass qualified as Pass
import Core.Pretty qualified as Pretty
import Core.Program qualified as Program
import Core.Refs qualified as Refs
import Core.Target qualified as Target
import Core.Wire qualified as Wire
import Data.ByteString qualified as BS
import Data.ByteString.Builder qualified as B
import Data.List qualified as List
import Data.Map ((!))
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name qualified as N
import Data.NonEmptyList qualified as NE
import Data.Set qualified as Set
import Data.Utf8 qualified as Utf8
import Generate.CoreJS qualified as CoreJS
import Generate.LowC qualified as LowC
import Generate.Mode qualified as Mode
import Gren.Details qualified as Details
import Gren.Kernel qualified as K
import Gren.ModuleName qualified as ModuleName
import Gren.Outline qualified as Outline
import Gren.Package qualified as Pkg
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
dev :: Target.Target -> Details.Details -> ExtSources -> Build.Artifacts -> Task CoreJS.GeneratedResult
dev target details sources artifacts =
  do
    checkTarget target details artifacts
    kernels <- kernelChunks details
    dumpCore target details artifacts kernels
    spikeC details artifacts
    program <- linkCore target details artifacts kernels
    exts <- externFiles target sources program
    return $ CoreJS.generate Mode.Dev program kernels exts

-- | An @--optimize@ build: 'dev', with the field table filled in and @Debug@
-- refused.
prod :: Target.Target -> Details.Details -> ExtSources -> Build.Artifacts -> Task CoreJS.GeneratedResult
prod target details sources artifacts =
  do
    checkTarget target details artifacts
    checkForDebugUses artifacts
    kernels <- kernelChunks details
    dumpCore target details artifacts kernels
    program <- linkCore target details artifacts kernels
    exts <- externFiles target sources program
    let mode = Mode.Prod (CoreJS.shortenFieldNames (Program._progFields program))
    return $ CoreJS.generate mode program kernels exts

-- TARGET

-- | The build's target against the modules it is made of, before any backend is
-- asked (@ffi.md@ F1, D77, D320), and then whether there is a backend.
--
-- The modules are the project's own and every module they refer to, a module
-- at a time ('Target.reached'), so a module is refused for an extern nothing
-- in the program calls, as F1 says a build that imports it is. That is what
-- leaves 'externFiles' only a missing file to find: an extern with no @js@ row
-- and no body can no longer reach it.
checkTarget :: Target.Target -> Details.Details -> Build.Artifacts -> Task ()
checkTarget target details artifacts@(Build.Artifacts pkg _ _ _) =
  let own = Map.mapKeys (ModuleName.Canonical pkg) (ownCore artifacts)
   in checkReached target (Map.union own (Details.loadCores details)) (Map.keys own)

checkReached :: Target.Target -> Map.Map ModuleName.Canonical Core.Module -> [ModuleName.Canonical] -> Task ()
checkReached target cores starts =
  case Target.refusals target (Target.reached cores starts) of
    [] ->
      if target == Target.Js
        then return ()
        else Task.throw (Exit.GenerateNoBackend target)
    refusals ->
      Task.throw (Exit.GenerateTargetRefused target refusals)

-- PROGRAM CORE

-- | Every module of the program, in Core (M1a).
--
-- The backend is handed a program rather than a module at a time, so Core has to
-- arrive the same way the objects do: the dependencies' from 'Details', the
-- project's own from the 'Build.Artifacts'. This is the plumbing the JS backend
-- will read; nothing generates code from it yet.
--
-- __Every module contributes, cached or not__ (D98). A 'Build.Cached' module
-- used to contribute nothing, because @.greni@ held an interface and no Core;
-- the day the artifact cache came back was going to be the day that became a
-- silently smaller program. It has a @.grenc@ beside it now, in C10's wire
-- format, and "Build" reads it before it will call a module cached at all. The
-- dependencies' side is the same change: 'Details.loadCores' was an
-- @IO (MVar (Maybe _))@ with a @fromMaybe Map.empty@ standing here, and is a
-- total function over a 'Details' that already holds them.
programCore :: Details.Details -> Build.Artifacts -> IO (Map.Map ModuleName.Canonical Core.Module)
programCore details artifacts@(Build.Artifacts pkg _ _ _) =
  do
    let deps = Details.loadCores details
    let own = Map.mapKeys (ModuleName.Canonical pkg) (ownCore artifacts)
    throughWire (Map.union own deps)

-- | Every module out through the wire format and back, when @GENG_WIRE=1@ asks
-- (D90) — and written to @GENG_DUMP_WIRE@ when that asks.
--
-- This is where the serializer becomes load-bearing rather than merely present.
-- It sits in 'programCore' rather than beside the backend so that one switch
-- covers a build, a @--optimize@ build and a @GENG_DUMP_PROGRAM_CORE@ dump; the
-- REPL has its own assembly and calls it too.
--
-- Failure is fatal and is not an @Exit.Generate@: a module that will not encode
-- or will not decode is a defect in the compiler, not a problem with the user's
-- program — except for D91's out-of-range integer literal, which is the one
-- thing a user can write that this refuses, and which says so.
throughWire :: Map.Map ModuleName.Canonical Core.Module -> IO (Map.Map ModuleName.Canonical Core.Module)
throughWire =
  roundTrip Dump.wireDir

-- | "Core.Pass" over the program, and the wire again after it (X19).
--
-- Every backend reads what this returns, so it is where the post-pass Core is
-- written when @GENG_DUMP_PASSED@ asks, and where @GENG_WIRE=1@ puts it through
-- the bytes a second time. Before this the passes ran after the only round
-- trip, so the Core a backend reads — join points, jumps, decision trees,
-- specialized copies — had never been encoded by any gate, and C11's Geng port
-- of the passes had nothing byte-level to be held to.
passed :: Map.Map ModuleName.Canonical Core.Module -> IO (Map.Map ModuleName.Canonical Core.Module)
passed cores =
  do
    let after = Pass.run cores
    case Dump.passedDir of
      Nothing -> return ()
      Just dir ->
        mapM_
          (\(home, core) -> Dump.writeModule dir home (Pretty.moduleToBuilder Pretty.defaultOptions core))
          (Map.toAscList after)
    roundTrip Dump.passedDir after

-- | Encode every module, write the bytes to @dir@ if there is one, and decode
-- them back if @GENG_WIRE=1@ asks.
roundTrip :: Maybe FilePath -> Map.Map ModuleName.Canonical Core.Module -> IO (Map.Map ModuleName.Canonical Core.Module)
roundTrip wireDir cores
  | not Dump.wireRoundTrip && Maybe.isNothing wireDir = return cores
  | otherwise = Map.traverseWithKey oneModule cores
  where
    oneModule home core =
      case Wire.encode core of
        Left problems ->
          error (unlines (("Core.Wire: " ++ ModuleName.toChars (ModuleName._module home)) : problems))
        Right encoded ->
          do
            case wireDir of
              Nothing -> return ()
              Just dir -> Dump.writeWire dir home (B.byteString encoded)
            if not Dump.wireRoundTrip
              then return core
              else case Wire.decode encoded of
                Right back -> return back
                Left err ->
                  error
                    ( "Core.Wire: what "
                        ++ ModuleName.toChars (ModuleName._module home)
                        ++ " encoded to does not decode: "
                        ++ Wire.renderError err
                    )

-- | The Core of the modules being built, by raw name.
--
-- 'programCore' is this plus the dependencies', keyed canonically. It is
-- separate because 'checkForDebugUses' wants exactly this half — @--optimize@
-- rejects a @Debug@ use in the project and not in a package it depends on — and
-- wants the raw name, which is what the error prints.
--
-- A cached module contributes its Core like any other, which matters twice
-- over here: 'checkForDebugUses' is @--optimize@'s check, and a cached
-- module whose @Debug@ use went unreported would be a rejection that depended
-- on whether the file happened to be in the cache.
ownCore :: Build.Artifacts -> Map.Map ModuleName.Raw Core.Module
ownCore (Build.Artifacts _ _ roots modules) =
  Map.fromList (map moduleCore modules ++ Maybe.mapMaybe rootCore (NE.toList roots))
  where
    moduleCore modul =
      case modul of
        Build.Fresh name _ core -> (name, core)
        Build.Cached name _ core -> (name, core)

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
backendFor kernels _ =
  Program.Backend
    { Program._backendKernels = Map.map kernelInfo kernels,
      Program._backendEdges = Map.empty
    }

kernelInfo :: [K.Chunk] -> Program.Kernel
kernelInfo chunks =
  Program.Kernel
    { Program._kernelGren = Set.fromList [Core.QualName home name | K.GrenVar home name <- chunks],
      Program._kernelKernels = Set.fromList [short | K.JsVar short _ <- chunks],
      Program._kernelFields = Map.keysSet (K.countFields chunks)
    }

-- A runtime's entry points used to be edges from here into kernel modules: a
-- @main@ to @Scheduler@ and @Platform@, and a @Task@ extern to @Scheduler@.
-- Since step 8b the scheduler and the export are helpers the backend emits
-- itself, ahead of every binding (D285, @m1b-source.md@ §SO24), so no
-- declaration needs an edge, and the REPL's to @Debug@ is the only one left
-- ('replBackend').

-- | The linked Core program (§J15).
--
-- This is the whole of what the emitter is handed besides the kernel chunks: one
-- call to `Core.Program.link`, with the roots 'coreRoots' names and the kernel
-- information 'kernelInfo' reads off those same chunks.
linkCore :: Target.Target -> Details.Details -> Build.Artifacts -> Map.Map N.Name [K.Chunk] -> Task Program.Program
linkCore target details artifacts kernels =
  Task.io $
    do
      cores <- Program.chooseExterns (Target.language target) Dump.externBodies <$> (programCore details artifacts >>= passed)
      let program = Program.link (backendFor kernels cores) cores (coreRoots artifacts cores)
      reported program
      return (checked program)

-- | @GENG_SPECIALIZE_REPORT@: the same question 'checked' asks, written down
-- instead of refused.
reported :: Program.Program -> IO ()
reported program =
  case Dump.specializeReport of
    Nothing -> return ()
    Just file ->
      writeFile file (unlines (List.sort (map Program.qualToChars (Program.unspecialized program))))

-- | @GENG_SPECIALIZE_STRICT=1@: the linked program carries no witness node.
--
-- D127 puts the question to a linked program rather than to a module, and this
-- is the only place it can be asked: 'Core.Pass.run' has every module but not
-- the roots, so it cannot tell a binding nothing reaches from one the pass
-- failed to reach. Off by default, because §G27.3 makes giving up on a site
-- legitimate — the witness path still runs. On for @harness/run.py@\'s
-- @geng-hs-spec@ target, where it is the standing form of the measurement that
-- the pass is complete on every program the corpus has.
checked :: Program.Program -> Program.Program
checked program
  | not Dump.specializeStrict = program
  | otherwise =
      case Program.unspecialized program of
        [] -> program
        names ->
          error $
            "GENG_SPECIALIZE_STRICT: "
              ++ show (length names)
              ++ " reachable binding(s) still carry a witness or type-abstraction node:\n"
              ++ unlines (map (("  " ++) . Program.qualToChars) names)

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
  return (Details.loadKernels details)

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
-- registers itself in. They were edges instead, and are now helpers the backend
-- emits ahead of everything (§SO24).
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

-- | Write what @GENG_DUMP_PROGRAM_CORE@, @GENG_DUMP_LINK@ and @GENG_DUMP_PRIMS@
-- ask for, if any names a place to put it.
--
-- The first is the program's Core, module by module, with the same file names as
-- "Compile"'s per-module dump so that the two are comparable as directories. The
-- second is 'Core.Program.link''s summary: what the roots reach, in what order,
-- and what they refer to that Core cannot supply yet.
dumpCore :: Target.Target -> Details.Details -> Build.Artifacts -> Map.Map N.Name [K.Chunk] -> Task ()
dumpCore target details artifacts kernels =
  case (Dump.programDir, Dump.linkFile, Dump.primsFile) of
    (Nothing, Nothing, Nothing) -> return ()
    (maybeDir, maybeFile, maybePrims) ->
      Task.io $
        do
          modules <- programCore details artifacts
          let cores = Program.chooseExterns (Target.language target) Dump.externBodies modules
          case maybeDir of
            Nothing -> return ()
            Just dir ->
              mapM_
                (\(home, core) -> Dump.writeModule dir home (Pretty.moduleToBuilder Pretty.defaultOptions core))
                (Map.toAscList modules)
          let roots =
                if Dump.linkEveryExport
                  then concatMap Core._moduleExports (Map.elems cores)
                  else coreRoots artifacts cores
              linked = Program.link (backendFor kernels cores) cores roots
          case maybeFile of
            Nothing -> return ()
            Just file -> B.writeFile file (Program.render linked)
          case maybePrims of
            Nothing -> return ()
            Just file -> B.writeFile file (Program.renderPrims linked)

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
          cores <- Program.chooseExterns Core.ExternC Dump.externBodies <$> (programCore details artifacts >>= passed)
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
repl :: Details.Details -> ExtSources -> Bool -> Build.ReplArtifacts -> N.Name -> Task B.Builder
repl details sources ansi artifacts@(Build.ReplArtifacts home _ localizer annotations) name =
  do
    kernels <- kernelChunks details
    program <- linkReplCore details artifacts name kernels
    exts <- externFiles Target.Js sources program
    return $ CoreJS.generateForRepl ansi localizer program kernels exts home name (annotations ! name)

-- | 'linkCore' for a REPL entry, which differs from a program in its roots.
--
-- The modules are the REPL\'s own — the generated @Gren_Repl@ module and
-- whatever it imports out of the project — plus the dependencies\' Core, exactly
-- as 'programCore' assembles them for a build, and a cached module contributes
-- its Core here too (D98).
linkReplCore :: Details.Details -> Build.ReplArtifacts -> N.Name -> Map.Map N.Name [K.Chunk] -> Task Program.Program
linkReplCore details (Build.ReplArtifacts home modules _ _) name kernels =
  do
    let deps = Details.loadCores details
    let own =
          Map.fromList
            [ (ModuleName.Canonical (ModuleName._package home) raw, core)
            | (raw, core) <- map replModuleCore modules
            ]
    checkReached Target.Js (Map.union own deps) (Map.keys own)
    Task.io $
      do
        cores <- Program.chooseExterns (Target.language Target.Js) Dump.externBodies <$> (throughWire (Map.union own deps) >>= passed)
        return (checked (Program.link (replBackend kernels cores home name) cores (replRoots home name)))

replModuleCore :: Build.Module -> (ModuleName.Raw, Core.Module)
replModuleCore modul =
  case modul of
    Build.Fresh raw _ core -> (raw, core)
    Build.Cached raw _ core -> (raw, core)

-- | What a REPL entry reaches: the value being printed, and nothing else.
--
-- It used to root @Debug.toString@ as well — not because anything generated
-- calls it, but because that binding was what reached the kernel @Debug@ module
-- the printer's @_Debug_toAnsiString@ lives in. §J13\'s rule said that should be
-- an /edge/ and not a root, since a root says a thing is reachable and says
-- nothing about when; the reason it was a root anyway was to keep the Core REPL
-- and the graph-walking one reaching the same set, so that comparing their
-- output tested the emitter rather than two different programs.
--
-- §J18 deleted the other REPL and §G45 deleted @Debug.toString@, so both halves
-- of that are spent. 'replBackend' supplies the edge §J13 always wanted.
replRoots :: ModuleName.Canonical -> N.Name -> [Core.QualName]
replRoots home name =
  [Core.QualName home name]

-- | A program's backend plus the one edge a REPL entry has that a program does
-- not: the printer.
--
-- @Generate.CoreJS.printForRepl@ is appended after every linked item and calls
-- kernel @Debug@\'s @_Debug_toAnsiString@ directly, so the kernel @Debug@ module
-- has to be emitted and has to come first. That is the same shape as a @port@\'s
-- constructor and a static @main@ in 'runtimeEdges' — a name a /runtime/ enters
-- a declaration through, which C16 keeps out of Core and the backend supplies
-- here — and it hangs off the printed value, which is the one binding a REPL
-- entry is guaranteed to have.
replBackend ::
  Map.Map N.Name [K.Chunk] ->
  Map.Map ModuleName.Canonical Core.Module ->
  ModuleName.Canonical ->
  N.Name ->
  Program.Backend
replBackend kernels cores home name =
  let backend = backendFor kernels cores
   in backend
        { Program._backendEdges =
            Map.insertWith
              (<>)
              (Core.QualName home name)
              (Refs.global (Program.kernelName N.debug))
              (Program._backendEdges backend)
        }

-- EXTERN FILES

-- | Every source the build was handed, by package: the project's own and each
-- dependency's, as "Make" and "Repl" hold them.
--
-- A @js@ extern's implementation is @src/Ext/<Module>.js@ (F1, D198), and the
-- front end reads it with the package's other sources under the name
-- @Ext.<Module>@, as it reads kernel JavaScript under @Gren.Kernel.<Module>@.
-- So it is already inside every dependency's fingerprint, and a changed
-- implementation file is a changed package without a second mechanism.
type ExtSources =
  Map.Map Pkg.Name (Map.Map ModuleName.Raw BS.ByteString)

-- | 'ExtSources' from what "Make" and "Repl" are handed. The project's own
-- package is named the way "Build" names it, a dummy name for an application.
extSources :: Outline.Outline -> Build.Sources -> Map.Map Pkg.Name Details.Dependency -> ExtSources
extSources outline sources deps =
  let own =
        case outline of
          Outline.App _ -> Pkg.application
          Outline.Pkg pkgOutline -> Outline._pkg_name pkgOutline
   in Map.insert own (Map.map Build._source_data sources) (Map.map Details._dep_sources deps)

-- | The implementation file of every reachable @js@ extern, by package and
-- module (D198).
--
-- A reachable extern whose file is not there is refused here, at build time,
-- rather than left for the program to find when it loads. One with no @js@ row
-- at all never gets here: 'checkTarget' has refused its module.
-- A file that is there but lacks the function, or has it at another arity, is
-- the load-time check F1's table gives JavaScript.
--
-- The rows are the target's language ('Target.language'), but the file is
-- still JavaScript's, since @js@ is the only target 'checkReached' lets
-- through; it moves behind the JavaScript backend with the rest (@m2-seam.md@
-- §DS5).
externFiles :: Target.Target -> ExtSources -> Program.Program -> Task (Map.Map (Pkg.Name, N.Name) BS.ByteString)
externFiles target sources program =
  let wanted =
        [ ( home,
            Core._binderName (Core._externBinder e),
            [modul | Core.ExternImpl language (modul : _) <- Core._externImpls e, language == Target.language target]
          )
        | (home, e) <- Program._progExterns program
        ]
      found =
        [ case moduls of
            [] -> error ("Generate.externFiles: " ++ N.toChars name ++ " has no js row, which checkTarget refuses")
            modul : _ ->
              let pkg = ModuleName._package home
                  short = N.fromChars (Utf8.toChars modul)
               in case Map.lookup (N.fromChars ("Ext." ++ Utf8.toChars modul)) =<< Map.lookup pkg sources of
                    Nothing -> Left (ModuleName._module home, name, "src/Ext/" ++ Utf8.toChars modul ++ ".js")
                    Just bytes -> Right ((pkg, short), bytes)
        | (home, name, moduls) <- wanted
        ]
   in case [problem | Left problem <- found] of
        [] -> return (Map.fromList [file | Right file <- found])
        problems -> Task.throw (Exit.GenerateExternUnimplemented problems)

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
