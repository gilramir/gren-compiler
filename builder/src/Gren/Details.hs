{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module Gren.Details
  ( Details (..),
    Artifacts (..),
    Header (..),
    BuildID,
    ValidOutline (..),
    Dependency (..),
    Local (..),
    Foreign (..),
    load,
    Interfaces,
    loadInterfaces,
    Cores,
    loadCores,
    Kernels,
    loadKernels,
    toHeader,
  )
where

import AST.Canonical qualified as Can
import AST.Source qualified as Src
import Compile qualified
import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (MVar, newEmptyMVar, putMVar, readMVar, takeMVar)
import Control.Monad (liftM2, liftM3)
import Core.AST qualified as Core
import Core.Wire qualified as Wire
import Data.Binary (Binary, get, getWord8, put, putWord8)
import Data.ByteString qualified as BS
import Data.ByteString.Internal (ByteString)
import Data.Either qualified as Either
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Map.Merge.Strict qualified as Map
import Data.Map.Utils qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name qualified as Name
import Data.NonEmptyList qualified as NE
import Data.OneOrMore qualified as OneOrMore
import Data.Word (Word64)
import Directories qualified as Dirs
import File qualified
import Gren.Docs qualified as Docs
import Gren.Fingerprint (Fingerprint)
import Gren.Fingerprint qualified as FP
import Gren.Interface qualified as I
import Gren.Kernel qualified as Kernel
import Gren.ModuleName qualified as ModuleName
import Gren.Outline (Outline)
import Gren.Outline qualified as Outline
import Gren.Package qualified as Pkg
import Gren.Platform qualified as P
import Gren.Version qualified as V
import Parse.Module qualified as Parse
import Reporting.Annotation qualified as A
import Reporting.Exit qualified as Exit
import Reporting.Task qualified as Task

-- DETAILS

-- | Everything a build needs to know before it starts, and everything it
-- learned last time.
--
-- __There is no @Binary Details@__, and that is deliberate (D98). A 'Details'
-- holds the dependencies' artifacts, which live in three files of their own;
-- what @d.dat@ holds is a 'Header', and the two types being different is what
-- stops the artifacts from being written into it by accident or, worse, read
-- back out of it as empty maps. Every 'ArtifactsCached' comment in this file and
-- in "Generate" was about exactly that hazard.
data Details = Details
  { _fingerprint :: Fingerprint,
    _outline :: ValidOutline,
    _buildID :: BuildID,
    _locals :: Map.Map ModuleName.Raw Local,
    _foreigns :: Map.Map ModuleName.Raw Foreign,
    _artifacts :: Artifacts
  }

-- | What @d.dat@ holds: a 'Details' without its artifacts.
data Header = Header
  { _hFingerprint :: Fingerprint,
    _hOutline :: ValidOutline,
    _hBuildID :: BuildID,
    _hLocals :: Map.Map ModuleName.Raw Local,
    _hForeigns :: Map.Map ModuleName.Raw Foreign
  }

toHeader :: Details -> Header
toHeader (Details fingerprint outline buildID locals foreigns _) =
  Header fingerprint outline buildID locals foreigns

type BuildID = Word64

data ValidOutline
  = ValidApp P.Platform (NE.List Outline.SrcDir)
  | ValidPkg P.Platform Pkg.Name [ModuleName.Raw]
  deriving (Eq)

data Dependency = Dependency
  { _dep_outline :: Outline,
    _dep_sources :: Map ModuleName.Raw ByteString
  }
  deriving (Show)

-- | What the last build knew about one of the project's own modules.
--
-- __Two independent reasons to recompile__, and a cache that keeps only one of
-- them is wrong in a way no test of a single build can see:
--
-- (1) '_source' is the fingerprint of the bytes the module was compiled from
-- (D96). If the bytes the frontend hands us now differ, the module is
-- recompiled. Stock keeps a modification time here and asks the same question
-- of the clock; "Gren.Fingerprint" says why the bytes are the better witness.
--
-- (2) '_lastChange' is the 'BuildID' at which this module's __interface__ last
-- changed, and '_lastCompile' the one at which it was last compiled. They
-- differ when a module is recompiled and its interface comes out the same. A
-- module must be recompiled when its '_lastCompile' is __less than__ the
-- '_lastChange' of anything it imports — which is not the same question as (1),
-- because the module's own source need not have moved. It happens whenever a
-- project has more than one entrypoint: @gren make A@ then @gren make B@ then
-- @gren make A@ again, where B's build changed an interface that A's modules
-- had already been compiled against. Reason (1) sees nothing there at all.
data Local = Local
  { _path :: FilePath,
    _source :: Fingerprint,
    _deps :: [ModuleName.Raw],
    _lastChange :: BuildID,
    _lastCompile :: BuildID
  }

data Foreign
  = Foreign Pkg.Name [Pkg.Name]

-- | The dependencies' artifacts, whether they were just built or just read.
--
-- One constructor, and it used to be two: 'ArtifactsCached' meant "they are on
-- disk somewhere, ask again later", which is why every reader of it returned a
-- 'Maybe' and why "Generate" had a @fromMaybe Map.empty@ standing where a
-- missing dependency would have produced a silently smaller program. 'load'
-- now reads the three files itself and falls back to building when any of them
-- will not load, so by the time anything holds a 'Details' the artifacts are in
-- hand. The hazard is gone as a type rather than as a comment.
data Artifacts = Artifacts Interfaces Cores Kernels

type Interfaces =
  Map.Map ModuleName.Canonical I.DependencyInterface

-- | Every dependency module's Core, on the way to the backend.
--
-- The same route the objects take, for the same reason: M1a re-targets the JS
-- backend onto Core, so Core has to reach 'Generate' for the dependencies and
-- not only for the modules being built. Nothing here is forced by a build that
-- does not generate code — 'Core.Lower.Module' is a pure function behind a lazy
-- field.
type Cores =
  Map.Map ModuleName.Canonical Core.Module

-- | Every kernel module's JavaScript, by its short name — @Array@ for
-- @Gren.Kernel.Array@, which is the name 'Core.Program.kernelName' builds a
-- 'Core.QualName' from.
--
-- C16 keeps kernel JavaScript in the build system and lets only names cross into
-- the IR, and this is where the build system keeps it. It used to be read back
-- out of the @AST.Optimized.GlobalGraph@, which @gatherObjects@ had folded it
-- into — the graph was the only thing that reached "Generate", so everything
-- travelled in it. Now that the backend is Core, a chunk has no reason to go
-- through the old pipeline's data structure to get to the emitter that splices
-- it.
--
-- Only a dependency contributes: a project's own kernel modules are 'RKernel' in
-- "Build", which adds nothing to a root's artifacts, and only a @gren-lang@
-- kernel package may contain one at all.
type Kernels =
  Map.Map Name.Name [Kernel.Chunk]

-- LOAD ARTIFACTS
--
-- Three accessors, all total. They were three readers returning a 'Maybe' each,
-- because 'ArtifactsCached' meant the file had not been read yet and might not
-- read; 'load' does that reading now.

loadInterfaces :: Details -> Interfaces
loadInterfaces (Details _ _ _ _ _ (Artifacts i _ _)) = i

-- | The dependency modules' Core, on its way to the backend.
loadCores :: Details -> Cores
loadCores (Details _ _ _ _ _ (Artifacts _ c _)) = c

-- | The kernel modules' JavaScript.
loadKernels :: Details -> Kernels
loadKernels (Details _ _ _ _ _ (Artifacts _ _ k)) = k

-- LOAD -- used by Make, Docs, Repl

-- | The project's details, from @d.dat@ when it still describes this build and
-- from the dependency sources when it does not (D96).
--
-- __What makes @d.dat@ believable is three equalities and three files.__ The
-- 'ValidOutline' it recorded must equal the one this build derives — the
-- platform, the source directories, the exposed list — and its 'Fingerprint'
-- must equal this build's dependency set, byte for byte, which is what
-- 'dependencyFingerprint' computes. Then @i.dat@, @c.dat@ and @k.dat@ must all
-- load. Any of the six failing means a fresh dependency build, which also
-- rewrites all three files.
--
-- Two things upstream needed and this does not. There is no modification-time
-- comparison, because the fingerprint is over the bytes. And there is no
-- @containsLocalDeps@ guard refusing to cache a project with a filesystem-path
-- dependency: a local dependency's sources arrive in the solution like any
-- other's and are fingerprinted like any other's, so the case that had to be
-- excluded is now just a case that invalidates when it changes.
load :: FilePath -> Outline.Outline -> Map.Map Pkg.Name Dependency -> IO (Either Exit.Details Details)
load root outline solution =
  let (validOutline, directDeps) =
        case outline of
          Outline.Pkg (Outline.PkgOutline pkg _ _ _ exposed direct _ rootPlatform) ->
            (ValidPkg rootPlatform pkg (Outline.flattenExposed exposed), Map.map (const ()) direct)
          Outline.App (Outline.AppOutline _ rootPlatform srcDirs direct _) ->
            (ValidApp rootPlatform srcDirs, Map.map (const ()) direct)
      fingerprint = dependencyFingerprint solution
   in do
        reused <- reuse root validOutline fingerprint
        case reused of
          Just details -> return (Right details)
          Nothing ->
            Task.run (verifyDependencies root fingerprint validOutline solution directDeps)

-- | @d.dat@ and the three artifact files, if all four are there and all four
-- describe this build.
reuse :: FilePath -> ValidOutline -> Fingerprint -> IO (Maybe Details)
reuse root validOutline fingerprint =
  do
    maybeHeader <- File.readBinary (Dirs.details root)
    case maybeHeader of
      Just (Header oldFingerprint oldOutline buildID locals foreigns)
        | oldFingerprint == fingerprint && oldOutline == validOutline ->
            do
              maybeArtifacts <- readArtifacts root
              case maybeArtifacts of
                Nothing -> return Nothing
                Just artifacts ->
                  return $ Just $ Details fingerprint validOutline (buildID + 1) locals foreigns artifacts
      _ ->
        return Nothing

-- | The three files, or nothing if any of them is missing or will not decode.
--
-- All three or none. A build that had the interfaces and not the Core would
-- link a program with modules missing from it, which is the failure §B11 of
-- @docs\/m1a-wire.md@ named and could not do anything about while the cache was
-- unreachable.
readArtifacts :: FilePath -> IO (Maybe Artifacts)
readArtifacts root =
  do
    ifacesMVar <- fork (File.readBinary (Dirs.interfaces root))
    coresMVar <- fork (readCores root)
    kernelsMVar <- fork (File.readBinary (Dirs.kernels root))
    maybeIfaces <- readMVar ifacesMVar
    maybeCores <- readMVar coresMVar
    maybeKernels <- readMVar kernelsMVar
    return (Artifacts <$> maybeIfaces <*> maybeCores <*> maybeKernels)

-- | The dependencies' Core, from @c.dat@ (D98).
--
-- The file is a @Data.Binary@ map from module to __C10 wire bytes__, and the
-- values are decoded by 'Core.Wire'. Core does not get a @Binary@ instance to
-- suit this file: it has a format of record, a schema, and a gate that holds
-- two codecs to it, and a second encoding written for the cache would be a
-- format nobody checked. That was the standing reason this branch could not be
-- written before C10 existed.
readCores :: FilePath -> IO (Maybe Cores)
readCores root =
  do
    maybeRaw <- File.readBinary (Dirs.cores root)
    case maybeRaw of
      Nothing -> return Nothing
      Just raw -> return (traverse decodeCore raw)

decodeCore :: BS.ByteString -> Maybe Core.Module
decodeCore encoded =
  case Wire.decode encoded of
    Right core -> Just core
    Left _ -> Nothing

-- | The whole dependency set as one number: every package, every module, every
-- byte of every source, each length-prefixed and in ascending order (D96).
--
-- Ascending order is C6's discipline and it is not decoration — @Map.toAscList@
-- is the only thing that makes this reproducible across two runs that solved
-- the dependency graph in different orders.
dependencyFingerprint :: Map.Map Pkg.Name Dependency -> Fingerprint
dependencyFingerprint solution =
  List.foldl' onePackage FP.empty (Map.toAscList solution)
  where
    onePackage acc (pkg, Dependency _ sources) =
      List.foldl' oneModule (FP.chars (Pkg.toChars pkg) acc) (Map.toAscList sources)

    oneModule acc (name, source) =
      FP.bytes source (FP.chars (ModuleName.toChars name) acc)

type Task a = Task.Task Exit.Details a

-- FORK

fork :: IO a -> IO (MVar a)
fork work =
  do
    mvar <- newEmptyMVar
    _ <- forkIO $ putMVar mvar =<< work
    return mvar

-- VERIFY DEPENDENCIES

verifyDependencies :: FilePath -> Fingerprint -> ValidOutline -> Map.Map Pkg.Name Dependency -> Map.Map Pkg.Name a -> Task Details
verifyDependencies root fingerprint outline solution directDeps =
  Task.eio id $
    do
      mvar <- newEmptyMVar
      mvars <- Map.traverseWithKey (\k v -> fork (build mvar k v)) solution
      putMVar mvar mvars
      deps <- traverse readMVar mvars
      case sequence deps of
        Left _ ->
          do
            home <- Dirs.getGrenHome
            return $
              Left $
                Exit.DetailsBadDeps home $
                  Maybe.catMaybes $
                    Either.lefts $
                      Map.elems deps
        Right artifacts ->
          let ifaces = Map.foldrWithKey (addInterfaces directDeps) Map.empty artifacts
              cores = Map.foldrWithKey addCores Map.empty artifacts
              kernels = Map.foldr addKernels Map.empty artifacts
              foreigns = Map.map (OneOrMore.destruct Foreign) $ Map.foldrWithKey gatherForeigns Map.empty $ Map.intersection artifacts directDeps
              details = Details fingerprint outline 0 Map.empty foreigns (Artifacts ifaces cores kernels)
           in do
                writeArtifacts root ifaces cores kernels
                return $ Right details

-- | The three files 'readArtifacts' will look for next time (D98).
--
-- __Written before @d.dat@ is, and that ordering is the whole of the crash
-- safety here.__ @Build.writeDetails@ writes @d.dat@ at the end of a successful
-- build, and @d.dat@ is what says the other three may be believed; a build
-- killed between these writes and that one leaves a @d.dat@ that is older than
-- the sources, which fails the fingerprint check and costs one rebuild.
--
-- __A module whose Core will not encode is not written and stops the file
-- being written at all__, rather than being quietly left out. D91's
-- out-of-range 'Core.AST.LIntLegacy' is the one thing a user can write that
-- does that, and a program containing one still compiles to JavaScript today —
-- so the cache must not be the thing that breaks it. No @c.dat@ means no reuse
-- next time, which is the honest outcome: slower, never wrong.
writeArtifacts :: FilePath -> Interfaces -> Cores -> Kernels -> IO ()
writeArtifacts root ifaces cores kernels =
  do
    File.writeBinary (Dirs.interfaces root) ifaces
    File.writeBinary (Dirs.kernels root) kernels
    case traverse encodeCore cores of
      Nothing -> File.remove (Dirs.cores root)
      Just encoded -> File.writeBinary (Dirs.cores root) encoded

encodeCore :: Core.Module -> Maybe BS.ByteString
encodeCore core =
  case Wire.encode core of
    Right bytes -> Just bytes
    Left _ -> Nothing

addCores :: Pkg.Name -> DepArtifacts -> Cores -> Cores
addCores pkg (DepArtifacts _ cores _) acc =
  Map.union acc (Map.mapKeysMonotonic (ModuleName.Canonical pkg) cores)

-- | A kernel module's short name is its whole identity — @Gren.Kernel.Array@ is
-- @Array@ in every package that could define one — so these merge by name and
-- not by package.
addKernels :: DepArtifacts -> Kernels -> Kernels
addKernels (DepArtifacts _ _ kernels) acc =
  Map.union acc kernels

addInterfaces :: Map.Map Pkg.Name a -> Pkg.Name -> DepArtifacts -> Interfaces -> Interfaces
addInterfaces directDeps pkg (DepArtifacts ifaces _ _) dependencyInterfaces =
  Map.union dependencyInterfaces $
    Map.mapKeysMonotonic (ModuleName.Canonical pkg) $
      if Map.member pkg directDeps
        then ifaces
        else Map.map I.privatize ifaces

gatherForeigns :: Pkg.Name -> DepArtifacts -> Map.Map ModuleName.Raw (OneOrMore.OneOrMore Pkg.Name) -> Map.Map ModuleName.Raw (OneOrMore.OneOrMore Pkg.Name)
gatherForeigns pkg (DepArtifacts ifaces _ _) foreigns =
  let isPublic di =
        case di of
          I.Public _ -> Just (OneOrMore.one pkg)
          I.Private _ _ _ -> Nothing
   in Map.unionWith OneOrMore.more foreigns (Map.mapMaybe isPublic ifaces)

-- VERIFY DEPENDENCY

-- | One dependency's artifacts, keyed by raw module name. 'Artifacts' is the
-- whole set, keyed canonically.
data DepArtifacts = DepArtifacts
  { _ifaces :: Map.Map ModuleName.Raw I.DependencyInterface,
    _cores :: Map.Map ModuleName.Raw Core.Module,
    _kernels :: Kernels
  }

type Dep =
  Either (Maybe Exit.DetailsBadDep) DepArtifacts

-- BUILD

build :: MVar (Map.Map Pkg.Name (MVar Dep)) -> Pkg.Name -> Dependency -> IO Dep
build depsMVar pkg (Dependency outline sources) =
  case outline of
    (Outline.App _) ->
      do
        return $ Left $ Just $ Exit.BD_BadBuild pkg V.one Map.empty
    (Outline.Pkg (Outline.PkgOutline _ _ _ _ exposed deps _ platform)) ->
      do
        allDeps <- readMVar depsMVar
        directDeps <- traverse readMVar (Map.intersection allDeps deps)
        case sequence directDeps of
          Left _ ->
            do
              return $ Left Nothing
          Right directArtifacts ->
            do
              let foreignDeps = gatherForeignInterfaces directArtifacts
              let exposedDict = Map.fromKeys (const ()) (Outline.flattenExposed exposed)
              let docsStatus = DocsNeeded
              let authorizedForKernelCode = Pkg.isKernel pkg
              mvar <- newEmptyMVar
              mvars <- Map.traverseWithKey (const . fork . crawlModule foreignDeps sources mvar pkg docsStatus authorizedForKernelCode) exposedDict
              putMVar mvar mvars
              mapM_ readMVar mvars
              maybeStatuses <- traverse readMVar =<< readMVar mvar
              case sequence maybeStatuses of
                Left CrawlCorruption ->
                  do
                    return $ Left $ Just $ Exit.BD_BadBuild pkg V.one Map.empty
                Left CrawlUnsignedKernelCode ->
                  do
                    return $ Left $ Just $ Exit.BD_UnsignedBuild pkg V.one
                Right statuses ->
                  do
                    rmvar <- newEmptyMVar
                    rmvars <- traverse (fork . compile platform pkg rmvar) statuses
                    putMVar rmvar rmvars
                    maybeResults <- traverse readMVar rmvars
                    case sequence maybeResults of
                      Nothing ->
                        do
                          return $ Left $ Just $ Exit.BD_BadBuild pkg V.one Map.empty
                      Just results ->
                        let ifaces = gatherInterfaces exposedDict results
                            cores = gatherCores results
                            kernels = gatherKernels results
                            artifacts = DepArtifacts ifaces cores kernels
                         in do
                              return (Right artifacts)

-- GATHER

-- | The Core of every module in this package that has any.
--
-- Kernel modules have none: they never reach 'Compile.compile', because their
-- JavaScript is spliced in as chunks rather than compiled from Gren.
gatherCores :: Map.Map ModuleName.Raw Result -> Map.Map ModuleName.Raw Core.Module
gatherCores = Map.mapMaybe getCore

getCore :: Result -> Maybe Core.Module
getCore result =
  case result of
    RLocal _ core _ -> Just core
    RForeign _ -> Nothing
    RKernelLocal _ -> Nothing
    RKernelForeign -> Nothing

-- | The kernel modules' chunks, keyed by short name.
gatherKernels :: Map.Map ModuleName.Raw Result -> Kernels
gatherKernels results =
  Map.fromList
    [ (Name.getKernel name, chunks)
    | (name, RKernelLocal chunks) <- Map.toList results
    ]

gatherInterfaces :: Map.Map ModuleName.Raw () -> Map.Map ModuleName.Raw Result -> Map.Map ModuleName.Raw I.DependencyInterface
gatherInterfaces exposed artifacts =
  let onLeft = Map.mapMissing (error "compiler bug manifesting in Gren.Details.gatherInterfaces")
      onRight = Map.mapMaybeMissing (\_ iface -> toLocalInterface I.private iface)
      onBoth = Map.zipWithMaybeMatched (\_ () iface -> toLocalInterface I.public iface)
   in Map.merge onLeft onRight onBoth exposed artifacts

toLocalInterface :: (I.Interface -> a) -> Result -> Maybe a
toLocalInterface func result =
  case result of
    RLocal iface _ _ -> Just (func iface)
    RForeign _ -> Nothing
    RKernelLocal _ -> Nothing
    RKernelForeign -> Nothing

-- GATHER FOREIGN INTERFACES

data ForeignInterface
  = ForeignAmbiguous
  | ForeignSpecific I.Interface

gatherForeignInterfaces :: Map.Map Pkg.Name DepArtifacts -> Map.Map ModuleName.Raw ForeignInterface
gatherForeignInterfaces directArtifacts =
  Map.map (OneOrMore.destruct finalize) $
    Map.foldrWithKey gather Map.empty directArtifacts
  where
    finalize :: I.Interface -> [I.Interface] -> ForeignInterface
    finalize i is =
      case is of
        [] -> ForeignSpecific i
        _ : _ -> ForeignAmbiguous

    gather :: Pkg.Name -> DepArtifacts -> Map.Map ModuleName.Raw (OneOrMore.OneOrMore I.Interface) -> Map.Map ModuleName.Raw (OneOrMore.OneOrMore I.Interface)
    gather _ (DepArtifacts ifaces _ _) buckets =
      Map.unionWith OneOrMore.more buckets (Map.mapMaybe isPublic ifaces)

    isPublic :: I.DependencyInterface -> Maybe (OneOrMore.OneOrMore I.Interface)
    isPublic di =
      case di of
        I.Public iface -> Just (OneOrMore.one iface)
        I.Private _ _ _ -> Nothing

-- CRAWL

type StatusDict =
  Map.Map ModuleName.Raw (MVar (Either CrawlError Status))

data Status
  = SLocal DocsStatus (Map.Map ModuleName.Raw ()) Src.Module
  | SForeign I.Interface
  | SKernelLocal [Kernel.Chunk]
  | SKernelForeign

data CrawlError
  = CrawlUnsignedKernelCode
  | CrawlCorruption

crawlModule :: Map.Map ModuleName.Raw ForeignInterface -> Map.Map ModuleName.Raw ByteString -> MVar StatusDict -> Pkg.Name -> DocsStatus -> Bool -> ModuleName.Raw -> IO (Either CrawlError Status)
crawlModule foreignDeps sources mvar pkg docsStatus authorizedForKernelCode name =
  case (Map.lookup name foreignDeps, Map.lookup name sources) of
    (Just ForeignAmbiguous, _) ->
      return $ Left CrawlCorruption
    (Just (ForeignSpecific iface), Nothing) ->
      return $ Right (SForeign iface)
    (Just (ForeignSpecific _), Just _) ->
      return $ Left CrawlCorruption
    (_, Just bytes) ->
      if Pkg.isKernel pkg && Name.isKernel name
        then
          if authorizedForKernelCode
            then crawlKernel foreignDeps sources mvar pkg bytes
            else return $ Left CrawlUnsignedKernelCode
        else crawlFile foreignDeps sources mvar pkg docsStatus authorizedForKernelCode name bytes
    (Nothing, Nothing) ->
      if Pkg.isKernel pkg && Name.isKernel name && authorizedForKernelCode
        then return $ Right SKernelForeign
        else return $ Left CrawlCorruption

crawlFile :: Map.Map ModuleName.Raw ForeignInterface -> Map.Map ModuleName.Raw ByteString -> MVar StatusDict -> Pkg.Name -> DocsStatus -> Bool -> ModuleName.Raw -> ByteString -> IO (Either CrawlError Status)
crawlFile foreignDeps sources mvar pkg docsStatus authorizedForKernelCode expectedName bytes =
  case Parse.fromByteString (Parse.Package pkg) bytes of
    Right modul@(Src.Module (Just (A.At _ actualName)) _ _ imports _ _ _ _ _ _ _) | expectedName == actualName ->
      do
        deps <- crawlImports foreignDeps sources mvar pkg authorizedForKernelCode (fmap snd imports)
        return (Right (SLocal docsStatus deps modul))
    _ ->
      return $ Left CrawlCorruption

crawlImports :: Map.Map ModuleName.Raw ForeignInterface -> Map.Map ModuleName.Raw ByteString -> MVar StatusDict -> Pkg.Name -> Bool -> [Src.Import] -> IO (Map.Map ModuleName.Raw ())
crawlImports foreignDeps sources mvar pkg authorizedForKernelCode imports =
  do
    statusDict <- takeMVar mvar
    let deps = Map.fromList (map (\i -> (Src.getImportName i, ())) imports)
    let news = Map.difference deps statusDict
    mvars <- Map.traverseWithKey (const . fork . crawlModule foreignDeps sources mvar pkg DocsNotNeeded authorizedForKernelCode) news
    putMVar mvar (Map.union mvars statusDict)
    mapM_ readMVar mvars
    return deps

crawlKernel :: Map.Map ModuleName.Raw ForeignInterface -> Map.Map ModuleName.Raw ByteString -> MVar StatusDict -> Pkg.Name -> ByteString -> IO (Either CrawlError Status)
crawlKernel foreignDeps sources mvar pkg bytes =
  case Kernel.fromByteString pkg (Map.mapMaybe getDepHome foreignDeps) bytes of
    Nothing ->
      return $ Left CrawlCorruption
    Just (Kernel.Content imports chunks) ->
      do
        _ <- crawlImports foreignDeps sources mvar pkg True imports
        return (Right (SKernelLocal chunks))

getDepHome :: ForeignInterface -> Maybe Pkg.Name
getDepHome fi =
  case fi of
    ForeignSpecific (I.Interface pkg _ _ _ _) -> Just pkg
    ForeignAmbiguous -> Nothing

-- COMPILE

data Result
  = -- | The 'Core.Module' field carries no bang: a build that generates no code
    -- never forces it, and lowering a module it is not going to use would be
    -- the one cost this plumbing could have added.
    RLocal !I.Interface Core.Module (Maybe Docs.Module)
  | RForeign I.Interface
  | RKernelLocal [Kernel.Chunk]
  | RKernelForeign

compile :: P.Platform -> Pkg.Name -> MVar (Map.Map ModuleName.Raw (MVar (Maybe Result))) -> Status -> IO (Maybe Result)
compile platform pkg mvar status =
  case status of
    SLocal docsStatus deps modul ->
      do
        resultsDict <- readMVar mvar
        maybeResults <- traverse readMVar (Map.intersection resultsDict deps)
        case sequence maybeResults of
          Nothing ->
            return Nothing
          Just results ->
            case Compile.compile platform pkg (Map.mapMaybe getInterface results) modul of
              Left _ ->
                return Nothing
              Right (Compile.Artifacts canonical annotations _nodeTypes core) ->
                let ifaces = I.fromModule pkg canonical annotations
                    docs = makeDocs docsStatus canonical
                 in return (Just (RLocal ifaces core docs))
    SForeign iface ->
      return (Just (RForeign iface))
    SKernelLocal chunks ->
      return (Just (RKernelLocal chunks))
    SKernelForeign ->
      return (Just RKernelForeign)

getInterface :: Result -> Maybe I.Interface
getInterface result =
  case result of
    RLocal iface _ _ -> Just iface
    RForeign iface -> Just iface
    RKernelLocal _ -> Nothing
    RKernelForeign -> Nothing

-- MAKE DOCS

data DocsStatus
  = DocsNeeded
  | DocsNotNeeded

makeDocs :: DocsStatus -> Can.Module -> Maybe Docs.Module
makeDocs status modul =
  case status of
    DocsNeeded ->
      case Docs.fromModule modul of
        Right docs -> Just docs
        Left _ -> Nothing
    DocsNotNeeded ->
      Nothing

-- BINARY

-- | @d.dat@'s. 'Details' has none, on purpose — see its own comment.
instance Binary Header where
  put (Header a b c d e) = put a >> put b >> put c >> put d >> put e
  get =
    do
      a <- get
      b <- get
      c <- get
      d <- get
      e <- get
      return (Header a b c d e)

instance Binary ValidOutline where
  put outline =
    case outline of
      ValidApp a b -> putWord8 0 >> put a >> put b
      ValidPkg a b c -> putWord8 1 >> put a >> put b >> put c

  get =
    do
      n <- getWord8
      case n of
        0 -> liftM2 ValidApp get get
        1 -> liftM3 ValidPkg get get get
        _ -> fail "binary encoding of ValidOutline was corrupted"

instance Binary Local where
  put (Local a b c d e) = put a >> put b >> put c >> put d >> put e
  get =
    do
      a <- get
      b <- get
      c <- get
      d <- get
      e <- get
      return (Local a b c d e)

instance Binary Foreign where
  get = liftM2 Foreign get get
  put (Foreign a b) = put a >> put b

-- | 'DepArtifacts' has no 'Binary' instance and does not need one.
--
-- It used to have one that dropped '_cores' on the way out and returned an
-- empty map on the way in, because Core had no format and inventing one for a
-- dead 'ArtifactCache' would have been a format nobody checked. Core has a
-- format now (C10) and the three fields go to three files, each written by
-- 'writeArtifacts' in the encoding that suits it — @Data.Binary@ for the
-- interfaces and the kernel chunks, C10's wire format for the Core.
