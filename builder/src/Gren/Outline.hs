{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module Gren.Outline
  ( Outline (..),
    AppOutline (..),
    PkgOutline (..),
    Exposed (..),
    SrcDir (..),
    PossibleFilePath (..),
    writeVersion,
    encode,
    decoder,
    defaultSummary,
    flattenExposed,
    toAbsoluteSrcDir,
    sourceDirs,
    platform,
    dependencyConstraints,
  )
where

import AbsoluteSrcDir (AbsoluteSrcDir)
import AbsoluteSrcDir qualified
import Control.Monad (liftM)
import Core.Target qualified as Target
import Data.Binary (Binary, get, getWord8, put, putWord8)
import Data.List qualified as List
import Data.Map qualified as Map
import Data.NonEmptyList qualified as NE
import Data.Set qualified as Set
import Foreign.Ptr (minusPtr)
import Gren.Constraint qualified as Con
import Gren.Licenses qualified as Licenses
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Gren.Platform qualified as Platform
import Gren.PossibleFilePath (PossibleFilePath)
import Gren.PossibleFilePath qualified as PossibleFilePath
import Gren.Version qualified as V
import Json.Decode qualified as D
import Json.Encode ((==>))
import Json.Encode qualified as E
import Json.String qualified as Json
import Parse.Primitives qualified as P
import Reporting.Annotation qualified as A
import Reporting.Exit qualified as Exit
import System.FilePath ((</>))
import System.FilePath qualified as FP
import Prelude hiding (read)

-- OUTLINE

data Outline
  = App AppOutline
  | Pkg PkgOutline
  deriving (Show)

data AppOutline = AppOutline
  { _app_gren_version :: V.Version,
    _app_platform :: Platform.Platform,
    _app_source_dirs :: NE.List SrcDir,
    _app_deps_direct :: Map.Map Pkg.Name (PossibleFilePath V.Version),
    _app_deps_indirect :: Map.Map Pkg.Name (PossibleFilePath V.Version),
    -- | The target the application is built for, @js@ unless its @geng.toml@
    -- says otherwise (D308, §MF9).
    _app_target :: Target.Target
  }
  deriving (Show)

data PkgOutline = PkgOutline
  { _pkg_name :: Pkg.Name,
    _pkg_summary :: Json.String,
    _pkg_license :: Licenses.License,
    _pkg_version :: V.Version,
    _pkg_exposed :: Exposed,
    _pkg_deps :: Map.Map Pkg.Name (PossibleFilePath Con.Constraint),
    _pkg_gren_version :: Con.Constraint,
    _pkg_platform :: Platform.Platform,
    -- | The targets the package's @geng.toml@ declares, @any@ being all of
    -- them, or 'Nothing' when it declares none. What its externs serve is
    -- derived, and this is checked against it (D50, D318).
    _pkg_target :: Maybe (Set.Set Target.Target)
  }
  deriving (Show)

data Exposed
  = ExposedList [ModuleName.Raw]
  | ExposedDict [(Json.String, [ModuleName.Raw])]
  deriving (Show)

data SrcDir
  = AbsoluteSrcDir FilePath
  | RelativeSrcDir FilePath
  deriving (Eq, Show)

-- DEFAULTS

defaultSummary :: Json.String
defaultSummary =
  Json.fromChars "helpful summary of your project, less than 80 characters"

-- HELPERS

flattenExposed :: Exposed -> [ModuleName.Raw]
flattenExposed exposed =
  case exposed of
    ExposedList names ->
      names
    ExposedDict sections ->
      concatMap snd sections

platform :: Outline -> Platform.Platform
platform outline =
  case outline of
    App (AppOutline _ pltform _ _ _ _) ->
      pltform
    Pkg (PkgOutline _ _ _ _ _ _ _ pltform _) ->
      pltform

dependencyConstraints :: Outline -> Map.Map Pkg.Name (PossibleFilePath Con.Constraint)
dependencyConstraints outline =
  case outline of
    App appOutline ->
      let direct = _app_deps_direct appOutline
          indirect = _app_deps_indirect appOutline
          appDeps = Map.union direct indirect
       in Map.map (PossibleFilePath.mapWith Con.exactly) appDeps
    Pkg pkgOutline ->
      _pkg_deps pkgOutline

-- WRITE

-- | Set the version in a package's @geng.toml@: the @version@ key of its
-- @[package]@ table, written on a line of its own, which is how @geng init@
-- writes it and how every manifest in the tree has it. The rest of the file,
-- comments included, is left as it was. 'False' means no such line was found and
-- nothing was written.
--
-- The front end reads and edits the manifest with a TOML library, and this is
-- the one write the backend makes (`geng package bump`), so it edits the one line
-- rather than bringing a TOML library to Haskell (geng-lang @m1b-manifest.md@).
writeVersion :: FilePath -> V.Version -> IO Bool
writeVersion root version =
  do
    let path = root </> "geng.toml"
    text <- readFile path
    length text `seq` return ()
    case setVersionLine version (lines text) of
      Nothing ->
        return False
      Just newLines ->
        do
          writeFile path (unlines newLines)
          return True

setVersionLine :: V.Version -> [String] -> Maybe [String]
setVersionLine version = go False
  where
    go _ [] = Nothing
    go inPackage (line : rest) =
      let trimmed = dropWhile (== ' ') line
       in if take 1 trimmed == "["
            then (line :) <$> go (takeWhile (/= ']') (drop 1 trimmed) == "package") rest
            else
              if inPackage && isVersionKey trimmed
                then Just (versionLine line : rest)
                else (line :) <$> go inPackage rest

    isVersionKey trimmed =
      case List.stripPrefix "version" trimmed of
        Just after -> take 1 (dropWhile (== ' ') after) == "="
        Nothing -> False

    versionLine line =
      let indent = takeWhile (== ' ') line
          afterValue = dropWhile (/= '"') (drop 1 (dropWhile (/= '"') line))
       in indent ++ "version = \"" ++ V.toChars version ++ "\"" ++ drop 1 afterValue

-- JSON ENCODE

encode :: Outline -> E.Value
encode outline =
  case outline of
    App (AppOutline gren pltform srcDirs depsDirect depsTrans target) ->
      E.object
        [ "type" ==> E.chars "application",
          "platform" ==> Platform.encode pltform,
          "source-directories" ==> E.list encodeSrcDir (NE.toList srcDirs),
          "gren-version" ==> V.encode gren,
          "dependencies"
            ==> E.object
              [ "direct" ==> encodeDeps V.encode depsDirect,
                "indirect" ==> encodeDeps V.encode depsTrans
              ],
          "target" ==> E.chars (Target.toChars target)
        ]
    Pkg (PkgOutline name summary license version exposed deps gren pltform target) ->
      E.object $
        [ "type" ==> E.string (Json.fromChars "package"),
          "platform" ==> Platform.encode pltform,
          "name" ==> Pkg.encode name,
          "summary" ==> E.string summary,
          "license" ==> Licenses.encode license,
          "version" ==> V.encode version,
          "exposed-modules" ==> encodeExposed exposed,
          "gren-version" ==> Con.encode gren,
          "dependencies" ==> encodeDeps Con.encode deps
        ]
          ++ case target of
            Nothing -> []
            Just targets
              | targets == Target.everything -> ["target" ==> E.chars "any"]
              | otherwise -> ["target" ==> E.list (E.chars . Target.toChars) (Set.toAscList targets)]

encodeExposed :: Exposed -> E.Value
encodeExposed exposed =
  case exposed of
    ExposedList modules ->
      E.list encodeModule modules
    ExposedDict chunks ->
      E.object (map (fmap (E.list encodeModule)) chunks)

encodeModule :: ModuleName.Raw -> E.Value
encodeModule name =
  E.name name

encodeDeps :: (a -> E.Value) -> Map.Map Pkg.Name (PossibleFilePath a) -> E.Value
encodeDeps encodeValue deps =
  E.dict Pkg.toJsonString (PossibleFilePath.encodeJson encodeValue) deps

encodeSrcDir :: SrcDir -> E.Value
encodeSrcDir srcDir =
  case srcDir of
    AbsoluteSrcDir dir -> E.chars dir
    RelativeSrcDir dir -> E.chars dir

-- SOURCE DIRECTORIES

toAbsolute :: FilePath -> SrcDir -> FilePath
toAbsolute root srcDir =
  case srcDir of
    AbsoluteSrcDir dir -> dir
    RelativeSrcDir dir -> root </> dir

toAbsoluteSrcDir :: FilePath -> SrcDir -> IO AbsoluteSrcDir
toAbsoluteSrcDir root srcDir =
  AbsoluteSrcDir.fromFilePath (toAbsolute root srcDir)

sourceDirs :: Outline -> NE.List SrcDir
sourceDirs outline =
  case outline of
    App (AppOutline _ _ srcDirs _ _ _) ->
      srcDirs
    Pkg _ ->
      NE.singleton (RelativeSrcDir "src")

-- JSON DECODE

type Decoder a =
  D.Decoder Exit.OutlineProblem a

decoder :: Decoder Outline
decoder =
  let application = Json.fromChars "application"
      package = Json.fromChars "package"
   in do
        tipe <- D.field "type" D.string
        if
          | tipe == application -> App <$> appDecoder
          | tipe == package -> Pkg <$> pkgDecoder
          | otherwise -> D.failure Exit.OP_BadType

appDecoder :: Decoder AppOutline
appDecoder =
  AppOutline
    <$> D.field "gren-version" versionDecoder
    <*> D.field "platform" (Platform.decoder Exit.OP_BadPlatform)
    <*> D.field "source-directories" dirsDecoder
    <*> D.field "dependencies" (D.field "direct" (depsDecoder versionOrFilePathDecoder))
    <*> D.field "dependencies" (D.field "indirect" (depsDecoder versionOrFilePathDecoder))
    <*> D.oneOf [D.field "target" targetDecoder, D.succeed Target.Js]

pkgDecoder :: Decoder PkgOutline
pkgDecoder =
  PkgOutline
    <$> D.field "name" nameDecoder
    <*> D.field "summary" summaryDecoder
    <*> D.field "license" (Licenses.decoder Exit.OP_BadLicense)
    <*> D.field "version" versionDecoder
    <*> D.field "exposed-modules" exposedDecoder
    <*> D.field "dependencies" (depsDecoder constraintOrFilePathDecoder)
    <*> D.field "gren-version" constraintDecoder
    <*> D.field "platform" (Platform.decoder Exit.OP_BadPlatform)
    <*> D.oneOf [Just <$> D.field "target" targetsDecoder, D.succeed Nothing]

-- JSON DECODE HELPERS

-- | One target. Only the front end writes the outline, and it has already
-- refused a name that is not one (@Compiler.Outline@).
targetDecoder :: Decoder Target.Target
targetDecoder =
  do
    chars <- D.string
    maybe (D.failure Exit.OP_BadTarget) D.succeed (Target.fromChars (Json.toChars chars))

-- | @"any"@, or a list of targets.
targetsDecoder :: Decoder (Set.Set Target.Target)
targetsDecoder =
  D.oneOf
    [ do
        chars <- D.string
        if Json.toChars chars == "any" then D.succeed Target.everything else D.failure Exit.OP_BadTarget,
      Set.fromList <$> D.list targetDecoder
    ]

nameDecoder :: Decoder Pkg.Name
nameDecoder =
  D.mapError (uncurry Exit.OP_BadPkgName) Pkg.decoder

summaryDecoder :: Decoder Json.String
summaryDecoder =
  D.customString
    (boundParser 80 Exit.OP_BadSummaryTooLong)
    (\_ _ -> Exit.OP_BadSummaryTooLong)

versionDecoder :: Decoder V.Version
versionDecoder =
  D.mapError (Exit.OP_BadVersion . Exit.OP_AttemptedOther) V.decoder

versionOrFilePathDecoder :: Decoder (PossibleFilePath V.Version)
versionOrFilePathDecoder =
  D.oneOf
    [ do
        vsn <- D.mapError (Exit.OP_BadVersion . Exit.OP_AttemptedOther) V.decoder
        D.succeed (PossibleFilePath.Other vsn),
      filePathDecoder Exit.OP_BadVersion
    ]

filePathDecoder :: (Exit.PossibleFilePath err -> Exit.OutlineProblem) -> Decoder (PossibleFilePath val)
filePathDecoder errorMapper =
  do
    jsonStr <- D.string
    D.Decoder $ \(A.At errRegion@(A.Region (A.Position row col) _) _) ok err ->
      let filePath = Json.toChars jsonStr
       in if List.isPrefixOf localDepPrefix filePath
            then ok (PossibleFilePath.Is $ List.drop (List.length localDepPrefix) filePath)
            else err (D.Failure errRegion $ errorMapper $ Exit.OP_AttemptedFilePath (row, col))

localDepPrefix :: String
localDepPrefix =
  "local:"

constraintDecoder :: Decoder Con.Constraint
constraintDecoder =
  D.mapError (Exit.OP_BadConstraint . Exit.OP_AttemptedOther) Con.decoder

constraintOrFilePathDecoder :: Decoder (PossibleFilePath Con.Constraint)
constraintOrFilePathDecoder =
  D.oneOf
    [ do
        con <- D.mapError (Exit.OP_BadConstraint . Exit.OP_AttemptedOther) Con.decoder
        D.succeed (PossibleFilePath.Other con),
      filePathDecoder Exit.OP_BadConstraint
    ]

depsDecoder :: Decoder a -> Decoder (Map.Map Pkg.Name a)
depsDecoder valueDecoder =
  D.dict (Pkg.keyDecoder Exit.OP_BadDependencyName) valueDecoder

dirsDecoder :: Decoder (NE.List SrcDir)
dirsDecoder =
  fmap (toSrcDir . Json.toChars) <$> D.nonEmptyList D.string Exit.OP_NoSrcDirs

toSrcDir :: FilePath -> SrcDir
toSrcDir path =
  if FP.isRelative path
    then RelativeSrcDir path
    else AbsoluteSrcDir path

-- EXPOSED MODULES DECODER

exposedDecoder :: Decoder Exposed
exposedDecoder =
  D.oneOf
    [ ExposedList <$> D.list moduleDecoder,
      ExposedDict <$> D.pairs headerKeyDecoder (D.list moduleDecoder)
    ]

moduleDecoder :: Decoder ModuleName.Raw
moduleDecoder =
  D.mapError (uncurry Exit.OP_BadModuleName) ModuleName.decoder

headerKeyDecoder :: D.KeyDecoder Exit.OutlineProblem Json.String
headerKeyDecoder =
  D.KeyDecoder
    (boundParser 20 Exit.OP_BadModuleHeaderTooLong)
    (\_ _ -> Exit.OP_BadModuleHeaderTooLong)

-- BOUND PARSER

boundParser :: Int -> x -> P.Parser x Json.String
boundParser bound tooLong =
  P.Parser $ \(P.State src pos end indent row col) cok _ cerr _ ->
    let len = minusPtr end pos
        newCol = col + fromIntegral len
     in if len < bound
          then cok (Json.fromPtr pos end) (P.State src end end indent row newCol)
          else cerr row newCol (\_ _ -> tooLong)

-- BINARY

instance Binary SrcDir where
  put outline =
    case outline of
      AbsoluteSrcDir a -> putWord8 0 >> put a
      RelativeSrcDir a -> putWord8 1 >> put a

  get =
    do
      n <- getWord8
      case n of
        0 -> liftM AbsoluteSrcDir get
        1 -> liftM RelativeSrcDir get
        _ -> fail "binary encoding of SrcDir was corrupted"
