{-# LANGUAGE OverloadedStrings #-}

module Package.Diff
  ( Flags (..),
    run,
  )
where

import AST.Canonical qualified as Can
import Build qualified
import Command qualified
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name qualified as Name
import Data.NonEmptyList qualified as NE
import Deps.Diff (Changes (..), ModuleChanges (..), PackageChanges (..))
import Deps.Diff qualified as DD
import Deps.Refinements qualified as Refinements
import Gren.Compiler.Type qualified as Type
import Gren.Details qualified as Details
import Gren.Docs qualified as Docs
import Gren.Magnitude qualified as M
import Gren.Outline qualified as Outline
import Gren.Package qualified as Pkg
import Reporting qualified
import Reporting.Doc ((<+>))
import Reporting.Doc qualified as D
import Reporting.Exit qualified as Exit
import Reporting.Exit.Help qualified as Help
import Reporting.Render.Type qualified as RT
import Reporting.Render.Type.Localizer qualified as L
import Reporting.Task qualified as Task

-- RUN

data Flags = Flags
  { _interactive :: Bool,
    _project_path :: String,
    _current_version :: Command.ProjectInfo,
    _published_version :: Command.ProjectInfo
  }
  deriving (Show)

run :: Flags -> IO ()
run flags@(Flags _ _ currentPackage publishedPackage) =
  Reporting.attempt Exit.diffToReport $
    case (Command._project_outline currentPackage, Command._project_outline publishedPackage) of
      (Outline.Pkg currentOutline, Outline.Pkg publishedOutline) ->
        Task.run (diff flags currentOutline publishedOutline)
      _ ->
        error "Received outlines are in the wrong format"

-- DIFF

type Task a =
  Task.Task Exit.Diff a

diff :: Flags -> Outline.PkgOutline -> Outline.PkgOutline -> Task ()
diff (Flags _ root (Command.ProjectInfo _ currentSources currentSolution) (Command.ProjectInfo _ publishedSources publishedSolution)) currentOutline publishedOutline =
  do
    new <- generateDocs root currentOutline currentSources currentSolution
    old <- generateDocs root publishedOutline publishedSources publishedSolution
    outcome <- Task.io $ Refinements.decide False old new
    case outcome of
      Refinements.Stopped -> return ()
      Refinements.Decided verdicts oldDocs newDocs -> writeDiff verdicts oldDocs newDocs

-- GENERATE DOCS

generateDocs :: FilePath -> Outline.PkgOutline -> Build.Sources -> Map Pkg.Name Details.Dependency -> Task.Task Exit.Diff Refinements.Version
generateDocs root outline@(Outline.PkgOutline _ _ _ _ exposed _ _ _ _) sources solution =
  do
    details <-
      Task.eio Exit.DiffBadDetails $
        Details.load root (Outline.Pkg outline) solution

    case Outline.flattenExposed exposed of
      [] ->
        Task.throw Exit.DiffNoExposed
      e : es ->
        (\(docs, cores) -> Refinements.Version docs cores details)
          <$> Task.eio Exit.DiffBadBuild (Build.fromExposed Reporting.silent root details sources Build.KeepDocsAndCore (NE.List e es))

-- WRITE DIFF

writeDiff :: DD.Verdicts -> Docs.Documentation -> Docs.Documentation -> Task ()
writeDiff verdicts oldDocs newDocs =
  let changes = DD.diff verdicts oldDocs newDocs
      localizer = L.fromNames (Map.union oldDocs newDocs)
   in Task.io $ Help.toStdout $ toDoc localizer changes <> "\n"

-- TO DOC

toDoc :: L.Localizer -> PackageChanges -> D.Doc
toDoc localizer changes@(PackageChanges added changed removed) =
  if null added && Map.null changed && null removed
    then "No API changes detected, so this is a" <+> D.green "PATCH" <+> "change."
    else
      let magDoc =
            D.fromChars (M.toChars (DD.toMagnitude changes))

          header =
            "This is a" <+> D.green magDoc <+> "change."

          addedChunk =
            if null added
              then []
              else
                [ Chunk "ADDED MODULES" M.MINOR $
                    D.vcat $
                      map D.fromName added
                ]

          removedChunk =
            if null removed
              then []
              else
                [ Chunk "REMOVED MODULES" M.MAJOR $
                    D.vcat $
                      map D.fromName removed
                ]

          chunks =
            addedChunk ++ removedChunk ++ map (changesToChunk localizer) (Map.toList changed)
       in D.vcat (header : "" : map chunkToDoc chunks)

data Chunk = Chunk
  { _title :: String,
    _magnitude :: M.Magnitude,
    _details :: D.Doc
  }

chunkToDoc :: Chunk -> D.Doc
chunkToDoc (Chunk title magnitude details) =
  let header =
        "----" <+> D.fromChars title <+> "-" <+> D.fromChars (M.toChars magnitude) <+> "----"
   in D.vcat
        [ D.dullcyan header,
          "",
          D.indent 4 details,
          "",
          ""
        ]

changesToChunk :: L.Localizer -> (Name.Name, ModuleChanges) -> Chunk
changesToChunk localizer (name, changes@(ModuleChanges unions aliases values binops verdicts)) =
  let magnitude =
        DD.moduleChangeMagnitude changes

      (unionAdd, unionChange, unionRemove) =
        changesToDocTriple (unionToDoc localizer) unions

      (aliasAdd, aliasChange, aliasRemove) =
        changesToDocTriple (aliasToDoc localizer) aliases

      (valueAdd, valueChange, valueRemove) =
        withReasons localizer verdicts (changesToDocTriple (valueToDoc localizer) values) values

      (binopAdd, binopChange, binopRemove) =
        changesToDocTriple (binopToDoc localizer) binops
   in Chunk (Name.toChars name) magnitude $
        D.vcat $
          List.intersperse "" $
            Maybe.catMaybes $
              [ changesToDoc "Added" unionAdd aliasAdd valueAdd binopAdd,
                changesToDoc "Removed" unionRemove aliasRemove valueRemove binopRemove,
                changesToDoc "Changed" unionChange aliasChange valueChange binopChange
              ]

changesToDocTriple :: (k -> v -> D.Doc) -> Changes k v -> ([D.Doc], [D.Doc], [D.Doc])
changesToDocTriple entryToDoc (Changes added changed removed) =
  let indented (name, value) =
        D.indent 4 (entryToDoc name value)

      diffed (name, (oldValue, newValue)) =
        D.vcat
          [ "  - " <> entryToDoc name oldValue,
            "  + " <> entryToDoc name newValue,
            ""
          ]
   in ( map indented (Map.toList added),
        map diffed (Map.toList changed),
        map indented (Map.toList removed)
      )

-- | Each changed value's lines with, under them, why the refinement checker
-- gave it its magnitude, when it did (D855).
withReasons :: L.Localizer -> Map Name.Name DD.Verdict -> ([D.Doc], [D.Doc], [D.Doc]) -> Changes Name.Name Docs.Value -> ([D.Doc], [D.Doc], [D.Doc])
withReasons localizer verdicts (added, _, removed) (Changes _ changedValues _) =
  let reasons name =
        case Map.lookup name verdicts of
          Just (DD.Verdict _ why) -> map (D.indent 4 . D.reflow) why
          Nothing -> []

      diffed (name, (oldValue, newValue)) =
        D.vcat $
          [ "  - " <> valueToDoc localizer name oldValue,
            "  + " <> valueToDoc localizer name newValue
          ]
            ++ reasons name
            ++ [""]
   in (added, map diffed (Map.toList changedValues), removed)

changesToDoc :: String -> [D.Doc] -> [D.Doc] -> [D.Doc] -> [D.Doc] -> Maybe D.Doc
changesToDoc categoryName unions aliases values binops =
  if null unions && null aliases && null values && null binops
    then Nothing
    else
      Just $
        D.vcat $
          D.fromChars categoryName <> ":" : unions ++ aliases ++ binops ++ values

unionToDoc :: L.Localizer -> Name.Name -> Docs.Union -> D.Doc
unionToDoc localizer name (Docs.Union _ tvars ctors affine) =
  let setup =
        (if affine then "@affine type" else "type") <+> D.fromName name <+> D.hsep (map D.fromName tvars)

      ctorDoc (ctor, tipes) =
        typeDoc localizer (Type.Type ctor tipes)
   in D.hang 4 (D.sep (setup : zipWith (<+>) ("=" : repeat "|") (map ctorDoc ctors)))

aliasToDoc :: L.Localizer -> Name.Name -> Docs.Alias -> D.Doc
aliasToDoc localizer name (Docs.Alias _ tvars tipe named) =
  let declaration =
        "type" <+> "alias" <+> D.hsep (map D.fromName (name : tvars)) <+> "="
   in D.hang 4 (D.sep [declaration, signatureDoc localizer named tipe])

valueToDoc :: L.Localizer -> Name.Name -> Docs.Value -> D.Doc
valueToDoc localizer name (Docs.Value _ tipe named facts) =
  D.vcat $
    D.hang 4 (D.sep [D.fromName name <+> ":", signatureDoc localizer named tipe])
      : map (\fact -> D.indent 4 ("--" <+> D.fromChars (Docs.factWords fact))) facts

-- | A value's type with the names its signature gives, each with its
-- predicate, as written (geng-lang @m4-refine.md@ §RF29, D854): what a caller
-- is asked and what it is given are part of the interface the diff shows.
signatureDoc :: L.Localizer -> [Docs.Named] -> Type.Type -> D.Doc
signatureDoc localizer named =
  place [] Type.None
  where
    place path context tipe =
      case List.find (\n -> Docs._namedPath n == path) named of
        Just (Docs.Named _ name source moved) ->
          "("
            <> (if moved then "moved " else D.empty)
            <> D.fromName name
            <+> ":"
            <+> inner path Type.None tipe
            <> (if null source then D.empty else " where" <+> D.fromChars source)
            <> ")"
        Nothing ->
          inner path context tipe

    inner path context tipe =
      let parts = collect tipe
          below = any (\n -> List.isPrefixOf path (Docs._namedPath n) && Docs._namedPath n /= path) named
       in case parts of
            a : b : cs
              | below ->
                  let args = zipWith (\i t -> place (path ++ [Can.Arg i]) Type.Func t) [0 ..] (init parts)
                      result = place (path ++ [Can.Result]) Type.Func (last parts)
                   in case args ++ [result] of
                        x : y : zs -> RT.lambda context x y zs
                        _ -> RT.lambda context (Type.toDoc localizer Type.Func a) (Type.toDoc localizer Type.Func b) (map (Type.toDoc localizer Type.Func) cs)
            _ ->
              Type.toDoc localizer context tipe

    collect tipe =
      case tipe of
        Type.Lambda a b -> a : collect b
        _ -> [tipe]

binopToDoc :: L.Localizer -> Name.Name -> Docs.Binop -> D.Doc
binopToDoc localizer name (Docs.Binop _ tipe associativity (Docs.Precedence n)) =
  "(" <> D.fromName name <> ")" <+> ":" <+> typeDoc localizer tipe <> D.black details
  where
    details =
      "    (" <> D.fromName assoc <> "/" <> D.fromInt n <> ")"

    assoc =
      case associativity of
        Docs.Left -> "left"
        Docs.Non -> "non"
        Docs.Right -> "right"

typeDoc :: L.Localizer -> Type.Type -> D.Doc
typeDoc localizer tipe =
  Type.toDoc localizer Type.None tipe
