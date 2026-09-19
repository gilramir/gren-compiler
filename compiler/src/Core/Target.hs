{-# OPTIONS_GHC -Wall #-}

-- | The @target@ axis, derived from @\@extern@ languages (@ffi.md@ F1, D50, D77).
--
-- An @\@extern@ names an implementation /language/, and D77's table says which
-- targets each one serves. A declaration serves the union of its rows' targets,
-- or every target when it has a Geng body as well (D222), since a backend with
-- no row compiles the body. A module serves what every one of its extern
-- declarations serves, and a package what every one of its modules does. None
-- of it is written down anywhere to drift: it is read off Core, which carries
-- each extern's rows and whether it has a body, so a cached module answers as a
-- fresh one does (@m1b-manifest.md@ §MF9).
module Core.Target
  ( Target (..),
    toChars,
    fromChars,
    everything,
    served,
    language,
    declarationTargets,
    moduleTargets,
    packageTargets,
    Refusal (..),
    refusals,
    reached,
  )
where

import Core.AST qualified as Core
import Core.Refs qualified as Refs
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Name (Name)
import Data.Set (Set)
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName

-- | A codegen target. The constructors are in the order their names sort, so a
-- set of them prints the way a manifest is told to write it.
data Target
  = Beam
  | Js
  | Native
  | Wasm
  deriving (Eq, Ord, Show, Enum, Bounded)

toChars :: Target -> String
toChars target =
  case target of
    Beam -> "beam"
    Js -> "js"
    Native -> "native"
    Wasm -> "wasm"

fromChars :: String -> Maybe Target
fromChars chars =
  case chars of
    "beam" -> Just Beam
    "js" -> Just Js
    "native" -> Just Native
    "wasm" -> Just Wasm
    _ -> Nothing

-- | What @target = "any"@ means: every target this compiler knows of.
everything :: Set Target
everything =
  Set.fromList [minBound .. maxBound]

-- | D77's table. @js@ serves @wasm@ as well, because a WasmGC module reaches
-- its host through a JavaScript import object, which is the @src/Ext@ file.
served :: Core.ExternLanguage -> Set Target
served lang =
  case lang of
    Core.ExternJs -> Set.fromList [Js, Wasm]
    Core.ExternErlang -> Set.singleton Beam
    Core.ExternC -> Set.singleton Native

-- | The language a target's backend reads externs in: the other way round from
-- 'served', and a function because each target has one (@m2-seam.md@ §DS5).
-- @wasm@ reads @js@ rows for the reason 'served' gives.
language :: Target -> Core.ExternLanguage
language target =
  case target of
    Beam -> Core.ExternErlang
    Js -> Core.ExternJs
    Native -> Core.ExternC
    Wasm -> Core.ExternJs

declarationTargets :: Core.Extern -> Set Target
declarationTargets e
  | Core._externHasBody e = everything
  | otherwise = Set.unions (map (served . Core._implLanguage) (Core._externImpls e))

moduleTargets :: Core.Module -> Set Target
moduleTargets m =
  foldr (Set.intersection . declarationTargets) everything (Core._moduleExterns m)

packageTargets :: Map k Core.Module -> Set Target
packageTargets =
  foldr (Set.intersection . moduleTargets) everything

-- | The extern declarations of one module that do not serve a target: each
-- one's name and the languages it has rows for.
data Refusal = Refusal
  { _refusalModule :: ModuleName.Canonical,
    _refusalExterns :: [(Name, [Core.ExternLanguage])]
  }

-- | Every module of those given that does not serve the target, with the
-- declarations that are why, in module order.
refusals :: Target -> Map ModuleName.Canonical Core.Module -> [Refusal]
refusals target modules =
  [ Refusal home refused
  | (home, m) <- Map.toAscList modules,
    let refused =
          [ (Core._binderName (Core._externBinder e), map Core._implLanguage (Core._externImpls e))
          | e <- Core._moduleExterns m,
            not (Set.member target (declarationTargets e))
          ],
    not (null refused)
  ]

-- | The modules a build is made of: those it starts from, and every module one
-- of them refers to, a module at a time (§MF9, D320).
--
-- A module is in when anything in a module that is in names a value or a
-- constructor of it, whether or not that thing is reached from @main@. Core
-- carries no import list, so an import nothing is used from brings no module in,
-- which costs nothing: such a module contributes no code to any backend.
reached :: Map ModuleName.Canonical Core.Module -> [ModuleName.Canonical] -> Map ModuleName.Canonical Core.Module
reached modules starts =
  Map.restrictKeys modules (go Set.empty starts)
  where
    go seen pending =
      case pending of
        [] -> seen
        home : rest
          | Set.member home seen -> go seen rest
          | otherwise ->
              case Map.lookup home modules of
                Nothing -> go (Set.insert home seen) rest
                Just m -> go (Set.insert home seen) (Set.toList (homes m) ++ rest)

    homes m =
      let refs =
            foldMap (Refs.refsIn . Core._bindValue) (Core._moduleDefs m)
              <> foldMap (foldMap (Refs.refsIn . snd) . Core._instMethods) (Core._moduleInstances m)
          named = Set.map Core._qnHome (Set.union (Refs._refGlobals refs) (Refs._refCtors refs))
       in Set.delete (Core._moduleName m) named
