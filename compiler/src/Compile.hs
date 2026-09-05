module Compile
  ( Artifacts (..),
    compile,
  )
where

import AST.Canonical qualified as Can
import AST.Optimized qualified as Opt
import AST.Source qualified as Src
import Canonicalize.Module qualified as Canonicalize
import Canonicalize.NodeId qualified as NodeId
import Data.Map qualified as Map
import Data.Name qualified as Name
import Gren.Interface qualified as I
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Gren.Platform qualified as P
import Nitpick.PatternMatches qualified as PatternMatches
import Optimize.Module qualified as Optimize
import Reporting.Error qualified as E
import Reporting.Render.Type.Localizer qualified as Localizer
import Reporting.Result qualified as R
import System.Environment qualified as Env
import System.IO.Unsafe (unsafePerformIO)
import Type.Constrain.Module qualified as Type
import Type.Solve qualified as Type

-- COMPILE

data Artifacts = Artifacts
  { _modul :: Can.Module,
    _types :: Map.Map Name.Name Can.Annotation,
    -- | One entry per expression node, keyed by the id `Canonicalize.NodeId`
    -- assigned. This is what a typed Core is lowered from
    -- (`docs/m1a-node-types.md`); nothing before Core needed it, so nothing
    -- before Core computed it.
    _nodeTypes :: Map.Map Can.NodeId Can.Type,
    _graph :: Opt.LocalGraph
  }

compile :: P.Platform -> Pkg.Name -> Map.Map ModuleName.Raw I.Interface -> Src.Module -> Either E.Error Artifacts
compile platform pkg ifaces modul =
  do
    -- Numbering happens between canonicalization and type checking, because
    -- the checker records a type per node id (`docs/m1a-node-types.md`) and
    -- everything downstream of it must see the same ids.
    canonical <- NodeId.number <$> canonicalize pkg ifaces modul
    Type.Solved annotations nodeTypes <- typeCheck modul canonical
    () <- checkNodeTypes canonical nodeTypes
    () <- nitpick canonical
    objects <- optimize platform modul annotations canonical
    return (Artifacts canonical annotations nodeTypes objects)

-- PHASES

canonicalize :: Pkg.Name -> Map.Map ModuleName.Raw I.Interface -> Src.Module -> Either E.Error Can.Module
canonicalize pkg ifaces modul =
  case snd $ R.run $ Canonicalize.canonicalize pkg ifaces modul of
    Right canonical ->
      Right canonical
    Left errors ->
      Left $ E.BadNames errors

typeCheck :: Src.Module -> Can.Module -> Either E.Error Type.Solved
typeCheck modul canonical =
  case unsafePerformIO (Type.run =<< Type.constrain canonical) of
    Right solved ->
      Right solved
    Left errors ->
      Left (E.BadTypes (Localizer.fromModule modul) errors)

-- | Assert that the type checker recorded a type for every expression node.
--
-- Off unless @GENG_CHECK_NODE_TYPES@ is set, because it walks the module a
-- second time and the invariant it checks is structural: `constrain` records
-- at the one place every node passes through, so a gap means a new expression
-- form bypassed it, not that a particular program is unusual.
--
-- It is a hard failure rather than a warning. A typed Core cannot be lowered
-- from a partially typed module, and "mostly typed" is exactly the state that
-- would go unnoticed until a backend hit the gap (`docs/m1a-node-types.md`
-- §N7).
checkNodeTypes :: Can.Module -> Map.Map Can.NodeId Can.Type -> Either E.Error ()
checkNodeTypes canonical nodeTypes
  | not nodeTypeCheckEnabled = Right ()
  | otherwise =
      let ids = NodeId.allIds canonical
          missing = filter (\nid -> not (Map.member nid nodeTypes)) ids
       in if null missing
            then Right ()
            else
              error $
                "GENG_CHECK_NODE_TYPES: "
                  ++ show (length missing)
                  ++ " of "
                  ++ show (length ids)
                  ++ " expression nodes in "
                  ++ show (Can._name canonical)
                  ++ " have no recorded type: "
                  ++ show (take 10 missing)

nodeTypeCheckEnabled :: Bool
nodeTypeCheckEnabled =
  unsafePerformIO (maybe False (/= "") <$> Env.lookupEnv "GENG_CHECK_NODE_TYPES")
{-# NOINLINE nodeTypeCheckEnabled #-}

nitpick :: Can.Module -> Either E.Error ()
nitpick canonical =
  case PatternMatches.check canonical of
    Right () ->
      Right ()
    Left errors ->
      Left (E.BadPatterns errors)

optimize :: P.Platform -> Src.Module -> Map.Map Name.Name Can.Annotation -> Can.Module -> Either E.Error Opt.LocalGraph
optimize platform modul annotations canonical =
  case snd $ R.run $ Optimize.optimize platform annotations canonical of
    Right localGraph ->
      Right localGraph
    Left errors ->
      Left (E.BadMains (Localizer.fromModule modul) errors)
