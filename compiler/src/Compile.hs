module Compile
  ( Artifacts (..),
    compile,
  )
where

import AST.Canonical qualified as Can
import AST.Source qualified as Src
import Canonicalize.Module qualified as Canonicalize
import Canonicalize.NodeId qualified as NodeId
import Core.AST qualified as Core
import Core.Dump qualified as Dump
import Core.Lower.Module qualified as Lower
import Core.Pretty qualified as Pretty
import Data.Map qualified as Map
import Data.Name qualified as Name
import Data.OneOrMore qualified as OneOrMore
import Gren.Interface qualified as I
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Gren.Platform qualified as P
import Nitpick.Main qualified as NitpickMain
import Nitpick.PatternMatches qualified as PatternMatches
import Reporting.Annotation qualified as A
import Reporting.Error qualified as E
import Reporting.Render.Type.Localizer qualified as Localizer
import Reporting.Result qualified as R
import System.Environment qualified as Env
import System.IO.Unsafe (unsafePerformIO)
import Type.Constrain.Module qualified as Type
import Type.Resolve qualified as Resolve
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
    -- | The module's Core (@docs/core.md@), which is the only thing the
    -- backend reads. Lazy: a build that generates no code never forces it.
    _core :: Core.Module
  }

compile :: P.Platform -> Pkg.Name -> Map.Map ModuleName.Raw I.Interface -> Src.Module -> Either E.Error Artifacts
compile platform pkg ifaces modul =
  do
    -- Numbering happens between canonicalization and type checking, because
    -- the checker records a type per node id (`docs/m1a-node-types.md`) and
    -- everything downstream of it must see the same ids.
    canonical <- NodeId.number <$> canonicalize pkg ifaces modul
    Type.Solved solved nodeTypes <- typeCheck modul canonical
    let annotations = withContexts canonical solved
    () <- checkNodeTypes canonical nodeTypes
    elaboration <- resolveInstances modul ifaces canonical nodeTypes
    () <- nitpick canonical
    () <- checkMain platform modul annotations canonical
    let core = Lower.lower platform annotations nodeTypes elaboration canonical
    () <- dumpCore canonical core
    return (Artifacts canonical annotations nodeTypes core)

-- | Put each written context back on the annotation the solver produced.
--
-- `Type.Type.toAnnotation` returns every variable unconstrained, and has to:
-- the unifier's classes are its own three-way enum and @Basics.Num@ is not
-- declared anywhere until @core@ is rewritten, so pointing a 'Can.Class' at one
-- would be inventing a reference (verb 7). What a module /wrote/ is a
-- 'Can.Class' already, and it is what an importer needs: a constrained
-- signature that publishes no constraint is a signature whose callers pass no
-- witness, which compiles and is wrong (§G26).
--
-- Only the payloads move. The variables and the type are the solved
-- annotation's, and the two agree about names because a rigid variable comes
-- back from the solver under the name the signature gave it.
withContexts :: Can.Module -> Map.Map Name.Name Can.Annotation -> Map.Map Name.Name Can.Annotation
withContexts canonical annotations =
  let written = writtenContexts (Can._decls canonical)
      apply name (Can.Forall freeVars tipe) =
        case Map.lookup name written of
          Nothing -> Can.Forall freeVars tipe
          Just context ->
            Can.Forall (Map.mapWithKey (\var _ -> Map.findWithDefault [] var context) freeVars) tipe
   in Map.mapWithKey apply annotations

writtenContexts :: Can.Decls -> Map.Map Name.Name Can.FreeVars
writtenContexts ds =
  case ds of
    Can.Declare d rest -> Map.union (contextOf d) (writtenContexts rest)
    Can.DeclareRec d others rest ->
      Map.unions (map contextOf (d : others) ++ [writtenContexts rest])
    Can.SaveTheEnvironment -> Map.empty

contextOf :: Can.Def -> Map.Map Name.Name Can.FreeVars
contextOf d =
  case d of
    Can.Def {} -> Map.empty
    Can.TypedDef (A.At _ name) freeVars _ _ _
      | all null (Map.elems freeVars) -> Map.empty
      | otherwise -> Map.singleton name freeVars

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

-- | Pick an instance for every class-method call (@docs/m1b-classes.md@ §G23).
--
-- Between the solve and the lowering because it needs both halves: the type at
-- the call site, which only the solver has, and the ability to report that
-- there is no instance for it, which the lowering does not have.
--
-- The environment is the module's own instances plus its imports' closure,
-- which is the same union `Canonicalize.Module` checks a new declaration
-- against (D122) and is that function rather than a second copy of the rule.
resolveInstances ::
  Src.Module ->
  Map.Map ModuleName.Raw I.Interface ->
  Can.Module ->
  Map.Map Can.NodeId Can.Type ->
  Either E.Error Resolve.Elaboration
resolveInstances modul ifaces canonical nodeTypes =
  let visible =
        Map.union
          (Map.map Can._in_head (Can._instances canonical))
          (Canonicalize.importedInstances ifaces)
      classes =
        Map.union
          (ownClasses canonical)
          (importedClasses ifaces)
   in case Resolve.run (Resolve.Env visible classes nodeTypes) canonical of
        Right elaboration ->
          Right elaboration
        Left errors ->
          Left (E.BadInstances (Localizer.fromModule modul) errors)

-- | The classes this module declares, keyed the way a constraint names one.
ownClasses :: Can.Module -> Map.Map Can.Class Can.ClassDecl
ownClasses canonical =
  Map.fromList
    [ (Can.Class (Can._name canonical) name, decl)
    | (name, decl) <- Map.toList (Can._classes canonical)
    ]

-- | The classes this module's imports declare, private ones included.
--
-- A private class is kept for the reason 'Gren.Interface' keeps it: an exposed
-- value's annotation may be constrained by a class the declaring module does
-- not expose, and a use of that value still needs a witness for it.
importedClasses :: Map.Map ModuleName.Raw I.Interface -> Map.Map Can.Class Can.ClassDecl
importedClasses ifaces =
  Map.fromList
    [ (Can.Class (ModuleName.Canonical (I._home iface) raw) name, I.classDecl iClass)
    | (raw, iface) <- Map.toList ifaces,
      (name, iClass) <- Map.toList (I._classes iface)
    ]

-- | Assert that the type checker recorded a usable type for every node.
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
--
-- Two things are checked, because for an untyped definition presence is not
-- enough. Its recorded type is what §N9 peels argument types off of, so a
-- definition of /n/ arguments whose type has fewer than /n/ arrows is a
-- recorded type that is the wrong type — the body's, say, rather than the
-- function's — and that is a silent gap of exactly the kind this check exists
-- to make loud.
checkNodeTypes :: Can.Module -> Map.Map Can.NodeId Can.Type -> Either E.Error ()
checkNodeTypes canonical nodeTypes
  | not nodeTypeCheckEnabled = Right ()
  | otherwise =
      case untyped ++ misshapen of
        [] ->
          Right ()
        problem : _ ->
          error $
            "GENG_CHECK_NODE_TYPES: in "
              ++ show (Can._name canonical)
              ++ ", "
              ++ problem
  where
    nodes = NodeId.nodes canonical

    untyped =
      case filter (\node -> not (Map.member (NodeId.nodeId node) nodeTypes)) nodes of
        [] -> []
        missing ->
          [ show (length missing)
              ++ " of "
              ++ show (length nodes)
              ++ " nodes have no recorded type: "
              ++ show (map NodeId.nodeId (take 10 missing))
          ]

    misshapen =
      case [ (nid, arity, recorded)
           | NodeId.DefNode nid arity <- nodes,
             Just recorded <- [Map.lookup nid nodeTypes],
             arrowCount recorded < arity
           ] of
        [] -> []
        bad ->
          [ show (length bad)
              ++ " definitions have a recorded type with too few arrows: "
              ++ show (take 3 bad)
          ]

arrowCount :: Can.Type -> Int
arrowCount tipe =
  case tipe of
    Can.TLambda _ result -> 1 + arrowCount result
    _ -> 0

nodeTypeCheckEnabled :: Bool
nodeTypeCheckEnabled =
  unsafePerformIO (maybe False (/= "") <$> Env.lookupEnv "GENG_CHECK_NODE_TYPES")
{-# NOINLINE nodeTypeCheckEnabled #-}

-- | Write every module's Core to a directory, if @GENG_DUMP_CORE@ names one.
--
-- It used to carry a @-- not lowered:@ trailer naming what the module declared
-- and Core dropped, so that a shorter list of definitions could not pass for a
-- complete one. Nothing is dropped any more — the manager went to Core at C17
-- and the ports at C18 — so the trailer is gone with the function that computed
-- it.
dumpCore :: Can.Module -> Core.Module -> Either E.Error ()
dumpCore canonical core =
  case Dump.moduleDir of
    Nothing ->
      Right ()
    Just dir ->
      unsafePerformIO $
        do
          Dump.writeModule dir (Can._name canonical) $
            Pretty.moduleToBuilder Pretty.defaultOptions core
          return (Right ())

nitpick :: Can.Module -> Either E.Error ()
nitpick canonical =
  case PatternMatches.check canonical of
    Right () ->
      Right ()
    Left errors ->
      Left (E.BadPatterns errors)

-- | The three rejections the old pipeline used to make on the way past.
--
-- @Optimize.Module@ made them while building a graph, and they were the only
-- user-facing checks it owned; `Nitpick.Main` is where they went when it was
-- retired. @reject\/main-bad-type@, @reject\/main-bad-flags@ and
-- @reject\/main-in-a-cycle@ pin the wording of all three.
checkMain :: P.Platform -> Src.Module -> Map.Map Name.Name Can.Annotation -> Can.Module -> Either E.Error ()
checkMain platform modul annotations canonical =
  case NitpickMain.check platform annotations canonical of
    Right () ->
      Right ()
    Left err ->
      Left (E.BadMains (Localizer.fromModule modul) (OneOrMore.one err))
