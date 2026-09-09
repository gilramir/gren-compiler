module Compile
  ( Artifacts (..),
    compile,
  )
where

import AST.Canonical qualified as Can
import AST.Source qualified as Src
import AST.Utils.Type qualified as Utils
import Canonicalize.Module qualified as Canonicalize
import Canonicalize.NodeId qualified as NodeId
import Core.AST qualified as Core
import Core.Dump qualified as Dump
import Core.Lower.Module qualified as Lower
import Core.Pretty qualified as Pretty
import Data.List qualified as List
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
    Type.Solved solved nodeTypes defaults <- typeCheck modul canonical
    () <- checkNodeTypes canonical nodeTypes
    -- Before the annotations, because half of one may come from it: an
    -- unannotated definition's open constraints are the elaborator's answer
    -- (§G33) and nothing earlier knows them. It may also change the types it
    -- was given, which is why they come back out of it (§G33.2).
    (elaboration, solved', nodeTypes') <-
      resolveInstances modul ifaces canonical defaults solved nodeTypes
    let annotations = withContexts canonical (Resolve._inferred elaboration) solved'
    () <- nitpick canonical
    () <- checkMain platform modul annotations canonical
    let core = Lower.lower platform annotations nodeTypes' elaboration canonical
    () <- dumpCore canonical core
    return (Artifacts canonical annotations nodeTypes' core)

-- | Put each open context back on the annotation the solver produced.
--
-- `Type.Type.toAnnotation` returns the /closed/ half of a context and no more,
-- and has to: an open class never reaches the unifier (D130), so the solver
-- has never heard of one. The other half has two sources and they are the same
-- fact seen twice — what a module __wrote__, which is a 'Can.Class' already,
-- and what the elaborator __inferred__ for a definition that wrote nothing
-- (§G33). Either way it is what an importer needs: a constrained signature
-- that publishes no constraint is a signature whose callers pass no witness,
-- which compiles and is wrong (§G26).
--
-- Only the payloads move. The variables and the type are the solved
-- annotation's, and the three agree about names because a rigid variable comes
-- back from the solver under the name the signature gave it, and an inferred
-- context is read off the node type the same zonking named.
--
-- The union rather than the replacement: an unannotated definition may be
-- constrained by a closed class the solver found /and/ an open one the
-- elaborator did — @countDown@ is both — and dropping either half is a wrong
-- signature. For a written context the union is the written context, because
-- unification cannot add a class to a rigid variable; it can only refuse one.
withContexts :: Can.Module -> Resolve.Inferred -> Map.Map Name.Name Can.Annotation -> Map.Map Name.Name Can.Annotation
withContexts canonical inferred annotations =
  let declared = contexts inferred (Can._decls canonical)
      apply name (Can.Forall freeVars tipe) =
        case Map.lookup name declared of
          Nothing -> Can.Forall freeVars tipe
          Just context ->
            Can.Forall
              (Map.mapWithKey (\var fromSolver -> List.union fromSolver (Map.findWithDefault [] var context)) freeVars)
              tipe
   in Map.mapWithKey apply annotations

contexts :: Resolve.Inferred -> Can.Decls -> Map.Map Name.Name Can.FreeVars
contexts inferred ds =
  case ds of
    Can.Declare d rest -> Map.union (contextOf inferred d) (contexts inferred rest)
    Can.DeclareRec d others rest ->
      Map.unions (map (contextOf inferred) (d : others) ++ [contexts inferred rest])
    Can.SaveTheEnvironment -> Map.empty

contextOf :: Resolve.Inferred -> Can.Def -> Map.Map Name.Name Can.FreeVars
contextOf inferred d =
  case d of
    Can.Def nid (A.At _ name) _ _ ->
      case Map.lookup nid inferred of
        Nothing -> Map.empty
        Just context -> Map.singleton name context
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
--
-- __It may have to be asked more than once__ (§G33.2). A definition that takes
-- no arguments and needs a witness would become a function, so `classes.md`
-- §0's rule closes its variable instead — and that changes the types every
-- later question is asked against, so the substitution is applied and the
-- elaborator is asked again. Each round replaces at least one variable by a
-- type with none, so there are at most as many rounds as the module has
-- constrained variables.
resolveInstances ::
  Src.Module ->
  Map.Map ModuleName.Raw I.Interface ->
  Can.Module ->
  Map.Map Name.Name Can.Type ->
  Map.Map Name.Name Can.Annotation ->
  Map.Map Can.NodeId Can.Type ->
  Either E.Error (Resolve.Elaboration, Map.Map Name.Name Can.Annotation, Map.Map Can.NodeId Can.Type)
resolveInstances modul ifaces canonical defaults solved nodeTypes =
  let visible =
        Map.union
          (Map.map Can._in_head (Can._instances canonical))
          (Canonicalize.importedInstances ifaces)
      classes =
        Map.union
          (ownClasses canonical)
          (importedClasses ifaces)
      ask anns types =
        case Resolve.run (Resolve.Env visible classes types defaults) canonical of
          Resolve.Answered elaboration ->
            Right (elaboration, anns, types)
          Resolve.Refused errors ->
            Left (E.BadInstances (Localizer.fromModule modul) errors)
          Resolve.Defaulted subs ->
            ask (foldr closeAnnotation anns subs) (foldr closeNodes types subs)
   in ask solved nodeTypes

-- | Apply one definition's defaults to the annotation it publishes, if it
-- publishes one, and stop quantifying what they closed.
closeAnnotation :: Resolve.Substitution -> Map.Map Name.Name Can.Annotation -> Map.Map Name.Name Can.Annotation
closeAnnotation s anns =
  case Resolve._sTopLevel s of
    Nothing -> anns
    Just name -> Map.adjust close name anns
  where
    close (Can.Forall freeVars tipe) =
      Can.Forall (Map.difference freeVars (Resolve._sTypes s)) (Utils.substitute (Resolve._sTypes s) tipe)

-- | Apply one definition's defaults to the types recorded at its own nodes.
closeNodes :: Resolve.Substitution -> Map.Map Can.NodeId Can.Type -> Map.Map Can.NodeId Can.Type
closeNodes s types =
  foldr (Map.adjust (Utils.substitute (Resolve._sTypes s))) types (Resolve._sNodes s)

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
