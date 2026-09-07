{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module Canonicalize.Environment.Local
  ( add,
  )
where

import AST.Canonical qualified as Can
import AST.Source qualified as Src
import Canonicalize.Environment qualified as Env
import Canonicalize.Environment.Dups qualified as Dups
import Canonicalize.Type qualified as Type
import Control.Monad (foldM)
import Data.Graph qualified as Graph
import Data.Index qualified as Index
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Name qualified as Name
import Gren.ModuleName qualified as ModuleName
import Reporting.Annotation qualified as A
import Reporting.Error.Canonicalize qualified as Error
import Reporting.Result qualified as Result

-- RESULT

type Result i w a =
  Result.Result i w Error.Error a

type Unions = Map.Map Name.Name Can.Union

type Aliases = Map.Map Name.Name Can.Alias

type Classes = Map.Map Name.Name Can.ClassDecl

-- | The local module's own names, added to an environment that already holds
-- the imported ones.
--
-- Classes go in between the types and the values, and it has to be there.
-- After the types, because a method's signature may name one; before the
-- values, because a method name and a top-level name are the same name and one
-- 'Dups.detect' has to see both (§G20).
add :: Src.Module -> Env.Env -> Result i w (Env.Env, Unions, Aliases, Classes)
add module_ env =
  do
    envWithTypes <- addTypes module_ env
    (envWithClasses, classes) <- addClasses module_ envWithTypes
    envWithVars <- addVars module_ classes envWithClasses
    (envWithCtors, unions, aliases) <- addCtors module_ envWithVars
    Result.ok (envWithCtors, unions, aliases, classes)

-- ADD VARS

addVars :: Src.Module -> Classes -> Env.Env -> Result i w Env.Env
addVars module_ classes (Env.Env home vs ts cs bs cls ms qvs qts qcs qcls qms) =
  do
    topLevelVars <- collectVars module_ classes
    -- Use union to overwrite foreign stuff. A local method overwrites it too,
    -- and has to: it is a local declaration of that name, so an imported value
    -- called `size` cannot go on answering for it once this module declares a
    -- `size` method.
    let vs2 = Map.union topLevelVars (Map.difference vs (methodIndex classes))
    Result.ok $ Env.Env home vs2 ts cs bs cls ms qvs qts qcs qcls qms

-- | The module's top-level value names, with its methods among them.
--
-- A method is not a top-level binding (§G19.2) and does not end up in
-- 'Env._vars', but it does occupy the name: a module cannot declare
-- @class Eq a where eq : ...@ and define @eq@ as well, because a use of @eq@
-- would then have two answers. So the duplicate check runs over both and only
-- the values are kept.
collectVars :: Src.Module -> Classes -> Result i w (Map.Map Name.Name Env.Var)
collectVars (Src.Module _ _ _ _ values classes _ _ _ _ _ _ effects) canClasses =
  let addDecl dict (A.At _ (Src.Value (A.At region name) _ _ _ _)) =
        Dups.insert name region (Env.TopLevel region) dict
      addMethod dict (A.At _ (Src.Class _ _ methods _)) =
        List.foldl' addOneMethod dict methods
      addOneMethod dict (_, A.At region name, _) =
        Dups.insert name region (Env.TopLevel region) dict
      dups =
        List.foldl'
          addDecl
          (List.foldl' addMethod (toEffectDups effects) (fmap snd classes))
          (fmap snd values)
   in do
        both <- Dups.detect Error.DuplicateDecl dups
        Result.ok (Map.difference both (methodIndex canClasses))

toEffectDups :: Src.Effects -> Dups.Dict Env.Var
toEffectDups effects =
  case effects of
    Src.NoEffects ->
      Dups.none
    Src.Ports ports _ ->
      let addPort dict (Src.Port (A.At region name) _) =
            Dups.insert name region (Env.TopLevel region) dict
       in List.foldl' addPort Dups.none (fmap snd ports)
    Src.Manager _ manager _ ->
      case manager of
        Src.Cmd (A.At region _) _ ->
          Dups.one "command" region (Env.TopLevel region)
        Src.Sub (A.At region _) _ ->
          Dups.one "subscription" region (Env.TopLevel region)
        Src.Fx (A.At regionCmd _) (A.At regionSub _) _ ->
          Dups.union
            (Dups.one "command" regionCmd (Env.TopLevel regionCmd))
            (Dups.one "subscription" regionSub (Env.TopLevel regionSub))

-- ADD CLASSES

-- | The module's class declarations, canonicalized and put in scope.
--
-- __A class declaration is self-contained__ (§G19.1). `class Eq a where
-- eq : a -> a -> Bool` publishes `eq : Eq a => a -> a -> Bool`, and the class
-- that constraint names is the one being declared, so nothing has to be
-- resolved to put it on. That is why this can run before anything else
-- resolves a class name, which is the only order the rest of verb 3 can be
-- built in.
--
-- A method's __own__ context is not self-contained — `sortBy : Ord b => …` has
-- to find `Ord` — but all it needs is a class's name and home, so two passes
-- over this module's declarations settle it and the declarations stay
-- unordered with respect to each other (§G21).
addClasses :: Src.Module -> Env.Env -> Result i w (Env.Env, Classes)
addClasses (Src.Module _ _ _ _ _ classes _ _ _ _ _ _ _) env =
  do
    canClasses <- traverse (canonicalizeClass (withClassNames env (fmap snd classes))) (fmap snd classes)
    Result.ok (withClasses env (Map.fromList canClasses))

-- | The module's class __names__ in scope, with no methods yet.
--
-- A method's own annotation may carry a context — @class Sortable a where
-- sortBy : Ord b => (a -> b) -> a -> a@ — and the class it names may be one of
-- this module's, including the one being declared. Resolving a constraint
-- needs the class's name and home and nothing else, so a pass that puts the
-- names up first is enough, and it is what makes the declarations in a module
-- unordered with respect to each other.
withClassNames :: Env.Env -> [A.Located Src.Class] -> Env.Env
withClassNames env classes =
  fst $
    withClasses env $
      Map.fromList
        [ (name, Can.ClassDecl param Map.empty)
        | A.At _ (Src.Class (A.At _ name) (A.At _ param) _ _) <- classes
        ]

withClasses :: Env.Env -> Classes -> (Env.Env, Classes)
withClasses (Env.Env home vs ts cs bs cls ms qvs qts qcs qcls qms) decls =
  ( Env.Env
      home
      vs
      ts
      cs
      bs
      (Map.union (Map.map (Env.Specific home) decls) cls)
      (Map.union (Map.map (Env.Specific home) (methodIndex decls)) ms)
      qvs
      qts
      qcs
      qcls
      qms,
    decls
  )

-- | The same declarations keyed by method name, which is the question an
-- expression asks. `Canonicalize.Environment.Foreign.methodsOf` builds it for
-- the imported ones.
methodIndex :: Classes -> Map.Map Name.Name Env.Method
methodIndex classes =
  Map.fromList
    [ (methodName, Env.Method className annotation)
    | (className, Can.ClassDecl _ methods) <- Map.toList classes,
      (methodName, annotation) <- Map.toList methods
    ]

canonicalizeClass :: Env.Env -> A.Located Src.Class -> Result i w (Name.Name, Can.ClassDecl)
canonicalizeClass env@(Env.Env home _ _ _ _ _ _ _ _ _ _ _) (A.At _ (Src.Class (A.At _ name) (A.At _ param) methods _)) =
  do
    canMethods <- traverse (canonicalizeMethod env home name param) methods
    Result.ok (name, Can.ClassDecl param (Map.fromList canMethods))

-- | One method's __published__ signature.
--
-- What the author wrote is unqualified — @eq : a -> a -> Bool@ — and what the
-- class publishes is @eq : Eq a => a -> a -> Bool@. The constraint is put on
-- here rather than written out there because it could not say anything else:
-- it names the class being declared, and a class whose methods were not
-- constrained by it would have no way to pick an instance.
--
-- The class parameter must appear in the signature, for the same reason: a
-- method whose type does not mention @a@ has nothing for a call site to
-- resolve against, and no program could ever use it.
canonicalizeMethod ::
  Env.Env ->
  ModuleName.Canonical ->
  Name.Name ->
  Name.Name ->
  Src.ClassMethod ->
  Result i w (Name.Name, Can.Annotation)
canonicalizeMethod env home className param (_, A.At region methodName, Src.Annotation maybeContext srcType _) =
  do
    (Can.Forall freeVars tipe) <- Type.toAnnotation env maybeContext srcType
    if Map.member param freeVars
      then Result.ok (methodName, Can.Forall (Map.insert param [Can.Class home className] freeVars) tipe)
      else Result.throw (Error.ClassMethodWithoutParam region className param methodName)

-- ADD TYPES

-- | The type names a module declares, and the classes among them.
--
-- A class name is checked here rather than beside the values because a class
-- shares the upper-case namespace with the types: an instance head is written
-- as a type (`Eq (Array a)`, §G16's reason for parsing one that way), so `Eq`
-- naming both a class and a custom type would be a name with two answers in
-- one position. They are checked together and stored apart — a class is not a
-- type and cannot appear where one does.
addTypes :: Src.Module -> Env.Env -> Result i w Env.Env
addTypes (Src.Module _ _ _ _ _ classes _ unions aliases _ _ _ _) (Env.Env home vs ts cs bs cls ms qvs qts qcs qcls qms) =
  let addAliasDups dups (A.At _ (Src.Alias (A.At region name) _ _)) = Dups.insert name region () dups
      addUnionDups dups (A.At _ (Src.Union (A.At region name) _ _ _ _)) = Dups.insert name region () dups
      addClassDups dups (A.At _ (Src.Class (A.At region name) _ _ _)) = Dups.insert name region () dups
      typeNameDups =
        List.foldl'
          addClassDups
          (List.foldl' addUnionDups (List.foldl' addAliasDups Dups.none (fmap snd aliases)) (fmap snd unions))
          (fmap snd classes)
   in do
        _ <- Dups.detect Error.DuplicateType typeNameDups
        ts1 <- foldM (addUnion home) ts (fmap snd unions)
        addAliases (fmap snd aliases) (Env.Env home vs ts1 cs bs cls ms qvs qts qcs qcls qms)

addUnion :: ModuleName.Canonical -> Env.Exposed Env.Type -> A.Located Src.Union -> Result i w (Env.Exposed Env.Type)
addUnion home types union@(A.At _ (Src.Union (A.At _ name) _ _ _ _)) =
  do
    arity <- checkUnionFreeVars union
    let one = Env.Specific home (Env.Union arity home)
    Result.ok $ Map.insert name one types

-- ADD TYPE ALIASES

addAliases :: [A.Located Src.Alias] -> Env.Env -> Result i w Env.Env
addAliases aliases env =
  let nodes = map toNode aliases
      sccs = Graph.stronglyConnComp nodes
   in foldM addAlias env sccs

addAlias :: Env.Env -> Graph.SCC (A.Located Src.Alias) -> Result i w Env.Env
addAlias env@(Env.Env home vs ts cs bs cls ms qvs qts qcs qcls qms) scc =
  case scc of
    Graph.AcyclicSCC alias@(A.At _ (Src.Alias (A.At _ name) _ tipe)) ->
      do
        args <- checkAliasFreeVars alias
        ctype <- Type.canonicalize env tipe
        let one = Env.Specific home (Env.Alias (length args) home args ctype)
        let ts1 = Map.insert name one ts
        Result.ok $ Env.Env home vs ts1 cs bs cls ms qvs qts qcs qcls qms
    Graph.CyclicSCC [] ->
      Result.ok env
    Graph.CyclicSCC (alias@(A.At _ (Src.Alias (A.At region name1) _ tipe)) : others) ->
      do
        args <- checkAliasFreeVars alias
        let toName (A.At _ (Src.Alias (A.At _ name) _ _)) = name
        Result.throw (Error.RecursiveAlias region name1 args tipe (map toName others))

-- DETECT TYPE ALIAS CYCLES

toNode :: A.Located Src.Alias -> (A.Located Src.Alias, Name.Name, [Name.Name])
toNode alias@(A.At _ (Src.Alias (A.At _ name) _ tipe)) =
  (alias, name, getEdges [] tipe)

getEdges :: [Name.Name] -> Src.Type -> [Name.Name]
getEdges edges (A.At _ tipe) =
  case tipe of
    Src.TLambda arg result _ ->
      getEdges (getEdges edges arg) result
    Src.TVar _ ->
      edges
    Src.TType _ name args ->
      List.foldl' getEdges (name : edges) (fmap snd args)
    Src.TTypeQual _ _ _ args ->
      List.foldl' getEdges edges (fmap snd args)
    Src.TRecord fields _ ->
      List.foldl' (\es (_, t, _) -> getEdges es t) edges fields
    Src.TParens inner _ ->
      getEdges edges inner

-- CHECK FREE VARIABLES

checkUnionFreeVars :: A.Located Src.Union -> Result i w Int
checkUnionFreeVars (A.At unionRegion (Src.Union (A.At _ name) args ctors _ _)) =
  let addArg (_, A.At region arg) dict =
        Dups.insert arg region region dict

      addCtorFreeVars (_, _, tipes, _) freeVars =
        List.foldl' addFreeVars freeVars (fmap snd tipes)
   in do
        boundVars <- Dups.detect (Error.DuplicateUnionArg name) (foldr addArg Dups.none args)
        let freeVars = foldr addCtorFreeVars Map.empty ctors
        case Map.toList (Map.difference freeVars boundVars) of
          [] ->
            Result.ok (length args)
          unbound : unbounds ->
            Result.throw $
              Error.TypeVarsUnboundInUnion unionRegion name (map (A.toValue . snd) args) unbound unbounds

checkAliasFreeVars :: A.Located Src.Alias -> Result i w [Name.Name]
checkAliasFreeVars (A.At aliasRegion (Src.Alias (A.At _ name) args tipe)) =
  let addArg (A.At region arg) dict =
        Dups.insert arg region region dict
   in do
        boundVars <- Dups.detect (Error.DuplicateAliasArg name) (foldr addArg Dups.none args)
        let freeVars = addFreeVars Map.empty tipe
        let overlap = Map.size (Map.intersection boundVars freeVars)
        if Map.size boundVars == overlap && Map.size freeVars == overlap
          then Result.ok (map A.toValue args)
          else
            Result.throw $
              Error.TypeVarsMessedUpInAlias
                aliasRegion
                name
                (map A.toValue args)
                (Map.toList (Map.difference boundVars freeVars))
                (Map.toList (Map.difference freeVars boundVars))

addFreeVars :: Map.Map Name.Name A.Region -> Src.Type -> Map.Map Name.Name A.Region
addFreeVars freeVars (A.At region tipe) =
  case tipe of
    Src.TLambda arg result _ ->
      addFreeVars (addFreeVars freeVars arg) result
    Src.TVar name ->
      Map.insert name region freeVars
    Src.TType _ _ args ->
      List.foldl' addFreeVars freeVars (fmap snd args)
    Src.TTypeQual _ _ _ args ->
      List.foldl' addFreeVars freeVars (fmap snd args)
    Src.TRecord fields maybeExt ->
      let extFreeVars =
            case maybeExt of
              Nothing ->
                freeVars
              Just (A.At extRegion ext, _) ->
                Map.insert ext extRegion freeVars
       in List.foldl' (\fvs (_, t, _) -> addFreeVars fvs t) extFreeVars fields
    Src.TParens inner _ ->
      addFreeVars freeVars inner

-- ADD CTORS

addCtors :: Src.Module -> Env.Env -> Result i w (Env.Env, Unions, Aliases)
addCtors (Src.Module _ _ _ _ _ _ _ unions aliases _ _ _ _) env@(Env.Env home vs ts cs bs cls ms qvs qts qcs qcls qms) =
  do
    unionInfo <- traverse (canonicalizeUnion env) (fmap snd unions)
    aliasInfo <- traverse (canonicalizeAlias env) (fmap snd aliases)

    ctors <-
      Dups.detect Error.DuplicateCtor $
        Dups.union
          (Dups.unions (map snd unionInfo))
          (Dups.unions (map snd aliasInfo))

    let cs2 = Map.union ctors cs

    Result.ok
      ( Env.Env home vs ts cs2 bs cls ms qvs qts qcs qcls qms,
        Map.fromList (map fst unionInfo),
        Map.fromList (map fst aliasInfo)
      )

type CtorDups = Dups.Dict (Env.Info Env.Ctor)

-- CANONICALIZE ALIAS

canonicalizeAlias :: Env.Env -> A.Located Src.Alias -> Result i w ((Name.Name, Can.Alias), CtorDups)
canonicalizeAlias env (A.At _ (Src.Alias (A.At _ name) args tipe)) =
  do
    let vars = map A.toValue args
    ctipe <- Type.canonicalize env tipe
    Result.ok
      ((name, Can.Alias vars ctipe), Dups.none)

-- CANONICALIZE UNION

canonicalizeUnion :: Env.Env -> A.Located Src.Union -> Result i w ((Name.Name, Can.Union), CtorDups)
canonicalizeUnion env@(Env.Env home _ _ _ _ _ _ _ _ _ _ _) (A.At _ (Src.Union (A.At _ name) avars ctors _ _)) =
  do
    cctors <- Index.indexedTraverse (canonicalizeCtor env) ctors
    let vars = map (A.toValue . snd) avars
    let alts = map A.toValue cctors
    let union = Can.Union vars alts (length alts) (toOpts ctors)
    Result.ok
      ( (name, union),
        Dups.unions $ map (toCtor home name union) cctors
      )

canonicalizeCtor :: Env.Env -> Index.ZeroBased -> Src.UnionVariant -> Result i w (A.Located Can.Ctor)
canonicalizeCtor env index (_, A.At region ctor, tipes, _) =
  let argLength = length tipes
   in if argLength > 1
        then Result.throw (Error.CustomTypeTooManyParams region ctor argLength)
        else do
          ctipes <- traverse (Type.canonicalize env) (fmap snd tipes)
          Result.ok $
            A.At region $
              Can.Ctor ctor index (length ctipes) ctipes

toOpts :: [Src.UnionVariant] -> Can.CtorOpts
toOpts ctors =
  case ctors of
    [(_, _, [_], _)] ->
      Can.Unbox
    _ ->
      if all (\(_, _, args, _) -> null args) ctors then Can.Enum else Can.Normal

toCtor :: ModuleName.Canonical -> Name.Name -> Can.Union -> A.Located Can.Ctor -> CtorDups
toCtor home typeName union (A.At region (Can.Ctor name index _ args)) =
  Dups.one name region $
    Env.Specific home $
      Env.Ctor home typeName union index args
