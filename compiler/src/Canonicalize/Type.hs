module Canonicalize.Type
  ( toAnnotation,
    canonicalize,
  )
where

import AST.Canonical qualified as Can
import AST.Source qualified as Src
import Canonicalize.Environment qualified as Env
import Canonicalize.Environment.Dups qualified as Dups
import Control.Monad (foldM)
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Name qualified as Name
import Reporting.Annotation qualified as A
import Reporting.Error.Canonicalize qualified as Error
import Reporting.Result qualified as Result

-- RESULT

type Result i w a =
  Result.Result i w Error.Error a

-- TO ANNOTATION

-- | An annotation: the type, the variables it binds, and what each is
-- constrained by (D111).
--
-- The context is taken here rather than checked separately because it is part
-- of what an annotation is — `Src.Annotation` already pairs them — and because
-- a constraint has no meaning apart from the variables the type binds. A port
-- has no context and passes `Nothing`.
toAnnotation :: Env.Env -> Maybe Src.Context -> Src.Type -> Result i w Can.Annotation
toAnnotation env maybeContext srcType =
  do
    tipe <- canonicalize env srcType
    freeVars <- addContext env (addFreeVars Map.empty tipe) maybeContext
    Result.ok $ Can.Forall freeVars tipe

-- CONTEXT

-- | `(Eq a, Ord b) =>`, resolved onto the variables the type binds.
--
-- Two things are checked and both are about the annotation rather than about
-- the class. __The variable has to be one the type binds__: `Eq b => a -> a`
-- has nowhere to put the constraint, because D111 keys the constraint list off
-- `FreeVars`, and a promise about a variable that does not occur is a promise
-- about nothing. And __a constraint may not be written twice__ on the same
-- variable; the second one says nothing the first did not.
--
-- The order the author wrote is kept. It is not Core's order — `lowerAnnotation`
-- sorts, because that is where types are compared — and keeping it here is the
-- same split `Can.TRecord` already makes, carrying a source-order index that
-- `lowerType` drops.
addContext :: Env.Env -> Can.FreeVars -> Maybe Src.Context -> Result i w Can.FreeVars
addContext env freeVars maybeContext =
  case maybeContext of
    Nothing ->
      Result.ok freeVars
    Just (Src.Context entries _) ->
      foldM (addConstraint env) freeVars entries

addConstraint :: Env.Env -> Can.FreeVars -> Src.ContextEntry -> Result i w Can.FreeVars
addConstraint env freeVars (A.At region constraint, _) =
  do
    (className, cls, A.At varRegion var) <-
      case constraint of
        Src.Constraint _ name varName ->
          (,,) name <$> Env.findClass region env name <*> pure varName
        Src.ConstraintQual _ home name varName ->
          (,,) name <$> Env.findClassQual region env home name <*> pure varName
    case Map.lookup var freeVars of
      Nothing ->
        Result.throw (Error.ConstraintVarUnbound varRegion className var)
      Just classes ->
        if cls `elem` classes
          then Result.throw (Error.ConstraintDuplicate region className var)
          else Result.ok (Map.insert var (classes ++ [cls]) freeVars)

-- CANONICALIZE TYPES

canonicalize :: Env.Env -> Src.Type -> Result i w Can.Type
canonicalize env (A.At typeRegion tipe) =
  case tipe of
    Src.TVar x ->
      Result.ok (Can.TVar x)
    Src.TType region name args ->
      canonicalizeType env typeRegion name (fmap snd args)
        =<< Env.findType region env name
    Src.TTypeQual region home name args ->
      canonicalizeType env typeRegion name (fmap snd args)
        =<< Env.findTypeQual region env home name
    Src.TLambda a b _ ->
      Can.TLambda
        <$> canonicalize env a
        <*> canonicalize env b
    Src.TRecord fields ext ->
      do
        cfields <- sequenceA =<< Dups.checkFields (canonicalizeFields env fields)
        return $ Can.TRecord cfields (fmap (A.toValue . fst) ext)
    Src.TParens inner _ ->
      canonicalize env inner

canonicalizeFields :: Env.Env -> [Src.TRecordField] -> [(A.Located Name.Name, Result i w Can.FieldType, ())]
canonicalizeFields env fields =
  let len = fromIntegral (length fields)
      canonicalizeField index (name, srcType, _) =
        (name, Can.FieldType index <$> canonicalize env srcType, ())
   in zipWith canonicalizeField [0 .. len] fields

-- CANONICALIZE TYPE

canonicalizeType :: Env.Env -> A.Region -> Name.Name -> [Src.Type] -> Env.Type -> Result i w Can.Type
canonicalizeType env region name args info =
  do
    cargs <- traverse (canonicalize env) args
    case info of
      Env.Alias arity home argNames aliasedType ->
        checkArity arity region name args $
          Can.TAlias home name (zip argNames cargs) (Can.Holey aliasedType)
      Env.Union arity home ->
        checkArity arity region name args $
          Can.TType home name cargs

checkArity :: Int -> A.Region -> Name.Name -> [A.Located arg] -> answer -> Result i w answer
checkArity expected region name args answer =
  let actual = length args
   in if expected == actual
        then Result.ok answer
        else Result.throw (Error.BadArity region Error.TypeArity name expected actual)

-- ADD FREE VARS

-- | The annotation's bound variables, each with an empty constraint list.
--
-- Empty here and filled by `addContext` above, which is the only thing that
-- may fill it: a constraint is written on the annotation, and a variable the
-- author said nothing about is unconstrained.
addFreeVars :: Map.Map Name.Name [Can.Class] -> Can.Type -> Map.Map Name.Name [Can.Class]
addFreeVars freeVars tipe =
  case tipe of
    Can.TLambda arg result ->
      addFreeVars (addFreeVars freeVars result) arg
    Can.TVar var ->
      Map.insert var [] freeVars
    Can.TType _ _ args ->
      List.foldl' addFreeVars freeVars args
    Can.TRecord fields Nothing ->
      Map.foldl addFieldFreeVars freeVars fields
    Can.TRecord fields (Just ext) ->
      Map.foldl addFieldFreeVars (Map.insert ext [] freeVars) fields
    Can.TAlias _ _ args _ ->
      List.foldl' (\fvs (_, arg) -> addFreeVars fvs arg) freeVars args

addFieldFreeVars :: Map.Map Name.Name [Can.Class] -> Can.FieldType -> Map.Map Name.Name [Can.Class]
addFieldFreeVars freeVars (Can.FieldType _ tipe) =
  addFreeVars freeVars tipe
