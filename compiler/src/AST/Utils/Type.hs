{-# OPTIONS_GHC -Wall #-}

module AST.Utils.Type
  ( delambda,
    dealias,
    substitute,
    deepDealias,
    iteratedDealias,
  )
where

import AST.Canonical (AliasType (..), FieldType (..), Type (..))
import Data.Map qualified as Map
import Data.Name qualified as Name

-- DELAMBDA

delambda :: Type -> [Type]
delambda tipe =
  case tipe of
    TLambda arg result ->
      arg : delambda result
    _ ->
      [tipe]

-- DEALIAS

dealias :: [(Name.Name, Type)] -> AliasType -> Type
dealias args aliasType =
  case aliasType of
    Holey tipe ->
      dealiasHelp (Map.fromList args) tipe
    Filled tipe ->
      tipe

-- | Replace type variables by types.
--
-- This is 'dealiasHelp' under the name of what it does, because specializing a
-- class method's signature at an instance head is the same operation as
-- filling an alias's parameters: @eq : a -> a -> Bool@ at @instance Eq (Array
-- b)@ is @a := Array b@. The 'TAlias' case is why it is worth sharing — an
-- alias's body binds the alias's /own/ parameter names, so nothing recurses
-- into it and only the arguments are substituted.
substitute :: Map.Map Name.Name Type -> Type -> Type
substitute =
  dealiasHelp

dealiasHelp :: Map.Map Name.Name Type -> Type -> Type
dealiasHelp typeTable tipe =
  case tipe of
    TLambda a b ->
      TLambda
        (dealiasHelp typeTable a)
        (dealiasHelp typeTable b)
    TVar x ->
      Map.findWithDefault tipe x typeTable
    TRecord fields ext ->
      TRecord (Map.map (dealiasField typeTable) fields) ext
    TAlias home name args t' ->
      TAlias home name (map (fmap (dealiasHelp typeTable)) args) t'
    TType home name args ->
      TType home name (map (dealiasHelp typeTable) args)

dealiasField :: Map.Map Name.Name Type -> FieldType -> FieldType
dealiasField typeTable (FieldType index tipe) =
  FieldType index (dealiasHelp typeTable tipe)

-- DEEP DEALIAS

deepDealias :: Type -> Type
deepDealias tipe =
  case tipe of
    TLambda a b ->
      TLambda (deepDealias a) (deepDealias b)
    TVar _ ->
      tipe
    TRecord fields ext ->
      TRecord (Map.map deepDealiasField fields) ext
    TAlias _ _ args tipe' ->
      deepDealias (dealias args tipe')
    TType home name args ->
      TType home name (map deepDealias args)

deepDealiasField :: FieldType -> FieldType
deepDealiasField (FieldType index tipe) =
  FieldType index (deepDealias tipe)

-- ITERATED DEALIAS

iteratedDealias :: Type -> Type
iteratedDealias tipe =
  case tipe of
    TAlias _ _ args realType ->
      iteratedDealias (dealias args realType)
    _ ->
      tipe
