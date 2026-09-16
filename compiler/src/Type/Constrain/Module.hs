{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module Type.Constrain.Module
  ( constrain,
  )
where

import AST.Canonical qualified as Can
import Data.Map.Strict qualified as Map
import Type.Constrain.Expression qualified as Expr
import Type.Type (Constraint (..))

-- CONSTRAIN

constrain :: Can.Module -> IO Constraint
constrain (Can.Module _ _ _ decls _ _ _ instances _ _ _) =
  constrainDecls decls =<< constrainInstances instances

-- CONSTRAIN INSTANCES

-- | Every instance method, checked where the module's own definitions are in
-- scope and none of them bound (`docs/m1b-classes.md` §G22).
--
-- Each method is its own `CLet` with 'CTrue' under it, so the name it binds
-- reaches nothing: two instances of one class define the same method name, and
-- an instance method is not a top-level binding in the first place (§G19.2).
-- That is also why none of them turns up in the annotations `Type.Solve`
-- saves, which is where 'Gren.Interface._values' comes from.
--
-- It replaces 'CSaveTheEnvironment' as the innermost constraint rather than
-- wrapping the declarations, because an instance body may call anything the
-- module defines.
constrainInstances :: Map.Map Can.InstanceKey Can.Instance -> IO Constraint
constrainInstances instances =
  case concatMap (Map.elems . Can._in_methods) (Map.elems instances) of
    [] ->
      return CSaveTheEnvironment
    methods ->
      do
        cons <- traverse (\d -> Expr.constrainDef Map.empty d CTrue) methods
        return (CAnd (cons ++ [CSaveTheEnvironment]))

-- CONSTRAIN DECLARATIONS

constrainDecls :: Can.Decls -> Constraint -> IO Constraint
constrainDecls decls finalConstraint =
  case decls of
    Can.Declare def otherDecls ->
      Expr.constrainDef Map.empty def =<< constrainDecls otherDecls finalConstraint
    Can.DeclareRec def defs otherDecls ->
      Expr.constrainRecursiveDefs Map.empty (def : defs) =<< constrainDecls otherDecls finalConstraint
    Can.SaveTheEnvironment ->
      return finalConstraint
