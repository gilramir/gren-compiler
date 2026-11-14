{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module Type.Constrain.Module
  ( constrain,
  )
where

import AST.Canonical qualified as Can
import Data.Map.Strict qualified as Map
import Data.Name qualified as Name
import Type.Constrain.Expression qualified as Expr
import Type.Type (Constraint (..))

-- CONSTRAIN

constrain :: Can.Module -> IO Constraint
constrain (Can.Module _ _ _ decls unions aliases _ instances _ _ _ _ _ ctorRefinements _ _ _) =
  do
    inner <- constrainInstances instances
    contracts <- constrainCtorRefinements unions ctorRefinements
    -- Each record alias's invariant (geng-lang m4-refine-t1.md TO17), typed
    -- as a contract is, its record the alias's body.
    invariants <- traverse (\(Can.Alias _ body _, r) -> Expr.constrainCtorRefinement body r) [(a, r) | a <- Map.elems aliases, Just r <- [Can.aliasInvariant a]]
    constrainDecls decls (if null (contracts ++ invariants) then inner else CAnd (contracts ++ invariants ++ [inner]))

-- | Each constructor's contract (geng-lang @m4-refine-t1.md@ TO13), where the
-- module's own definitions are in scope, as an instance method is, since a
-- predicate may read a measure the module declares.
constrainCtorRefinements :: Map.Map Name.Name Can.Union -> Map.Map Name.Name Can.AliasRefinement -> IO [Constraint]
constrainCtorRefinements unions refinements =
  traverse
    (\(argType, refinement) -> Expr.constrainCtorRefinement argType refinement)
    [ (argType, refinement)
    | Can.Union _ ctors _ _ <- Map.elems unions,
      Can.Ctor name _ _ [argType] <- ctors,
      Just refinement <- [Map.lookup name refinements]
    ]

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
