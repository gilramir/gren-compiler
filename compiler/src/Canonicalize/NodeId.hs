{-# OPTIONS_GHC -Wall #-}

-- | Give every expression node in a module a distinct identity.
--
-- Canonicalization builds every node as 'Can.unnumbered'; this pass replaces
-- them in one traversal, in a fixed order. Two reasons it is a separate pass
-- rather than a counter threaded through the canonicalizer:
--
--   * The canonicalizer runs inside a 'Result' applicative whose effects are
--     error collection, not state. Threading a counter through it would order
--     the numbering by the applicative's evaluation, which is not the order
--     anybody reading the code would predict.
--   * The order is then decided in one place, by one function, which is what
--     C6 asks of every traversal that can affect Core output. Numbering that
--     depends on evaluation order is exactly the byte-determinism hazard C6
--     exists to remove.
--
-- The order is source order: a node is numbered before its children, and
-- children left to right, matching the order the constructors are written in
-- "AST.Canonical". Ids start at 1, so that 'Can.unnumbered' — which is 0 —
-- is never a valid id and an unnumbered node that escapes this pass is
-- distinguishable rather than merely wrong.
module Canonicalize.NodeId
  ( number,
    numberExpr,
  )
where

import AST.Canonical qualified as Can
import Control.Monad.Trans.State.Strict (State, runState, state)
import Data.Map qualified as Map

type Numbering a = State Int a

fresh :: Numbering Can.NodeId
fresh = state (\n -> (Can.NodeId (n + 1), n + 1))

-- | Number every expression node in a module.
number :: Can.Module -> Can.Module
number modul =
  modul {Can._decls = fst (runState (decls (Can._decls modul)) 0)}

-- | Number one expression, starting from zero. For tests, and for anything
-- that needs a numbered subtree without a module around it.
numberExpr :: Can.Expr -> Can.Expr
numberExpr e = fst (runState (expr e) 0)

decls :: Can.Decls -> Numbering Can.Decls
decls ds =
  case ds of
    Can.Declare d rest ->
      Can.Declare <$> def d <*> decls rest
    Can.DeclareRec d others rest ->
      Can.DeclareRec <$> def d <*> traverse def others <*> decls rest
    Can.SaveTheEnvironment ->
      pure Can.SaveTheEnvironment

def :: Can.Def -> Numbering Can.Def
def d =
  case d of
    Can.Def name args body ->
      Can.Def name args <$> expr body
    Can.TypedDef name freeVars args body result ->
      (\b -> Can.TypedDef name freeVars args b result) <$> expr body

expr :: Can.Expr -> Numbering Can.Expr
expr (Can.Expr _ region value) =
  do
    nid <- fresh
    Can.Expr nid region <$> expr_ value

expr_ :: Can.Expr_ -> Numbering Can.Expr_
expr_ e =
  case e of
    Can.VarLocal _ -> pure e
    Can.VarTopLevel _ _ -> pure e
    Can.VarKernel _ _ -> pure e
    Can.VarForeign _ _ _ -> pure e
    Can.VarCtor _ _ _ _ _ -> pure e
    Can.VarDebug _ _ _ -> pure e
    Can.VarOperator _ _ _ _ -> pure e
    Can.Chr _ -> pure e
    Can.Str _ -> pure e
    Can.Int _ -> pure e
    Can.Float _ -> pure e
    Can.Accessor _ -> pure e
    Can.Array items ->
      Can.Array <$> traverse expr items
    Can.Negate inner ->
      Can.Negate <$> expr inner
    Can.Binop op home name annotation left right ->
      Can.Binop op home name annotation <$> expr left <*> expr right
    Can.Lambda args body ->
      Can.Lambda args <$> expr body
    Can.Call func args ->
      Can.Call <$> expr func <*> traverse expr args
    Can.If branches final ->
      Can.If
        <$> traverse (\(c, b) -> (,) <$> expr c <*> expr b) branches
        <*> expr final
    Can.Let d body ->
      Can.Let <$> def d <*> expr body
    Can.LetRec ds body ->
      Can.LetRec <$> traverse def ds <*> expr body
    Can.LetDestruct pattern value body ->
      Can.LetDestruct pattern <$> expr value <*> expr body
    Can.Case scrutinee branches ->
      Can.Case
        <$> expr scrutinee
        <*> traverse
          (\(Can.CaseBranch p b) -> Can.CaseBranch p <$> expr b)
          branches
    Can.Access record field ->
      (\r -> Can.Access r field) <$> expr record
    Can.Update record fields ->
      Can.Update <$> expr record <*> traverseOrdered fieldUpdate fields
    Can.Record fields ->
      Can.Record <$> traverseOrdered expr fields
  where
    fieldUpdate (Can.FieldUpdate region value) =
      Can.FieldUpdate region <$> expr value

-- | Walk a field map in key order.
--
-- 'Map.traverseWithKey' already visits in key order, but the guarantee is what
-- matters here rather than the mechanism: a record's fields must be numbered
-- the same way on every run and in every frontend, and C6 requires every
-- 'Map' traversal that can affect Core output to say so out loud rather than
-- inherit it.
--
-- The key is @A.Located Name@, whose 'Ord' includes the region, so two frontends
-- agree only because they agree on regions too. That holds — both parse the
-- same bytes — but it is why this is a named function rather than an inline
-- 'traverse'.
traverseOrdered ::
  (a -> Numbering b) ->
  Map.Map k a ->
  Numbering (Map.Map k b)
traverseOrdered f = Map.traverseWithKey (\_ v -> f v)
