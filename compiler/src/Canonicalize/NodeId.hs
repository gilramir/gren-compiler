{-# OPTIONS_GHC -Wall #-}

-- | Give every expression node — and every untyped definition — in a module a
-- distinct identity.
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
    Node (..),
    nodeId,
    nodes,
  )
where

import AST.Canonical qualified as Can
import Control.Monad.Trans.State.Strict (State, runState, state)
import Data.Map qualified as Map

type Numbering a = State Int a

-- | A node the type checker is expected to have recorded a type for.
data Node
  = ExprNode !Can.NodeId
  | -- | An untyped definition and its argument count. The count is what makes
    -- the recorded type checkable rather than merely present: the type is the
    -- function type the solver built from the argument patterns and the body,
    -- so it has at least that many arrows, and peeling them is how §N9 gets a
    -- type onto each argument pattern.
    DefNode !Can.NodeId !Int

nodeId :: Node -> Can.NodeId
nodeId n =
  case n of
    ExprNode nid -> nid
    DefNode nid _ -> nid

-- | Every node in a module, in numbering order.
--
-- Used to check that the type checker recorded a type for all of them
-- (`docs/m1a-node-types.md` §N7). A typed Core cannot be lowered from a
-- partially typed module, and "mostly typed" is exactly the state that would
-- pass unnoticed until a backend hit the gap.
nodes :: Can.Module -> [Node]
nodes modul =
  declNodes (Can._decls modul)
    ++ concatMap instanceNodes (Map.elems (Can._instances modul))

-- | An instance's methods, in the order 'number' visits them: after every
-- top-level definition, and among themselves in the key order the map already
-- imposes, which is a class and a type constructor rather than anything a
-- traversal chose.
instanceNodes :: Can.Instance -> [Node]
instanceNodes i = concatMap defNodes (Map.elems (Can._in_methods i))

declNodes :: Can.Decls -> [Node]
declNodes ds =
  case ds of
    Can.Declare d rest -> defNodes d ++ declNodes rest
    Can.DeclareRec d others rest -> defNodes d ++ concatMap defNodes others ++ declNodes rest
    Can.SaveTheEnvironment -> []

defNodes :: Can.Def -> [Node]
defNodes d =
  case d of
    Can.Def nid _ args body -> DefNode nid (length args) : exprNodes body
    Can.TypedDef _ _ _ body _ -> exprNodes body

exprNodes :: Can.Expr -> [Node]
exprNodes (Can.Expr nid _ value) = ExprNode nid : childNodes value

childNodes :: Can.Expr_ -> [Node]
childNodes e =
  case e of
    Can.Array items -> concatMap exprNodes items
    Can.Negate inner -> exprNodes inner
    Can.Binop _ _ _ _ left right -> exprNodes left ++ exprNodes right
    Can.Lambda _ body -> exprNodes body
    Can.Call func args -> concatMap exprNodes (func : args)
    Can.If branches final ->
      concatMap (\(c, b) -> exprNodes c ++ exprNodes b) branches ++ exprNodes final
    Can.Let d body -> defNodes d ++ exprNodes body
    Can.LetRec ds body -> concatMap defNodes ds ++ exprNodes body
    Can.LetDestruct _ value body -> exprNodes value ++ exprNodes body
    Can.Case scrutinee branches ->
      exprNodes scrutinee ++ concatMap (\(Can.CaseBranch _ b) -> exprNodes b) branches
    Can.Access record _ -> exprNodes record
    Can.Update record fields ->
      exprNodes record ++ concatMap (\(Can.FieldUpdate _ v) -> exprNodes v) (Map.elems fields)
    Can.Record fields -> concatMap exprNodes (Map.elems fields)
    _ -> []

fresh :: Numbering Can.NodeId
fresh = state (\n -> (Can.NodeId (n + 1), n + 1))

-- | Number every node in a module.
number :: Can.Module -> Can.Module
number modul =
  let numbered =
        do
          ds <- decls (Can._decls modul)
          is <- traverse instanceMethods (Can._instances modul)
          pure (ds, is)
      ((ds', is'), _) = runState numbered 0
   in modul {Can._decls = ds', Can._instances = is'}

instanceMethods :: Can.Instance -> Numbering Can.Instance
instanceMethods (Can.Instance head_ origin methods) =
  Can.Instance head_ origin <$> traverse def methods

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

-- | An untyped `Def` is numbered like an expression node and for the same
-- reason: its type — the function type the solver builds from its argument
-- patterns and its body — is recorded nowhere else, and Core's binders need it
-- (`docs/m1a-node-types.md` §N9). It is numbered before its body, the same
-- parent-before-children rule the expression traversal follows.
--
-- A `TypedDef` gets no id. Its argument types are cached on it already, so
-- there is nothing for the solver to tell us that the tree does not say.
def :: Can.Def -> Numbering Can.Def
def d =
  case d of
    Can.Def _ name args body ->
      do
        nid <- fresh
        Can.Def nid name args <$> expr body
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
    Can.VarMethod _ _ _ _ -> pure e
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
-- The key is @A.Located Name@, whose 'Ord' compares the name and ignores the
-- region, so the order is the field names' — which is what a second frontend
-- can reproduce without agreeing about source positions.
traverseOrdered ::
  (a -> Numbering b) ->
  Map.Map k a ->
  Numbering (Map.Map k b)
traverseOrdered f = Map.traverseWithKey (\_ v -> f v)
