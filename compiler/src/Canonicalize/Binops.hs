-- | Infix operators given their precedence and associativity: the chain the
-- parser reads flat, @a + b * c@, made a tree. Shared by expressions and by a
-- refinement's predicate (geng-lang @m4-refine.md@ §RF17), which the parser
-- reads as the same chain.
module Canonicalize.Binops
  ( Step (..),
    run,
  )
where

import AST.Canonical qualified as Can
import AST.Utils.Binop qualified as Binop
import Canonicalize.Environment qualified as Env
import Reporting.Annotation qualified as A
import Reporting.Error.Canonicalize qualified as Error
import Reporting.Result qualified as Result

data Step
  = Done Can.Expr
  | More [(Can.Expr, Env.Binop)] Can.Expr
  | Error Env.Binop Env.Binop

run :: A.Region -> Step -> Result.Result i w Error.Error Can.Expr
run overallRegion step =
  case step of
    Done expr ->
      Result.ok expr
    More [] expr ->
      Result.ok expr
    More ((expr, op) : rest) final ->
      run overallRegion $
        toBinopStep (toBinop op expr) op rest final
    Error (Env.Binop op1 _ _ _ _) (Env.Binop op2 _ _ _ _) ->
      Result.throw (Error.Binop overallRegion op1 op2)

toBinopStep :: (Can.Expr -> Can.Expr) -> Env.Binop -> [(Can.Expr, Env.Binop)] -> Can.Expr -> Step
toBinopStep makeBinop rootOp@(Env.Binop _ _ _ rootAssociativity rootPrecedence) middle final =
  case middle of
    [] ->
      Done (makeBinop final)
    (expr, op@(Env.Binop _ _ _ associativity precedence)) : rest ->
      if precedence < rootPrecedence
        then More ((makeBinop expr, op) : rest) final
        else
          if precedence > rootPrecedence
            then case toBinopStep (toBinop op expr) op rest final of
              Done newLast ->
                Done (makeBinop newLast)
              More newMiddle newLast ->
                toBinopStep makeBinop rootOp newMiddle newLast
              Error a b ->
                Error a b
            else case (rootAssociativity, associativity) of
              (Binop.Left, Binop.Left) ->
                toBinopStep (\right -> toBinop op (makeBinop expr) right) op rest final
              (Binop.Right, Binop.Right) ->
                toBinopStep (\right -> makeBinop (toBinop op expr right)) op rest final
              (_, _) ->
                Error rootOp op

toBinop :: Env.Binop -> Can.Expr -> Can.Expr -> Can.Expr
toBinop (Env.Binop op target annotation _ _) left right =
  Can.at
    (A.mergeRegions (Can.exprRegion left) (Can.exprRegion right))
    (Can.Binop op target annotation left right)

