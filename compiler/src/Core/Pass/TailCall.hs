{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | Self tail calls become a loop (@docs/core.md@ C9 and C15,
-- @docs/m1a-js-on-core.md@ §J3 item 4).
--
-- C9 said this would be "a pass, not a node": Core has ordinary recursive
-- calls, and a Core→Core pass rewrites the self tail calls "to a loop form".
-- What it did not say was what a loop is in Core, and §J3 item 4 reopened that
-- as a specification question — a new node, an annotation on 'Core.Bind', or
-- recognition inside each backend.
--
-- C15 had already answered it. A loop __is__ a join point: a function whose
-- body is a join over its own parameters, entered once with them, is a
-- @while (true)@ with a @continue@ at every tail call, and that is what every
-- backend does with it anyway. So this pass adds no node and needs no
-- annotation:
--
-- > sum total array =           sum = \total array ->
-- >   when ... is                 join $t0 = \total array ->
-- >     [] -> total                 when ... is
-- >     _ -> sum (…) (…)              [] -> total
-- >                                   _ -> jump $t0 (…) (…)
-- >                               in jump $t0 total array
--
-- __What counts as a tail call__: a saturated application of the function being
-- defined, in tail position of its own body. Tail position runs through 'ELet',
-- 'ELetRec', the alternatives and fallback of an 'ECase', and both halves of an
-- 'EJoin' — a jump is in tail position, so what a join's body evaluates to is
-- what the function returns. A call anywhere else stays a call.
--
-- __Mutual recursion is not here__, and is not this pass's job: D14 gives it a
-- trampoline in @Low@, and the BEAM does it natively.
module Core.Pass.TailCall
  ( run,
  )
where

import Control.Monad.Trans.State.Strict (State, evalState, state)
import Core.AST qualified as Core
import Data.Name (Name)
import Data.Name qualified as Name
import Gren.ModuleName qualified as ModuleName

-- | A @port@'s converters are deliberately left alone.
--
-- The pass rewrites a call a definition makes to /itself/ into a jump, and it
-- knows which call that is from the name the definition is bound to. A
-- converter is not bound to a name: the name a port defines stands for the port,
-- so a reference to it inside a converter would be a reference to the port and
-- not to the converter, and turning it into a jump would be wrong. Generated
-- converters contain no recursion of any kind, so there is nothing being given
-- up.
run :: Core.Module -> Core.Module
run m =
  let home = Core._moduleName m
   in m {Core._moduleDefs = map (topLevel home) (Core._moduleDefs m)}

-- | Fresh join names, from a counter that restarts at every definition. @$@
-- cannot appear in a Gren name, and the prefix is not "Core.Pass.Case"'s, so a
-- module compiled by both passes has no two joins with one name.
type Fresh a = State Int a

fresh :: Fresh Name
fresh = state (\uid -> (Name.fromChars ("$t" ++ show uid), uid + 1))

-- DEFINITIONS

topLevel :: ModuleName.Canonical -> Core.Bind -> Core.Bind
topLevel home (Core.Bind binder value) =
  let self = Core.EGlobal (Core.QualName home (Core._binderName binder))
   in Core.Bind binder (evalState (definition self value) 0)

-- | Rewrite a definition, and every function bound inside it.
--
-- The order matters only in that the outer function is rewritten first, so an
-- inner function that tail-calls itself is found while walking the outer one's
-- new body rather than the old one.
definition :: Core.Expr_ -> Core.Expr -> Fresh Core.Expr
definition self value =
  do
    looped <- loopify self value
    walk looped

-- | Turn a function whose body tail-calls itself into a join over its own
-- parameters, entered with them.
loopify :: Core.Expr_ -> Core.Expr -> Fresh Core.Expr
loopify self value =
  case Core._exprValue value of
    Core.ELam params body
      | calls self (length params) body ->
          do
            join <- fresh
            let rewritten = rewrite self join (length params) body
                lam = Core.Expr (Core.ELam params rewritten) (Core.typeOf value) (Core.spanOf value)
                binder = Core.Binder join (Core.typeOf value) (Core.spanOf value)
                entry =
                  Core.Expr
                    (Core.EJump join [Core.Expr (Core.EVar (Core._binderName p)) (Core._binderType p) (Core._binderSpan p) | p <- params])
                    (Core.typeOf body)
                    (Core.spanOf body)
                joined =
                  Core.Expr (Core.EJoin [Core.Bind binder lam] entry) (Core.typeOf body) (Core.spanOf body)
             in pure (Core.Expr (Core.ELam params joined) (Core.typeOf value) (Core.spanOf value))
    _ -> pure value

-- | Whether the body has a saturated self call in tail position.
calls :: Core.Expr_ -> Int -> Core.Expr -> Bool
calls self arity body =
  case Core._exprValue body of
    Core.EApp fn args -> Core._exprValue fn == self && length args == arity
    Core.ELet _ inner -> calls self arity inner
    Core.ELetRec _ inner -> calls self arity inner
    Core.EJoin binds inner ->
      calls self arity inner || any (calls self arity . Core._bindValue) binds
    Core.ECase _ alts fallback ->
      any (calls self arity . Core._altBody) alts || any (calls self arity) fallback
    _ -> False

-- | Replace every saturated self call in tail position with a jump. Everything
-- else is left exactly as it is, including a self call that is not in tail
-- position: that one still needs a stack frame, and the definition is still
-- there to be called.
rewrite :: Core.Expr_ -> Name -> Int -> Core.Expr -> Core.Expr
rewrite self join arity expr =
  let node v = Core.Expr v (Core.typeOf expr) (Core.spanOf expr)
      recur = rewrite self join arity
   in case Core._exprValue expr of
        Core.EApp fn args
          | Core._exprValue fn == self && length args == arity -> node (Core.EJump join args)
        Core.ELet binds inner -> node (Core.ELet binds (recur inner))
        Core.ELetRec binds inner -> node (Core.ELetRec binds (recur inner))
        Core.EJoin binds inner ->
          node (Core.EJoin [Core.Bind b (recur v) | Core.Bind b v <- binds] (recur inner))
        Core.ECase scrutinee alts fallback ->
          node
            ( Core.ECase
                scrutinee
                [Core.Alt p (recur b) | Core.Alt p b <- alts]
                (fmap recur fallback)
            )
        _ -> expr

-- WALKING THE REST

-- | Every other function in the expression: a @let@-bound one is rewritten the
-- same way, against its own name.
walk :: Core.Expr -> Fresh Core.Expr
walk expr =
  let node v = Core.Expr v (Core.typeOf expr) (Core.spanOf expr)
   in case Core._exprValue expr of
        Core.ELet binds body -> node <$> (Core.ELet <$> traverse local binds <*> walk body)
        Core.ELetRec binds body -> node <$> (Core.ELetRec <$> traverse local binds <*> walk body)
        Core.EJoin binds body -> node <$> (Core.EJoin <$> traverse local binds <*> walk body)
        Core.EJump j args -> node . Core.EJump j <$> traverse walk args
        Core.ELam binders body -> node . Core.ELam binders <$> walk body
        Core.EApp fn args -> node <$> (Core.EApp <$> walk fn <*> traverse walk args)
        Core.ECase scrutinee alts fallback ->
          node
            <$> ( Core.ECase
                    <$> walk scrutinee
                    <*> traverse (\(Core.Alt p b) -> Core.Alt p <$> walk b) alts
                    <*> traverse walk fallback
                )
        Core.ECtor q tag args -> node . Core.ECtor q tag <$> traverse walk args
        Core.ERecord fields -> node . Core.ERecord <$> traverse field fields
        Core.EUpdate base fields -> node <$> (Core.EUpdate <$> walk base <*> traverse field fields)
        Core.EAccess base f -> node . (`Core.EAccess` f) <$> walk base
        Core.EArray items -> node . Core.EArray <$> traverse walk items
        Core.EPrim op args -> node . Core.EPrim op <$> traverse walk args
        Core.ETyLam vars body -> node . Core.ETyLam vars <$> walk body
        Core.ETyApp body types -> node . (`Core.ETyApp` types) <$> walk body
        Core.EWitLam binders body -> node . Core.EWitLam binders <$> walk body
        Core.EWitApp body args -> node <$> (Core.EWitApp <$> walk body <*> traverse walk args)
        Core.EVar _ -> pure expr
        Core.EGlobal _ -> pure expr
        Core.ELit _ -> pure expr
        Core.ECrash _ -> pure expr

local :: Core.Bind -> Fresh Core.Bind
local (Core.Bind binder value) =
  Core.Bind binder <$> definition (Core.EVar (Core._binderName binder)) value

field :: (Core.Field, Core.Expr) -> Fresh (Core.Field, Core.Expr)
field (f, e) = (,) f <$> walk e
