{-# OPTIONS_GHC -Wall #-}

-- | Does a module still call @Debug@?
--
-- @--optimize@ refuses to compile one that does, and the question is asked of
-- Core. Canonicalization is where a @Debug@ reference stops being an ordinary
-- foreign variable: 'Canonicalize.Expression.findVar' turns any value whose home
-- is 'ModuleName.debug' into @Can.VarDebug@, whatever its name, and
-- "Core.Lower.Expression" lowers that to an @EGlobal@ with the same home. So the
-- check is one walk over a module's bindings looking for that home, and it needs
-- no list of the @Debug@ functions to keep in step with.
--
-- The old pipeline asked its own graph the same question by looking for
-- @Opt.VarDebug@ nodes. Both were built from the same @Can.VarDebug@.
--
-- __Except @Debug.todo@__, which since D335 is not an @EGlobal@: the lowering
-- makes it @ECrash (Todo place message)@, so the walk for globals stopped
-- seeing it and @--optimize@ began to accept a program stock refuses. D346 asks
-- for it by name: a module with a 'Core.Todo' crash is a @Debug@ use.
module Nitpick.Debug
  ( hasDebugUses,
  )
where

import Core.AST qualified as Core
import Core.Refs qualified as Refs
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName

hasDebugUses :: Core.Module -> Bool
hasDebugUses modul =
  any isDebug (Set.toList (Refs._refGlobals (foldMap bindRefs (Core._moduleDefs modul))))
    || any (hasTodo . Core._bindValue) (Core._moduleDefs modul)

bindRefs :: Core.Bind -> Refs.Refs
bindRefs = Refs.refsIn . Core._bindValue

isDebug :: Core.QualName -> Bool
isDebug (Core.QualName home _) =
  home == ModuleName.debug

-- | Whether an expression holds a @Debug.todo@ anywhere.
hasTodo :: Core.Expr -> Bool
hasTodo (Core.Expr value _ _) =
  case value of
    Core.EVar _ -> False
    Core.EGlobal _ -> False
    Core.ELit _ -> False
    Core.ECrash (Core.Todo _ _) -> True
    Core.ECrash _ -> False
    Core.ELam _ body -> hasTodo body
    Core.EApp fn args -> any hasTodo (fn : args)
    Core.ELet binds body -> any (hasTodo . Core._bindValue) binds || hasTodo body
    Core.ELetRec binds body -> any (hasTodo . Core._bindValue) binds || hasTodo body
    Core.EJoin binds body -> any (hasTodo . Core._bindValue) binds || hasTodo body
    Core.EJump _ args -> any hasTodo args
    Core.ECase scrut alts fallback ->
      hasTodo scrut || any (hasTodo . Core._altBody) alts || any hasTodo fallback
    Core.ECtor _ _ args -> any hasTodo args
    Core.ERecord fields -> any (hasTodo . snd) fields
    Core.EUpdate base fields -> hasTodo base || any (hasTodo . snd) fields
    Core.EAccess base _ -> hasTodo base
    Core.EArray items -> any hasTodo items
    Core.EPrim _ args -> any hasTodo args
    Core.ETyLam _ body -> hasTodo body
    Core.ETyApp body _ -> hasTodo body
    Core.EWitLam _ body -> hasTodo body
    Core.EWitApp body args -> any hasTodo (body : args)
