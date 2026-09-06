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

bindRefs :: Core.Bind -> Refs.Refs
bindRefs = Refs.refsIn . Core._bindValue

isDebug :: Core.QualName -> Bool
isDebug (Core.QualName home _) =
  home == ModuleName.debug
