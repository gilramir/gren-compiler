{-# OPTIONS_GHC -Wall #-}

-- | The Core→Core passes, and which of them run.
--
-- @docs/core.md@ C11 puts the passes in Haskell through M1b and gives M1a's
-- pipeline none of them, so these are off unless @GENG_CORE_PASSES@ asks:
--
-- > GENG_CORE_PASSES=case          -- decision trees (C4, "Core.Pass.Case")
-- > GENG_CORE_PASSES=case,tailcall -- and self tail calls ("Core.Pass.TailCall")
--
-- A switch rather than a mode, for the reason C4 gives: the pass is optional,
-- its output is still Core, and a program has to answer the same either way.
-- The differential harness runs the corpus through both — @geng-core-js@ and
-- @geng-core-js-passes@ — which is what makes that a test rather than a claim.
--
-- __Order__: tail calls first, then decision trees. The tail-call pass looks for
-- self calls in tail position, and a case that has not been compiled yet has its
-- branch bodies exactly where the reader wrote them; running it second would
-- mean looking for the same calls through the joins and cases the other pass
-- introduced. Both orders find the same calls — 'Core.Pass.TailCall' walks
-- 'Core.AST.EJoin' too — and this one is easier to reason about.
module Core.Pass
  ( run,
    enabled,
  )
where

import Core.AST qualified as Core
import Core.Dump qualified as Dump
import Core.Pass.Case qualified as Case
import Core.Pass.TailCall qualified as TailCall
import Data.Map (Map)
import Data.Map qualified as Map
import Gren.ModuleName qualified as ModuleName

-- | Whether any pass is on, so that a caller can skip the work of asking.
enabled :: Bool
enabled = not (null Dump.corePasses)

run :: Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
run cores =
  let tbl = Case.table (Map.elems cores)
      pass name f = if name `elem` Dump.corePasses then f else id
   in Map.map (pass "case" (Case.run tbl) . pass "tailcall" TailCall.run) cores
