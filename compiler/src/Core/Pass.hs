{-# OPTIONS_GHC -Wall #-}

-- | The Core→Core passes, and which of them run.
--
-- @docs/core.md@ C11 puts the passes in Haskell through M1b and gives M1a's
-- pipeline none of them, so these are off unless @GENG_CORE_PASSES@ asks:
--
-- > GENG_CORE_PASSES=case          -- decision trees (C4, "Core.Pass.Case")
-- > GENG_CORE_PASSES=case,tailcall -- and self tail calls ("Core.Pass.TailCall")
-- > GENG_CORE_PASSES=specialize    -- witness erasure ("Core.Pass.Specialize")
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
--
-- __Specialization runs before either__, and it is the one pass that is not a
-- function of a single module: it needs every module's Core to know what
-- instantiations a program asks for (§G27). It runs first because the copies it
-- makes are definitions like any other, and a copy that exists before the
-- per-module passes run gets the same treatment as the code it was copied from
-- — 'Core.Pass.TailCall' in particular finds a copy's self call, which is to the
-- copy's own name and not to the generic one.
module Core.Pass
  ( run,
    enabled,
  )
where

import Core.AST qualified as Core
import Core.Dump qualified as Dump
import Core.Pass.Case qualified as Case
import Core.Pass.Specialize qualified as Specialize
import Core.Pass.TailCall qualified as TailCall
import Data.Map (Map)
import Data.Map qualified as Map
import Gren.ModuleName qualified as ModuleName

-- | Whether any pass is on, so that a caller can skip the work of asking.
enabled :: Bool
enabled = not (null Dump.corePasses)

run :: Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
run cores =
  let pass name f = if name `elem` Dump.corePasses then f else id
      specialized = pass "specialize" Specialize.run cores
      tbl = Case.table (Map.elems specialized)
   in Map.map (pass "case" (Case.run tbl) . pass "tailcall" TailCall.run) specialized
