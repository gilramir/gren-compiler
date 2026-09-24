{-# OPTIONS_GHC -Wall #-}

-- | The Core→Core passes, and which of them run.
--
-- @docs/core.md@ C11 puts the passes in Haskell through M1b. M1a's pipeline
-- had none of them; since D169 they all run (four since D442) unless @GENG_CORE_PASSES@ says
-- otherwise ('Core.Dump.corePasses'):
--
-- > GENG_CORE_PASSES=none          -- none of them
-- > GENG_CORE_PASSES=case          -- decision trees (C4, "Core.Pass.Case")
-- > GENG_CORE_PASSES=case,tailcall -- and self tail calls ("Core.Pass.TailCall")
-- > GENG_CORE_PASSES=specialize    -- witness erasure ("Core.Pass.Specialize")
-- > GENG_CORE_PASSES=inline        -- small functions inlined ("Core.Pass.Inline")
--
-- A switch rather than a mode, for the reason C4 gives: the pass is optional,
-- its output is still Core, and a program has to answer the same either way.
-- The differential harness runs the corpus through both — @geng-hs@, the
-- default, and @geng-hs-nopasses@ — which is what makes that a test rather
-- than a claim.
--
-- __Order__: tail calls first, then decision trees. The tail-call pass looks for
-- self calls in tail position, and a case that has not been compiled yet has its
-- branch bodies exactly where the reader wrote them; running it second would
-- mean looking for the same calls through the joins and cases the other pass
-- introduced. Both orders find the same calls — 'Core.Pass.TailCall' walks
-- 'Core.AST.EJoin' too — and this one is easier to reason about.
--
-- __Inlining runs between them__ (D442): after specialization, whose copies
-- are the monomorphic chains it collapses, and before the per-module passes,
-- which then see plain cases of primitives rather than calls. It is the second
-- whole-program pass, because what it copies is another module's body.
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
import Core.Pass.Inline qualified as Inline
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
      inlined = pass "inline" Inline.run specialized
      tbl = Case.table (Map.elems inlined)
   in Map.map (pass "case" (Case.run tbl) . pass "tailcall" TailCall.run) inlined
