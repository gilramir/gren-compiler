{-# OPTIONS_GHC -Wall #-}

-- | The Core→Core passes, and which of them run.
--
-- @docs/core.md@ C11 puts the passes in Haskell through M1b. M1a's pipeline
-- had none of them; since D169 they all run (four since D442, five since D479,
-- six since D483), except @inline@ on JavaScript since D487, unless
-- @GENG_CORE_PASSES@ says otherwise ('Core.Dump.corePasses'):
--
-- > GENG_CORE_PASSES=none          -- none of them
-- > GENG_CORE_PASSES=case          -- decision trees (C4, "Core.Pass.Case")
-- > GENG_CORE_PASSES=case,tailcall -- and self tail calls ("Core.Pass.TailCall")
-- > GENG_CORE_PASSES=specialize    -- witness erasure ("Core.Pass.Specialize")
-- > GENG_CORE_PASSES=inline        -- small functions inlined ("Core.Pass.Inline")
-- > GENG_CORE_PASSES=mutual        -- local mutual tail calls, one function ("Core.Pass.Mutual")
-- > GENG_CORE_PASSES=float         -- a let in a let's right-hand side floated out ("Core.Pass.Float")
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
-- __Floating follows it__ (D483): the inliner binds an inlined call's
-- arguments with @let@s where the call was, so a call used as a value leaves a
-- @let@ in a @let@'s right-hand side, which JavaScript and C can only compile as
-- a function called on the spot. "Core.Pass.Float" moves those bindings out
-- beside the one they were inside, per module.
--
-- __Mutual tail calls are next__ (D479): a local group whose calls to one
-- another are all tail calls becomes one self-recursive function, which the
-- tail-call pass then makes a loop. It is per module, but it runs before the
-- case pass builds its constructor table, since the second form declares a
-- data type whose constructors the case pass has to know.
--
-- __Inlining is the BEAM's, not JavaScript's__ (D487, @pre-m3-js.md@ §JS12).
-- D442 was measured on the BEAM, where nothing else inlines across modules. On
-- node, after D483 took out what it left in expression position, it still cost
-- the compiler's own front end 12% on @geng fmt --check@, spread over its
-- candidates rather than in any one, and gained only on micro-benchmarks, which
-- V8 inlines anyway. So 'defaults' leaves it out for 'Target.Js'; a list named
-- in @GENG_CORE_PASSES@ still turns it on there, which is how it is measured.
-- The other targets keep it until their own measurements say otherwise.
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
    names,
  )
where

import Core.AST qualified as Core
import Core.Dump qualified as Dump
import Core.Pass.Case qualified as Case
import Core.Pass.Float qualified as Float
import Core.Pass.Inline qualified as Inline
import Core.Pass.Mutual qualified as Mutual
import Core.Pass.Specialize qualified as Specialize
import Core.Pass.TailCall qualified as TailCall
import Core.Target qualified as Target
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Gren.ModuleName qualified as ModuleName

-- | The passes that run for a target: @GENG_CORE_PASSES@'s list when it names
-- one, and 'defaults' when it does not.
names :: Target.Target -> [String]
names target =
  Maybe.fromMaybe (defaults target) Dump.corePasses

-- | Every pass, less @inline@ on JavaScript (D487).
defaults :: Target.Target -> [String]
defaults target =
  case target of
    Target.Js -> ["specialize", "float", "mutual", "case", "tailcall"]
    _ -> ["specialize", "inline", "float", "mutual", "case", "tailcall"]

run :: Target.Target -> Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
run target cores =
  let pass name f = if name `elem` names target then f else id
      specialized = pass "specialize" Specialize.run cores
      inlined = pass "inline" Inline.run specialized
      floated = pass "float" (Map.map Float.run) inlined
      grouped = pass "mutual" (Map.map Mutual.run) floated
      tbl = Case.table (Map.elems grouped)
   in Map.map (pass "case" (Case.run tbl) . pass "tailcall" TailCall.run) grouped
