{-# OPTIONS_GHC -Wall #-}

-- | The Core→Core passes, and which of them run.
--
-- @docs/core.md@ C11 puts the passes in Haskell through M1b. M1a's pipeline
-- had none of them; since D169 they all run (four since D442, five since D479,
-- six since D483), except @inline@ on JavaScript since D487, which runs
-- @inlinematch@ in its place since D792, unless @GENG_CORE_PASSES@ says
-- otherwise ('Core.Dump.corePasses'):
--
-- > GENG_CORE_PASSES=none          -- none of them
-- > GENG_CORE_PASSES=case          -- decision trees (C4, "Core.Pass.Case")
-- > GENG_CORE_PASSES=case,tailcall -- and self tail calls ("Core.Pass.TailCall")
-- > GENG_CORE_PASSES=specialize    -- witness erasure ("Core.Pass.Specialize")
-- > GENG_CORE_PASSES=inline        -- small functions inlined ("Core.Pass.Inline")
-- > GENG_CORE_PASSES=inlinematch   -- only where a case matches them, and @prim wrappers (JavaScript's, D792)
-- > GENG_CORE_PASSES=mutual        -- local mutual tail calls, one function ("Core.Pass.Mutual")
-- > GENG_CORE_PASSES=float         -- a let in a let's right-hand side floated out ("Core.Pass.Float")
-- > GENG_CORE_PASSES=mono          -- every type variable copied away by shape ("Core.Pass.Mono")
-- > GENG_CORE_PASSES=foldspec      -- a fold copied for the function it is handed ("Core.Pass.FoldSpec")
-- > GENG_CORE_PASSES=transient     -- a Dict a loop threads updated in place ("Core.Pass.Transient")
-- > GENG_CORE_PASSES=arraytr       -- an Array a loop only appends to, grown through the transient ("Core.Pass.ArrayTransient")
-- > GENG_CORE_PASSES=arraypop      -- the same, for a loop that pops and pushes back alone (D699)
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
-- __JavaScript inlines narrowly instead__ (D792, geng-lang
-- @m3-js-inline.md@): @inlinematch@ is the same pass in a mode that opens a
-- call only where a @case@ matches its constructor and is then decided, and
-- @core@'s one-primitive wrappers anywhere. It takes the @Just@ a
-- @Bytes.get@ loop built on every byte (§BA4) and @fib@'s comparison chain,
-- and with the backend's statements for a @let@'s block (D793) the byte loops
-- are 3× faster, the stage read 15% and @geng fmt@ 2%. With both named, the
-- full pass runs first and the narrow one finds nothing left.
--
-- __Monomorphization is native's__ (D491, @m3-native.md@ §NA19). It is in
-- 'defaults' for 'Target.Native' alone, since JavaScript and the BEAM have a
-- uniform representation and would only pay for its copies; a list naming it
-- runs it anywhere, which is how the corpus holds it on node (@run.py@'s
-- @geng-hs-mono@). It runs straight after specialization, whose copies are the
-- per-type ones it relies on (D492), and before inlining, so that what the
-- inliner copies is already monomorphic.
--
-- __A fold is copied for its function next__ (D579, geng-lang @m3-fold.md@):
-- after specialization, so that what it copies passes no witness, and before
-- monomorphization, which copies the copy by shape like any other definition.
-- It is in every target's 'defaults': alone it saves nothing measurable
-- (§FL5), and what it is for is the loop it leaves, a fold's accumulator a
-- loop's parameter.
--
-- __The @Dict@ transient follows it__ (D579, D582): a loop that threads a
-- @Dict@ and keeps no old version of it calls @core@'s twins of @set@ and
-- the rest, which write the nodes the loop made. It reads the fold pass's
-- copies and names the twins by the specializer's, and it runs where
-- something is written in place: natively and on JavaScript, not on the BEAM
-- (D518).
--
-- __The @Array@ transient follows that__ (D697, geng-lang @m3-pushlast.md@
-- §PL16): a loop that only appends to an @Array@, or to a record's @Array@
-- field, threads C7's transient in its place. It was the BEAM's alone (D703),
-- until the BEAM's @Array@ grew as a persistent tree past a short tuple
-- (D715), which makes every loop it took linear without it; it is in no
-- target's defaults now (D716), and @GENG_CORE_PASSES@ still runs it.
-- Natively and on JavaScript an @Array@ is a slice, on which a push already
-- writes in place, and @arraypop@ runs (D699, D713): the same pass, taking
-- only a loop that pops the last element and pushes back, which a slice
-- leaves quadratic (D708).
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
import Core.Pass.ArrayTransient qualified as ArrayTransient
import Core.Pass.Case qualified as Case
import Core.Pass.Float qualified as Float
import Core.Pass.FoldSpec qualified as FoldSpec
import Core.Pass.Inline qualified as Inline
import Core.Pass.Mono qualified as Mono
import Core.Pass.Mutual qualified as Mutual
import Core.Pass.Specialize qualified as Specialize
import Core.Pass.TailCall qualified as TailCall
import Core.Pass.Transient qualified as Transient
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

-- | Every pass, less @inline@ on JavaScript (D487), which runs @inlinematch@
-- in its place (D792), @mono@ only on native (D491), and @arraypop@ natively
-- and on JavaScript (D713). @arraytr@ is in no target's defaults: the BEAM's
-- Array grows as a tree (D715, D716).
defaults :: Target.Target -> [String]
defaults target =
  case target of
    Target.Js -> ["specialize", "foldspec", "transient", "arraypop", "inlinematch", "float", "mutual", "case", "tailcall"]
    Target.Native -> ["specialize", "foldspec", "transient", "arraypop", "mono", "inline", "float", "mutual", "case", "tailcall"]
    _ -> ["specialize", "foldspec", "inline", "float", "mutual", "case", "tailcall"]

run :: Target.Target -> Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
run target cores =
  let pass name f = if name `elem` names target then f else id
      specialized = pass "specialize" Specialize.run cores
      folded = pass "foldspec" FoldSpec.run specialized
      transient = pass "transient" Transient.run folded
      arrays = pass "arraypop" (ArrayTransient.run True) (pass "arraytr" (ArrayTransient.run False) transient)
      monomorphized = pass "mono" (Mono.run (Target.language target) Dump.externBodies) arrays
      inlined = pass "inlinematch" (Inline.runWith Inline.Matched) (pass "inline" Inline.run monomorphized)
      floated = pass "float" (Map.map Float.run) inlined
      grouped = pass "mutual" (Map.map Mutual.run) floated
      tbl = Case.table (Map.elems grouped)
   in Map.map (pass "case" (Case.run tbl) . pass "tailcall" TailCall.run) grouped
