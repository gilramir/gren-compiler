{-# OPTIONS_GHC -Wall #-}

-- | A @let@ nested in a @let@'s right-hand side, or in a @case@'s scrutinee, is
-- floated out to sit before it (@docs/pre-m3-js.md@ §JS2, D483):
--
-- > let a = (let b = e in c) in d     ⟹     let b = e in let a = c in d
-- > case (let b = e in c) of …        ⟹     let b = e in case c of …
--
-- The inliner is what makes the shape. It binds every argument of an inlined
-- call that is not already a value to a @$nK@ @let@ where the call was, so a
-- call used as a value leaves its arguments' bindings inside that value. A
-- backend with @let@ expressions — the BEAM's @begin … end@ — pays nothing for
-- it. JavaScript has none, and a @let@ in expression position is an
-- immediately-invoked function: 7,988 of them in the compiler's front end,
-- against 621 without the inliner, and @geng fmt@ 17% slower for it. C has none
-- either, so @Low@ would meet the same nesting at M3.
--
-- __It is sound__ because it changes no evaluation and no binding:
--
--   * Core's @let@ is strict and sequential (a later binding sees an earlier
--     one), so @e@ is evaluated before @c@, and @c@ before @d@, as they were;
--     and a scrutinee is evaluated before any branch.
--   * A binder is floated only if it is bound __once__ in its whole top-level
--     definition. Then no other scope refers to that name, so widening its
--     scope to the rest of the outer @let@ captures nothing, and no floated
--     binding can shadow another. The inliner's @$nK@ names are unique per
--     definition by construction; a name the source repeats in sibling scopes
--     stays where it is.
--   * A recursive group floats as a group, under the same rule.
--
-- It runs after "Core.Pass.Inline", which makes the shape, and before
-- "Core.Pass.Mutual", "Core.Pass.Case" and "Core.Pass.TailCall", which then see
-- one flat run of bindings.
module Core.Pass.Float
  ( run,
  )
where

import Core.AST qualified as Core
import Core.Pass.Specialize qualified as Specialize
import Data.Functor.Identity (Identity (..))
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name (Name)

run :: Core.Module -> Core.Module
run m =
  m {Core._moduleDefs = map topLevel (Core._moduleDefs m)}

topLevel :: Core.Bind -> Core.Bind
topLevel (Core.Bind binder value) =
  let counts = bound value
      once name = Map.lookup name counts == Just (1 :: Int)
   in Core.Bind binder (float once value)

-- | Bottom up, so an inner @let@ is already flat when the one around it is
-- looked at.
float :: (Name -> Bool) -> Core.Expr -> Core.Expr
float once e =
  let e' = runIdentity (Specialize.childrenA (Identity . float once) e)
   in case Core._exprValue e' of
        Core.ELet binds body ->
          rebuild e' (concatMap (flatBind once) binds) body
        Core.ECase scrut alts fallback ->
          case peel once scrut of
            ([], _) -> e'
            (segments, inner) -> rebuild e' segments (e' {Core._exprValue = Core.ECase inner alts fallback})
        _ -> e'

-- | One run of a @let@: plain bindings, or a recursive group.
data Segment
  = Plain Core.Bind
  | Group [Core.Bind]

-- | The segments one binding becomes: its right-hand side's own bindings,
-- then the binding itself of what is left.
flatBind :: (Name -> Bool) -> Core.Bind -> [Segment]
flatBind once (Core.Bind x v) =
  let (segments, inner) = peel once v
   in segments ++ [Plain (Core.Bind x inner)]

-- | The @let@s around an expression that may move, outermost first, and what
-- they were around.
peel :: (Name -> Bool) -> Core.Expr -> ([Segment], Core.Expr)
peel once v =
  case Core._exprValue v of
    Core.ELet inner body
      | all (once . name) inner ->
          let (rest, core) = peel once body in (map Plain inner ++ rest, core)
    Core.ELetRec inner body
      | all (once . name) inner ->
          let (rest, core) = peel once body in (Group inner : rest, core)
    _ -> ([], v)
  where
    name = Core._binderName . Core._bindBinder

-- | Nested @let@s from segments: a run of plain bindings is one 'Core.ELet', a
-- group is one 'Core.ELetRec', each around the rest, all of the outer
-- @let@'s type and span.
rebuild :: Core.Expr -> [Segment] -> Core.Expr -> Core.Expr
rebuild outer segments body =
  case segments of
    [] -> body
    Group group : rest -> wrap (Core.ELetRec group (rebuild outer rest body))
    _ ->
      let (plains, rest) = span isPlain segments
       in wrap (Core.ELet [b | Plain b <- plains] (rebuild outer rest body))
  where
    wrap v = Core.Expr v (Core.typeOf outer) (Core.spanOf outer)
    isPlain s = case s of Plain _ -> True; Group _ -> False

-- | How many times each local name is bound in a definition.
bound :: Core.Expr -> Map Name Int
bound e =
  let here = Map.fromListWith (+) [(Core._binderName b, 1) | b <- binders (Core._exprValue e)]
   in Map.unionWith (+) here (Specialize.children_ bound e)

binders :: Core.Expr_ -> [Core.Binder]
binders v =
  case v of
    Core.ELam bs _ -> bs
    Core.EWitLam bs _ -> bs
    Core.ELet bs _ -> map Core._bindBinder bs
    Core.ELetRec bs _ -> map Core._bindBinder bs
    Core.EJoin bs _ -> map Core._bindBinder bs
    Core.ECase _ alts _ -> concatMap (patternBinders . Core._altPattern) alts
    _ -> []

patternBinders :: Core.Pattern -> [Core.Binder]
patternBinders p =
  case p of
    Core.PVar b -> [b]
    Core.PAs b inner -> b : patternBinders inner
    Core.PCtor _ _ subs -> concatMap patternBinders subs
    Core.PRecord fields -> concatMap (patternBinders . snd) fields
    Core.PArray items tail_ -> concatMap patternBinders items ++ Maybe.maybeToList tail_
    Core.PWild -> []
    Core.PLit _ -> []
