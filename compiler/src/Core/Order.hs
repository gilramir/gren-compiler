{-# OPTIONS_GHC -Wall #-}

-- | The order every list of Core bindings is in (@docs/core.md@ C14).
--
-- > Bindings are grouped into strongly connected components and the groups are
-- > emitted in dependency order; where more than one group is ready, the one
-- > with the least name goes first, and a group's own members are in codepoint
-- > order of their names.
--
-- That sentence is the specification, and this module is the only
-- implementation of it: a module's definitions ("Core.Lower.Module"), a @let@
-- run's bindings ("Core.Lower.Expression") and a linked program's bindings
-- ("Core.Program") are all ordered by this function, so C10's second frontend
-- has one rule to reproduce rather than three.
--
-- The __grouping__ is 'Graph.stronglyConnComp'\'s, because a partition into
-- mutually recursive groups is canonical however it is computed. Only the
-- __order__ of the groups is chosen here, which is the half a library's
-- depth-first search does not specify — @docs/m1a-determinism.md@ §T2 is where
-- that distinction was found.
module Core.Order
  ( groups,
  )
where

import Data.Graph qualified as Graph
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

-- | Names in, groups in C14's order out.
--
-- @deps@ may name anything; only edges that land inside @names@ are followed,
-- so a caller can hand over a whole reference set without pruning it first. A
-- name with no entry depends on nothing.
groups :: (Ord k) => [k] -> Map k (Set k) -> [[k]]
groups names deps =
  let known = Set.fromList names
      edges k = Set.toAscList (Set.intersection known (Map.findWithDefault Set.empty k deps))

      components =
        [ List.sort component
        | component <- map Graph.flattenSCC (Graph.stronglyConnComp [(k, k, edges k) | k <- names])
        ]

      indexed = zip [0 :: Int ..] components
      byIndex = Map.fromList indexed
      groupOf = Map.fromList [(k, i) | (i, component) <- indexed, k <- component]
      groupDeps =
        Map.fromList
          [ ( i,
              Set.delete i $
                Set.fromList
                  [ j
                  | k <- component,
                    d <- edges k,
                    Just j <- [Map.lookup d groupOf]
                  ]
            )
          | (i, component) <- indexed
          ]

      -- The least name in the group is what orders it, so that "ready" is a set
      -- the smallest element can be taken from.
      key i = (minimum (byIndex Map.! i), i)

      kahn ready waiting =
        case Set.minView ready of
          Nothing -> []
          Just ((_, i), rest) ->
            let (freed, stillWaiting) = Map.partition Set.null (Map.map (Set.delete i) waiting)
             in (byIndex Map.! i) : kahn (Set.union rest (Set.fromList (map key (Map.keys freed)))) stillWaiting

      (initial, blocked) = Map.partition Set.null groupDeps
   in kahn (Set.fromList (map key (Map.keys initial))) blocked
