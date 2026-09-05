{-# LANGUAGE OverloadedStrings #-}

-- | Node identity (@docs/m1a-node-types.md@ §N4, §N7).
--
-- Core is typed at every node, and the type checker records those types
-- against node ids. The two properties that has to rest on are that ids are
-- distinct and that they do not depend on anything that varies between runs —
-- and in particular that they do not depend on regions, which are not distinct.
module Canonicalize.NodeIdSpec where

import AST.Canonical qualified as Can
import Canonicalize.NodeId qualified as NodeId
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Name qualified as Name
import Reporting.Annotation qualified as A
import Test.Hspec

spec :: Spec
spec = do
  describe "numbering" $ do
    it "gives every node a distinct id" $
      let ids = collect (NodeId.numberExpr sample)
       in length (List.nub ids) `shouldBe` length ids

    it "numbers contiguously from one" $
      -- One, not zero: 'Can.unnumbered' is zero, so a node this pass missed is
      -- distinguishable from one it numbered rather than merely wrong.
      List.sort (collect (NodeId.numberExpr sample))
        `shouldBe` map Can.NodeId [1 .. length (collect sample)]

    it "never leaves a node unnumbered" $
      filter (== Can.unnumbered) (collect (NodeId.numberExpr sample))
        `shouldBe` []

    it "is idempotent" $
      collect (NodeId.numberExpr (NodeId.numberExpr sample))
        `shouldBe` collect (NodeId.numberExpr sample)

    it "distinguishes nodes that share a region" $
      -- The reason node ids exist at all. `detectCycles` gives every nested
      -- `Let` of a `let` block the same `letRegion`, and `Parens` hands the
      -- outer region to the inner expression, so a (region, type) map would
      -- collapse nodes whose types differ.
      let nested = letChain 4 (int 0)
          ids = collect (NodeId.numberExpr nested)
          regions = collectRegions nested
       in do
            length (List.nub regions) `shouldSatisfy` (< length regions)
            length (List.nub ids) `shouldBe` length ids

    it "numbers a parent before its children" $
      case NodeId.numberExpr (arr [int 1, int 2]) of
        Can.Expr outer _ (Can.Array [Can.Expr a _ _, Can.Expr b _ _]) ->
          [outer, a, b] `shouldBe` map Can.NodeId [1, 2, 3]
        other ->
          expectationFailure ("unexpected shape: " ++ show other)

    it "numbers record fields in key order" $
      -- Field order in a record is a `Map` traversal, and C6 requires every
      -- one that can affect Core output to be ordered. Here the observable
      -- consequence is which field gets the lower id.
      let record = Can.at region (Can.Record (Map.fromList [(name "b", int 2), (name "a", int 1)]))
       in case NodeId.numberExpr record of
            Can.Expr _ _ (Can.Record fields) ->
              [i | Can.Expr i _ _ <- Map.elems fields] `shouldBe` map Can.NodeId [2, 3]
            other ->
              expectationFailure ("unexpected shape: " ++ show other)

-- A TREE

region :: A.Region
region = A.Region (A.Position 1 1) (A.Position 1 2)

name :: String -> A.Located Name.Name
name = A.At region . Name.fromChars

int :: Int -> Can.Expr
int n = Can.at region (Can.Int n)

arr :: [Can.Expr] -> Can.Expr
arr items = Can.at region (Can.Array items)

sample :: Can.Expr
sample =
  Can.at
    region
    ( Can.Call
        (arr [int 1, int 2])
        [ Can.at region (Can.Negate (int 3)),
          letChain 2 (int 4)
        ]
    )

-- | @n@ nested `Let` nodes over one body, all sharing a region — the shape
-- `detectCycles` produces for a `let` block with @n@ bindings.
letChain :: Int -> Can.Expr -> Can.Expr
letChain 0 body = body
letChain n body =
  Can.at
    region
    ( Can.Let
        (Can.Def (name "x") [] (int n))
        (letChain (n - 1) body)
    )

collect :: Can.Expr -> [Can.NodeId]
collect = map fst . walk

collectRegions :: Can.Expr -> [A.Region]
collectRegions = map snd . walk

walk :: Can.Expr -> [(Can.NodeId, A.Region)]
walk (Can.Expr nid reg value) = (nid, reg) : children value
  where
    children e =
      case e of
        Can.Array items -> concatMap walk items
        Can.Negate inner -> walk inner
        Can.Call func args -> concatMap walk (func : args)
        Can.Let d body -> defWalk d ++ walk body
        Can.LetRec ds body -> concatMap defWalk ds ++ walk body
        Can.LetDestruct _ value' body -> walk value' ++ walk body
        Can.Record fields -> concatMap walk (Map.elems fields)
        _ -> []
    defWalk d =
      case d of
        Can.Def _ _ body -> walk body
        Can.TypedDef _ _ _ body _ -> walk body
