{-# LANGUAGE OverloadedStrings #-}

-- | The order every list of Core bindings is in (@docs/core.md@ C14).
--
-- The rule is one sentence — dependency order, least-named ready group first,
-- a group's members by name — and a second frontend has to reproduce it from
-- that sentence alone. These are the clauses of it, one test each, plus the
-- property that makes it a specification rather than a description: the answer
-- does not depend on the order the names arrive in.
module Core.OrderSpec where

import Core.Order (groups)
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Set qualified as Set
import Test.Hspec

spec :: Spec
spec = do
  describe "dependency order" $ do
    it "puts a name after everything it uses" $
      -- Written in the opposite order on purpose.
      order ["c", "b", "a"] [("c", ["b"]), ("b", ["a"])] `shouldBe` [["a"], ["b"], ["c"]]

    it "follows dependencies across independent chains" $
      order
        ["y2", "y1", "x2", "x1"]
        [("y2", ["y1"]), ("x2", ["x1"])]
        `shouldBe` [["x1"], ["x2"], ["y1"], ["y2"]]

  describe "the tie-break" $ do
    it "takes the least name when more than one group is ready" $
      order ["zed", "abc"] [] `shouldBe` [["abc"], ["zed"]]

    it "prefers a ready name over a smaller one that is not ready yet" $
      -- `a` waits for `z`, so `z` goes first even though `a` sorts before it.
      order ["a", "z"] [("a", ["z"])] `shouldBe` [["z"], ["a"]]

    it "is not source order" $
      order ["b", "a"] [] `shouldBe` [["a"], ["b"]]

  describe "groups" $ do
    it "keeps a cycle together, with its members in name order" $
      order ["isOdd", "isEven"] [("isOdd", ["isEven"]), ("isEven", ["isOdd"])]
        `shouldBe` [["isEven", "isOdd"]]

    it "orders a group by its least name" $
      -- The group's least name is `b`, so it goes between `a` and `c`.
      order
        ["a", "c", "d", "b"]
        [("b", ["d"]), ("d", ["b"])]
        `shouldBe` [["a"], ["b", "d"], ["c"]]

    it "makes a self-referring name a group of one" $
      order ["loop"] [("loop", ["loop"])] `shouldBe` [["loop"]]

  describe "what it ignores" $ do
    it "drops edges to names it was not given" $
      -- A binding refers to imports and kernel functions too; a caller should
      -- not have to prune its reference set before asking.
      order ["a"] [("a", ["elsewhere"])] `shouldBe` [["a"]]

    it "does not depend on the order the names arrive in" $
      let deps = [("c", ["b"]), ("b", ["a"]), ("e", ["d"])]
          arrivals = List.permutations ["a", "b", "c", "d", "e"]
       in map (`order` deps) arrivals
            `shouldBe` map (const [["a"], ["b"], ["c"], ["d"], ["e"]]) arrivals

    it "returns every name exactly once" $
      concat (order ["c", "b", "a"] [("c", ["a"]), ("b", ["a"])])
        `shouldMatchList` (["a", "b", "c"] :: [String])

order :: [String] -> [(String, [String])] -> [[String]]
order names deps =
  groups names (Map.fromList [(k, Set.fromList vs) | (k, vs) <- deps])
