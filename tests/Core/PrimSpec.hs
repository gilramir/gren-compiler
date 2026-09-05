{-# LANGUAGE OverloadedStrings #-}

-- | The primitive table's invariants (@docs/core.md@ §C13).
--
-- These are cheap properties that go wrong quietly. A duplicated name means
-- two primitives answer to the same @\@prim@ declaration; a renumbered code
-- means every previously serialized Core module is reinterpreted; a missing
-- arity means a malformed 'Core.AST.EPrim' passes the well-formedness check.
module Core.PrimSpec where

import Core.Prim
import Data.List qualified as List
import Test.Hspec

spec :: Spec
spec = do
  describe "the table" $ do
    it "has the size C13 promises" $
      -- "About 150 primitives in total." The exact number is a fact about the
      -- table rather than a requirement, but it should not move without
      -- someone noticing.
      length allPrims `shouldBe` 158

    it "gives every primitive a distinct name" $
      duplicates (map primName allPrims) `shouldBe` []

    it "gives every primitive a distinct code" $
      duplicates (map primCode allPrims) `shouldBe` []

    it "numbers codes contiguously from zero" $
      map primCode allPrims `shouldBe` [0 .. length allPrims - 1]

    it "round-trips every primitive through its name" $
      map (primFromName . primName) allPrims `shouldBe` map Just allPrims

    it "round-trips every primitive through its code" $
      map (primFromCode . primCode) allPrims `shouldBe` map Just allPrims

    it "rejects a name it does not know" $
      primFromName "i32_frobnicate" `shouldBe` Nothing

  describe "shapes" $ do
    it "names primitives as <type>_<op>" $ do
      primName (IntOp I32 IAdd) `shouldBe` "i32_add"
      primName (IntOp U64 IUshr) `shouldBe` "u64_ushr"
      primName (FloatOp F32 FSqrt) `shouldBe` "f32_sqrt"
      primName (ArrOp AGet) `shouldBe` "arr_get"
      primName (TransientOp TrToArray) `shouldBe` "tr_to_array"
      primName (StrOp SFromCodepoints) `shouldBe` "str_from_codepoints"
      primName (BytesOp BGetU8) `shouldBe` "bytes_get_u8"
      primName (TaskOp TaskAndThen) `shouldBe` "task_and_then"
      primName DebugLog `shouldBe` "debug_log"

    it "provides an arithmetic right shift for signed types only" $ do
      -- A11: on `u32` and `u64` the arithmetic and logical shifts coincide, so
      -- `Bits` binds both to `ushr` rather than carrying a second name that
      -- means the same thing.
      primFromName "i32_shr" `shouldBe` Just (IntOp I32 IShr)
      primFromName "i64_shr" `shouldBe` Just (IntOp I64 IShr)
      primFromName "u32_shr" `shouldBe` Nothing
      primFromName "u64_shr" `shouldBe` Nothing

    it "provides every other integer operation for all four types" $
      let ops = ["add", "sub", "mul", "neg", "div", "rem", "eq", "lt", "and", "or", "xor", "not", "shl", "ushr"]
          names = [t <> "_" <> op | t <- ["i32", "i64", "u32", "u64"], op <- ops]
       in filter (\n -> primFromName n == Nothing) names `shouldBe` []

    it "gives every primitive an arity of at least one" $
      filter (\p -> primArity p < 1) allPrims `shouldBe` []

  describe "the wire codes" $
    it "keeps the first primitive at zero" $
      -- 'allPrims' is append-only: a primitive's code is its index, so
      -- inserting one in the middle silently reinterprets every serialized
      -- module written before the change.
      primCode (IntOp I32 IAdd) `shouldBe` 0

duplicates :: (Ord a) => [a] -> [a]
duplicates xs = map head (filter ((> 1) . length) (List.group (List.sort xs)))
