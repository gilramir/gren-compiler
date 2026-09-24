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
      length allPrims `shouldBe` 185

    it "appends D206's and D210's primitives after every code that existed" $
      -- A code is an index into `allPrims`, so a primitive added in its
      -- group's place would renumber every later one (m1b-str-prim.md §Z9).
      ( primCode DebugLog,
        primCode (StrOp SEnd),
        primCode (ConvOp F64FromDecimal),
        primCode (StrOp SIndexOf)
      )
        `shouldBe` (157, 158, 165, 117)

    it "appends D345's primitive after every code that existed" $
      -- `i32_clz` is the last code, and `i64_add` is where it would have gone
      -- had the int group's comprehension taken it (m1b-extern.md §H18.7).
      (primCode (IntOp I32 IClz), primCode (IntOp I64 IAdd), primName (IntOp I32 IClz))
        `shouldBe` (170, 15, "i32_clz")

    it "appends D348's primitives after every code that existed" $
      -- The eight conversions of D342's narrow types, widenings then wraps,
      -- after `i32_clz` (m1b-narrow-int.md §NI3).
      ( primCode (ConvOp I8ToI32),
        primCode (ConvOp I32ToU16),
        primName (ConvOp I32ToI8),
        primCode (IntOp I32 IClz)
      )
        `shouldBe` (171, 178, "i32_to_i8", 170)

    it "appends D391's primitives after every code that existed" $
      -- A double's two words and the double two words make, after D348's
      -- wraps (m2-fdlibm.md §FD9). `f64_from_words` is the one conversion
      -- with two arguments.
      ( primCode (ConvOp F64HighWord),
        primCode (ConvOp F64FromWords),
        primName (ConvOp F64LowWord),
        primArity (ConvOp F64FromWords),
        primCode (ConvOp I32ToU16)
      )
        `shouldBe` (179, 181, "f64_low_word", 2, 178)

    it "appends D398's primitive after every code that existed" $
      -- `Task.parallel` (D373), after D391's words (m2-beam.md §BM29), and
      -- the task group's own appended run did not move.
      ( primCode (TaskOp TaskParallel),
        primName (TaskOp TaskParallel),
        primArity (TaskOp TaskParallel),
        primCode (TaskOp TaskKill),
        primCode (ConvOp F64FromWords)
      )
        `shouldBe` (182, "task_parallel", 1, 169, 181)

    it "appends D449's two primitives after every code that existed" $
      -- A Geng process's context (m2-beam-toptier.md §TT21), after
      -- `task_parallel`, which did not move.
      ( map (primCode . TaskOp) [TaskContext, TaskWithContext],
        map (primName . TaskOp) [TaskContext, TaskWithContext],
        map (primArity . TaskOp) [TaskContext, TaskWithContext],
        primCode (TaskOp TaskParallel)
      )
        `shouldBe` ([183, 184], ["task_context", "task_with_context"], [0, 2], 182)

    it "appends D233's primitive after every code that existed" $
      -- The four D233 retires keep their codes, so nothing after them moved
      -- either (m1b-bytes-prim.md §BY12).
      ( primCode (BytesOp BtSetBytes),
        primCode (BytesOp BAppend),
        primCode (BytesOp BtToBytes),
        primCode (ArrOp ALength)
      )
        `shouldBe` (166, 124, 131, 132)

    it "appends D282's and D283's primitives after every code that existed" $
      -- `task_race`'s arity changed and `task_finally` retired, and both kept
      -- their codes (m1b-source.md §SO22.9).
      ( primCode (TaskOp TaskMap2),
        primCode (TaskOp TaskSpawn),
        primCode (TaskOp TaskKill),
        primCode (TaskOp SourceClose),
        primCode (BytesOp BtSetBytes)
      )
        `shouldBe` (167, 168, 169, 156, 166)

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

    it "gives every primitive but source_new and task_context an arity of at least one" $
      -- @source_new@ takes nothing (D252): @Source.new@ is a @Task@, and a
      -- @Task@ is a description that allocates nothing until it is run, so a
      -- unit argument would buy no delay the type does not already give.
      -- @task_context@ is the same case (D449). Everything that eta-expands a
      -- primitive used as a value has to cope with an empty argument list
      -- because of them ('Core.Lower.Expression.primValue').
      filter (\p -> primArity p < 1) allPrims `shouldBe` [TaskOp SourceNew, TaskOp TaskContext]

  describe "the wire codes" $
    it "keeps the first primitive at zero" $
      -- 'allPrims' is append-only: a primitive's code is its index, so
      -- inserting one in the middle silently reinterprets every serialized
      -- module written before the change.
      primCode (IntOp I32 IAdd) `shouldBe` 0

duplicates :: (Ord a) => [a] -> [a]
duplicates xs = map head (filter ((> 1) . length) (List.group (List.sort xs)))
