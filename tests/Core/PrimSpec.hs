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
      -- someone noticing. 217 since Dnene27's bytes_span_within, code 216
      -- (geng-lang m3-bytes-access.md §BA19).
      length allPrims `shouldBe` 217

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

    it "appends D477's task_map after every code that existed" $
      -- Task.map as a node of its own (m2-beam-toptier.md §TT46), after
      -- `task_with_context`, which did not move.
      (primCode (TaskOp TaskMap), primName (TaskOp TaskMap), primArity (TaskOp TaskMap), primCode (TaskOp TaskWithContext))
        `shouldBe` (185, "task_map", 2, 184)

    it "appends D582's dict_ primitives after every code that existed" $
      -- D579's Dict transient (geng-lang m3-fold.md §FL10), after `task_map`,
      -- which did not move.
      ( map (\p -> (primCode (DictOp p), primName (DictOp p), primArity (DictOp p))) [minBound .. maxBound],
        primCode (TaskOp TaskMap)
      )
        `shouldBe` ([(186, "dict_owner", 1), (187, "dict_node", 6), (188, "dict_edit", 5), (189, "dict_edit_value", 3)], 185)

    it "appends D904's and D905's tr_ primitives after every code that existed" $
      -- A run, a fill, a block move and a generated push, each one handle
      -- (geng-lang m4-puritty.md §VA11), after `bt_length`, which did not
      -- move, and apart from the seven `tr_` codes, which did not either.
      ( map (\p -> (primCode (TransientOp p), primName (TransientOp p), primArity (TransientOp p))) [TrFill .. TrDrop],
        primCode (BytesOp BtLength),
        primCode (TransientOp TrToArray)
      )
        `shouldBe` ([(191, "tr_fill", 4), (192, "tr_set_array", 3), (193, "tr_copy_within", 4), (194, "tr_generate", 4), (195, "tr_slice", 3), (196, "tr_rotate", 4), (197, "tr_append_slice", 4), (198, "tr_drop", 2)], 190, 145)

    it "appends D1031's bo_ primitives after every code that existed" $
      -- `Bytes.Owned`'s seven (geng-lang m4-owned-pages.md §OP13), after
      -- D1026's `tr_drop`, which did not move.
      ( map (\p -> (primCode (BytesOp p), primName (BytesOp p), primArity (BytesOp p))) [BoFromBuilder .. BoDrop],
        primCode (TransientOp TrDrop)
      )
        `shouldBe` ([(199, "bo_from_builder", 1), (200, "bo_length", 1), (201, "bo_get_u8", 2), (202, "bo_append_to", 4), (203, "bo_take_first", 2), (204, "bo_to_bytes", 1), (205, "bo_drop", 2)], 198)

    it "appends D1052's str_join after every code that existed" $
      -- geng-lang m4-memory-proofs.md §MP11: after D1031's `bo_drop`, which
      -- did not move, and after `char_at`, the string group's last before it.
      (primCode (StrOp SJoin), primName (StrOp SJoin), primArity (StrOp SJoin), primCode (BytesOp BoDrop), primCode (StrOp SCharAt))
        `shouldBe` (206, "str_join", 2, 205, 164)

    it "appends D1056's four appends after str_join" $
      -- geng-lang m4-memory-proofs.md §MP12: only the native appends pass
      -- makes them, and `arr_remove` keeps the code it had before `ArrPrim`
      -- grew past it.
      ( [(primCode p, primName p, primArity p) | p <- [StrOp SAppendU, ArrOp AAppendU, StrOp SAppendUU, ArrOp AAppendUU]],
        primCode (StrOp SJoin),
        primCode (ArrOp ARemove)
      )
        `shouldBe` ([(207, "str_append_u", 2), (208, "arr_append_u", 2), (209, "str_append_uu", 2), (210, "arr_append_uu", 2)], 206, 138)

    it "appends D1059's two copies after the appends" $
      -- geng-lang m4-memory-proofs.md §MP16: only the native appends pass
      -- makes them, at a loop's entry.
      [(primCode p, primName p, primArity p) | p <- [StrOp SFresh, ArrOp AFresh]]
        `shouldBe` [(211, "str_fresh", 1), (212, "arr_fresh", 1)]

    it "appends D1100's emit and deliver after the copies" $
      -- geng-lang source-emit.md §SE6: Geng code pushing into a source,
      -- after D1059's `arr_fresh`, and apart from `source_close`, which did
      -- not move.
      ( [(primCode p, primName p, primArity p) | p <- [TaskOp SourceEmit, TaskOp SourceDeliver]],
        primCode (ArrOp AFresh),
        primCode (TaskOp SourceClose)
      )
        `shouldBe` ([(213, "source_emit", 2), (214, "source_deliver", 2)], 212, 156)

    it "appends Dnene5's tr_new_or_crash after emit and deliver" $
      -- geng-lang m4-refine.md §RF41: after D1100's `source_deliver`, and
      -- apart from the transient group, whose codes did not move.
      (primCode (TransientOp TrNewOrCrash), primName (TransientOp TrNewOrCrash), primArity (TransientOp TrNewOrCrash), primCode (TaskOp SourceDeliver), primCode (TransientOp TrDrop))
        `shouldBe` (215, "tr_new_or_crash", 1, 214, 198)

    it "appends Dnene27's bytes_span_within after tr_new_or_crash" $
      -- geng-lang m3-bytes-access.md §BA19: after Dnene5's 215, and apart
      -- from the bytes group, whose codes did not move.
      (primCode (BytesOp BSpanWithin), primName (BytesOp BSpanWithin), primArity (BytesOp BSpanWithin), primCode (TransientOp TrNewOrCrash), primCode (BytesOp BoDrop))
        `shouldBe` (216, "bytes_span_within", 5, 215, 205)

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
      primName (TransientOp TrCopyWithin) `shouldBe` "tr_copy_within"
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
