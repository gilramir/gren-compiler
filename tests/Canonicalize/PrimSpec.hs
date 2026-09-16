{-# LANGUAGE OverloadedStrings #-}

module Canonicalize.PrimSpec where

import AST.Canonical qualified as Can
import Canonicalize.Prim qualified as Prim
import Core.Prim qualified as Core
import Data.Map qualified as Map
import Data.Name qualified as Name
import Data.Text (Text)
import Data.Text qualified as Text
import Gren.ModuleName qualified as ModuleName
import Test.Hspec

-- | The type table a @\@prim@ declaration is checked against (`core.md` C13).
--
-- The check itself is unification -- the node is inferred against the
-- annotation this table gives it, so a declaration that disagrees is reported
-- as an ordinary type mismatch at the @\@prim@ line -- which leaves this table
-- as the thing worth testing on its own: what it says, and where it
-- deliberately says nothing.
--
-- The corpus cannot ask any of this. @\@prim@ is refused outside `gren/core`
-- and every corpus case is third-party (`classes.md` §8.3 keeps them that way),
-- so `reject/prim-outside-core` is the only case that can contain one.
spec :: Spec
spec = do
  describe "The primitive type table" $ do
    it "an integer operation is its width twice over" $
      typeOf "i32_add" `shouldBe` Just (fn [tInt, tInt] tInt)

    it "a comparison returns Bool" $
      typeOf "i32_lt" `shouldBe` Just (fn [tInt, tInt] tBool)

    it "a negation takes one argument" $
      typeOf "i32_neg" `shouldBe` Just (fn [tInt] tInt)

    it "a shift count is an Int at every width" $
      typeOf "u64_shl" `shouldBe` Just (fn [tUInt64, tInt] tUInt64)

    it "`shr` does not exist on an unsigned width, so neither does its type" $
      -- A11: `Bits` on `u32`/`u64` binds both right shifts to `ushr`, so
      -- `Core.Prim.allPrims` never builds this one and the name is unknown.
      answer "u32_shr" `shouldBe` Unknown

    it "a float operation is its width" $
      typeOf "f64_sqrt" `shouldBe` Just (fn [tFloat] tFloat)

    it "`isnan` returns Bool" $
      typeOf "f64_isnan" `shouldBe` Just (fn [tFloat] tBool)

    it "a conversion reads its two widths off its name" $
      typeOf "f64_to_i32_trunc" `shouldBe` Just (fn [tFloat] tInt)

    it "`f64_bits` is unsigned, which is the width Ryu's reference uses" $
      typeOf "f64_bits" `shouldBe` Just (fn [tFloat] tUInt64)

    it "a Char conversion names the Char module's type" $
      typeOf "char_to_i32" `shouldBe` Just (fn [tChar] tInt)

    it "a width that is not a Gren type yet still has an entry" $
      -- Which costs nothing and states nothing false: the entry is unreachable
      -- until `Basics.Int64` exists, because a declaration cannot mention a
      -- type `core` has not declared.
      typeOf "i64_add" `shouldBe` Just (fn [tInt64, tInt64] tInt64)

    it "`arr_get` answers the element, with an in-range index as its precondition (D236)" $
      -- What the public `Array.get` does with an index out of range is Geng's
      -- (D239): a negative index from the end, a `Maybe` at either edge, and
      -- the clamping rules `accept/array-edges` pins. The primitive under it
      -- is total only in range, and its type says so by answering `a`.
      typeOf "arr_get" `shouldBe` Just (fn [tArray, tInt] a)

    it "every arr_ primitive is polymorphic in the element (D236)" $
      map typeOf ["arr_length", "arr_set", "arr_slice", "arr_append", "arr_insert", "arr_remove"]
        `shouldBe` [ Just (fn [tArray] tInt),
                     Just (fn [tArray, tInt, a] tArray),
                     Just (fn [tArray, tInt, tInt] tArray),
                     Just (fn [tArray, tArray] tArray),
                     Just (fn [tArray, tInt, a] tArray),
                     Just (fn [tArray, tInt] tArray)
                   ]

    it "a bytes transient is Bytes.Transient's type, answered back (D233)" $
      typeOf "bt_set_u8" `shouldBe` Just (fn [tTransient, tInt, tInt] tTransient)

    it "`bt_set_bytes` copies a Bytes in at an offset (D233)" $
      typeOf "bt_set_bytes" `shouldBe` Just (fn [tTransient, tInt, tBytes] tTransient)

    it "`bytes_slice` answers Bytes" $
      typeOf "bytes_slice" `shouldBe` Just (fn [tBytes, tInt, tInt] tBytes)

    it "a retired bytes primitive has no type, so core cannot name it (D233)" $
      map answer ["bytes_append", "bytes_cmp", "bytes_to_array", "bytes_from_array"]
        `shouldBe` [NoTypeYet, NoTypeYet, NoTypeYet, NoTypeYet]

    it "`str_cmp` answers an Int, and Geng makes the Order (D207)" $
      typeOf "str_cmp" `shouldBe` Just (fn [tString, tString] tInt)

    it "a string offset is an Int in the table, and core wraps it (D206)" $
      typeOf "str_find" `shouldBe` Just (fn [tString, tString, tInt] tInt)

    it "a fold is the first polymorphic entry" $
      answer "str_foldl" `shouldBe` Found

    it "a retired string primitive has no type, so core cannot name it" $
      (answer "str_index_of", answer "str_to_codepoints") `shouldBe` (NoTypeYet, NoTypeYet)

    it "`f64_from_decimal` reads a String" $
      typeOf "f64_from_decimal" `shouldBe` Just (fn [tString] tFloat)

    it "the array transient is Array.Transient's type, parameterized (D240)" $
      -- Unlike the bytes transient, which holds bytes and so needs no
      -- parameter, this one carries its element type through every operation.
      map typeOf ["tr_new", "tr_from_array", "tr_push", "tr_set", "tr_get", "tr_length", "tr_to_array"]
        `shouldBe` [ Just (fn [tInt] tTransientA),
                     Just (fn [tArray] tTransientA),
                     Just (fn [tTransientA, a] tTransientA),
                     Just (fn [tTransientA, tInt, a] tTransientA),
                     Just (fn [tTransientA, tInt] a),
                     Just (fn [tTransientA] tInt),
                     Just (fn [tTransientA] tArray)
                   ]

    it "the three source primitives are D71's mailbox (D252, D253, D254)" $
      map typeOf ["source_new", "source_next", "source_close"]
        `shouldBe` [ Just (tTask tSourceA),
                     Just (fn [tSourceA] (tTask tArray)),
                     Just (fn [tSourceA] (tTask tUnit))
                   ]

    it "`source_new` takes no argument at all, so its type is not a function (D252)" $
      -- The table's only zero-arity entry. `Source.new` is a `Task`, which is
      -- already a description that allocates nothing until it is run.
      typeOf "source_new" `shouldBe` Just (tTask tSourceA)

    it "`source_next` answers an Array and not a Maybe (D254)" $
      -- A primitive answers a sentinel and Geng builds the `Maybe`, as
      -- `arr_get` and `str_find` do -- except that here it is forced: the
      -- helper is emitted JavaScript, and a `Just` built there would name a
      -- constructor the linker had no reason to keep.
      typeOf "source_next" `shouldBe` Just (fn [tSourceA] (tTask tArray))

    it "the task primitives are `Task`'s and `Process`'s own signatures (D246, D282, D283)" $
      let t x ok = Can.TType ModuleName.taskInternal "Task" [x, ok]
          v = Can.TVar
          arr e = Can.TType ModuleName.array "Array" [e]
          never = Can.TType ModuleName.basics "Never" []
          pid = Can.TType ModuleName.process "Id" []
       in map typeOf ["task_succeed", "task_fail", "task_and_then", "task_on_error", "task_concurrent", "task_race", "task_bracket", "task_map2", "task_spawn", "task_kill"]
            `shouldBe` [ Just (fn [v "a"] (t (v "x") (v "a"))),
                         Just (fn [v "x"] (t (v "x") (v "a"))),
                         Just (fn [fn [v "a"] (t (v "x") (v "b")), t (v "x") (v "a")] (t (v "x") (v "b"))),
                         Just (fn [fn [v "x"] (t (v "y") (v "a")), t (v "x") (v "a")] (t (v "y") (v "a"))),
                         Just (fn [arr (t (v "x") (v "a"))] (t (v "x") (arr (v "a")))),
                         Just (fn [t (v "x") (v "a"), arr (t (v "x") (v "a"))] (t (v "x") (v "a"))),
                         Just (fn [t (v "x") (v "r"), fn [v "r"] (t never tUnit), fn [v "r"] (t (v "x") (v "a"))] (t (v "x") (v "a"))),
                         Just (fn [fn [v "a", v "b"] (v "c"), t (v "x") (v "a"), t (v "x") (v "b")] (t (v "x") (v "c"))),
                         Just (fn [t (v "x") (v "a")] (t (v "y") pid)),
                         Just (fn [pid] (t (v "x") tUnit))
                       ]

    it "`task_finally` is retired and has no type (D282)" $
      -- `finally` is Geng over `bracket` (D103).
      answer "task_finally" `shouldBe` NoTypeYet

    it "a transient's type is not the bytes one" $
      (typeOf "tr_new" == typeOf "bt_new") `shouldBe` False

    it "a name the compiler does not know is not a primitive" $
      answer "i32_addd" `shouldBe` Unknown

    it "a real primitive with a type is found" $
      answer "i32_add" `shouldBe` Found

    it "every primitive with a type takes as many arguments as its arity says" $
      -- The two tables are one fact written twice, which is the shape §G43.3
      -- paid for once already, and this is the check that costs nothing.
      [Core.primName op | op <- Core.allPrims, not (arityAgrees op)] `shouldBe` []

-- WHAT THE TABLE SAID

data Answer = Unknown | NoTypeYet | Found
  deriving (Eq, Show)

answer :: Text -> Answer
answer name =
  case Prim.lookup (Name.fromChars (Text.unpack name)) of
    Prim.Unknown -> Unknown
    Prim.NoTypeYet -> NoTypeYet
    Prim.Found _ _ -> Found

typeOf :: Text -> Maybe Can.Type
typeOf name = Prim.primType =<< Core.primFromName name

arityAgrees :: Core.PrimOp -> Bool
arityAgrees op =
  case Prim.primType op of
    Nothing -> True
    Just tipe -> arrows tipe == Core.primArity op

arrows :: Can.Type -> Int
arrows tipe =
  case tipe of
    Can.TLambda _ result -> 1 + arrows result
    _ -> 0

-- TYPES

fn :: [Can.Type] -> Can.Type -> Can.Type
fn args result = foldr Can.TLambda result args

tInt :: Can.Type
tInt = Can.TType ModuleName.basics "Int" []

-- | The element every `arr_` and `tr_` entry is polymorphic in.
a :: Can.Type
a = Can.TVar "a"

tArray :: Can.Type
tArray = Can.TType ModuleName.array "Array" [a]

tTransientA :: Can.Type
tTransientA = Can.TType ModuleName.arrayTransient "Transient" [a]

tSourceA :: Can.Type
tSourceA = Can.TType ModuleName.source "Source" [a]

tTask :: Can.Type -> Can.Type
tTask ok = Can.TType ModuleName.taskInternal "Task" [Can.TVar "x", ok]

tUnit :: Can.Type
tUnit = Can.TRecord Map.empty Nothing

tInt64 :: Can.Type
tInt64 = Can.TType ModuleName.basics "Int64" []

tUInt64 :: Can.Type
tUInt64 = Can.TType ModuleName.basics "UInt64" []

tFloat :: Can.Type
tFloat = Can.TType ModuleName.basics "Float" []

tBool :: Can.Type
tBool = Can.TType ModuleName.basics "Bool" []

tChar :: Can.Type
tChar = Can.TType ModuleName.char "Char" []

tString :: Can.Type
tString = Can.TType ModuleName.string "String" []

tBytes :: Can.Type
tBytes = Can.TType ModuleName.bytes "Bytes" []

tTransient :: Can.Type
tTransient = Can.TType ModuleName.bytesTransient "Transient" []
