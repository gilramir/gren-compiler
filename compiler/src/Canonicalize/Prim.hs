{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | The type a primitive has, which is what makes @\@prim@ unlike @\@extern@.
--
-- @docs/core.md@ C13:
--
-- > unlike @\@extern@ both sides are compiler-known: the compiler checks the
-- > declared type against its own table and rejects a mismatch.
--
-- This is that table. It is /partial/, and deliberately so — see 'primType'.
module Canonicalize.Prim
  ( Lookup (..),
    lookup,
    primType,
  )
where

import AST.Canonical qualified as Can
import Core.Prim (ArrPrim (..), BytesPrim (..), ConvPrim (..), FloatPrim (..), FloatType (..), IntPrim (..), IntType (..), PrimOp (..), StrPrim (..), TaskPrim (..), TransientPrim (..))
import Core.Prim qualified as Prim
import Data.Map qualified as Map
import Data.Name qualified as Name
import Data.Text qualified as Text
import Gren.ModuleName qualified as ModuleName
import Prelude hiding (lookup)

-- | What the name in a @\@prim("...")@ turned out to be.
data Lookup
  = -- | `Core.Prim` has no primitive of this name.
    Unknown
  | -- | A real primitive, whose Gren type this table does not carry yet.
    NoTypeYet
  | Found PrimOp Can.Annotation

-- | The name @core@ wrote, answered against both tables at once.
--
-- The annotation's free variables are the type's own: the folds are the first
-- polymorphic entries (@str_foldl@'s accumulator), and none of them is
-- constrained, since a primitive never is (C13).
lookup :: Name.Name -> Lookup
lookup name =
  case Prim.primFromName (Text.pack (Name.toChars name)) of
    Nothing -> Unknown
    Just op ->
      case primType op of
        Nothing -> NoTypeYet
        Just tipe -> Found op (Can.Forall (Map.fromList [(v, []) | v <- freeVars tipe]) tipe)

freeVars :: Can.Type -> [Name.Name]
freeVars tipe =
  case tipe of
    Can.TVar v -> [v]
    Can.TLambda a b -> freeVars a ++ freeVars b
    Can.TType _ _ args -> concatMap freeVars args
    _ -> []

-- | The type @core@ must declare a primitive with, or 'Nothing' when the table
-- has no entry for it yet.
--
-- __Why the table has holes.__ Every entry here is mechanical: an integer
-- primitive's type is read off its width and its shape, a conversion's off the
-- two widths in its name. Nothing is a judgement call, so nothing here is a
-- guess. The @arr_@, @tr_@ and @task_@ groups are not
-- like that — C13's table said what @str_cmp@ /does/ and not what it returns,
-- and @Transient@ and @Source@ are types @core@ does not have yet. An entry
-- invented for one of those would be speculation compiled into the compiler
-- and checked by nothing, so those primitives have no entry and a @\@prim@
-- naming one is rejected as not available yet. Each entry lands with the Geng
-- type it names: @str_@'s landed with D206–D211 (@m1b-str-prim.md@ §Z3), and
-- @bytes_@'s and @bt_@'s with D233 (@m1b-bytes-prim.md@ §BY4).
--
-- The four widths\' /types/ were named here before they existed, which cost
-- nothing while a declaration could not mention them. They exist as of
-- @docs/m1b-int.md@ §I13, so every entry below is now reachable and @core@
-- declares a binding at nearly all of them — the exception is the four
-- @*_bits@ conversions, which are A9\'s and wait for @m1b-ryu.md@ §Y7.
primType :: PrimOp -> Maybe Can.Type
primType op =
  case op of
    IntOp t p -> Just (intType (intWidth t) p)
    FloatOp t p -> Just (floatType (floatWidth t) p)
    ConvOp p -> Just (convType p)
    StrOp p -> strType p
    BytesOp p -> bytesType p
    ArrOp p -> Just (arrType p)
    TransientOp p -> Just (transientType p)
    TaskOp p -> sourceType p
    _ -> Nothing

-- INTEGERS

-- | The shift primitives take an @Int@ count at every width, which is the type
-- a count has in @Bitwise@ and the type every backend wants: a shift by more
-- than 63 is a precondition violation, not a number a wider type would help
-- express.
intType :: Can.Type -> IntPrim -> Can.Type
intType w p =
  case p of
    IAdd -> binary w
    ISub -> binary w
    IMul -> binary w
    IDiv -> binary w
    IRem -> binary w
    IAnd -> binary w
    IOr -> binary w
    IXor -> binary w
    INeg -> unary w
    INot -> unary w
    IEq -> comparison w
    ILt -> comparison w
    IShl -> shift w
    IShr -> shift w
    IUshr -> shift w

-- FLOATS

floatType :: Can.Type -> FloatPrim -> Can.Type
floatType w p =
  case p of
    FAdd -> binary w
    FSub -> binary w
    FMul -> binary w
    FDiv -> binary w
    FNeg -> unary w
    FAbs -> unary w
    FSqrt -> unary w
    FFloor -> unary w
    FCeil -> unary w
    FTrunc -> unary w
    FEq -> comparison w
    FLt -> comparison w
    FIsNan -> Can.TLambda w tBool
    FIsInf -> Can.TLambda w tBool

-- CONVERSIONS

-- | Every conversion is one argument and one result, and the two are read off
-- the name. @f64_bits@ and @f32_bits@ are unsigned, which is the width Ryu's
-- reference implementation uses and what @docs/m1b-ryu.md@ §Y7 ports.
convType :: ConvPrim -> Can.Type
convType p =
  case p of
    I32ToI64 -> Can.TLambda tInt tInt64
    U32ToI64 -> Can.TLambda tUInt32 tInt64
    U32ToU64 -> Can.TLambda tUInt32 tUInt64
    I64ToI32 -> Can.TLambda tInt64 tInt
    U64ToU32 -> Can.TLambda tUInt64 tUInt32
    I32AsU32 -> Can.TLambda tInt tUInt32
    U32AsI32 -> Can.TLambda tUInt32 tInt
    I64AsU64 -> Can.TLambda tInt64 tUInt64
    U64AsI64 -> Can.TLambda tUInt64 tInt64
    I32ToF64 -> Can.TLambda tInt tFloat
    I64ToF64 -> Can.TLambda tInt64 tFloat
    U64ToF64 -> Can.TLambda tUInt64 tFloat
    F64ToI32Trunc -> Can.TLambda tFloat tInt
    F64ToI64Trunc -> Can.TLambda tFloat tInt64
    F32ToF64 -> Can.TLambda tFloat32 tFloat
    F64ToF32 -> Can.TLambda tFloat tFloat32
    F64Bits -> Can.TLambda tFloat tUInt64
    F64FromBits -> Can.TLambda tUInt64 tFloat
    F32Bits -> Can.TLambda tFloat32 tUInt32
    F32FromBits -> Can.TLambda tUInt32 tFloat32
    CharToI32 -> Can.TLambda tChar tInt
    I32ToChar -> Can.TLambda tInt tChar
    F64FromDecimal -> Can.TLambda tString tFloat

-- STRINGS

-- | D206's table. An offset is an @Int@ here: a primitive's JavaScript is an
-- expression and cannot build @core@'s @String.Offset@, which is a box in a
-- development build (@m1b-extern.md@ §H16.1), so @String.gren@ wraps what these
-- answer. The two retired primitives have no type, so no @core@ can name them.
strType :: StrPrim -> Maybe Can.Type
strType p =
  case p of
    SLength -> Just (fn [tString] tInt)
    SAppend -> Just (fn [tString, tString] tString)
    SSlice -> Just (fn [tString, tInt, tInt] tString)
    SEq -> Just (fn [tString, tString] tBool)
    SCmp -> Just (fn [tString, tString] tInt)
    SFoldl -> Just fold
    SFoldr -> Just fold
    SToCodepoints -> Nothing
    SFromCodepoints -> Just (fn [Can.TType ModuleName.array "Array" [tChar]] tString)
    SIndexOf -> Nothing
    SToUtf8 -> Just (fn [tString] tBytes)
    SFromUtf8 -> Just (fn [tBytes] tString)
    SUtf8Valid -> Just (fn [tBytes] tBool)
    SEnd -> Just (fn [tString] tInt)
    SFind -> Just (fn [tString, tString, tInt] tInt)
    SFindLast -> Just (fn [tString, tString, tInt] tInt)
    SOffsetToIndex -> Just (fn [tString, tInt] tInt)
    SNext -> Just (fn [tString, tInt] tInt)
    SPrev -> Just (fn [tString, tInt] tInt)
    SCharAt -> Just (fn [tString, tInt] tChar)
  where
    b = Can.TVar "b"
    fold = fn [tString, b, fn [tChar, b] b] b

-- BYTES

-- | D233's eight. The transient is @Bytes.Transient.Transient@, declared in a
-- module @core@ does not expose; the four retired primitives have no type.
bytesType :: BytesPrim -> Maybe Can.Type
bytesType p =
  case p of
    BLength -> Just (fn [tBytes] tInt)
    BGetU8 -> Just (fn [tBytes, tInt] tInt)
    BSlice -> Just (fn [tBytes, tInt, tInt] tBytes)
    BAppend -> Nothing
    BEq -> Just (fn [tBytes, tBytes] tBool)
    BCmp -> Nothing
    BToArray -> Nothing
    BFromArray -> Nothing
    BtNew -> Just (fn [tInt] tTransient)
    BtSetU8 -> Just (fn [tTransient, tInt, tInt] tTransient)
    BtToBytes -> Just (fn [tTransient] tBytes)
    BtSetBytes -> Just (fn [tTransient, tInt, tBytes] tTransient)
  where
    tTransient = Can.TType ModuleName.bytesTransient "Transient" []

-- ARRAYS

-- | D236's fourteen (@docs/m1b-arr-prim.md@ §AR2), which is C13's list with
-- nothing added and nothing retired.
--
-- Every one is polymorphic in the element, and none of them is constrained: an
-- @Array@ is flat and dense whatever it holds (C7), and a primitive never
-- carries a class (C13). The index rules are @core@\'s, not these: each of
-- these has C13\'s in-range precondition and D239 puts the negative index, the
-- clamping and the crossed bounds in Geng around them.
arrType :: ArrPrim -> Can.Type
arrType p =
  case p of
    ALength -> fn [tArray] tInt
    AGet -> fn [tArray, tInt] a
    ASet -> fn [tArray, tInt, a] tArray
    ASlice -> fn [tArray, tInt, tInt] tArray
    AAppend -> fn [tArray, tArray] tArray
    AInsert -> fn [tArray, tInt, a] tArray
    ARemove -> fn [tArray, tInt] tArray
  where
    a = Can.TVar "a"
    tArray = Can.TType ModuleName.array "Array" [a]

-- | C7\'s transient, whose type is @Array.Transient.Transient@ — a module
-- @core@ does not expose (D240), as the bytes transient\'s is. Each operation
-- answers the transient it was given, and a non-linear use copies rather than
-- corrupting what it was taken from; nothing here checks linear use.
transientType :: TransientPrim -> Can.Type
transientType p =
  case p of
    TrNew -> fn [tInt] tTransient
    TrFromArray -> fn [tArray] tTransient
    TrPush -> fn [tTransient, a] tTransient
    TrSet -> fn [tTransient, tInt, a] tTransient
    TrGet -> fn [tTransient, tInt] a
    TrLength -> fn [tTransient] tInt
    TrToArray -> fn [tTransient] tArray
  where
    a = Can.TVar "a"
    tArray = Can.TType ModuleName.array "Array" [a]
    tTransient = Can.TType ModuleName.arrayTransient "Transient" [a]

-- | D71's mailbox (@ffi.md@ F4). Only the three @source_@ primitives have a
-- type; the eight @task_@ ones beside them in 'Core.Prim.TaskPrim' wait for
-- D246, which makes @Task@ Geng over them.
--
-- @source_new@ takes no argument at all (D252), which makes it the table's only
-- zero-arity entry: @Source.new@ is a @Task@, and a @Task@ is a description
-- that allocates nothing until it is run, so a unit argument would buy no delay
-- the type does not already give. 'fn' over an empty list is the result type,
-- so nothing here is special-cased.
--
-- __@source_next@ answers an @Array@, not a @Maybe@__ (D254), empty meaning the
-- source is closed and drained. The reason is the one D239 gave for @arr_get@
-- and D206 for @str_find@: a primitive answers a sentinel and Geng builds the
-- @Maybe@ around it. Here it is forced rather than chosen — the helper that
-- would build a @Just@ is emitted JavaScript, and the constructor it named
-- would be a name the linker had no reason to keep, since a type mentioning
-- @Maybe@ creates no dependency on its constructors and a @when@ tests a tag
-- rather than calling one.
sourceType :: TaskPrim -> Maybe Can.Type
sourceType p =
  case p of
    SourceNew -> Just (fn [] (tTask (Can.TVar "x") tSource))
    SourceNext -> Just (fn [tSource] (tTask (Can.TVar "x") tArray))
    SourceClose -> Just (fn [tSource] (tTask (Can.TVar "x") tUnit))
    _ -> Nothing
  where
    a = Can.TVar "a"
    tSource = Can.TType ModuleName.source "Source" [a]
    tArray = Can.TType ModuleName.array "Array" [a]

tTask :: Can.Type -> Can.Type -> Can.Type
tTask x ok = Can.TType ModuleName.taskInternal "Task" [x, ok]

tUnit :: Can.Type
tUnit = Can.TRecord Map.empty Nothing

fn :: [Can.Type] -> Can.Type -> Can.Type
fn args result = foldr Can.TLambda result args

tString :: Can.Type
tString = Can.TType ModuleName.string "String" []

tBytes :: Can.Type
tBytes = Can.TType ModuleName.bytes "Bytes" []

-- SHAPES

binary :: Can.Type -> Can.Type
binary w = Can.TLambda w (Can.TLambda w w)

unary :: Can.Type -> Can.Type
unary w = Can.TLambda w w

comparison :: Can.Type -> Can.Type
comparison w = Can.TLambda w (Can.TLambda w tBool)

shift :: Can.Type -> Can.Type
shift w = Can.TLambda w (Can.TLambda tInt w)

-- THE WIDTHS

intWidth :: IntType -> Can.Type
intWidth t =
  case t of
    I32 -> tInt
    I64 -> tInt64
    U32 -> tUInt32
    U64 -> tUInt64

floatWidth :: FloatType -> Can.Type
floatWidth t =
  case t of
    F64 -> tFloat
    F32 -> tFloat32

tInt :: Can.Type
tInt = Can.TType ModuleName.basics "Int" []

tInt64 :: Can.Type
tInt64 = Can.TType ModuleName.basics "Int64" []

tUInt32 :: Can.Type
tUInt32 = Can.TType ModuleName.basics "UInt32" []

tUInt64 :: Can.Type
tUInt64 = Can.TType ModuleName.basics "UInt64" []

tFloat :: Can.Type
tFloat = Can.TType ModuleName.basics "Float" []

tFloat32 :: Can.Type
tFloat32 = Can.TType ModuleName.basics "Float32" []

tBool :: Can.Type
tBool = Can.TType ModuleName.basics "Bool" []

tChar :: Can.Type
tChar = Can.TType ModuleName.char "Char" []
