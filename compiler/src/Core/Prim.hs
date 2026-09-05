{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | The primitive set. @docs/core.md@ §C13.
--
-- The rule that decides membership:
--
-- > A primitive exists for an operation on a type whose representation the
-- > backend owns — the six numeric types, @Char@, @String@, @Bytes@, @Array@
-- > and its transient — and for the @Task@ and @Source@ nodes the scheduler
-- > owns. Everything else in @core@ is Geng source.
--
-- Three things follow, and they are why this list is as short as it is:
--
--   * __Semantics live in Geng wherever they can.__ A primitive is the /raw/
--     operation — wrapping add, IEEE compare, truncating divide with a
--     non-zero divisor. A2's totalized @Eq Float@, A3's zero-divisor rule,
--     A4's shift clamping, A6's @checked*@ family, A10's saturating
--     conversions and A11's @divFloor@ are Geng source over these. One
--     implementation, and the four backends audit it rather than each
--     reimplementing it.
--   * __Preconditions are the frontend's problem.__ Some primitives have them:
--     an in-range index, a non-zero divisor, a shift count in @[0, width)@.
--     User code cannot name a primitive — only @core@ can, through @\@prim@ —
--     and @core@'s wrappers guard every one. A backend may treat a violation
--     as unreachable.
--   * __The intrinsics rule.__ A backend may replace any @core@ function that
--     is Geng source with a native implementation, provided the corpus cannot
--     tell the difference. Switched off for the Unicode-table functions of
--     @unicode.md@ U2, where the host's tables are the divergence.
--
-- The type is structured rather than a flat enumeration of 158 constructors,
-- so that a backend can dispatch on the group — which is the shape backends
-- actually take — while still getting an exhaustiveness warning when a group
-- grows.
module Core.Prim
  ( PrimOp (..),
    IntType (..),
    FloatType (..),
    IntPrim (..),
    FloatPrim (..),
    ConvPrim (..),
    StrPrim (..),
    BytesPrim (..),
    ArrPrim (..),
    TransientPrim (..),
    TaskPrim (..),

    -- * The table
    allPrims,
    primName,
    primFromName,
    primCode,
    primFromCode,

    -- * Well-formedness
    isSignedInt,
    primArity,
  )
where

import Data.Map qualified as Map
import Data.Text (Text)

-- | @i32@, @i64@, @u32@, @u64@ — the names primitives are spelled with.
data IntType = I32 | I64 | U32 | U64
  deriving (Eq, Ord, Show, Enum, Bounded)

data FloatType = F64 | F32
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Arithmetic wraps (A6); @div@ and @rem@ truncate and have a non-zero
-- divisor as a precondition; @shr@ is arithmetic and exists for signed types
-- only, because @Bits@ on @u32@\/@u64@ binds both right shifts to @Ushr@ (A11).
data IntPrim
  = IAdd
  | ISub
  | IMul
  | INeg
  | IDiv
  | IRem
  | IEq
  | ILt
  | IAnd
  | IOr
  | IXor
  | INot
  | IShl
  | -- | Arithmetic right shift. Signed types only.
    IShr
  | IUshr
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | IEEE correctly rounded, which is exactly the set IEEE 754 requires to be
-- correctly rounded — @f32@ through @fround@ (A8). @round@ is Geng over
-- @floor@; @pow@ and every transcendental are the fdlibm port (A9), because
-- V8, glibc, musl and Erlang already disagree in the last bits and a corpus
-- program computing @sin 1.0@ would otherwise diverge across backends.
--
-- @FEq@ and @FLt@ are __IEEE__: NaN is unequal and unordered. A2's lawful
-- @Eq@\/@Ord@ are Geng source over these plus @FIsNan@.
data FloatPrim
  = FAdd
  | FSub
  | FMul
  | FDiv
  | FNeg
  | FAbs
  | FSqrt
  | FFloor
  | FCeil
  | FTrunc
  | FEq
  | FLt
  | -- | Per-backend by necessity: the BEAM cannot hold a non-finite float and
    -- represents them as the sentinel atoms of A1.
    FIsNan
  | FIsInf
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Conversions. The rule is that arithmetic wraps and conversions saturate
-- (A10) — but saturation is Geng source, so these are the raw forms.
data ConvPrim
  = -- | Sign-extend.
    I32ToI64
  | -- | Zero-extend.
    U32ToI64
  | U32ToU64
  | -- | Low bits.
    I64ToI32
  | U64ToU32
  | -- | Same-width reinterpretation; the identity on native and on the BEAM.
    I32AsU32
  | U32AsI32
  | I64AsU64
  | U64AsI64
  | -- | Exact; round-to-nearest-even above 2^53.
    I32ToF64
  | I64ToF64
  | U64ToF64
  | -- | Precondition: finite and in range. A10's saturation and @NaN -> 0@ are
    -- Geng. Both widths exist so the common @Int@ case on JS is @|0@ rather
    -- than a @BigInt@ round trip.
    F64ToI32Trunc
  | F64ToI64Trunc
  | F32ToF64
  | -- | @fround@.
    F64ToF32
  | -- | A9's requirement: the fdlibm port needs to take a float apart.
    F64Bits
  | F64FromBits
  | F32Bits
  | F32FromBits
  | -- | The identity. Precondition: a scalar value, guarded by @Char.fromCode@,
    -- since surrogates are not valid @Char@ values (C8).
    CharToI32
  | I32ToChar
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | @String@ is opaque with a codepoint API (D8), so lengths and indices here
-- are codepoint lengths and indices, and @cmp@ is codepoint order.
data StrPrim
  = SLength
  | SAppend
  | -- | Precondition: @0 <= i <= j <= length@.
    SSlice
  | SEq
  | SCmp
  | -- | The only higher-order primitives, and what keeps every traversal O(n)
    -- on a UTF-8 backend rather than O(n) per index.
    SFoldl
  | SFoldr
  | SToCodepoints
  | SFromCodepoints
  | -- | Substring search from an index; @-1@ when absent, wrapped to @Maybe@ in
    -- Geng.
    SIndexOf
  | -- | D8's one encoding leak.
    SToUtf8
  | -- | Precondition: 'SUtf8Valid'.
    SFromUtf8
  | SUtf8Valid
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Multi-byte and float accessors are Geng over 'BGetU8' and the @*_from_bits@
-- conversions, with the intrinsics rule covering @DataView@.
data BytesPrim
  = BLength
  | -- | Precondition: in-range index.
    BGetU8
  | BSlice
  | BAppend
  | BEq
  | BCmp
  | BToArray
  | -- | Precondition: elements in @0..255@.
    BFromArray
  | -- | A bytes transient for @Bytes.Encode@, with the same linear-use
    -- semantics as the array transient.
    BtNew
  | BtSetU8
  | BtToBytes
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | C7's contract: @Array@ is flat and dense, @get@ and @length@ are O(1) and
-- everything that changes its shape is O(n). @pushLast@, @pushFirst@, @map@,
-- @foldl@ and the rest are Geng, intrinsics permitted; literals are 'EArray'.
--
-- Precondition throughout: in-range index.
data ArrPrim
  = ALength
  | AGet
  | ASet
  | ASlice
  | AAppend
  | AInsert
  | ARemove
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | C7's transient — a real mutable array plus a @finalized@ flag, mutating in
-- place on first use and copying on any later use of the same value. Linear
-- use is O(1) amortized, non-linear use stays correct, and nothing observable
-- is impure.
--
-- N7.1: the transient carries its owning thread, and a @push@, @set@ or
-- @to_array@ from any other thread takes the copy path. It is the only mutable
-- value in the language and therefore the only data race Geng could have.
data TransientPrim
  = TrNew
  | TrFromArray
  | TrPush
  | TrSet
  | TrGet
  | TrLength
  | TrToArray
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The reified @Task@ tree the runtime steps. @map@, @sequence@ and friends
-- are Geng over these.
data TaskPrim
  = TaskSucceed
  | TaskFail
  | TaskAndThen
  | TaskOnError
  | TaskConcurrent
  | TaskRace
  | -- | D57. Release runs on success, on failure and on cancellation; without
    -- it M3's @os@ programs leak every file handle on the failure path.
    TaskBracket
  | TaskFinally
  | -- | D71's mailbox (@ffi.md@ F4), the pull-based replacement for @Sub@.
    SourceNew
  | SourceNext
  | SourceClose
  deriving (Eq, Ord, Show, Enum, Bounded)

data PrimOp
  = IntOp !IntType !IntPrim
  | FloatOp !FloatType !FloatPrim
  | ConvOp !ConvPrim
  | StrOp !StrPrim
  | BytesOp !BytesPrim
  | ArrOp !ArrPrim
  | TransientOp !TransientPrim
  | TaskOp !TaskPrim
  | -- | The barrier. No Core→Core pass may eliminate, duplicate, hoist or
    -- reorder it against another 'DebugLog' or a @task_@ boundary (S8). Dev
    -- builds only.
    DebugLog
  deriving (Eq, Ord, Show)

-- THE TABLE

isSignedInt :: IntType -> Bool
isSignedInt I32 = True
isSignedInt I64 = True
isSignedInt U32 = False
isSignedInt U64 = False

-- | Every primitive, in the order that defines their wire codes.
--
-- __Append only.__ A primitive's code is its index here, so inserting one in
-- the middle renumbers everything after it and silently reinterprets every
-- previously serialized module. Removing one is a schema version bump.
allPrims :: [PrimOp]
allPrims =
  [ IntOp t p
  | t <- [minBound .. maxBound],
    p <- [minBound .. maxBound],
    p /= IShr || isSignedInt t
  ]
    ++ [FloatOp t p | t <- [minBound .. maxBound], p <- [minBound .. maxBound]]
    ++ map ConvOp [minBound .. maxBound]
    ++ map StrOp [minBound .. maxBound]
    ++ map BytesOp [minBound .. maxBound]
    ++ map ArrOp [minBound .. maxBound]
    ++ map TransientOp [minBound .. maxBound]
    ++ map TaskOp [minBound .. maxBound]
    ++ [DebugLog]

-- | The spelling @core@ uses in an @\@prim@ declaration: @\<type\>_\<op\>@.
primName :: PrimOp -> Text
primName op =
  case op of
    IntOp t p -> intTypeName t <> "_" <> intPrimName p
    FloatOp t p -> floatTypeName t <> "_" <> floatPrimName p
    ConvOp p -> convPrimName p
    StrOp p -> "str_" <> strPrimName p
    BytesOp p -> bytesPrimName p
    ArrOp p -> "arr_" <> arrPrimName p
    TransientOp p -> "tr_" <> transientPrimName p
    TaskOp p -> taskPrimName p
    DebugLog -> "debug_log"

intTypeName :: IntType -> Text
intTypeName I32 = "i32"
intTypeName I64 = "i64"
intTypeName U32 = "u32"
intTypeName U64 = "u64"

floatTypeName :: FloatType -> Text
floatTypeName F64 = "f64"
floatTypeName F32 = "f32"

intPrimName :: IntPrim -> Text
intPrimName p =
  case p of
    IAdd -> "add"
    ISub -> "sub"
    IMul -> "mul"
    INeg -> "neg"
    IDiv -> "div"
    IRem -> "rem"
    IEq -> "eq"
    ILt -> "lt"
    IAnd -> "and"
    IOr -> "or"
    IXor -> "xor"
    INot -> "not"
    IShl -> "shl"
    IShr -> "shr"
    IUshr -> "ushr"

floatPrimName :: FloatPrim -> Text
floatPrimName p =
  case p of
    FAdd -> "add"
    FSub -> "sub"
    FMul -> "mul"
    FDiv -> "div"
    FNeg -> "neg"
    FAbs -> "abs"
    FSqrt -> "sqrt"
    FFloor -> "floor"
    FCeil -> "ceil"
    FTrunc -> "trunc"
    FEq -> "eq"
    FLt -> "lt"
    FIsNan -> "isnan"
    FIsInf -> "isinf"

convPrimName :: ConvPrim -> Text
convPrimName p =
  case p of
    I32ToI64 -> "i32_to_i64"
    U32ToI64 -> "u32_to_i64"
    U32ToU64 -> "u32_to_u64"
    I64ToI32 -> "i64_to_i32"
    U64ToU32 -> "u64_to_u32"
    I32AsU32 -> "i32_as_u32"
    U32AsI32 -> "u32_as_i32"
    I64AsU64 -> "i64_as_u64"
    U64AsI64 -> "u64_as_i64"
    I32ToF64 -> "i32_to_f64"
    I64ToF64 -> "i64_to_f64"
    U64ToF64 -> "u64_to_f64"
    F64ToI32Trunc -> "f64_to_i32_trunc"
    F64ToI64Trunc -> "f64_to_i64_trunc"
    F32ToF64 -> "f32_to_f64"
    F64ToF32 -> "f64_to_f32"
    F64Bits -> "f64_bits"
    F64FromBits -> "f64_from_bits"
    F32Bits -> "f32_bits"
    F32FromBits -> "f32_from_bits"
    CharToI32 -> "char_to_i32"
    I32ToChar -> "i32_to_char"

strPrimName :: StrPrim -> Text
strPrimName p =
  case p of
    SLength -> "length"
    SAppend -> "append"
    SSlice -> "slice"
    SEq -> "eq"
    SCmp -> "cmp"
    SFoldl -> "foldl"
    SFoldr -> "foldr"
    SToCodepoints -> "to_codepoints"
    SFromCodepoints -> "from_codepoints"
    SIndexOf -> "index_of"
    SToUtf8 -> "to_utf8"
    SFromUtf8 -> "from_utf8"
    SUtf8Valid -> "utf8_valid"

bytesPrimName :: BytesPrim -> Text
bytesPrimName p =
  case p of
    BLength -> "bytes_length"
    BGetU8 -> "bytes_get_u8"
    BSlice -> "bytes_slice"
    BAppend -> "bytes_append"
    BEq -> "bytes_eq"
    BCmp -> "bytes_cmp"
    BToArray -> "bytes_to_array"
    BFromArray -> "bytes_from_array"
    BtNew -> "bt_new"
    BtSetU8 -> "bt_set_u8"
    BtToBytes -> "bt_to_bytes"

arrPrimName :: ArrPrim -> Text
arrPrimName p =
  case p of
    ALength -> "length"
    AGet -> "get"
    ASet -> "set"
    ASlice -> "slice"
    AAppend -> "append"
    AInsert -> "insert"
    ARemove -> "remove"

transientPrimName :: TransientPrim -> Text
transientPrimName p =
  case p of
    TrNew -> "new"
    TrFromArray -> "from_array"
    TrPush -> "push"
    TrSet -> "set"
    TrGet -> "get"
    TrLength -> "length"
    TrToArray -> "to_array"

taskPrimName :: TaskPrim -> Text
taskPrimName p =
  case p of
    TaskSucceed -> "task_succeed"
    TaskFail -> "task_fail"
    TaskAndThen -> "task_and_then"
    TaskOnError -> "task_on_error"
    TaskConcurrent -> "task_concurrent"
    TaskRace -> "task_race"
    TaskBracket -> "task_bracket"
    TaskFinally -> "task_finally"
    SourceNew -> "source_new"
    SourceNext -> "source_next"
    SourceClose -> "source_close"

nameTable :: Map.Map Text PrimOp
nameTable = Map.fromList [(primName p, p) | p <- allPrims]

-- | Look a primitive up by the name @core@ spells it with. The compiler checks
-- an @\@prim@ declaration against this table and rejects a name it does not
-- know, which is what makes @\@prim@ unlike @\@extern@: both sides are
-- compiler-known.
primFromName :: Text -> Maybe PrimOp
primFromName name = Map.lookup name nameTable

codeTable :: Map.Map PrimOp Int
codeTable = Map.fromList (zip allPrims [0 ..])

decodeTable :: Map.Map Int PrimOp
decodeTable = Map.fromList (zip [0 ..] allPrims)

-- | The wire code: the primitive's index in 'allPrims'.
primCode :: PrimOp -> Int
primCode op =
  case Map.lookup op codeTable of
    Just code -> code
    Nothing ->
      -- Unreachable: 'allPrims' is exhaustive over the type, and the only
      -- excluded combination is 'IShr' on an unsigned type, which the frontend
      -- never builds. Reaching here means 'allPrims' and 'PrimOp' disagree.
      error ("Core.Prim: no wire code for " ++ show op)

primFromCode :: Int -> Maybe PrimOp
primFromCode code = Map.lookup code decodeTable

-- | How many arguments an 'Core.AST.EPrim' node must carry. Every primitive is
-- saturated in Core, so this is a well-formedness check rather than a hint.
primArity :: PrimOp -> Int
primArity op =
  case op of
    IntOp _ p ->
      case p of
        INeg -> 1
        INot -> 1
        _ -> 2
    FloatOp _ p ->
      case p of
        FNeg -> 1
        FAbs -> 1
        FSqrt -> 1
        FFloor -> 1
        FCeil -> 1
        FTrunc -> 1
        FIsNan -> 1
        FIsInf -> 1
        _ -> 2
    ConvOp _ -> 1
    StrOp p ->
      case p of
        SLength -> 1
        SToCodepoints -> 1
        SFromCodepoints -> 1
        SToUtf8 -> 1
        SFromUtf8 -> 1
        SUtf8Valid -> 1
        SAppend -> 2
        SEq -> 2
        SCmp -> 2
        -- string, from-index
        SIndexOf -> 3
        -- string, start, end
        SSlice -> 3
        -- string, initial accumulator, step function
        SFoldl -> 3
        SFoldr -> 3
    BytesOp p ->
      case p of
        BLength -> 1
        BToArray -> 1
        BFromArray -> 1
        BtNew -> 1
        BtToBytes -> 1
        BGetU8 -> 2
        BAppend -> 2
        BEq -> 2
        BCmp -> 2
        BSlice -> 3
        BtSetU8 -> 3
    ArrOp p ->
      case p of
        ALength -> 1
        AGet -> 2
        AAppend -> 2
        ARemove -> 2
        ASet -> 3
        ASlice -> 3
        AInsert -> 3
    TransientOp p ->
      case p of
        TrNew -> 1
        TrFromArray -> 1
        TrLength -> 1
        TrToArray -> 1
        TrGet -> 2
        TrPush -> 2
        TrSet -> 3
    TaskOp p ->
      case p of
        TaskSucceed -> 1
        TaskFail -> 1
        SourceNew -> 1
        SourceNext -> 1
        SourceClose -> 1
        TaskAndThen -> 2
        TaskOnError -> 2
        TaskConcurrent -> 1
        TaskRace -> 1
        TaskBracket -> 3
        TaskFinally -> 2
    DebugLog -> 2
