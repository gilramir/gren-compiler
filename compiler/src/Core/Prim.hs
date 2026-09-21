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
-- The type is structured rather than a flat enumeration of 167 constructors,
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
    primVarName,
    primFromName,
    primCode,
    primFromCode,

    -- * Well-formedness
    isSignedInt,
    primArity,
  )
where

import Data.Map qualified as Map
import Data.Name qualified as Name
import Data.Text (Text)
import Data.Text qualified as Text

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
  | -- | The number of leading zero bits, the width at zero. @i32@ only, and
    -- __appended__ to 'allPrims' by D345 rather than given a code at every
    -- width, because @Bitwise.countLeadingZeros@ at @Int@ is the one caller:
    -- it was the last name in @Bitwise.js@ (@warts.md@ X21).
    IClz
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
  | -- | A decimal string to the nearest @Float@, correctly rounded (D210).
    -- Precondition: the string is one R5's grammar admits, checked in Geng by
    -- @String.toFloat@. __Appended__ to 'allPrims' after every other group, so
    -- its code follows 'DebugLog''s and nothing before it moved.
    F64FromDecimal
  | -- | D342's four narrow types (@arithmetic.md@ A12) are each stored as a
    -- canonical @i32@, sign- or zero-extended from its width, so widening one
    -- to @Int@ is the identity, as 'CharToI32' is. __Appended__ by D348
    -- (@docs/m1b-narrow-int.md@ §NI3), after every other primitive.
    I8ToI32
  | U8ToI32
  | I16ToI32
  | U16ToI32
  | -- | The low 8 or 16 bits, sign-extended for the signed two: D342's wrap,
    -- and the only thing a narrow type has that @Int@ does not.
    I32ToI8
  | I32ToU8
  | I32ToI16
  | I32ToU16
  | -- | A double's high and low 32 bits as an @Int@ each, and the double two
    -- such words make: fdlibm's @__HI@, @__LO@ and the pair written back
    -- (@arithmetic.md@ A9, D391, geng-lang @m2-fdlibm.md@ §FD3). The same bits
    -- 'F64Bits' reads, without the @UInt64@, which is a @BigInt@ on JavaScript
    -- and doubled what a word costs the port there. @f64_from_words@ is the
    -- one conversion with two arguments, the high word first. __Appended__
    -- after every other primitive.
    F64HighWord
  | F64LowWord
  | F64FromWords
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | @String@ is opaque with a codepoint API (D8). @length@ counts codepoints
-- and @cmp@ is codepoint order, but __a position inside a string is an
-- offset__, not a codepoint index (D206, @docs/m1b-str-prim.md@ §Z2, §Z3): a
-- code unit offset on JavaScript and a byte offset on a UTF-8 backend, which
-- only @core@ ever holds, and which becomes a codepoint index only through
-- 'SOffsetToIndex'. A codepoint index made every search O(n) per call on both.
--
-- The constructors from 'SEnd' on were added by D206 and are __appended__ to
-- 'allPrims' after 'DebugLog', so that no earlier wire code moved. Two of the
-- originals are retired: 'SToCodepoints' and 'SIndexOf' keep their codes and
-- have no type, so no @core@ can name them.
data StrPrim
  = SLength
  | SAppend
  | -- | Precondition: offsets on codepoint boundaries, @0 <= i <= j <= end@.
    SSlice
  | SEq
  | -- | -1, 0 or 1 (D207); Geng makes the @Order@.
    SCmp
  | -- | The only higher-order primitives: string, initial accumulator, step.
    SFoldl
  | SFoldr
  | -- | Retired by D206: @toArray@ is a fold into the transient (D163).
    SToCodepoints
  | SFromCodepoints
  | -- | Retired by D206, for 'SFind'.
    SIndexOf
  | -- | D8's one encoding leak.
    SToUtf8
  | -- | Precondition: 'SUtf8Valid'.
    SFromUtf8
  | SUtf8Valid
  | -- | The offset past the last codepoint.
    SEnd
  | -- | The first offset at or after the given one where the needle occurs on
    -- codepoint boundaries at both ends (D160), or -1.
    SFind
  | -- | The last such offset at or before the given one, or -1.
    SFindLast
  | -- | The number of codepoints before an offset. O(n) on both encodings,
    -- which is why it is only paid where a public function answers an index.
    SOffsetToIndex
  | -- | The offset of the codepoint after the one at this offset.
    -- Precondition: an offset before 'SEnd'.
    SNext
  | -- | The offset of the codepoint before the one at this offset. Added as
    -- built: @popLast@ cannot find the last codepoint without it, since an
    -- offset is a code unit on one backend and a byte on another.
    -- Precondition: an offset after 0.
    SPrev
  | -- | The codepoint at an offset. Precondition: an offset before 'SEnd'.
    SCharAt
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Every width, both byte orders and both float widths are Geng over 'BGetU8',
-- 'BtSetU8' and the @*_bits@ conversions, with no width primitive and no
-- intrinsic (D232, @docs/m1b-bytes-prim.md@ §BY5).
--
-- The group is D233's eight. 'BtSetBytes' was added by it and is __appended__
-- to 'allPrims' after every other primitive, so no earlier wire code moved.
-- Four of C13's are retired and keep their codes with no type, so no @core@
-- can name them: @flatten@ is one 'BtNew' and a 'BtSetBytes' a piece, so
-- there is no 'BAppend'; @Bytes@ has no @Ord@, so nothing calls 'BCmp';
-- @toArray@ is a Geng loop over 'BGetU8'; and nothing builds @Bytes@ from an
-- @Array Int@.
data BytesPrim
  = BLength
  | -- | Precondition: in-range index.
    BGetU8
  | -- | Precondition: @0 <= i <= j <= length@. Shares its argument's storage
    -- where the backend can.
    BSlice
  | -- | Retired by D233.
    BAppend
  | -- | Content, not identity.
    BEq
  | -- | Retired by D233.
    BCmp
  | -- | Retired by D233.
    BToArray
  | -- | Retired by D233.
    BFromArray
  | -- | A bytes transient for @Bytes.Encode@ and @Bytes.flatten@, zeroed, of
    -- the given length. Its linear use is not checked (D233).
    BtNew
  | -- | Precondition: in-range index and a value in @0..255@. Answers the
    -- transient.
    BtSetU8
  | BtToBytes
  | -- | Copies a @Bytes@ into the transient at an offset. Precondition: it
    -- fits. Added by D233: as a Geng loop over 'BtSetU8', flattening a
    -- megabyte took five times as long (@docs/m1b-bytes-prim.md@ §BY4).
    BtSetBytes
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
--
-- 'TaskMap2', 'TaskSpawn' and 'TaskKill' were added by D282 and D283
-- (@m1b-source.md@ §SO22.9) and are __appended__ in 'allPrims': @map2@'s two
-- tasks have different result types, so it cannot be Geng over 'TaskConcurrent'
-- and its one array, and @Process.spawn@ and @kill@ are the scheduler's until
-- D56's package replaces them. 'TaskFinally' is retired by D282, since @finally@
-- is Geng over @bracket@ (D103), and keeps its code with no type.
--
-- 'TaskParallel' is D373's, __appended__ after every other primitive by D398
-- (geng-lang @m2-beam.md@ §BM29): 'TaskConcurrent''s contract exactly, with
-- each child in a scheduler of its own where the backend has more than one
-- core to give it. A backend that has not is free to emit it as
-- 'TaskConcurrent', and JavaScript does.
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
  | TaskMap2
  | TaskSpawn
  | TaskKill
  | TaskParallel
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
    p <- [minBound .. IUshr],
    p /= IShr || isSignedInt t
  ]
    ++ [FloatOp t p | t <- [minBound .. maxBound], p <- [minBound .. maxBound]]
    ++ map ConvOp [minBound .. I32ToChar]
    ++ map StrOp [minBound .. SUtf8Valid]
    ++ map BytesOp [minBound .. BtToBytes]
    ++ map ArrOp [minBound .. maxBound]
    ++ map TransientOp [minBound .. maxBound]
    ++ map TaskOp [minBound .. SourceClose]
    ++ [DebugLog]
    -- Appended by D206 and D210 (m1b-str-prim.md §Z9). Everything above keeps
    -- its code.
    ++ map StrOp [SEnd .. maxBound]
    ++ [ConvOp F64FromDecimal]
    -- Appended by D233 (m1b-bytes-prim.md §BY12).
    ++ [BytesOp BtSetBytes]
    -- Appended by D282 and D283 (m1b-source.md §SO22.9).
    ++ map TaskOp [TaskMap2 .. TaskKill]
    -- Appended by D345 (m1b-extern.md §H18.7).
    ++ [IntOp I32 IClz]
    -- Appended by D348 (m1b-narrow-int.md §NI3).
    ++ map ConvOp [I8ToI32 .. I32ToU16]
    -- Appended by D391 (m2-fdlibm.md §FD9).
    ++ map ConvOp [F64HighWord .. maxBound]
    -- Appended by D398 (m2-beam.md §BM29).
    ++ [TaskOp TaskParallel]

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

-- | 'primName' as a 'Name.Name', which is the form an error report and a
-- type-inference node want it in.
primVarName :: PrimOp -> Name.Name
primVarName = Name.fromChars . Text.unpack . primName

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
    IClz -> "clz"

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
    F64FromDecimal -> "f64_from_decimal"
    I8ToI32 -> "i8_to_i32"
    U8ToI32 -> "u8_to_i32"
    I16ToI32 -> "i16_to_i32"
    U16ToI32 -> "u16_to_i32"
    I32ToI8 -> "i32_to_i8"
    I32ToU8 -> "i32_to_u8"
    I32ToI16 -> "i32_to_i16"
    I32ToU16 -> "i32_to_u16"
    F64HighWord -> "f64_high_word"
    F64LowWord -> "f64_low_word"
    F64FromWords -> "f64_from_words"

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
    SEnd -> "end"
    SFind -> "find"
    SFindLast -> "find_last"
    SOffsetToIndex -> "offset_to_index"
    SNext -> "next"
    SPrev -> "prev"
    SCharAt -> "char_at"

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
    BtSetBytes -> "bt_set_bytes"

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
    TaskMap2 -> "task_map2"
    TaskSpawn -> "task_spawn"
    TaskKill -> "task_kill"
    TaskParallel -> "task_parallel"

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
        IClz -> 1
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
    ConvOp F64FromWords -> 2
    ConvOp _ -> 1
    StrOp p ->
      case p of
        SLength -> 1
        SToCodepoints -> 1
        SFromCodepoints -> 1
        SToUtf8 -> 1
        SFromUtf8 -> 1
        SUtf8Valid -> 1
        SEnd -> 1
        SAppend -> 2
        SOffsetToIndex -> 2
        SNext -> 2
        SPrev -> 2
        SCharAt -> 2
        -- string, needle, offset
        SFind -> 3
        SFindLast -> 3
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
        -- transient, offset, bytes
        BtSetBytes -> 3
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
        -- The table's only zero-argument primitive (D252). @Source.new@ is a
        -- @Task@, and a @Task@ is a description: a unit argument would buy no
        -- delay that the @Task@ does not already give, and @core@ holds one
        -- @Source.new@ value either way. Allocating is what /running/ it does.
        SourceNew -> 0
        SourceNext -> 1
        SourceClose -> 1
        TaskAndThen -> 2
        TaskOnError -> 2
        TaskConcurrent -> 1
        -- the first task, and the rest: `Task.race`'s own shape (D110, D282)
        TaskRace -> 2
        TaskBracket -> 3
        TaskFinally -> 2
        -- the function, and the two tasks
        TaskMap2 -> 3
        TaskSpawn -> 1
        TaskKill -> 1
        TaskParallel -> 1
    DebugLog -> 2
