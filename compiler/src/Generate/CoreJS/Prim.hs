{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -Wall #-}

-- | A primitive as JavaScript (@docs/core.md@ C13).
--
-- The rule this is written to is C13's first corollary: __a primitive is the
-- raw operation__. Nothing here totalizes a divisor, clamps a shift count or
-- turns a @NaN@ into a zero -- @core@'s Geng wrappers do all of that, once, and
-- the four backends audit that one implementation instead of each writing its
-- own. So @i32_div@ is @(a \/ b) | 0@ with a non-zero divisor as a
-- precondition, and a backend may treat a violation as unreachable.
--
-- __Every primitive with a type in @Canonicalize.Prim@ has its JavaScript
-- here__, and so is reachable from @core@: the numeric groups, the
-- conversions, @str_@ (D206), @bytes_@ with @bt_@ (D233), @arr_@ and @tr_@
-- (D236), and the @task_@ group with its three @source_@ ones (D252, D282,
-- D283). @task_finally@ is retired and has neither.
--
-- __The five representations__, which is the whole of what this module knows
-- that the rest of the compiler does not: an @Int@ is a number brought back
-- into range by @| 0@; a @UInt32@ a number brought back by @>>> 0@; an
-- @Int64@ a BigInt brought back by @BigInt.asIntN(64, x)@; a @UInt64@ a BigInt
-- brought back by @BigInt.asUintN(64, x)@; a @Float32@ a number rounded by
-- @Math.fround@. A @Float@ is a number and needs nothing. The rule that picks
-- each of them is the same one: the host coercion that is exactly the type's
-- wrap, applied once per operation rather than once per read.
module Generate.CoreJS.Prim
  ( prim,
    inlines,
    helpers,
    bitsHelpers,
    isFloatBits,
    bytesHelpers,
    isBytes,
    arrayHelpers,
    isArray,
    sourceHelpers,
    isSource,
    taskHelpers,
    isTask,
    exportHelpers,
    recordHelpers,
  )
where

import Core.Prim (ArrPrim (..), BytesPrim (..), ConvPrim (..), FloatPrim (..), FloatType (..), IntPrim (..), IntType (..), PrimOp (..), StrPrim (..), TaskPrim (..), TransientPrim (..))
import Core.Prim qualified as Prim
import Data.ByteString.Builder qualified as B
import Data.Name qualified as Name
import Generate.JavaScript.Builder qualified as JS
import Generate.JavaScript.Name qualified as JsName
import Text.RawString.QQ (r)

-- | Whether a saturated call to a binding whose body is this primitive may be
-- replaced by the primitive itself.
--
-- Almost all of them: 'prim' names each argument once, so substituting a call
-- site's expressions for the binding's parameters evaluates each exactly once
-- and in order, which is what the call did. Two do not. @f64_isnan@ is
-- @a !== a@ and @f64_isinf@ compares @a@ to both infinities, so inlining one
-- would evaluate its argument twice — @isNaN (f x)@ would call @f@ twice, and
-- a @|0@ coercion is not worth that. They stay ordinary calls, which is all
-- they ever were.
inlines :: PrimOp -> Bool
inlines op =
  case op of
    FloatOp _ FIsNan -> False
    FloatOp _ FIsInf -> False
    _ -> True

-- | The primitive applied to its arguments, which are always exactly as many
-- as 'Core.Prim.primArity' says: Core keeps an @EPrim@ saturated.
prim :: PrimOp -> [JS.Expr] -> JS.Expr
prim op args =
  case (op, args) of
    (IntOp I32 p, _) -> int32 p args
    (IntOp U32 p, _) -> uint32 p args
    (IntOp I64 p, _) -> bigint Signed p args
    (IntOp U64 p, _) -> bigint Unsigned p args
    (FloatOp w p, _) -> float w p args
    (ConvOp p, [a]) -> conversion p a
    (StrOp p, _) -> string p args
    (BytesOp p, _) -> bytes p args
    (ArrOp p, _) -> array p args
    (TransientOp p, _) -> transient p args
    (TaskOp p, _) -> task p args
    _ ->
      error $
        "Generate.CoreJS.Prim: no JavaScript for "
          ++ Name.toChars (Prim.primVarName op)
          ++ " yet (docs/m1b-int.md §I8)"

-- INTEGERS

-- | @Int@ is a 32-bit signed integer (D2), which on JavaScript means a double
-- that every operation coerces back into range. @| 0@ is the coercion, and
-- @int64-migration.md@ M2 measured it a third /faster/ than leaving the value
-- a double: V8 keeps a coerced value as a SMI rather than boxing it.
--
-- @&@, @|@, @^@, @~@, @\<\<@ and @\>\>@ coerce to a signed 32-bit integer
-- themselves, so they need no second @| 0@. @\>\>\>@ produces an /unsigned/
-- 32-bit value, so it does.
int32 :: IntPrim -> [JS.Expr] -> JS.Expr
int32 p args =
  case (p, args) of
    (IAdd, [a, b]) -> coerce (JS.Infix JS.OpAdd a b)
    (ISub, [a, b]) -> coerce (JS.Infix JS.OpSub a b)
    -- Not `(a * b) | 0`: a product of two 32-bit integers can exceed 2^53, and
    -- past that the double has already lost the low bits `| 0` would keep.
    (IMul, [a, b]) -> JS.Call (global "Math" "imul") [a, b]
    (INeg, [a]) -> coerce (JS.Prefix JS.PrefixNegate a)
    -- A6's wrap at the minimum falls out: `(-2147483648 / -1) | 0` is
    -- `2147483648 | 0`, which is -2147483648 again.
    (IDiv, [a, b]) -> coerce (JS.Infix JS.OpDiv a b)
    -- `%` in JavaScript truncates toward zero on integers, which is the
    -- remainder A11 wants. The coercion is for `-2147483648 % -1`, which is
    -- `-0`.
    (IRem, [a, b]) -> coerce (JS.Infix JS.OpMod a b)
    (IEq, [a, b]) -> JS.Infix JS.OpEq a b
    (ILt, [a, b]) -> JS.Infix JS.OpLt a b
    (IAnd, [a, b]) -> JS.Infix JS.OpBitwiseAnd a b
    (IOr, [a, b]) -> JS.Infix JS.OpBitwiseOr a b
    (IXor, [a, b]) -> JS.Infix JS.OpBitwiseXor a b
    (INot, [a]) -> JS.Prefix JS.PrefixComplement a
    (IShl, [a, b]) -> JS.Infix JS.OpLShift a b
    (IShr, [a, b]) -> JS.Infix JS.OpSpRShift a b
    (IUshr, [a, b]) -> coerce (JS.Infix JS.OpZfRShift a b)
    _ -> arityError (IntOp I32 p) args

-- | A @UInt32@ is a JavaScript number in @[0, 2^32)@, and @>>> 0@ is the
-- coercion that keeps it there — the same instruction @Int@ uses, read the
-- other way. @>>> 0@ is also what stock Gren reached for as a /conversion/ to
-- an unsigned reading, at a type that cannot hold one, and §I12.4 is where
-- that stopped working: an unsigned reading is a type, not a shift by zero.
--
-- The bitwise operators produce a /signed/ 32-bit value, so every one of them
-- needs the coercion, which is the mirror image of 'int32', where only @>>>@
-- did.
uint32 :: IntPrim -> [JS.Expr] -> JS.Expr
uint32 p args =
  case (p, args) of
    (IAdd, [a, b]) -> unsign (JS.Infix JS.OpAdd a b)
    (ISub, [a, b]) -> unsign (JS.Infix JS.OpSub a b)
    -- `Math.imul` gives the low 32 bits as a signed value, which is the same
    -- bit pattern; `>>> 0` reads it unsigned. `a * b` would lose the low bits
    -- above 2^53, which is `core`'s own `Random` bug (§I12.5).
    (IMul, [a, b]) -> unsign (JS.Call (global "Math" "imul") [a, b])
    (INeg, [a]) -> unsign (JS.Prefix JS.PrefixNegate a)
    -- Both operands are non-negative, so `/` then `>>> 0` truncates toward
    -- zero, which is what a truncating division of two non-negative numbers
    -- is. `%` on non-negative numbers is already in range.
    (IDiv, [a, b]) -> unsign (JS.Infix JS.OpDiv a b)
    (IRem, [a, b]) -> JS.Infix JS.OpMod a b
    (IEq, [a, b]) -> JS.Infix JS.OpEq a b
    (ILt, [a, b]) -> JS.Infix JS.OpLt a b
    (IAnd, [a, b]) -> unsign (JS.Infix JS.OpBitwiseAnd a b)
    (IOr, [a, b]) -> unsign (JS.Infix JS.OpBitwiseOr a b)
    (IXor, [a, b]) -> unsign (JS.Infix JS.OpBitwiseXor a b)
    (INot, [a]) -> unsign (JS.Prefix JS.PrefixComplement a)
    (IShl, [a, b]) -> unsign (JS.Infix JS.OpLShift a b)
    (IUshr, [a, b]) -> JS.Infix JS.OpZfRShift a b
    -- A11: the two right shifts coincide on an unsigned type, so `Bits UInt32`
    -- binds both to `u32_ushr` and `Core.Prim.allPrims` has no `u32_shr` to
    -- reach this case.
    (IShr, _) -> arityError (IntOp U32 IShr) args
    _ -> arityError (IntOp U32 p) args

-- | Which of the two 64-bit types is being generated, and so which of
-- @BigInt@'s two truncations wraps it.
data Sign = Signed | Unsigned

-- | @Int64@ and @UInt64@ are JavaScript BigInts, which is the only exact
-- 64-bit integer the host has — @int64-migration.md@ §M2 measured the cost and
-- D2 is the decision that keeps it off @Int@.
--
-- @BigInt.asIntN(64, x)@ and @BigInt.asUintN(64, x)@ are the wrap, and they are
-- applied where the operation can leave the range and nowhere else: @&@, @|@,
-- @^@, @%@ and @\>\>@ cannot, and neither can @~@ on a signed value.
bigint :: Sign -> IntPrim -> [JS.Expr] -> JS.Expr
bigint sign p args =
  let wrap = wrap64 sign
   in case (p, args) of
        (IAdd, [a, b]) -> wrap (JS.Infix JS.OpAdd a b)
        (ISub, [a, b]) -> wrap (JS.Infix JS.OpSub a b)
        (IMul, [a, b]) -> wrap (JS.Infix JS.OpMul a b)
        (INeg, [a]) -> wrap (JS.Prefix JS.PrefixNegate a)
        -- BigInt division truncates toward zero, which is what `i64_div` is.
        -- The wrap is A6's one overflowing quotient, `minValue / -1n`.
        (IDiv, [a, b]) -> wrap (JS.Infix JS.OpDiv a b)
        (IRem, [a, b]) -> JS.Infix JS.OpMod a b
        (IEq, [a, b]) -> JS.Infix JS.OpEq a b
        (ILt, [a, b]) -> JS.Infix JS.OpLt a b
        (IAnd, [a, b]) -> JS.Infix JS.OpBitwiseAnd a b
        (IOr, [a, b]) -> JS.Infix JS.OpBitwiseOr a b
        (IXor, [a, b]) -> JS.Infix JS.OpBitwiseXor a b
        -- `~x` on a BigInt is `-x - 1`, which stays in a signed 64-bit range
        -- and leaves an unsigned one.
        (INot, [a]) ->
          case sign of
            Signed -> JS.Prefix JS.PrefixComplement a
            Unsigned -> wrap (JS.Prefix JS.PrefixComplement a)
        -- A shift count is an `Int` at every width (A5), so it is a number and
        -- has to be widened: JavaScript refuses to mix a BigInt and a number in
        -- one operator.
        (IShl, [a, b]) -> wrap (JS.Infix JS.OpLShift a (toBigInt b))
        -- `>>` on a BigInt is arithmetic, so it is `i64_shr` as written and
        -- `u64_ushr` by the value being non-negative.
        (IShr, [a, b]) -> JS.Infix JS.OpSpRShift a (toBigInt b)
        (IUshr, [a, b]) ->
          case sign of
            Unsigned -> JS.Infix JS.OpSpRShift a (toBigInt b)
            -- BigInt has no `>>>`: an arbitrary-precision integer has no top
            -- bit to shift into. The unsigned reading is the conversion, and
            -- it is the same pair `i64_as_u64` and `u64_as_i64` name.
            Signed ->
              wrap
                ( JS.Infix
                    JS.OpSpRShift
                    (asUintN 64 a)
                    (toBigInt b)
                )
        _ -> arityError (IntOp (sign64 sign) p) args

sign64 :: Sign -> IntType
sign64 Signed = I64
sign64 Unsigned = U64

wrap64 :: Sign -> JS.Expr -> JS.Expr
wrap64 Signed = asIntN 64
wrap64 Unsigned = asUintN 64

-- FLOATS

-- | A @Float@ is a JavaScript number, so at @F64@ every one of these is the
-- machine operation with nothing around it. @eq@ and @lt@ are __IEEE__ (C13):
-- @NaN@ is unequal to itself and unordered, and A2's lawful @Eq@\/@Ord@ are
-- Geng source over these plus @isnan@.
--
-- A @Float32@ is a JavaScript number too, rounded to single precision after
-- every operation that can leave it — which is exactly what @Math.fround@ is,
-- and what A8 asks of the type. Five operations need the rounding and the rest
-- would be wrong to imply it: negation and absolute value touch only the sign
-- bit, @floor@, @ceil@ and @trunc@ of a single-precision value are
-- single-precision already, and the comparisons and predicates answer a
-- @Bool@.
float :: FloatType -> FloatPrim -> [JS.Expr] -> JS.Expr
float w p args =
  let narrow = case w of
        F64 -> id
        F32 -> fround
   in case (p, args) of
        (FAdd, [a, b]) -> narrow (JS.Infix JS.OpAdd a b)
        (FSub, [a, b]) -> narrow (JS.Infix JS.OpSub a b)
        (FMul, [a, b]) -> narrow (JS.Infix JS.OpMul a b)
        (FDiv, [a, b]) -> narrow (JS.Infix JS.OpDiv a b)
        (FNeg, [a]) -> JS.Prefix JS.PrefixNegate a
        (FAbs, [a]) -> JS.Call (global "Math" "abs") [a]
        (FSqrt, [a]) -> narrow (JS.Call (global "Math" "sqrt") [a])
        (FFloor, [a]) -> JS.Call (global "Math" "floor") [a]
        (FCeil, [a]) -> JS.Call (global "Math" "ceil") [a]
        (FTrunc, [a]) -> JS.Call (global "Math" "trunc") [a]
        (FEq, [a, b]) -> JS.Infix JS.OpEq a b
        (FLt, [a, b]) -> JS.Infix JS.OpLt a b
        -- `a !== a` rather than `isNaN(a)`: `isNaN` coerces its argument, and
        -- this is the idiom every JavaScript engine recognizes.
        (FIsNan, [a]) -> JS.Infix JS.OpNe a a
        (FIsInf, [a]) ->
          JS.Infix
            JS.OpOr
            (JS.Infix JS.OpEq a infinity)
            (JS.Infix JS.OpEq a (JS.Prefix JS.PrefixNegate infinity))
        _ -> arityError (FloatOp w p) args

-- CONVERSIONS

-- | A10's raw forms. Saturation, @NaN -> 0@ and every @*Checked@ sibling are
-- Geng in the four width modules; what is here is the truncation or the
-- widening itself, with the precondition C13 gives it.
--
-- The four @*_bits@ conversions are here too, and they are the one group that
-- is neither: a reinterpretation changes no value at all, which is why A9's
-- fdlibm port and §Y7's Ryu can both be written over it.
conversion :: ConvPrim -> JS.Expr -> JS.Expr
conversion p a =
  case p of
    -- INTEGER WIDENING. `BigInt(x)` is exact for any number that is an
    -- integer, which both 32-bit types are by construction.
    I32ToI64 -> toBigInt a
    U32ToI64 -> toBigInt a
    U32ToU64 -> toBigInt a
    -- INTEGER NARROWING -- the low bits, which is what A10's `*Wrap` family is
    -- written over. `Number` of a 32-bit BigInt is exact.
    I64ToI32 -> fromBigInt (asIntN 32 a)
    U64ToU32 -> fromBigInt (asUintN 32 a)
    -- SAME-WIDTH REINTERPRETATION. At 32 bits these are the two coercions
    -- themselves, read against each other; at 64 they are `BigInt`'s two
    -- truncations. None of the four changes a bit pattern.
    I32AsU32 -> unsign a
    U32AsI32 -> coerce a
    I64AsU64 -> asUintN 64 a
    U64AsI64 -> asIntN 64 a
    -- INTEGER TO FLOAT. Exact below 2^53 and round-to-nearest-even above it,
    -- which is what `Number` of a BigInt does and what A10 says these do.
    I32ToF64 -> a
    I64ToF64 -> fromBigInt a
    U64ToF64 -> fromBigInt a
    -- FLOAT TO INTEGER. Precondition: finite and in range, so these truncate
    -- rather than wrap. `BigInt` refuses a non-integer, so the `Math.trunc` is
    -- the conversion and not a tidying-up.
    F64ToI32Trunc -> coerce a
    F64ToI64Trunc -> toBigInt (JS.Call (global "Math" "trunc") [a])
    -- FLOAT WIDTHS. Widening is free -- a single-precision value is already a
    -- double -- and narrowing is the same `Math.fround` every `f32` operation
    -- ends with.
    F32ToF64 -> a
    F64ToF32 -> fround a
    -- A FLOAT'S BITS (A9, and `docs/m1b-ryu.md` §Y11). JavaScript has no
    -- operator that reads a double's bit pattern, so the conversion is two
    -- typed arrays over one buffer: the value is stored through the float view
    -- and read back through the integer one. Both views are native-endian, so
    -- the pair agrees with itself on a big-endian machine as well -- the bytes
    -- move, the bits do not.
    --
    -- The buffer is shared, in 'bitsHelpers'. It was a new buffer and two views
    -- per call, because a shared one had nowhere to live until D206 gave
    -- primitives helpers emitted once per program; that made a float read in
    -- Geng 5.7 to 6.9 times the kernel's, and 1.3 to 2.4 with the buffer shared
    -- (@docs/m1b-bytes-prim.md@ §BY3, D235). Each helper writes and reads the
    -- buffer in one call and names its argument once.
    F64Bits -> bitsCall "_Float_bits64" a
    F64FromBits -> bitsCall "_Float_fromBits64" a
    F32Bits -> bitsCall "_Float_bits32" a
    F32FromBits -> bitsCall "_Float_fromBits32" a
    -- A `Char` *is* its code point (C8, `docs/m1b-str.md` §T12), so both of
    -- these are the identity and `core`'s `Char.toCode`/`fromCode` are the
    -- primitive unchanged. They were a `codePointAt(0)` and a
    -- `String.fromCodePoint` through the kernel's `chr` box, because a `Char`
    -- was a one-character string; this is the whole of what that
    -- representation cost on this backend, and the two lines that replace it
    -- are what `Generate.LowC` already did.
    --
    -- `i32_to_char` is unchecked, and that is `core`'s to guard: `Char.fromCode`
    -- answers `Nothing` outside the two valid ranges and nothing else in `core`
    -- may reach the primitive.
    CharToI32 -> a
    I32ToChar -> a
    -- `+s` is correctly rounded, and the precondition (R5's grammar, checked
    -- by `String.toFloat`) is what keeps JavaScript's wider number syntax --
    -- hex, whitespace, `Infinity` -- from ever reaching it (D210). `Number` is `+`.
    F64FromDecimal -> JS.Call (JS.Ref (JsName.fromLocalHumanReadable "Number")) [a]

-- STRINGS

-- | D206's primitives (@docs/m1b-str-prim.md@ §Z3). A @String@ is a JavaScript
-- string and an offset is a code unit offset, so the searches and the slice
-- are the host's own. What is not a single expression is a helper in
-- 'helpers', which is emitted once in a program that reaches any of these.
-- Each helper names each argument once, so 'inlines' holds for all of them.
string :: StrPrim -> [JS.Expr] -> JS.Expr
string p args =
  case (p, args) of
    (SAppend, [a, b]) -> JS.Infix JS.OpAdd a b
    (SEq, [a, b]) -> JS.Infix JS.OpEq a b
    (SSlice, [s, i, j]) -> method s "slice" [i, j]
    (SEnd, [s]) -> JS.Access s (JsName.fromLocalHumanReadable "length")
    (SCharAt, [s, o]) -> method s "codePointAt" [o]
    (SLength, _) -> helper "_Str_length" args
    (SCmp, _) -> helper "_Str_cmp" args
    (SFoldl, _) -> helper "_Str_foldl" args
    (SFoldr, _) -> helper "_Str_foldr" args
    (SFromCodepoints, _) -> helper "_Str_fromCodepoints" args
    (SToUtf8, _) -> helper "_Str_toUtf8" args
    (SFromUtf8, _) -> helper "_Str_fromUtf8" args
    (SUtf8Valid, _) -> helper "_Str_utf8Valid" args
    (SFind, _) -> helper "_Str_find" args
    (SFindLast, _) -> helper "_Str_findLast" args
    (SOffsetToIndex, _) -> helper "_Str_offsetToIndex" args
    (SNext, _) -> helper "_Str_next" args
    (SPrev, _) -> helper "_Str_prev" args
    _ -> arityError (StrOp p) args
  where
    method obj name as = JS.Call (JS.Access obj (JsName.fromLocalHumanReadable name)) as
    helper name as = JS.Call (JS.Ref (JsName.fromLocalHumanReadable name)) as

-- | The @str_@ helpers, which 'Generate.CoreJS' emits once when a program
-- reaches a string primitive.
--
-- __Why a lone surrogate needs no case.__ D209 keeps one out of every
-- @String@, but these do not rely on it: a lone surrogate is one code unit
-- and one codepoint, so 'SNext' steps over it, and 'SOffsetToIndex' counts
-- only pairs, as §T15 already did.
helpers :: B.Builder
helpers =
  [r|
// A pair is the only thing that spends two code units on one codepoint
// (docs/m1b-str-prim.md §Z3). V8 answers this regex without reading a string
// whose every character is at or below U+00FF (m1b-str.md §T15.2).
var _Str_pair = /[\uD800-\uDBFF][\uDC00-\uDFFF]/g;
var _Str_surrogate = /[\uD800-\uDFFF]/;

function _Str_pairsBefore(s, u) {
  _Str_pair.lastIndex = 0;
  var pairs = 0, m;
  while ((m = _Str_pair.exec(s)) !== null && m.index + 2 <= u) pairs++;
  return pairs;
}
function _Str_length(s) { return s.length - _Str_pairsBefore(s, s.length); }
function _Str_offsetToIndex(s, u) { return u - _Str_pairsBefore(s, u); }

// Codepoint order (D8, m1b-str.md §T13): `<` is code unit order, and the two
// differ only where a surrogate is involved, so the regex guards the scan.
function _Str_cmp(a, b) {
  if (a === b) return 0;
  if (!_Str_surrogate.test(a) && !_Str_surrogate.test(b)) return a < b ? -1 : 1;
  var n = a.length < b.length ? a.length : b.length, i = 0;
  while (i < n && a.charCodeAt(i) === b.charCodeAt(i)) i++;
  if (i === n) return a.length < b.length ? -1 : 1;
  return a.codePointAt(i) < b.codePointAt(i) ? -1 : 1;
}

function _Str_foldl(s, acc, f) {
  for (var c of s) acc = A2(f, c.codePointAt(0), acc);
  return acc;
}
function _Str_foldr(s, acc, f) {
  var i = s.length;
  while (i > 0) {
    var u = s.charCodeAt(i - 1);
    var cp = u >= 0xDC00 && u <= 0xDFFF && i > 1 && (s.charCodeAt(i - 2) & 0xFC00) === 0xD800
      ? s.codePointAt(i - 2) : u;
    i -= cp > 0xFFFF ? 2 : 1;
    acc = A2(f, cp, acc);
  }
  return acc;
}

// Not `String.fromCodePoint(...cs)`: an argument list has a length limit.
function _Str_fromCodepoints(cs) {
  var out = "";
  for (var i = 0; i < cs.length; i++) out += String.fromCodePoint(cs[i]);
  return out;
}

function _Str_next(s, u) {
  var c = s.charCodeAt(u);
  return c >= 0xD800 && c <= 0xDBFF && u + 1 < s.length && (s.charCodeAt(u + 1) & 0xFC00) === 0xDC00 ? u + 2 : u + 1;
}

function _Str_prev(s, u) {
  var c = s.charCodeAt(u - 1);
  return c >= 0xDC00 && c <= 0xDFFF && u >= 2 && (s.charCodeAt(u - 2) & 0xFC00) === 0xD800 ? u - 2 : u - 1;
}

// D160: a match that splits a surrogate pair at either end is not a match.
function _Str_splitsPair(s, u) {
  if (u <= 0 || u >= s.length) return false;
  var lead = s.charCodeAt(u - 1);
  if (lead < 0xD800 || lead > 0xDBFF) return false;
  var trail = s.charCodeAt(u);
  return trail >= 0xDC00 && trail <= 0xDFFF;
}
function _Str_find(s, needle, from) {
  var u = s.indexOf(needle, from);
  while (u > -1 && (_Str_splitsPair(s, u) || _Str_splitsPair(s, u + needle.length))) u = s.indexOf(needle, u + 1);
  return u;
}
function _Str_findLast(s, needle, from) {
  var u = s.lastIndexOf(needle, from);
  while (u > -1 && (_Str_splitsPair(s, u) || _Str_splitsPair(s, u + needle.length))) u = u === 0 ? -1 : s.lastIndexOf(needle, u - 1);
  return u;
}

// Bytes is a DataView over its own slice of a buffer (D202).
function _Str_toUtf8(s) {
  var u8 = new TextEncoder().encode(s);
  return new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
}
function _Str_fromUtf8(b) {
  // `ignoreBOM` keeps a leading U+FEFF (m1b-protobuf.md §Q14).
  return new TextDecoder("utf-8", { ignoreBOM: true }).decode(b);
}
function _Str_utf8Valid(b) {
  try {
    new TextDecoder("utf-8", { fatal: true, ignoreBOM: true }).decode(b);
    return true;
  } catch (e) {
    return false;
  }
}
|]

-- BYTES

-- | D233's eight (@docs/m1b-bytes-prim.md@ §BY4). A @Bytes@ is a @DataView@
-- over its own slice of a buffer, as it was in the kernel (D202), and a bytes
-- transient is a @DataView@ too, which 'BtToBytes' hands over as it is. What
-- names an argument twice is a helper in 'bytesHelpers', so 'inlines' holds
-- for all of them. The retired four have no type, so no @core@ reaches them.
bytes :: BytesPrim -> [JS.Expr] -> JS.Expr
bytes p args =
  case (p, args) of
    (BLength, [b]) -> JS.Access b (JsName.fromLocalHumanReadable "byteLength")
    (BGetU8, [b, i]) -> JS.Call (JS.Access b (JsName.fromLocalHumanReadable "getUint8")) [i]
    (BSlice, _) -> helper "_BytesPrim_slice" args
    (BEq, _) -> helper "_BytesPrim_eq" args
    (BtNew, [n]) -> JS.New (ref "DataView") [JS.New (ref "ArrayBuffer") [n]]
    (BtSetU8, _) -> helper "_BytesPrim_setU8" args
    (BtToBytes, [t]) -> t
    (BtSetBytes, _) -> helper "_BytesPrim_setBytes" args
    _ -> arityError (BytesOp p) args
  where
    ref name = JS.Ref (JsName.fromLocalHumanReadable name)
    helper name as = JS.Call (ref name) as

-- | Whether a primitive is one of the @bytes_@ or @bt_@ group, whose helpers
-- 'Generate.CoreJS' emits once in a program that reaches any of them.
isBytes :: PrimOp -> Bool
isBytes op =
  case op of
    BytesOp _ -> True
    _ -> False

-- | The @bytes_@ and @bt_@ helpers. A @Bytes@ out of 'BSlice' shares its
-- parent's buffer at a non-zero @byteOffset@ (core#137), so every copy goes
-- through the views' own offsets.
--
-- Not @_Bytes_@: that is the kernel's @Bytes.js@, whose @var _Bytes_slice@
-- replaced the helper of the same name in a program holding both
-- (@docs/m1b-bytes-prim.md@ §BY12).
bytesHelpers :: B.Builder
bytesHelpers =
  [r|
// A view onto the same buffer, O(1) (docs/m1b-bytes-prim.md §BY4).
function _BytesPrim_slice(b, i, j) { return new DataView(b.buffer, b.byteOffset + i, j - i); }

// Content, not identity: two views of different buffers, or of one buffer at
// different offsets, are equal when their bytes are.
function _BytesPrim_eq(a, b) {
  var len = a.byteLength;
  if (len !== b.byteLength) return false;
  for (var i = 0; i < len; i++) {
    if (a.getUint8(i) !== b.getUint8(i)) return false;
  }
  return true;
}

function _BytesPrim_setU8(t, i, v) { t.setUint8(i, v); return t; }

function _BytesPrim_setBytes(t, i, b) {
  new Uint8Array(t.buffer, t.byteOffset + i, b.byteLength).set(new Uint8Array(b.buffer, b.byteOffset, b.byteLength));
  return t;
}
|]

-- ARRAYS

-- | D236's fourteen (@docs/m1b-arr-prim.md@ §AR2). An @Array@ is a dense JS
-- array, which is what C7's contract says on this backend and what an extern
-- sees (D192), so the seven @arr_@ primitives are the JS method of the same
-- shape and each names its argument once. Every index here is in range, and
-- every splice bound is already clamped: D239 puts those rules in Geng.
array :: ArrPrim -> [JS.Expr] -> JS.Expr
array p args =
  case (p, args) of
    (ALength, [a]) -> JS.Access a (JsName.fromLocalHumanReadable "length")
    (AGet, [a, i]) -> JS.Index a i
    (ASet, [a, i, v]) -> method a "with" [i, v]
    (ASlice, [a, i, j]) -> method a "slice" [i, j]
    (AAppend, [a, b]) -> method a "concat" [b]
    (AInsert, [a, i, v]) -> method a "toSpliced" [i, JS.Int 0, v]
    (ARemove, [a, i]) -> method a "toSpliced" [i, JS.Int 1]
    _ -> arityError (ArrOp p) args
  where
    method target name as = JS.Call (JS.Access target (JsName.fromLocalHumanReadable name)) as

-- | C7's transient. Every one is a helper: the type is the helpers' own class,
-- and @push@, @set@ and @to_array@ each read their transient more than once on
-- the path that copies.
transient :: TransientPrim -> [JS.Expr] -> JS.Expr
transient p args =
  case (p, args) of
    (TrNew, [_]) -> helper "_ArrayPrim_trNew" args
    (TrFromArray, [_]) -> helper "_ArrayPrim_trFromArray" args
    (TrPush, [_, _]) -> helper "_ArrayPrim_trPush" args
    (TrSet, [_, _, _]) -> helper "_ArrayPrim_trSet" args
    (TrGet, [_, _]) -> helper "_ArrayPrim_trGet" args
    (TrLength, [_]) -> helper "_ArrayPrim_trLength" args
    (TrToArray, [_]) -> helper "_ArrayPrim_trToArray" args
    _ -> arityError (TransientOp p) args
  where
    helper name as = JS.Call (JS.Ref (JsName.fromLocalHumanReadable name)) as

-- | The @Task@ tree (D246, @m1b-source.md@ §SO24): each primitive is a call to
-- the helper that builds its node, or starts or stops a process.
task :: TaskPrim -> [JS.Expr] -> JS.Expr
task p args =
  case (p, args) of
    (TaskSucceed, [_]) -> helper "_TaskPrim_succeed" args
    (TaskFail, [_]) -> helper "_TaskPrim_fail" args
    (TaskAndThen, [_, _]) -> helper "_TaskPrim_andThen" args
    (TaskOnError, [_, _]) -> helper "_TaskPrim_onError" args
    (TaskConcurrent, [_]) -> helper "_TaskPrim_concurrent" args
    (TaskRace, [_, _]) -> helper "_TaskPrim_race" args
    (TaskBracket, [_, _, _]) -> helper "_TaskPrim_bracket" args
    (TaskMap2, [_, _, _]) -> helper "_TaskPrim_map2" args
    (TaskSpawn, [_]) -> helper "_TaskPrim_spawn" args
    (TaskKill, [_]) -> helper "_TaskPrim_kill" args
    (TaskFinally, _) -> arityError (TaskOp p) args
    _ -> source p args
  where
    helper name as = JS.Call (JS.Ref (JsName.fromLocalHumanReadable name)) as

-- | Whether a primitive is one of the @task_@ group, the @source_@ ones
-- included, all of which are emitted over 'taskHelpers'.
isTask :: PrimOp -> Bool
isTask op =
  case op of
    TaskOp _ -> True
    _ -> False

-- | The scheduler: the node builders, the processes, cancellation, @main@ and
-- the step. It was @core@'s kernel @Scheduler.js@ until step 8b, and is that
-- file as step 8a left it (D286), with its names and tags spelled out
-- (@m1b-source.md@ §SO24). 'Generate.CoreJS' emits it before every other
-- helper, because the @source_@ helpers and an extern with no arguments build a
-- binding node when the program loads.
--
-- A binding node holds only what to run, and a wait and its cancel function are
-- the process's, so one node may be shared by any number of processes. That is
-- what makes @_SourcePrim_new@ and a zero-argument extern's single node safe.
taskHelpers :: B.Builder
taskHelpers =
  [r|
// TASKS
//
// A task is a tree of nodes, and `$` is the kind of node:
//
//   0 SUCCEED   { value }
//   1 FAIL      { value }
//   2 BINDING   { callback }               a wait, begun by calling callback
//   3 AND_THEN  { callback, task }
//   4 ON_ERROR  { callback, task }
//   5 BRACKET   { release, task }
//
// A process's stack holds frames of kind 0 and 1, which continue a success or a
// failure, and 6 RELEASE { release }. The tags are numbers because the REPL's
// printer shows any object whose `$` is a number as `<internals>`, which is
// what a task is to a reader.

function _TaskPrim_succeed(value) {
  return {
    $: 0,
    value: value,
  };
}

function _TaskPrim_fail(error) {
  return {
    $: 1,
    value: error,
  };
}

// A binding node holds only what to run. The wait it starts, and the function
// that cancels that wait, belong to the process that runs it (D286), because a
// node is a value: an extern with no arguments is one node for the whole
// program, and two processes may be waiting on it at once.
function _TaskPrim_binding(callback) {
  return {
    $: 2,
    callback: callback,
  };
}

function _TaskPrim_andThen(callback, task) {
  return {
    $: 3,
    callback: callback,
    task: task,
  };
}

function _TaskPrim_onError(callback, task) {
  return {
    $: 4,
    callback: callback,
    task: task,
  };
}

// `bracket` cannot be written on `andThen` and `onError`, because those two
// only see a task that finished. A cancelled task does not finish: `rawKill`
// below drops the process's stack, and with it every release handler a library
// implementation would have parked there. So the release handler is a third
// kind of stack frame, which the interpreter answers to on success, on failure
// and on cancellation alike.
function _TaskPrim_bracket(acquire, release, use) {
  return _TaskPrim_andThen(function (resource) {
    return {
      $: 5,
      release: function () {
        return release(resource);
      },
      task: use(resource),
    };
  }, acquire);
}

// Run one release handler, then carry the outcome that reached it on unchanged.
// The handler is a `Task Never {}`, so the outcome cannot be lost to a second
// failure on the way out.
function _TaskPrim_releasing(frame, outcome) {
  return _TaskPrim_andThen(function (_) {
    return outcome;
  }, frame.release());
}

// CANCELLATION IS SOMETHING TO WAIT FOR
//
// Cancelling a task is not instantaneous: what it leaves to do is the release
// handlers of every `bracket` it interrupted. So `rawKill` hands back a task —
// null if there is nothing left — and each of its callers waits for it rather
// than merely starting it. That is what lets `concurrent` keep the promise
// `portable-core.md` P2 makes for it, and what orders an outer release handler
// after the inner ones when both are cancelled at once.
//
// The steps are thunks, because a release handler builds its task when it runs.

function _TaskPrim_inOrder(steps) {
  if (steps.length === 0) {
    return null;
  }

  var chain = steps[0]();
  for (var i = 1; i < steps.length; i++) {
    chain = _TaskPrim_andThen(_TaskPrim_thenRun(steps[i]), chain);
  }

  return chain;
}

function _TaskPrim_thenRun(step) {
  return function (_) {
    return step();
  };
}

function _TaskPrim_always(task) {
  return function () {
    return task;
  };
}

// A scope with a fixed child set. `concurrent` and `race` are both one, and
// they differ in a single question: what a child *succeeding* means. Failure is
// the same for both — §N9.3's first failure cancels the siblings and fails the
// scope — and so is everything below it, which is why this is one function.
//
// `makeAnswer` is called once per run, not once per task value: a `Task` is a
// value and may be run twice, so the counting a `concurrent` does cannot live
// out here.
function _TaskPrim_scope(tasks, makeAnswer) {
  return _TaskPrim_binding(function (callback) {
    const answer = makeAnswer();
    let procs;
    // An outcome has been chosen; and, separately, nobody is listening for one
    // any more because this task was itself cancelled.
    let settled = false;
    let abandoned = false;

    // Cancel every task and hand back what those cancellations have left to
    // do. Killing a process that already finished takes nothing and returns
    // nothing, so this is also how the successful siblings are disposed of.
    function cancelAll() {
      const steps = [];
      for (let i = 0; i < procs.length; i++) {
        const pending = _TaskPrim_rawKill(procs[i]);
        if (pending) {
          steps.push(_TaskPrim_always(pending));
        }
      }
      return _TaskPrim_inOrder(steps);
    }

    // The first failure cancels the siblings — and this task does not answer
    // until they are finished, release handlers included. `concurrent` is
    // specified as a scope with a fixed child set (`portable-core.md` P2), and
    // a scope does not complete before its children do
    // (`concurrency-native.md` §N9.3).
    function settle(outcome) {
      if (settled || abandoned) {
        return;
      }
      settled = true;

      const pending = cancelAll();
      if (!pending) {
        callback(outcome);
        return;
      }

      _TaskPrim_rawSpawn(
        _TaskPrim_andThen(function (_) {
            if (!abandoned) {
              callback(outcome);
            }
            return _TaskPrim_succeed({});
          },
          pending
        )
      );
    }

    procs = tasks.map((task, i) => {
      function onSuccess(res) {
        // Null means "not yet": a `concurrent` still waiting on a sibling.
        const outcome = answer(i, res);
        if (outcome) {
          settle(outcome);
        }
      }
      function onError(e) {
        settle(_TaskPrim_fail(e));
      }
      const success = _TaskPrim_andThen(onSuccess, task);
      const handled = _TaskPrim_onError(onError, success);
      return _TaskPrim_rawSpawn(handled);
    });

    // Cancelled from outside: no answer is owed any more, but the children
    // still have to be finished with, and whoever did the killing waits.
    return function () {
      abandoned = true;
      return cancelAll();
    };
  });
}

function _TaskPrim_concurrent(tasks) {
  if (tasks.length === 0) return _TaskPrim_succeed([]);

  return _TaskPrim_scope(tasks, function () {
    const results = new Array(tasks.length);
    let count = 0;

    return function (i, res) {
      results[i] = res;
      count++;
      return count === tasks.length ? _TaskPrim_succeed(results) : null;
    };
  });
}

// The first child to *settle* is the answer, and settling means succeeding or
// failing: the branch that wins a `race [ work, timeout ]` is the one that
// fails, so a `race` that waited for a success could never time out. The first
// task is apart from the rest, as in `Task.race` (D110), so there is always at
// least one and this always has an answer to give.
function _TaskPrim_race(first, rest) {
  return _TaskPrim_scope([first].concat(rest), function () {
    return function (i, res) {
      return _TaskPrim_succeed(res);
    };
  });
}

function _TaskPrim_map2(callback, taskA, taskB) {
  function combine([resA, resB]) {
    return _TaskPrim_succeed(A2(callback, resA, resB));
  }
  return _TaskPrim_andThen(combine, _TaskPrim_concurrent([taskA, taskB]));
}

// PROCESSES

var _TaskPrim_guid = 0;

function _TaskPrim_rawSpawn(task) {
  var proc = {
    $: 0,
    id: _TaskPrim_guid++,
    root: task,
    stack: null,
    wait: null,
    cancel: null,
  };

  _TaskPrim_enqueue(proc);

  return proc;
}

function _TaskPrim_spawn(task) {
  return _TaskPrim_binding(function (callback) {
    callback(_TaskPrim_succeed(_TaskPrim_rawSpawn(task)));
  });
}

// MAIN

// A `main : Task Never {}` (D72; geng-lang m1b-source.md §SO12). What the
// export's `init` is: a function, as a `Program`'s is, which runs the task in a
// process of its own. The type says the task cannot fail, so the program ends in
// one of two ways, and each ends the process (D257):
//
// - `main` completes, and the status is `process.exitCode`, which is 0 unless
//   the program chose one with `Node.setExitCode`.
// - something throws, in the first slice of the task, which runs inside this
//   call, or in any later one, which runs from a host callback. Both are
//   reported the same way, the error on standard error and status 1, where
//   left to node the first would be caught by the output's `try` and exit 0
//   (compiler#385) and the second would print a source line before the error.
function _TaskPrim_runMain(task) {
  return function (args) {
    var host = typeof process !== "undefined" && process.stdout && process.stderr;
    if (host) {
      process.on("uncaughtException", _TaskPrim_mainCrashed);
      process.once("beforeExit", _TaskPrim_mainStalled);
    }
    try {
      _TaskPrim_rawSpawn(
        _TaskPrim_andThen(function (value) {
          if (host) {
            _TaskPrim_mainEnd();
          }
          return _TaskPrim_succeed(value);
        }, task),
      );
    } catch (e) {
      if (!host) {
        throw e;
      }
      _TaskPrim_mainCrashed(e);
    }
  };
}

function _TaskPrim_mainCrashed(e) {
  console.error(e);
  process.exitCode = 1;
  _TaskPrim_mainEnd();
}

// Node's event loop has emptied while `main` is still waiting, so nothing is
// left that could wake it and it can never complete. Ending with status 0 would
// say it did; this is `ffi.md` F4's rule for a source nothing can deliver to,
// on JavaScript (D263). A completed `main` never gets here, since
// `process.exit` does not emit `beforeExit`.
function _TaskPrim_mainStalled() {
  console.error(
    "main cannot complete: it is waiting for an event that nothing still running can deliver",
  );
  process.exitCode = 1;
  _TaskPrim_mainEnd();
}

// The program ends when `main` does (D72), even if a host resource it opened
// and did not close would keep node's event loop alive: nothing can be
// listening to it, since only `main` could have been. Standard output and error
// are written through first, because a write to a pipe is asynchronous on POSIX
// and `process.exit` drops what is still queued (§SO12 measured 64 KiB of 8 MiB
// arriving). `process.exit()` takes `process.exitCode`.
function _TaskPrim_mainEnd() {
  process.stdout.write("", function () {
    process.stderr.write("", function () {
      process.exit();
    });
  });
}

function _TaskPrim_kill(proc) {
  return _TaskPrim_binding(function (callback) {
    var pending = _TaskPrim_rawKill(proc);

    if (!pending) {
      callback(_TaskPrim_succeed({}));
      return;
    }

    // `kill` answers when the cancellation is finished rather than when it is
    // started, which is the difference between a release handler being a
    // guarantee and being a hope.
    _TaskPrim_rawSpawn(
      _TaskPrim_andThen(function (_) {
        callback(_TaskPrim_succeed({}));
        return _TaskPrim_succeed({});
      }, pending),
    );
  });
}

// Returns what this cancellation has left to do, or null if it is finished.
// The caller waits for it: `_TaskPrim_kill` and `concurrent`'s `cancelAll`
// are the two, and neither may merely start it.
function _TaskPrim_rawKill(proc) {
  var steps = [];

  // A process that is waiting stops waiting here, whether or not the wait can
  // be cancelled: clearing `wait` is what makes the operation's callback do
  // nothing when it comes, and most operations have no cancel function.
  if (proc.wait) {
    var cancel = proc.cancel;
    proc.wait = null;
    proc.cancel = null;
    // A cancel function returns nothing, or the task its *own* cancellation
    // has left to do. `concurrent`'s scope is the only one that returns
    // anything. It is sequenced first, so an inner scope is finished with
    // before this process's own handlers run: innermost-first holds across a
    // `concurrent` as well as within one.
    var pending = typeof cancel === "function" ? cancel() : null;
    if (pending) {
      steps.push(_TaskPrim_always(pending));
    }
  }

  // Everything the process was going to do next is abandoned — except its
  // release handlers, which are exactly what cancellation must still run. They
  // live in the process's own state rather than in the interpreter's call
  // stack, which is what makes reaching them here possible at all, and the
  // frames are already in innermost-first order. Each is taken as it is found,
  // so that killing an already-killed process releases nothing twice.
  for (var frame = proc.stack; frame; frame = frame.rest) {
    if (frame.$ === 6 && frame.release) {
      steps.push(frame.release);
      frame.release = null;
    }
  }

  // `root` is the only field a kill may clear. `rawKill` is reachable from
  // inside a callback that `_TaskPrim_step` is part-way through running — a
  // task of a `concurrent` fails, and the failure handler kills its siblings
  // and itself — and that callback's caller still reads `stack` afterwards.
  proc.root = null;

  return _TaskPrim_inOrder(steps);
}

/* STEP PROCESSES

type alias Process =
  { $ : tag
  , id : unique_id
  , root : Task
  , stack : null | { $: SUCCEED | FAIL, callback, rest: stack }
                 | { $: RELEASE, release: () -> Task Never {}, rest: stack }
  , wait : null | {}               the token of the wait in progress
  , cancel : null | () -> ?Task    that wait's cancel function
  }

*/

var _TaskPrim_working = false;
var _TaskPrim_queue = [];

function _TaskPrim_enqueue(proc) {
  _TaskPrim_queue.push(proc);
  if (_TaskPrim_working) {
    return;
  }
  _TaskPrim_working = true;
  // Make sure tasks created during _step are run
  while (_TaskPrim_queue.length > 0) {
    const activeProcs = _TaskPrim_queue;
    _TaskPrim_queue = [];

    for (const proc of activeProcs) {
      _TaskPrim_step(proc);
    }
  }
  _TaskPrim_working = false;
}

function _TaskPrim_step(proc) {
  stepping: while (proc.root) {
    var rootTag = proc.root.$;
    if (rootTag === 0 || rootTag === 1) {
      while (proc.stack && proc.stack.$ !== rootTag) {
        // A release frame matches neither tag, so it is reached on both, which
        // is the whole of what `bracket` promises about success and failure.
        if (proc.stack.$ === 6) {
          proc.root = _TaskPrim_releasing(proc.stack, proc.root);
          proc.stack = proc.stack.rest;
          continue stepping;
        }
        proc.stack = proc.stack.rest;
      }
      if (!proc.stack) {
        return;
      }
      proc.root = proc.stack.callback(proc.root.value);
      proc.stack = proc.stack.rest;
    } else if (rootTag === 2) {
      // Each wait is a fresh token (D286). The callback answers only the wait
      // that is still current: one that comes after a kill, or a second one
      // for the same wait, finds a different token or none and does nothing.
      // Without that, a killed process ran on once an operation with no
      // cancel function finished, and unwound into release frames its kill
      // had already emptied (m1b-source.md §SO22.3).
      var wait = {};
      proc.wait = wait;
      proc.cancel = null;
      var cancel = proc.root.callback(function (newRoot) {
        if (proc.wait !== wait) {
          return;
        }
        proc.wait = null;
        proc.cancel = null;
        proc.root = newRoot;
        _TaskPrim_enqueue(proc);
      });
      // A callback that answered before returning has already ended the
      // wait, and its cancel function has nothing left to cancel.
      if (proc.wait === wait) {
        proc.cancel = cancel;
      }
      return;
    } else if (rootTag === 5) {
      proc.stack = {
        $: 6,
        release: proc.root.release,
        rest: proc.stack,
      };
      proc.root = proc.root.task;
    } // if (rootTag === 3 || rootTag === 4)
    else {
      proc.stack = {
        $: rootTag === 3 ? 0 : 1,
        callback: proc.root.callback,
        rest: proc.stack,
      };
      proc.root = proc.root.task;
    }
  }
}
|]

-- | The export every program ends with: merge the program's @main@s into
-- @scope.Gren@, refusing a second @init@ under one module name. It was
-- @_Platform_export@ in @core@'s kernel @Platform.js@, whose other half, JSON at
-- the host boundary, left with @Sqlite@ (D284, D285).
exportHelpers :: B.Builder
exportHelpers =
  [r|
function _Program_export(exports) {
  scope["Gren"]
    ? _Program_mergeExports("Gren", scope["Gren"], exports)
    : (scope["Gren"] = exports);
}

function _Program_mergeExports(moduleName, obj, exports) {
  for (var name in exports) {
    name in obj
      ? name == "init"
        ? _Program_duplicate(moduleName)
        : _Program_mergeExports(moduleName + "." + name, obj[name], exports[name])
      : (obj[name] = exports[name]);
  }
}

function _Program_duplicate(moduleName) {
  throw new Error(
    "Your page is loading multiple Gren scripts with a module named " +
      moduleName +
      ". Maybe a duplicate script is getting loaded accidentally? If not, rename one of them so I know which is which!",
  );
}
|]

-- | Record update, which @Generate.CoreJS.Expression@ writes for every
-- @{ r | f = v }@ (D288, @m1b-source.md@ §SO24). It was @_Utils_update@ in
-- @core@'s kernel, and nothing linked @Utils.js@ because of it: a program
-- reached the file through the import chain that began at @Scheduler.js@, and
-- step 8b's first build is what found that out.
recordHelpers :: B.Builder
recordHelpers =
  [r|
function _Record_update(oldRecord, updatedFields) {
  var newRecord = {};

  for (var key in oldRecord) {
    newRecord[key] = oldRecord[key];
  }

  for (var key in updatedFields) {
    newRecord[key] = updatedFields[key];
  }

  return newRecord;
}
|]

-- | D71's mailbox.
--
-- @source_new@ carries no arguments (D252), so it is the one primitive whose
-- JavaScript is a bare reference rather than a call: it names a single
-- @_TaskPrim_binding@ node, shared by every run. Each run allocates its own
-- mailbox, because allocating is what running the node does. Sharing the node
-- was safe here only because its callback answers before it returns, until
-- D286 moved a wait and its cancel function from the node onto the process
-- (@m1b-source.md@ §SO22.3), which makes any binding node safe to share.
source :: TaskPrim -> [JS.Expr] -> JS.Expr
source p args =
  case (p, args) of
    (SourceNew, []) -> JS.Ref (JsName.fromLocalHumanReadable "_SourcePrim_new")
    (SourceNext, [_]) -> helper "_SourcePrim_next" args
    (SourceClose, [_]) -> helper "_SourcePrim_close" args
    _ -> arityError (TaskOp p) args
  where
    helper name as = JS.Call (JS.Ref (JsName.fromLocalHumanReadable name)) as

-- | Whether a primitive is one of the three @source_@ ones, whose helpers
-- 'Generate.CoreJS' emits once in a program that reaches any of them.
isSource :: PrimOp -> Bool
isSource op =
  case op of
    TaskOp SourceNew -> True
    TaskOp SourceNext -> True
    TaskOp SourceClose -> True
    _ -> False

-- | The @source_@ helpers: D71's single-reader mailbox, which is a queue, at
-- most one parked reader, and a closed flag.
--
-- @next@ answers a one-element array per queued value and an empty one once the
-- source is closed and drained, and parks otherwise. It answers an array rather
-- than a @Maybe@ (D254) because a helper is emitted JavaScript: a @Just@ built
-- here would name a constructor the linker had no reason to keep. @Source.next@
-- turns it into a @Maybe@ in Geng, where the dependency is real.
--
-- Nothing checks that there is only one reader (D245): a second one takes
-- events from the first, the way a non-linear transient copies, and only the
-- documentation says not to.
--
-- @emit@ and @close@ are what an extern implementation is handed (@ffi.md@ F4);
-- they are not primitives, and they are reached from the wrapper the extern
-- generator writes rather than from Geng.
sourceHelpers :: B.Builder
sourceHelpers =
  [r|
function _SourcePrim_Source() {
  this.queue = [];
  this.waiting = null;
  this.closed = false;
}

var _SourcePrim_new = _TaskPrim_binding(function (callback) {
  callback(_TaskPrim_succeed(new _SourcePrim_Source()));
});

function _SourcePrim_next(source) {
  return _TaskPrim_binding(function (callback) {
    if (source.queue.length > 0) {
      callback(_TaskPrim_succeed([source.queue.shift()]));
      return;
    }
    if (source.closed) {
      callback(_TaskPrim_succeed([]));
      return;
    }
    source.waiting = callback;
    return function () { source.waiting = null; };
  });
}

function _SourcePrim_close(source) {
  return _TaskPrim_binding(function (callback) {
    _SourcePrim_shut(source);
    callback(_TaskPrim_succeed({}));
  });
}

// Shared by `close` and by the `close` an extern implementation is handed: a
// parked reader is answered with the empty array rather than left parked
// forever.
function _SourcePrim_shut(source) {
  source.closed = true;
  var waiting = source.waiting;
  if (waiting) {
    source.waiting = null;
    waiting(_TaskPrim_succeed([]));
  }
}

function _SourcePrim_emit(source, value) {
  if (source.closed) return;
  var waiting = source.waiting;
  if (waiting) {
    source.waiting = null;
    waiting(_TaskPrim_succeed([value]));
  } else {
    source.queue.push(value);
  }
}
|]

-- | Whether a primitive is one of the @arr_@ or @tr_@ group, whose helpers
-- 'Generate.CoreJS' emits once in a program that reaches any of them.
isArray :: PrimOp -> Bool
isArray op =
  case op of
    ArrOp _ -> True
    TransientOp _ -> True
    _ -> False

-- | The @tr_@ helpers: C7's transient, which is a real JS array plus the number
-- of elements that are live and a flag saying whether the array has been handed
-- out. A first write mutates in place; a write to a transient whose array has
-- escaped copies first, so a non-linear use stays correct without anything
-- checking linearity.
--
-- Not @_Array_@: that is the kernel's @Array.js@, whose @var _Array_slice@
-- would replace a helper of the same name in a program holding both
-- (@docs/m1b-bytes-prim.md@ §BY12.2, where it happened).
arrayHelpers :: B.Builder
arrayHelpers =
  [r|
function _ArrayPrim_Transient(live, escaped, array) {
  this.live = live;
  this.escaped = escaped;
  this.array = array;
}

function _ArrayPrim_trNew(capacity) {
  return new _ArrayPrim_Transient(0, false, new Array(capacity));
}

function _ArrayPrim_trFromArray(array) {
  return new _ArrayPrim_Transient(array.length, true, array);
}

// The array to write into: its own when nothing else holds it, a copy of the
// live elements when it has escaped.
function _ArrayPrim_trOwn(t) {
  if (t.escaped) return t.array.slice(0, t.live);
  t.escaped = true;
  return t.array;
}

function _ArrayPrim_trPush(t, value) {
  var array = _ArrayPrim_trOwn(t);
  var live = t.live;
  if (live < array.length) { array[live] = value; } else { array.push(value); }
  return new _ArrayPrim_Transient(live + 1, false, array);
}

function _ArrayPrim_trSet(t, index, value) {
  var array = _ArrayPrim_trOwn(t);
  array[index] = value;
  return new _ArrayPrim_Transient(t.live, false, array);
}

function _ArrayPrim_trGet(t, index) { return t.array[index]; }

function _ArrayPrim_trLength(t) { return t.live; }

function _ArrayPrim_trToArray(t) {
  var array = t.array;
  if (t.escaped) return array.slice(0, t.live);
  t.escaped = true;
  array.length = t.live;
  return array;
}
|]

-- PIECES

-- | @x | 0@ -- the coercion that makes an @Int@ 32 bits wide.
coerce :: JS.Expr -> JS.Expr
coerce e = JS.Infix JS.OpBitwiseOr e (JS.Int 0)

-- | @x >>> 0@ -- the same instruction read unsigned, which is what makes a
-- @UInt32@ 32 bits wide.
unsign :: JS.Expr -> JS.Expr
unsign e = JS.Infix JS.OpZfRShift e (JS.Int 0)

-- | A call to one of 'bitsHelpers'.
bitsCall :: Name.Name -> JS.Expr -> JS.Expr
bitsCall name e =
  JS.Call (JS.Ref (JsName.fromLocalHumanReadable name)) [e]

-- | @Math.fround(x)@ -- the rounding that makes a @Float32@ single precision.
fround :: JS.Expr -> JS.Expr
fround e = JS.Call (global "Math" "fround") [e]

-- | @BigInt(x)@ and @Number(x)@ -- the two crossings between a JavaScript
-- number and a JavaScript BigInt. A shift count is an `Int` at every width
-- (A5), so 'toBigInt' is also what a 64-bit shift does to its second argument:
-- JavaScript refuses to mix the two in one operator.
toBigInt :: JS.Expr -> JS.Expr
toBigInt e = JS.Call (JS.Ref (JsName.fromLocalHumanReadable "BigInt")) [e]

fromBigInt :: JS.Expr -> JS.Expr
fromBigInt e = JS.Call (JS.Ref (JsName.fromLocalHumanReadable "Number")) [e]

-- | @BigInt.asIntN(w, x)@ and @BigInt.asUintN(w, x)@ -- the wrap at a 64-bit
-- type, and the truncation at a narrowing conversion.
asIntN :: Int -> JS.Expr -> JS.Expr
asIntN w e = JS.Call (global "BigInt" "asIntN") [JS.Int w, e]

asUintN :: Int -> JS.Expr -> JS.Expr
asUintN w e = JS.Call (global "BigInt" "asUintN") [JS.Int w, e]

infinity :: JS.Expr
infinity = JS.Float "Infinity"

-- | A JavaScript built-in, as @Math.imul@ is. Not a kernel reference: these
-- are the host's own names and no `core` module supplies them.
global :: Name.Name -> Name.Name -> JS.Expr
global object field =
  JS.Access (JS.Ref (JsName.fromLocalHumanReadable object)) (JsName.fromLocalHumanReadable field)

arityError :: PrimOp -> [JS.Expr] -> a
arityError op args =
  -- Unreachable: `Core.Prim.primArity` is checked when the node is built and
  -- the wire decoder checks it again. Reaching here means an `EPrim` that is
  -- not saturated got past both.
  error $
    "Generate.CoreJS.Prim: "
      ++ Name.toChars (Prim.primVarName op)
      ++ " applied to "
      ++ show (length args)
      ++ " arguments, not "
      ++ show (Prim.primArity op)

-- | Whether a primitive is one of the four that go through 'bitsHelpers'.
isFloatBits :: PrimOp -> Bool
isFloatBits op =
  case op of
    ConvOp F64Bits -> True
    ConvOp F64FromBits -> True
    ConvOp F32Bits -> True
    ConvOp F32FromBits -> True
    _ -> False

-- | The float bits helpers, which 'Generate.CoreJS' emits once when a program
-- reaches any of the four (@docs/m1b-bytes-prim.md@ §BY3).
bitsHelpers :: B.Builder
bitsHelpers =
  [r|
// One buffer for every float bits primitive (docs/m1b-bytes-prim.md §BY3). A
// call writes it and reads it back before returning, so nothing can see it
// between two calls.
var _Float_f64 = new Float64Array(1);
var _Float_u64 = new BigUint64Array(_Float_f64.buffer);
var _Float_f32 = new Float32Array(1);
var _Float_u32 = new Uint32Array(_Float_f32.buffer);
function _Float_bits64(x) { _Float_f64[0] = x; return _Float_u64[0]; }
function _Float_fromBits64(x) { _Float_u64[0] = x; return _Float_f64[0]; }
function _Float_bits32(x) { _Float_f32[0] = x; return _Float_u32[0]; }
function _Float_fromBits32(x) { _Float_u32[0] = x; return _Float_f32[0]; }
|]
