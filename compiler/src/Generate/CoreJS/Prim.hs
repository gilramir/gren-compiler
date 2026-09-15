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
-- __Every primitive C13 names has its JavaScript here__, as of
-- @docs\/m1b-ryu.md@ §Y11: the four @*_bits@ conversions were the last hole,
-- and they are two typed arrays over one buffer.
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
  )
where

import Core.Prim (ConvPrim (..), FloatPrim (..), FloatType (..), IntPrim (..), IntType (..), PrimOp (..), StrPrim (..))
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
