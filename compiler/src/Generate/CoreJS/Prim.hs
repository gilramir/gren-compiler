{-# LANGUAGE OverloadedStrings #-}
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
  )
where

import Core.Prim (ConvPrim (..), FloatPrim (..), FloatType (..), IntPrim (..), IntType (..), PrimOp (..))
import Core.Prim qualified as Prim
import Data.Name qualified as Name
import Generate.JavaScript.Builder qualified as JS
import Generate.JavaScript.Name qualified as JsName

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
    -- and read back through the integer one, and `new Float64Array([a])` is
    -- the shortest way to say "a buffer holding this double". Both views are
    -- native-endian, so the pair agrees with itself on a big-endian machine as
    -- well -- the bytes move, the bits do not.
    --
    -- The allocation is per call and is not free. It is what the host offers
    -- without a scratch buffer living somewhere, and a scratch buffer would
    -- have to live in a kernel module that nothing here can make the linker
    -- include (C13: a primitive is an expression, not a dependency).
    F64Bits -> viewThrough "BigUint64Array" "Float64Array" a
    F64FromBits -> viewThrough "Float64Array" "BigUint64Array" a
    F32Bits -> viewThrough "Uint32Array" "Float32Array" a
    F32FromBits -> viewThrough "Float32Array" "Uint32Array" a
    -- A `Char` is a one-character JavaScript string, which is what
    -- `_Char_toCode` and `_Char_fromCode` in `core`'s kernel already assume.
    -- `chr` is the kernel's own wrapper, and it is what boxes the string in
    -- dev builds so the untyped printer can tell a `Char` from a `String`.
    CharToI32 -> JS.Call (JS.Access a (JsName.fromLocalHumanReadable "codePointAt")) [JS.Int 0]
    I32ToChar ->
      JS.Call
        (JS.Ref (JsName.fromKernel Name.utils "chr"))
        [JS.Call (global "String" "fromCodePoint") [a]]

-- PIECES

-- | @x | 0@ -- the coercion that makes an @Int@ 32 bits wide.
coerce :: JS.Expr -> JS.Expr
coerce e = JS.Infix JS.OpBitwiseOr e (JS.Int 0)

-- | @x >>> 0@ -- the same instruction read unsigned, which is what makes a
-- @UInt32@ 32 bits wide.
unsign :: JS.Expr -> JS.Expr
unsign e = JS.Infix JS.OpZfRShift e (JS.Int 0)

-- | @new Out(new In([x]).buffer)[0]@ -- one value written through one typed
-- array and read back through another, which is a reinterpretation of its bits
-- and not a conversion of its value.
viewThrough :: Name.Name -> Name.Name -> JS.Expr -> JS.Expr
viewThrough out in_ e =
  JS.Index
    ( JS.New
        (JS.Ref (JsName.fromLocalHumanReadable out))
        [ JS.Access
            (JS.New (JS.Ref (JsName.fromLocalHumanReadable in_)) [JS.Array [e]])
            (JsName.fromLocalHumanReadable "buffer")
        ]
    )
    (JS.Int 0)

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
