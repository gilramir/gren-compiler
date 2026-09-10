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
-- __What is here is what can be declared.__ 'Canonicalize.Prim.primType'
-- carries the four integer widths and both float widths, but @Int64@,
-- @UInt32@, @UInt64@ and @Float32@ are not Gren types yet, so a @\@prim@ at
-- one of those widths cannot canonicalize its own annotation and cannot reach
-- this module. Writing their JavaScript now would be writing code no test
-- could run; it lands with the types, at @docs\/m1b-int.md@ §I8 step 4.
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
    (FloatOp F64 p, _) -> float64 p args
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

-- FLOATS

-- | A @Float@ is a JavaScript number, so every one of these is the machine
-- operation with nothing around it. @eq@ and @lt@ are __IEEE__ (C13): @NaN@ is
-- unequal to itself and unordered, and A2's lawful @Eq@\/@Ord@ are Geng source
-- over these plus @isnan@.
float64 :: FloatPrim -> [JS.Expr] -> JS.Expr
float64 p args =
  case (p, args) of
    (FAdd, [a, b]) -> JS.Infix JS.OpAdd a b
    (FSub, [a, b]) -> JS.Infix JS.OpSub a b
    (FMul, [a, b]) -> JS.Infix JS.OpMul a b
    (FDiv, [a, b]) -> JS.Infix JS.OpDiv a b
    (FNeg, [a]) -> JS.Prefix JS.PrefixNegate a
    (FAbs, [a]) -> JS.Call (global "Math" "abs") [a]
    (FSqrt, [a]) -> JS.Call (global "Math" "sqrt") [a]
    (FFloor, [a]) -> JS.Call (global "Math" "floor") [a]
    (FCeil, [a]) -> JS.Call (global "Math" "ceil") [a]
    (FTrunc, [a]) -> JS.Call (global "Math" "trunc") [a]
    (FEq, [a, b]) -> JS.Infix JS.OpEq a b
    (FLt, [a, b]) -> JS.Infix JS.OpLt a b
    -- `a !== a` rather than `isNaN(a)`: `isNaN` coerces its argument, and this
    -- is the idiom every JavaScript engine recognizes.
    (FIsNan, [a]) -> JS.Infix JS.OpNe a a
    (FIsInf, [a]) ->
      JS.Infix
        JS.OpOr
        (JS.Infix JS.OpEq a infinity)
        (JS.Infix JS.OpEq a (JS.Prefix JS.PrefixNegate infinity))
    _ -> arityError (FloatOp F64 p) args

-- CONVERSIONS

-- | Only the conversions between types @core@ has today. The rest are at
-- widths that do not exist yet -- see this module's header.
conversion :: ConvPrim -> JS.Expr -> JS.Expr
conversion p a =
  case p of
    -- Exact and free: a 32-bit integer is already a double.
    I32ToF64 -> a
    -- Precondition: finite and in range, so `| 0` is the truncation itself
    -- rather than a wrap. A10's saturation and `NaN -> 0` are Geng.
    F64ToI32Trunc -> coerce a
    -- A `Char` is a one-character JavaScript string, which is what
    -- `_Char_toCode` and `_Char_fromCode` in `core`'s kernel already assume.
    -- `chr` is the kernel's own wrapper, and it is what boxes the string in
    -- dev builds so the untyped printer can tell a `Char` from a `String`.
    CharToI32 -> JS.Call (JS.Access a (JsName.fromLocalHumanReadable "codePointAt")) [JS.Int 0]
    I32ToChar ->
      JS.Call
        (JS.Ref (JsName.fromKernel Name.utils "chr"))
        [JS.Call (global "String" "fromCodePoint") [a]]
    _ ->
      error $
        "Generate.CoreJS.Prim: no JavaScript for "
          ++ Name.toChars (Prim.primVarName (ConvOp p))
          ++ " yet (docs/m1b-int.md §I8)"

-- PIECES

-- | @x | 0@ -- the coercion that makes an @Int@ 32 bits wide.
coerce :: JS.Expr -> JS.Expr
coerce e = JS.Infix JS.OpBitwiseOr e (JS.Int 0)

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
