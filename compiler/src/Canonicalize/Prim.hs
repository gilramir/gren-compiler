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
import Core.Prim (ConvPrim (..), FloatPrim (..), FloatType (..), IntPrim (..), IntType (..), PrimOp (..))
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
-- The annotation has no free variables because no primitive with an entry here
-- is polymorphic; the groups that would be ('Prim.ArrOp', 'Prim.StrOp') are the
-- ones with no entry.
lookup :: Name.Name -> Lookup
lookup name =
  case Prim.primFromName (Text.pack (Name.toChars name)) of
    Nothing -> Unknown
    Just op ->
      case primType op of
        Nothing -> NoTypeYet
        Just tipe -> Found op (Can.Forall Map.empty tipe)

-- | The type @core@ must declare a primitive with, or 'Nothing' when the table
-- has no entry for it yet.
--
-- __Why the table has holes.__ Every entry here is mechanical: an integer
-- primitive's type is read off its width and its shape, a conversion's off the
-- two widths in its name. Nothing is a judgement call, so nothing here is a
-- guess. The @str_@, @bytes_@, @arr_@, @tr_@, @bt_@ and @task_@ groups are not
-- like that — C13's table says what @str_cmp@ /does/ and not what it returns,
-- and @Transient@ and @Source@ are types @core@ does not have yet. An entry
-- invented for one of those would be speculation compiled into the compiler
-- and checked by nothing, so those primitives have no entry and a @\@prim@
-- naming one is rejected as not available yet. Each entry lands with the Geng
-- type it names.
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
