{-# LANGUAGE OverloadedStrings #-}

module Canonicalize.PrimSpec where

import AST.Canonical qualified as Can
import Canonicalize.Prim qualified as Prim
import Core.Prim qualified as Core
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

    it "a group whose Gren-facing type is undecided has no entry" $
      -- `str_cmp` is a real primitive; what it returns is a design question
      -- C13's table does not answer, and an answer invented here would be
      -- speculation compiled into the compiler and checked by nothing.
      answer "str_cmp" `shouldBe` NoTypeYet

    it "so does the transient group, whose type does not exist at all" $
      answer "tr_new" `shouldBe` NoTypeYet

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
