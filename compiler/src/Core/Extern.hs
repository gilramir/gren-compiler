{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | What crosses a @js@ extern's boundary, read off its declared type
-- (@m1b-extern.md@ §H13, D192 and D199–D203).
--
-- One reading, two readers. "Canonicalize.Module" refuses a declaration whose
-- type does not classify, and "Generate.CoreJS" writes the wrapper from the
-- 'Signature' the same function returns, so the rule the author is held to and
-- the code the wrapper normalizes by cannot drift apart.
--
-- It reads Core's type rather than Canonical's because Core's is already the
-- shape the wrapper needs: aliases expanded, and a function type collapsed to
-- one argument list (C3), which is the implementation's arity.
module Core.Extern
  ( Signature (..),
    Arg (..),
    Value (..),
    Scalar (..),
    Outcome (..),
    Problem (..),
    classify,
    arity,
    handle,
  )
where

import Core.AST qualified as Core
import Data.Name (Name)
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg

-- | An extern's declared type, as the boundary sees it.
data Signature = Signature
  { _sigArgs :: [Arg],
    _sigOutcome :: Outcome
  }
  deriving (Eq, Show)

-- | What the implementation returns: a value, or, for an @\@extern@, a @Task@'s
-- error and success.
data Outcome
  = Pure Value
  | Task Value Value
  deriving (Eq, Show)

-- | One argument: a value, or a Geng function the implementation may call
-- (D194, D201), with its own parameters and result.
data Arg
  = ArgValue Value
  | ArgFunction [Value] Value
  deriving (Eq, Show)

data Value
  = Scalar Scalar
  | Array Value
  | -- | @Extern.Handle@ (D199): any JavaScript value, unchanged.
    Handle
  | -- | A type variable (D200): believed, unchanged.
    Var
  | -- | @{}@ (D203): only ever a result, and ignored.
    Unit
  | -- | @Never@: only ever a @Task@'s error, which the implementation must not
    -- produce.
    Never
  | -- | D71's mailbox (@ffi.md@ F4). Only ever an /argument/: the wrapper hands
    -- the implementation @{ emit, close }@ rather than the source itself, so
    -- the only two things it can do are the two the design gives it. The value
    -- it carries is checked on the way in, as an array's element is.
    SourceOf Value
  deriving (Eq, Show)

data Scalar
  = Int
  | UInt32
  | Int64
  | UInt64
  | Float
  | Float32
  | Bool
  | Char
  | String
  | Bytes
  deriving (Eq, Show)

-- | Why a type does not cross, and the part of it that does not.
data Problem
  = -- | A type that is none of D192's: a record, or a custom type other than
    -- the scalars, @Array@ and @Extern.Handle@.
    DoesNotCross Core.Type
  | -- | A @{}@ argument (D203).
    UnitArgument
  | -- | A function anywhere but an argument, or one whose own parameters or
    -- result are a function or a @Task@ (D201).
    FunctionPosition Core.Type
  | -- | @Never@ anywhere but a @Task@'s error.
    NeverPosition
  deriving (Eq, Show)

-- | The implementation's JavaScript arity: the arguments, plus @succeed@ and
-- @fail@ for a @Task@ (D193).
arity :: Signature -> Int
arity (Signature args outcome) =
  length args + case outcome of
    Pure _ -> 0
    Task _ _ -> 2

handle :: Core.QualName
handle =
  Core.QualName (ModuleName.Canonical Pkg.core "Extern") "Handle"

classify :: Bool -> Core.Type -> Either Problem Signature
classify isPure tipe =
  case tipe of
    Core.TForall _ _ inner -> classify isPure inner
    Core.TFun params result ->
      Signature <$> traverse argument params <*> outcome result
    _ ->
      Signature [] <$> outcome tipe
  where
    outcome t
      | isPure = Pure <$> resultValue t
      | otherwise =
          case t of
            Core.TCon (Core.QualName home name) [x, a]
              | home == ModuleName.taskInternal && name == "Task" ->
                  Task <$> errorValue x <*> resultValue a
            -- The front half refused a non-Task @\@extern@ already.
            _ -> Left (DoesNotCross t)

argument :: Core.Type -> Either Problem Arg
argument t =
  case t of
    Core.TFun params result ->
      ArgFunction <$> traverse argValue params <*> resultValue result
    _ -> ArgValue <$> argValue t

argValue :: Core.Type -> Either Problem Value
argValue t =
  do
    v <- value t
    case v of
      Unit -> Left UnitArgument
      Never -> Left NeverPosition
      _ -> Right v

resultValue :: Core.Type -> Either Problem Value
resultValue t =
  do
    v <- value t
    case v of
      Never -> Left NeverPosition
      -- A `Source` is the caller's, and an implementation is handed the two
      -- functions that write into it rather than the mailbox itself, so there
      -- is nothing it could answer with.
      SourceOf _ -> Left (DoesNotCross t)
      _ -> Right v

errorValue :: Core.Type -> Either Problem Value
errorValue =
  value

value :: Core.Type -> Either Problem Value
value t =
  case t of
    Core.TVar _ -> Right Var
    Core.TRecord [] Nothing -> Right Unit
    Core.TFun _ _ -> Left (FunctionPosition t)
    Core.TCon q@(Core.QualName home name) args
      | q == handle, null args -> Right Handle
      | home == ModuleName.array,
        name == "Array",
        [element] <- args ->
          do
            v <- value element
            case v of
              Unit -> Left (DoesNotCross t)
              Never -> Left NeverPosition
              _ -> Right (Array v)
      | home == ModuleName.taskInternal, name == "Task" -> Left (FunctionPosition t)
      | home == ModuleName.source,
        name == "Source",
        [msg] <- args ->
          do
            v <- value msg
            case v of
              Unit -> Left (DoesNotCross t)
              Never -> Left NeverPosition
              _ -> Right (SourceOf v)
      | home == ModuleName.basics, name == "Never", null args -> Right Never
      | null args, Just s <- scalar home name -> Right (Scalar s)
    _ -> Left (DoesNotCross t)

scalar :: ModuleName.Canonical -> Name -> Maybe Scalar
scalar home name
  | home == ModuleName.basics =
      lookup name [("Int", Int), ("UInt32", UInt32), ("Int64", Int64), ("UInt64", UInt64), ("Float", Float), ("Float32", Float32), ("Bool", Bool)]
  | home == ModuleName.char && name == "Char" = Just Char
  | home == ModuleName.string && name == "String" = Just String
  | home == ModuleName.bytes && name == "Bytes" = Just Bytes
  | otherwise = Nothing
