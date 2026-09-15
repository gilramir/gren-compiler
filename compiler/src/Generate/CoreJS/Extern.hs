{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -Wall #-}

-- | A @js@ extern, emitted (@m1b-extern.md@ §H8 step 4, §H15).
--
-- Three things, all written from the declared type through "Core.Extern" and
-- never from the implementation file, which is placed and not read:
--
--   * __The implementation file__, once per module, as D198 has it: its text
--     unaltered inside a function of its own, which returns the declarations
--     the program's externs name.
--   * __The boundary helpers__, once per program: the inbound check for each
--     scalar row F3 keeps, and the two views D202 puts @Bytes@ through.
--   * __A wrapper per extern__, in link order, which has the Geng calling
--     convention on one side and D193's and D194's on the other. It checks the
--     implementation's arity when it is emitted, which is F1's load-time check.
module Generate.CoreJS.Extern
  ( files,
    wrapper,
    arity,
  )
where

import Core.AST qualified as Core
import Core.Extern qualified as Extern
import Data.ByteString qualified as BS
import Data.ByteString.Builder qualified as B
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set qualified as Set
import Data.Utf8 qualified as Utf8
import Generate.JavaScript.Name qualified as JsName
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Text.RawString.QQ (r)

-- FILES

-- | The helpers and every implementation file the reachable externs name, or
-- nothing when there are none.
files :: Map (Pkg.Name, Name) BS.ByteString -> [(ModuleName.Canonical, Core.Extern)] -> B.Builder
files sources externs
  | null externs = mempty
  | otherwise =
      helpers
        <> mconcat
          [ file pkg modul bytes (Set.toAscList functions)
          | ((pkg, modul), functions) <- Map.toAscList wanted,
            Just bytes <- [Map.lookup (pkg, modul) sources]
          ]
  where
    wanted =
      Map.fromListWith
        Set.union
        [ ((ModuleName._package home, modul), Set.singleton function)
        | (home, e) <- externs,
          Just (modul, function) <- [jsNames e]
        ]

file :: Pkg.Name -> Name -> BS.ByteString -> [Name] -> B.Builder
file pkg modul bytes functions =
  "var "
    <> extObject pkg modul
    <> " = (function () {\n"
    <> B.byteString bytes
    <> "\n;return {"
    <> mconcat
      ( List.intersperse
          ", "
          [ fn <> ": typeof " <> fn <> " === 'undefined' ? undefined : " <> fn
          | f <- functions,
            let fn = Name.toBuilder f
          ]
      )
    <> "};\n}());\n"

extObject :: Pkg.Name -> Name -> B.Builder
extObject pkg modul =
  JsName.toBuilder (JsName.fromGlobal (ModuleName.Canonical pkg (Name.fromChars ("Ext." ++ Name.toChars modul))) Name.dollar)

jsNames :: Core.Extern -> Maybe (Name, Name)
jsNames e =
  case [names | Core.ExternImpl Core.ExternJs names <- Core._externImpls e] of
    [[modul, function]] -> Just (Name.fromChars (Utf8.toChars modul), Name.fromChars (Utf8.toChars function))
    _ -> Nothing

-- | F3's inbound rows, D202's views, and the one way a boundary fails.
--
-- A crash is a thrown @Error@, as @Debug.todo@'s is, naming the extern and the
-- value. Each check is one function so that a wrapper is a composition of
-- names and reads as its declared type does.
helpers :: B.Builder
helpers =
  [r|
function _Extern_crash(extern, value, says) {
  var shown;
  try { shown = JSON.stringify(value); } catch (e) { shown = undefined; }
  if (typeof value === 'bigint') shown = value + 'n';
  if (shown === undefined) shown = String(value);
  throw new Error('extern ' + extern + ': the implementation gave ' + shown + ' where the type says ' + says);
}
function _Extern_number(extern, type, v) {
  if (typeof v !== 'number') _Extern_crash(extern, v, type);
  return v;
}
function _Extern_Int(extern, v) { return _Extern_number(extern, 'Int', v) | 0; }
function _Extern_UInt32(extern, v) { return _Extern_number(extern, 'UInt32', v) >>> 0; }
function _Extern_Float(extern, v) { return _Extern_number(extern, 'Float', v); }
function _Extern_Float32(extern, v) { return Math.fround(_Extern_number(extern, 'Float32', v)); }
function _Extern_wide(extern, type, v) {
  if (typeof v === 'bigint') return v;
  if (typeof v === 'number' && Number.isSafeInteger(v)) return BigInt(v);
  _Extern_crash(extern, v, type + ', which takes a BigInt or a safe integer');
}
function _Extern_Int64(extern, v) { return BigInt.asIntN(64, _Extern_wide(extern, 'Int64', v)); }
function _Extern_UInt64(extern, v) { return BigInt.asUintN(64, _Extern_wide(extern, 'UInt64', v)); }
function _Extern_Bool(extern, v) {
  if (typeof v !== 'boolean') _Extern_crash(extern, v, 'Bool');
  return v;
}
function _Extern_Char(extern, v) {
  if (!(Number.isInteger(v) && v >= 0 && v <= 0x10FFFF && !(v >= 0xD800 && v <= 0xDFFF))) {
    _Extern_crash(extern, v, 'Char, a code point that is not a surrogate');
  }
  return v;
}
function _Extern_String(extern, v) {
  if (typeof v !== 'string') _Extern_crash(extern, v, 'String');
  if (!v.isWellFormed()) _Extern_crash(extern, v, 'String, which has no lone surrogate');
  return v;
}
function _Extern_Bytes(extern, v) {
  if (!(v instanceof Uint8Array)) _Extern_crash(extern, v, 'Bytes, which takes a Uint8Array');
  return new DataView(v.buffer, v.byteOffset, v.byteLength);
}
function _Extern_bytesOut(v) { return new Uint8Array(v.buffer, v.byteOffset, v.byteLength); }
function _Extern_Array(extern, v, element) {
  if (!Array.isArray(v)) _Extern_crash(extern, v, 'Array');
  return v.map(function (x) { return element(extern, x); });
}
function _Extern_Never(extern, v) {
  _Extern_crash(extern, v, 'Never, so the implementation may not fail');
}
function _Extern_twice(extern) {
  throw new Error('extern ' + extern + ': the implementation completed more than once');
}
function _Extern_arity(extern, file, name, wanted, fn) {
  if (typeof fn !== 'function') {
    throw new Error('extern ' + extern + ': ' + file + ' declares no function ' + name);
  }
  if (fn.length !== wanted) {
    throw new Error('extern ' + extern + ': ' + file + ' declares ' + name + ' with ' + fn.length + (fn.length === 1 ? ' parameter' : ' parameters') + ', and the type needs ' + wanted);
  }
}
|]

-- WRAPPER

-- | The declared arity, for "Generate.CoreJS"'s saturated-call table.
arity :: Core.Extern -> Int
arity e =
  case Core._binderType (Core._externBinder e) of
    Core.TFun params _ -> length params
    _ -> 0

-- | The extern's binding: the arity check, then the Geng-side value.
wrapper :: ModuleName.Canonical -> Core.Extern -> B.Builder
wrapper home@(ModuleName.Canonical pkg raw) e =
  case (jsNames e, Extern.classify (Core._externPure e) (Core._binderType binder)) of
    (Nothing, _) ->
      error ("Generate.CoreJS.Extern: no js implementation for " ++ Name.toChars name)
    (_, Left problem) ->
      error ("Generate.CoreJS.Extern: the front half let through " ++ Name.toChars name ++ ": " ++ show problem)
    (Just (modul, function), Right sig@(Extern.Signature args outcome)) ->
      let impl = extObject pkg modul <> "." <> Name.toBuilder function
          label = quote (Name.toBuilder raw <> "." <> Name.toBuilder name)
          params = [B.stringUtf8 ("p" ++ show i) | i <- [0 .. length args - 1]]
          call extra = impl <> "(" <> commas (zipWith (outArg label) args params ++ extra) <> ")"
          body =
            case outcome of
              Extern.Pure result ->
                "return " <> inbound label result (call []) <> ";"
              Extern.Task x a ->
                "return _Scheduler_binding(function (callback) {\n\
                \  var settled = false;\n\
                \  var cancel = "
                  <> call
                    [ "function (v) { if (settled) _Extern_twice("
                        <> label
                        <> "); settled = true; callback(_Scheduler_succeed("
                        <> inbound label a "v"
                        <> ")); }",
                      "function (v) { if (settled) _Extern_twice("
                        <> label
                        <> "); settled = true; callback(_Scheduler_fail("
                        <> inbound label x "v"
                        <> ")); }"
                    ]
                  <> ";\n  return typeof cancel === 'function' ? cancel : null;\n});"
          global = JsName.toBuilder (JsName.fromGlobal home name)
          direct = JsName.toBuilder (JsName.fromGlobalDirectFn home name)
          check =
            "_Extern_arity("
              <> label
              <> ", "
              <> quote ("src/Ext/" <> Name.toBuilder modul <> ".js")
              <> ", "
              <> quote (Name.toBuilder function)
              <> ", "
              <> B.intDec (Extern.arity sig)
              <> ", "
              <> impl
              <> ");\n"
          definition =
            case length params of
              0 ->
                "var " <> global <> " = (function () {\n" <> body <> "\n}());\n"
              1 ->
                "var " <> global <> " = function (" <> commas params <> ") {\n" <> body <> "\n};\n"
              n
                | n <= 9 ->
                    "var "
                      <> direct
                      <> " = function ("
                      <> commas params
                      <> ") {\n"
                      <> body
                      <> "\n};\nvar "
                      <> global
                      <> " = F"
                      <> B.intDec n
                      <> "("
                      <> direct
                      <> ");\n"
                | otherwise ->
                    "var "
                      <> direct
                      <> " = function ("
                      <> commas params
                      <> ") {\n"
                      <> body
                      <> "\n};\nvar "
                      <> global
                      <> " = "
                      <> mconcat ["function (" <> p <> ") { return " | p <- params]
                      <> direct
                      <> "("
                      <> commas params
                      <> ")"
                      <> mconcat ["; }" | _ <- params]
                      <> ";\n"
       in check <> definition
  where
    binder = Core._externBinder e
    name = Core._binderName binder

-- | A Geng value on its way to the implementation: the identity but for
-- @Bytes@, which D202 views as a @Uint8Array@, and a function, which D194
-- hands over n-ary.
outArg :: B.Builder -> Extern.Arg -> B.Builder -> B.Builder
outArg label arg v =
  case arg of
    Extern.ArgValue value -> outbound 0 value v
    Extern.ArgFunction params result ->
      let names = [B.stringUtf8 ("a" ++ show i) | i <- [0 .. length params - 1]]
          ins = zipWith (inbound label) params names
          applied =
            case length params of
              1 -> v <> "(" <> commas ins <> ")"
              n
                | n <= 9 -> "A" <> B.intDec n <> "(" <> commas (v : ins) <> ")"
                | otherwise -> v <> mconcat ["(" <> i <> ")" | i <- ins]
       in "function (" <> commas names <> ") { return " <> outbound 0 result applied <> "; }"

outbound :: Int -> Extern.Value -> B.Builder -> B.Builder
outbound depth value v =
  case value of
    Extern.Scalar Extern.Bytes -> "_Extern_bytesOut(" <> v <> ")"
    Extern.Array element
      | holdsBytes element ->
          let x = B.stringUtf8 ("x" ++ show depth)
           in v <> ".map(function (" <> x <> ") { return " <> outbound (depth + 1) element x <> "; })"
    _ -> v

holdsBytes :: Extern.Value -> Bool
holdsBytes value =
  case value of
    Extern.Scalar Extern.Bytes -> True
    Extern.Array element -> holdsBytes element
    _ -> False

-- | A host value on its way into Geng: F3's check for a scalar, elementwise for
-- an array, nothing for a handle or a type variable (D199, D200), and @{}@ for
-- a unit result whatever the implementation passed (D203).
inbound :: B.Builder -> Extern.Value -> B.Builder -> B.Builder
inbound label value v =
  case value of
    Extern.Scalar s -> "_Extern_" <> scalarName s <> "(" <> label <> ", " <> v <> ")"
    Extern.Array element -> "_Extern_Array(" <> label <> ", " <> v <> ", " <> elementFn element <> ")"
    Extern.Handle -> v
    Extern.Var -> v
    Extern.Unit -> "{}"
    Extern.Never -> "_Extern_Never(" <> label <> ", " <> v <> ")"
  where
    elementFn element =
      case element of
        Extern.Scalar s -> "_Extern_" <> scalarName s
        _ -> "function (e, x) { return " <> inbound "e" element "x" <> "; }"

scalarName :: Extern.Scalar -> B.Builder
scalarName s =
  case s of
    Extern.Int -> "Int"
    Extern.UInt32 -> "UInt32"
    Extern.Int64 -> "Int64"
    Extern.UInt64 -> "UInt64"
    Extern.Float -> "Float"
    Extern.Float32 -> "Float32"
    Extern.Bool -> "Bool"
    Extern.Char -> "Char"
    Extern.String -> "String"
    Extern.Bytes -> "Bytes"

commas :: [B.Builder] -> B.Builder
commas =
  mconcat . List.intersperse ", "

quote :: B.Builder -> B.Builder
quote b =
  "'" <> b <> "'"
