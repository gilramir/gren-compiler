{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | The converters a @port@ needs, as Core. @docs/core.md@ C18 (D84).
--
-- This is @Optimize.Port@ written against 'Core.AST' instead of
-- @AST.Optimized@, and it is the half of a port that really is a value: a JSON
-- encoder or decoder derived from the payload type, out of @Json.Encode@,
-- @Json.Decode@ and @Maybe@. Nothing in it is JavaScript. The other half —
-- handing the converter to the runtime's port constructor — is not a value and
-- is not written here; 'Core.AST.Port' names the pieces and each backend
-- assembles the call its runtime wants.
--
-- Two places where this deliberately differs from @Optimize.Port@:
--
--   * __A @Maybe@ payload decodes with @Json.Decode.nullable@__, which is
--     defined in @core@ as @oneOf [ null Nothing, map Just decoder ]@ — the
--     exact expression @Optimize.Port@ inlines. Naming the function instead of
--     re-deriving it is what keeps @Maybe@'s constructor /tags/ out of a
--     per-module lowering that has no way to know them: a module being lowered
--     sees its own declarations and not @core@'s.
--   * __Every node carries its type__ (C2), and the types here are written down
--     rather than solved, because the expression has no source to have been
--     inferred from. They are the instantiated ones — @Core.Lower.Expression@
--     emits no 'Core.AST.ETyApp' at M1a and neither does this.
--
-- @portable-core.md@ P3 deletes the port mechanism at M1b and this with it.
module Core.Lower.Port
  ( lower,
    decoder,
  )
where

import AST.Canonical qualified as Can
import AST.Utils.Type qualified as Type
import Core.AST qualified as Core
import Core.Lower.Type (lowerAnnotation, lowerType)
import Data.Map qualified as Map
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Utf8 qualified as Utf8
import Gren.ModuleName qualified as ModuleName

-- LOWER

-- | One @port@ declaration.
--
-- The span is the module's own zero span, as an @effect module@'s entry
-- bindings are: @Canonical@ keeps no region on a port — @Can.Ports@ is a bare
-- map — and inventing one from the payload type would be worse than saying the
-- code was generated.
lower :: Core.Span -> Name -> Can.Port -> Core.Port
lower sp name port_ =
  case port_ of
    Can.Outgoing freeVars payload func ->
      Core.Port (binder freeVars func) (Core.PortOut (encoder sp payload))
    Can.Incoming freeVars payload func ->
      Core.Port (binder freeVars func) (Core.PortIn (decoder sp payload))
    Can.Task freeVars input payload func ->
      Core.Port
        (binder freeVars func)
        (Core.PortTask (fmap (encoder sp) input) (decoder sp payload))
  where
    binder freeVars func =
      Core.Binder name (lowerAnnotation (Can.Forall freeVars func)) sp

-- | The payload's bytes flag and its encoder, which always travel together: the
-- flag is what the runtime branches on, and a @Bytes@ payload's \"encoder\" is
-- the identity that lets it read the payload back out unchanged.
encoder :: Core.Span -> Can.Type -> Core.Converter
encoder sp tipe = Core.Converter (isBytes tipe) (toEncoder sp tipe)

-- | Also a program's flags decoder (C19), which is the same function: flags
-- arrive from the same JavaScript as an incoming port's payload and are checked
-- by the same @Effects.checkPayload@, and @Optimize.Port.toFlagsDecoder@ is
-- defined as @toDecoder@ for exactly that reason.
decoder :: Core.Span -> Can.Type -> Core.Converter
decoder sp tipe = Core.Converter (isBytes tipe) (toDecoder sp tipe)

-- | Whether the payload is @Bytes@.
--
-- Re-implemented rather than imported from @Optimize.Port@: @Core.*@ does not
-- depend on @Optimize.*@, and it is @Optimize.*@ that goes away.
isBytes :: Can.Type -> Bool
isBytes tipe =
  case tipe of
    Can.TAlias _ _ args alias -> isBytes (Type.dealias args alias)
    Can.TType _ name [] -> name == Name.bytes
    _ -> False

-- ENCODE

-- | @payload -> Json.Encode.Value@, except for the two payloads that cross
-- unconverted, where it is @Basics.identity@ at @payload -> payload@.
--
-- The @error@s are the same ones @Optimize.Port@ has, and for the same reason:
-- @Canonicalize.Effects.checkPayload@ has already rejected every shape they
-- cover, so reaching one is a broken invariant rather than a bad program.
toEncoder :: Core.Span -> Can.Type -> Core.Expr
toEncoder sp tipe =
  case tipe of
    Can.TAlias _ _ args alias ->
      toEncoder sp (Type.dealias args alias)
    Can.TLambda _ _ ->
      error "Core.Lower.Port.toEncoder: function"
    Can.TVar _ ->
      error "Core.Lower.Port.toEncoder: type variable"
    Can.TType _ name args ->
      let payload = lowerType tipe
       in case args of
            []
              | name == Name.float -> encode sp "float" (Core.TFun [payload] valueTy)
              | name == Name.int -> encode sp "int" (Core.TFun [payload] valueTy)
              | name == Name.bool -> encode sp "bool" (Core.TFun [payload] valueTy)
              | name == Name.string -> encode sp "string" (Core.TFun [payload] valueTy)
              -- `Bytes` moves as bytes and a `Value` is already one, so both
              -- are the identity — at its own type, not at the encoder's. The
              -- flag beside it is what tells the runtime which of the two.
              | name == Name.bytes -> identity sp payload
              | name == Name.value -> identity sp payload
            [arg]
              | name == Name.maybe -> encodeMaybe sp payload arg
              | name == Name.array -> encodeArray sp payload arg
            _ ->
              error "Core.Lower.Port.toEncoder: bad custom type"
    Can.TRecord _ (Just _) ->
      error "Core.Lower.Port.toEncoder: bad record"
    Can.TRecord fields Nothing ->
      encodeRecord sp (lowerType tipe) fields

-- | @\\$ -> Maybe.destruct Json.Encode.null <encoder> $@
encodeMaybe :: Core.Span -> Core.Type -> Can.Type -> Core.Expr
encodeMaybe sp payload arg =
  let inner = lowerType arg
      innerEncoder = Core.TFun [inner] valueTy
      destruct =
        ref sp ModuleName.maybe "destruct" $
          Core.TFun [valueTy, innerEncoder, payload] valueTy
      body =
        app
          sp
          destruct
          [ ref sp ModuleName.jsonEncode "null" valueTy,
            toEncoder sp arg,
            var sp Name.dollar payload
          ]
          valueTy
   in lam sp [Core.Binder Name.dollar payload sp] body

-- | @Json.Encode.array <encoder>@
encodeArray :: Core.Span -> Core.Type -> Can.Type -> Core.Expr
encodeArray sp payload arg =
  let inner = lowerType arg
      array =
        ref sp ModuleName.jsonEncode "array" $
          Core.TFun [Core.TFun [inner] valueTy, payload] valueTy
   in app sp array [toEncoder sp arg] (Core.TFun [payload] valueTy)

-- | @\\$ -> Json.Encode.object [ { key = \"f\", value = <encoder> $.f }, … ]@
--
-- Fields ascending, which is C2's order for a record and also
-- @Optimize.Port@'s: @Map.toList@ on a @Map Name@ is ascending, so the two
-- pipelines emit the same object in the same order without either having said
-- so out loud. This one says so.
encodeRecord :: Core.Span -> Core.Type -> Map.Map Name Can.FieldType -> Core.Expr
encodeRecord sp payload fields =
  let entries = Core.TCon (Core.QualName ModuleName.array Name.array) [keyValueTy]
      object = ref sp ModuleName.jsonEncode "object" (Core.TFun [entries] valueTy)
      pair (name, Can.FieldType _ ft) =
        let fieldTy = lowerType ft
            encoded =
              app
                sp
                (toEncoder sp ft)
                [Core.Expr (Core.EAccess (var sp Name.dollar payload) name) fieldTy sp]
                valueTy
         in Core.Expr
              (Core.ERecord [("key", text sp (Name.toChars name)), ("value", encoded)])
              keyValueTy
              sp
      array = Core.Expr (Core.EArray (map pair (Map.toAscList fields))) entries sp
   in lam sp [Core.Binder Name.dollar payload sp] (app sp object [array] valueTy)

-- | @{ key : String, value : Json.Encode.Value }@, the shape
-- @Json.Encode.object@ takes. Fields ascending, as everywhere.
keyValueTy :: Core.Type
keyValueTy = Core.TRecord [("key", stringTy), ("value", valueTy)] Nothing

-- DECODE

-- | @Json.Decode.Decoder payload@, except for a @Bytes@ payload, which crosses
-- unconverted and gets the identity the runtime never calls.
toDecoder :: Core.Span -> Can.Type -> Core.Expr
toDecoder sp tipe =
  case tipe of
    Can.TAlias _ _ args alias ->
      toDecoder sp (Type.dealias args alias)
    Can.TLambda _ _ ->
      error "Core.Lower.Port.toDecoder: functions should not be allowed through input ports"
    Can.TVar _ ->
      error "Core.Lower.Port.toDecoder: type variables should not be allowed through input ports"
    Can.TType _ name args ->
      let payload = lowerType tipe
       in case args of
            []
              | name == Name.float -> decode sp "float" (decoderTy payload)
              | name == Name.int -> decode sp "int" (decoderTy payload)
              | name == Name.bool -> decode sp "bool" (decoderTy payload)
              | name == Name.string -> decode sp "string" (decoderTy payload)
              | name == Name.bytes -> identity sp payload
              | name == Name.value -> decode sp "value" (decoderTy payload)
            [arg]
              | name == Name.maybe -> decodeMaybe sp payload arg
              | name == Name.array -> decodeArray sp payload arg
            _ ->
              error "Core.Lower.Port.toDecoder: bad type"
    Can.TRecord _ (Just _) ->
      error "Core.Lower.Port.toDecoder: bad record"
    Can.TRecord fields Nothing ->
      decodeRecord sp (lowerType tipe) fields

-- | @Json.Decode.nullable <decoder>@.
--
-- @core@ defines @nullable@ as @oneOf [ null Nothing, map Just decoder ]@,
-- which is exactly what @Optimize.Port@ builds by hand. Naming it costs a call
-- and buys the lowering its independence from @Maybe@'s constructor tags,
-- which a module being lowered has no way to know.
decodeMaybe :: Core.Span -> Core.Type -> Can.Type -> Core.Expr
decodeMaybe sp payload arg =
  let inner = decoderTy (lowerType arg)
      nullable = ref sp ModuleName.jsonDecode "nullable" (Core.TFun [inner] (decoderTy payload))
   in app sp nullable [toDecoder sp arg] (decoderTy payload)

-- | @Json.Decode.array <decoder>@
decodeArray :: Core.Span -> Core.Type -> Can.Type -> Core.Expr
decodeArray sp payload arg =
  let inner = decoderTy (lowerType arg)
      array = ref sp ModuleName.jsonDecode "array" (Core.TFun [inner] (decoderTy payload))
   in app sp array [toDecoder sp arg] (decoderTy payload)

-- | @andThen (\\f -> … succeed { f = f, … }) (field \"f\" <decoder>)@, one
-- @andThen@ per field, fields ascending.
--
-- The fold is @Optimize.Port@'s: the innermost expression is the record, and
-- each field wraps what is already there, so the /last/ field ascending is the
-- outermost @andThen@ and the first one is nearest the record.
decodeRecord :: Core.Span -> Core.Type -> Map.Map Name Can.FieldType -> Core.Expr
decodeRecord sp payload fields =
  let entries = Map.toAscList fields
      record =
        Core.Expr
          (Core.ERecord [(name, var sp name (lowerType ft)) | (name, Can.FieldType _ ft) <- entries])
          payload
          sp
      succeed = ref sp ModuleName.jsonDecode "succeed" (Core.TFun [payload] (decoderTy payload))
   in foldl (fieldAndThen sp payload) (app sp succeed [record] (decoderTy payload)) entries

fieldAndThen :: Core.Span -> Core.Type -> Core.Expr -> (Name, Can.FieldType) -> Core.Expr
fieldAndThen sp payload inner (name, Can.FieldType _ ft) =
  let fieldTy = lowerType ft
      andThen =
        ref sp ModuleName.jsonDecode "andThen" $
          Core.TFun
            [Core.TFun [fieldTy] (decoderTy payload), decoderTy fieldTy]
            (decoderTy payload)
      field =
        ref sp ModuleName.jsonDecode "field" $
          Core.TFun [stringTy, decoderTy fieldTy] (decoderTy fieldTy)
   in app
        sp
        andThen
        [ lam sp [Core.Binder name fieldTy sp] inner,
          app sp field [text sp (Name.toChars name), toDecoder sp ft] (decoderTy fieldTy)
        ]
        (decoderTy payload)

-- BUILDING BLOCKS

encode :: Core.Span -> Name -> Core.Type -> Core.Expr
encode sp name = ref sp ModuleName.jsonEncode name

decode :: Core.Span -> Name -> Core.Type -> Core.Expr
decode sp name = ref sp ModuleName.jsonDecode name

-- | @Basics.identity@, at the payload's own type. See 'Core.AST.Converter'.
identity :: Core.Span -> Core.Type -> Core.Expr
identity sp payload = ref sp ModuleName.basics Name.identity (Core.TFun [payload] payload)

ref :: Core.Span -> ModuleName.Canonical -> Name -> Core.Type -> Core.Expr
ref sp home name tipe = Core.Expr (Core.EGlobal (Core.QualName home name)) tipe sp

var :: Core.Span -> Name -> Core.Type -> Core.Expr
var sp name tipe = Core.Expr (Core.EVar name) tipe sp

app :: Core.Span -> Core.Expr -> [Core.Expr] -> Core.Type -> Core.Expr
app sp fn args tipe = Core.Expr (Core.EApp fn args) tipe sp

lam :: Core.Span -> [Core.Binder] -> Core.Expr -> Core.Expr
lam sp binders body =
  Core.Expr
    (Core.ELam binders body)
    (Core.TFun (map Core._binderType binders) (Core.typeOf body))
    sp

-- | A string literal. A field name and a port name are both plain identifiers,
-- so this never has an escape to decode — which is why it can go straight to
-- 'Core.AST.Text' rather than through "Core.Lower.Literal".
text :: Core.Span -> String -> Core.Expr
text sp chars = Core.Expr (Core.ELit (Core.LString (Utf8.fromChars chars))) stringTy sp

-- TYPES

valueTy :: Core.Type
valueTy = Core.TCon (Core.QualName ModuleName.jsonEncode Name.value) []

decoderTy :: Core.Type -> Core.Type
decoderTy t = Core.TCon (Core.QualName ModuleName.jsonDecode "Decoder") [t]

stringTy :: Core.Type
stringTy = Core.TCon (Core.QualName ModuleName.string Name.string) []
