{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | Core to bytes, against @schema/geng/core/v1.proto@.
--
-- Read this beside the schema; each function below is one message, in the
-- schema's order, and each field is one line in the schema's tag order. That
-- correspondence is the whole review strategy — D88 puts the codec in our hands
-- precisely so that it can be checked by eye against the definition of record,
-- and @harness/wire.py@ decodes what this writes using the schema alone.
--
-- __The profile is a property of the code and not of a configuration__ (C10):
--
--   * fields are written in ascending tag order, because they are written in
--     source order and the source is in tag order;
--   * varints are minimal, because 'varint' emits the minimal form and there is
--     no other;
--   * an implicit-presence field holding its default is skipped ('u32', 'bool_',
--     'enum_', 'text'), while an @optional@ field is written exactly when the
--     'Maybe' is 'Just' and a @oneof@ member is written whenever it is selected;
--   * there are no @map@ fields — 'Core.AST.FileTable' is written as
--     @repeated FileEntry@ in key order, which 'Map.toAscList' already is;
--   * there is nothing to preserve from a previous version, so nothing does.
--
-- __Sizes are arithmetic, not a second pass.__ 'Enc' carries the byte count
-- beside the builder, so a length-delimited submessage knows its own length
-- without being rendered and measured. A naive encoder renders every nesting
-- level once per level, which for a Core expression tree is depth-many copies of
-- the whole subtree.
module Core.Wire.Encode
  ( Enc (..),
    run,
    moduleEnc,
  )
where

import Core.AST
import Core.Prim qualified as Prim
import Core.Wire.Protobuf
import Data.ByteString.Builder qualified as B
import Data.Int (Int32, Int64)
import Data.Map qualified as Map
import Data.Name qualified as Name
import Data.Utf8 qualified as Utf8
import Data.Word (Word32, Word64)
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg

-- THE ENCODING MONOID

-- | Bytes and how many of them there are — or the reasons there are none.
--
-- The failure case exists for exactly one rule, D91's: 'LIntLegacy' carries an
-- unbounded 'Integer' and the wire format carries a @sint64@. Accumulating the
-- messages rather than stopping at the first means a module with three
-- out-of-range literals reports three, which is what a person fixing them wants.
data Enc
  = Enc !Int B.Builder
  | EncBad [String]

instance Semigroup Enc where
  EncBad a <> EncBad b = EncBad (a ++ b)
  EncBad a <> _ = EncBad a
  _ <> EncBad b = EncBad b
  Enc n1 b1 <> Enc n2 b2 = Enc (n1 + n2) (b1 <> b2)

instance Monoid Enc where
  mempty = Enc 0 mempty

-- | The bytes, or what stopped them.
run :: Enc -> Either [String] B.Builder
run e =
  case e of
    Enc _ b -> Right b
    EncBad problems -> Left problems

-- PRIMITIVES

varint :: Word64 -> Enc
varint n = Enc (varintSize n) (go n)
  where
    go w =
      if w < 0x80
        then B.word8 (fromIntegral w)
        else B.word8 (fromIntegral (w `mod` 0x80) + 0x80) <> go (w `div` 0x80)

key :: Word32 -> WireType -> Enc
key tag wire = varint (tagKey tag wire)

bytes :: Int -> B.Builder -> Enc
bytes = Enc

-- FIELDS
--
-- One function per shape a field can have. The name says what the schema says:
-- `u32` is an implicit-presence `uint32` and skips zero; `optMsg` is an
-- `optional` message and writes exactly when it is `Just`; `oneofText` is a
-- `oneof` member and writes even when it is empty.

-- | @uint32@, implicit presence.
u32 :: Word32 -> Word32 -> Enc
u32 _ 0 = mempty
u32 tag n = key tag WVarint <> varint (fromIntegral n)

-- | @bool@, implicit presence.
bool_ :: Word32 -> Bool -> Enc
bool_ _ False = mempty
bool_ tag True = key tag WVarint <> varint 1

-- | An enum, implicit presence. Code 0 is the default and is skipped.
enum_ :: Word32 -> Word32 -> Enc
enum_ _ 0 = mempty
enum_ tag code = key tag WVarint <> varint (fromIntegral code)

-- | @string@, implicit presence. Empty is the default and is skipped.
text :: Word32 -> Utf8.Utf8 t -> Enc
text tag s
  | Utf8.size s == 0 = mempty
  | otherwise = utf8Field tag s

-- | A @oneof@ member of string type: written whenever selected, empty or not.
oneofText :: Word32 -> Utf8.Utf8 t -> Enc
oneofText = utf8Field

utf8Field :: Word32 -> Utf8.Utf8 t -> Enc
utf8Field tag s =
  let n = Utf8.size s
   in key tag WBytes <> varint (fromIntegral n) <> bytes n (Utf8.toBuilder s)

-- | A submessage: always written, because a message field has explicit presence.
msg :: Word32 -> Enc -> Enc
msg tag inner =
  case inner of
    EncBad problems -> EncBad problems
    Enc n b -> key tag WBytes <> varint (fromIntegral n) <> bytes n b

-- | An @optional@ submessage.
optMsg :: Word32 -> (a -> Enc) -> Maybe a -> Enc
optMsg _ _ Nothing = mempty
optMsg tag f (Just a) = msg tag (f a)

-- | An @optional@ string: explicit presence, so an empty one is still written.
optText :: Word32 -> Maybe (Utf8.Utf8 t) -> Enc
optText _ Nothing = mempty
optText tag (Just s) = utf8Field tag s

-- | @repeated@ of a message type. Records with one tag, in list order — which
-- is C14's order for a binding list, and the schema's stated order elsewhere.
rep :: Word32 -> (a -> Enc) -> [a] -> Enc
rep tag f = foldMap (msg tag . f)

-- | @repeated string@. Not packed: only numeric scalars can be, and this schema
-- has no repeated numeric scalar at all — rule 3 has no instance in it.
repText :: Word32 -> [Utf8.Utf8 t] -> Enc
repText tag = foldMap (utf8Field tag)

-- | A @oneof@ member of message type, and the shape @Unit@ takes: a tag and a
-- zero length, which is how a nullary constructor is spelled.
unit :: Word32 -> Enc
unit tag = msg tag mempty

-- NAMES

moduleNameEnc :: ModuleName.Canonical -> Enc
moduleNameEnc (ModuleName.Canonical (Pkg.Name author project) modul) =
  text 1 author
    <> text 2 project
    <> text 3 modul

qualEnc :: QualName -> Enc
qualEnc (QualName home name) =
  msg 1 (moduleNameEnc home)
    <> text 2 name

-- SPANS

spanEnc :: Span -> Enc
spanEnc (Span (FileId file) sr sc er ec) =
  u32 1 (fromIntegral file)
    <> u32 2 sr
    <> u32 3 sc
    <> u32 4 er
    <> u32 5 ec

fileEntryEnc :: (FileId, ModuleName.Canonical) -> Enc
fileEntryEnc (FileId i, home) =
  u32 1 (fromIntegral i)
    <> msg 2 (moduleNameEnc home)

-- TYPES

typeEnc :: Type -> Enc
typeEnc t =
  case t of
    TVar n -> oneofText 1 n
    TCon name args -> msg 2 (msg 1 (qualEnc name) <> rep 2 typeEnc args)
    TFun args result -> msg 3 (rep 1 typeEnc args <> msg 2 (typeEnc result))
    TRecord fields row ->
      msg 4 (rep 1 fieldTypeEnc fields <> optText 2 row)
    TForall vars constraints body ->
      msg 5 (repText 1 vars <> rep 2 constraintEnc constraints <> msg 3 (typeEnc body))

fieldTypeEnc :: (Field, Type) -> Enc
fieldTypeEnc (field, t) = text 1 field <> msg 2 (typeEnc t)

constraintEnc :: Constraint -> Enc
constraintEnc (CClass cls t) = msg 1 (qualEnc cls) <> msg 2 (typeEnc t)

-- DECLARATIONS

dataDeclEnc :: DataDecl -> Enc
dataDeclEnc (DataDecl name params transparency ctors classes) =
  msg 1 (qualEnc name)
    <> repText 2 params
    <> enum_ 3 (transparencyCode transparency)
    <> rep 4 ctorEnc ctors
    <> rep 5 qualEnc classes

ctorEnc :: Ctor -> Enc
ctorEnc (Ctor name tag fields) =
  msg 1 (qualEnc name)
    <> u32 2 (fromIntegral tag)
    <> rep 3 typeEnc fields

-- | C10 and §B10: an enum's wire codes come from a table in the source, so that
-- reordering a data declaration cannot silently reinterpret a serialized
-- module. Append only, exactly as "Core.Prim"'s @allPrims@ is.
transparencyCode :: Transparency -> Word32
transparencyCode Transparent = 0
transparencyCode Abstract = 1

opennessCode :: Openness -> Word32
opennessCode Open = 0
opennessCode Closed = 1

originCode :: Origin -> Word32
originCode Derived = 0
originCode Written = 1

managerKindCode :: ManagerKind -> Word32
managerKindCode ManagerCmd = 0
managerKindCode ManagerSub = 1
managerKindCode ManagerFx = 2

classDeclEnc :: ClassDecl -> Enc
classDeclEnc (ClassDecl name param openness methods) =
  msg 1 (qualEnc name)
    <> text 2 param
    <> enum_ 3 (opennessCode openness)
    <> rep 4 methodSigEnc methods

methodSigEnc :: (Name.Name, Type) -> Enc
methodSigEnc (name, t) = text 1 name <> msg 2 (typeEnc t)

instanceDeclEnc :: InstanceDecl -> Enc
instanceDeclEnc (InstanceDecl cls head_ origin methods) =
  msg 1 (qualEnc cls)
    <> msg 2 (typeEnc head_)
    <> enum_ 3 (originCode origin)
    <> rep 4 methodImplEnc methods

methodImplEnc :: (Name.Name, Expr) -> Enc
methodImplEnc (name, body) = text 1 name <> msg 2 (exprEnc body)

-- MODULE

moduleEnc :: Module -> Enc
moduleEnc m =
  msg 1 (moduleNameEnc (_moduleName m))
    <> rep 2 fileEntryEnc (Map.toAscList (_moduleFiles m))
    <> rep 3 dataDeclEnc (_moduleData m)
    <> rep 4 classDeclEnc (_moduleClasses m)
    <> rep 5 instanceDeclEnc (_moduleInstances m)
    <> rep 6 bindEnc (_moduleDefs m)
    <> rep 7 recGroupEnc (_moduleDefsRec m)
    <> rep 8 qualEnc (_moduleExports m)
    <> optMsg 9 managerEnc (_moduleManager m)
    <> rep 10 portEnc (_modulePorts m)
    <> optMsg 11 mainEnc (_moduleMain m)

recGroupEnc :: [QualName] -> Enc
recGroupEnc names = rep 1 qualEnc names

mainEnc :: Main -> Enc
mainEnc main_ =
  case main_ of
    MainString -> enum_ 1 0
    MainHtml -> enum_ 1 1
    MainProgram converter -> enum_ 1 2 <> msg 2 (converterEnc converter)

managerEnc :: Manager -> Enc
managerEnc (Manager kind entries init_ onEffects onSelfMsg cmdMap subMap) =
  enum_ 1 (managerKindCode kind)
    <> rep 2 qualEnc entries
    <> msg 3 (qualEnc init_)
    <> msg 4 (qualEnc onEffects)
    <> msg 5 (qualEnc onSelfMsg)
    <> optMsg 6 qualEnc cmdMap
    <> optMsg 7 qualEnc subMap

portEnc :: Port -> Enc
portEnc (Port binder flow) =
  msg 1 (binderEnc binder)
    <> msg 2 (portFlowEnc flow)

portFlowEnc :: PortFlow -> Enc
portFlowEnc flow =
  case flow of
    PortOut converter -> msg 1 (converterEnc converter)
    PortIn converter -> msg 2 (converterEnc converter)
    PortTask input payload ->
      msg 3 (optMsg 1 converterEnc input <> msg 2 (converterEnc payload))

converterEnc :: Converter -> Enc
converterEnc (Converter isBytes code) =
  bool_ 1 isBytes
    <> msg 2 (exprEnc code)

-- EXPRESSIONS

exprEnc :: Expr -> Enc
exprEnc (Expr node t s) =
  msg 1 (typeEnc t)
    <> msg 2 (spanEnc s)
    <> nodeEnc node

nodeEnc :: Expr_ -> Enc
nodeEnc node =
  case node of
    EVar n -> oneofText 3 n
    EGlobal q -> msg 4 (qualEnc q)
    ELit l -> msg 5 (literalEnc l)
    ELam binders body -> msg 6 (absEnc binders body)
    EApp fn args -> msg 7 (appEnc fn args)
    ELet binds body -> msg 8 (bindsEnc binds body)
    ELetRec binds body -> msg 9 (bindsEnc binds body)
    ECase scrut alts fallback ->
      msg 10 (msg 1 (exprEnc scrut) <> rep 2 altEnc alts <> optMsg 3 exprEnc fallback)
    ECtor name tag args ->
      msg 11 (msg 1 (qualEnc name) <> u32 2 (fromIntegral tag) <> rep 3 exprEnc args)
    ERecord fields -> msg 12 (rep 1 fieldExprEnc fields)
    EUpdate base fields -> msg 13 (msg 1 (exprEnc base) <> rep 2 fieldExprEnc fields)
    EAccess base field -> msg 14 (msg 1 (exprEnc base) <> text 2 field)
    EArray items -> msg 15 (rep 1 exprEnc items)
    EPrim op args ->
      msg 16 (u32 1 (fromIntegral (Prim.primCode op)) <> rep 2 exprEnc args)
    EJoin binds body -> msg 17 (bindsEnc binds body)
    EJump j args -> msg 18 (text 1 j <> rep 2 exprEnc args)
    ETyLam vars body -> msg 19 (repText 1 vars <> msg 2 (exprEnc body))
    ETyApp fn args -> msg 20 (msg 1 (exprEnc fn) <> rep 2 typeEnc args)
    EWitLam binders body -> msg 21 (absEnc binders body)
    EWitApp fn args -> msg 22 (appEnc fn args)
    ECrash kind -> msg 23 (crashEnc kind)

absEnc :: [Binder] -> Expr -> Enc
absEnc binders body = rep 1 binderEnc binders <> msg 2 (exprEnc body)

appEnc :: Expr -> [Expr] -> Enc
appEnc fn args = msg 1 (exprEnc fn) <> rep 2 exprEnc args

bindsEnc :: [Bind] -> Expr -> Enc
bindsEnc binds body = rep 1 bindEnc binds <> msg 2 (exprEnc body)

fieldExprEnc :: (Field, Expr) -> Enc
fieldExprEnc (field, e) = text 1 field <> msg 2 (exprEnc e)

crashEnc :: CrashKind -> Enc
crashEnc kind =
  case kind of
    Todo message -> enum_ 1 0 <> optText 2 (Just message)
    IncompleteMatch -> enum_ 1 1
    StackExhausted -> enum_ 1 2
    Unreachable -> enum_ 1 3

binderEnc :: Binder -> Enc
binderEnc (Binder name t s) =
  text 1 name
    <> msg 2 (typeEnc t)
    <> msg 3 (spanEnc s)

bindEnc :: Bind -> Enc
bindEnc (Bind binder value) =
  msg 1 (binderEnc binder)
    <> msg 2 (exprEnc value)

altEnc :: Alt -> Enc
altEnc (Alt pattern body) =
  msg 1 (patternEnc pattern)
    <> msg 2 (exprEnc body)

-- PATTERNS

patternEnc :: Pattern -> Enc
patternEnc pattern =
  case pattern of
    PVar binder -> msg 1 (binderEnc binder)
    PWild -> unit 2
    PLit l -> msg 3 (literalEnc l)
    PCtor name tag args ->
      msg 4 (msg 1 (qualEnc name) <> u32 2 (fromIntegral tag) <> rep 3 patternEnc args)
    PRecord fields -> msg 5 (rep 1 fieldPatternEnc fields)
    PArray items tail_ -> msg 6 (rep 1 patternEnc items <> optMsg 2 binderEnc tail_)
    PAs binder inner -> msg 7 (msg 1 (binderEnc binder) <> msg 2 (patternEnc inner))

fieldPatternEnc :: (Field, Pattern) -> Enc
fieldPatternEnc (field, p) = text 1 field <> msg 2 (patternEnc p)

-- LITERALS

literalEnc :: Literal -> Enc
literalEnc l =
  case l of
    LInt n -> sint32Oneof 1 n
    LInt64 n -> sint64Oneof 2 n
    LUInt32 n -> key 3 WVarint <> varint (fromIntegral n)
    LUInt64 n -> key 4 WVarint <> varint n
    LFloat d -> key 5 WFixed64 <> bytes 8 (B.doubleLE d)
    LFloat32 f -> key 6 WFixed32 <> bytes 4 (B.floatLE f)
    LChar c -> sint32Oneof 7 c
    LString s -> oneofText 8 s
    LIntLegacy n
      | n >= legacyMin && n <= legacyMax -> sint64Oneof 9 (fromIntegral n)
      | otherwise -> EncBad [legacyProblem n]

sint32Oneof :: Word32 -> Int32 -> Enc
sint32Oneof tag n = key tag WVarint <> varint (zigzag32 n)

sint64Oneof :: Word32 -> Int64 -> Enc
sint64Oneof tag n = key tag WVarint <> varint (zigzag64 n)

legacyMin :: Integer
legacyMin = toInteger (minBound :: Int64)

legacyMax :: Integer
legacyMax = toInteger (maxBound :: Int64)

-- | D91. The message is user-facing, so it says the number, the bound and why
-- the bound is where it is.
legacyProblem :: Integer -> String
legacyProblem n =
  "the integer literal "
    ++ show n
    ++ " does not fit in 64 bits, so it cannot be written to Core.\n"
    ++ "Int is a JavaScript double until D2 lands, exact only to 2^53, so a\n"
    ++ "literal this large is not the number this program will compute with."
