{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoPolyKinds #-}
{-# OPTIONS_GHC -Wall #-}

-- | Core to bytes, against @schema/geng/core/v2.proto@.
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
  ( Enc,
    run,
    moduleEnc,
  )
where

import Core.AST
import Core.Prim qualified as Prim
import Core.Wire.Protobuf
import Data.Bits (shiftR, (.&.))
import Data.ByteString.Builder qualified as B
import Data.Coerce qualified as Coerce
import Data.Int (Int32, Int64)
import Data.Map qualified as Map
import Data.Name qualified as Name
import Data.Set qualified as Set
import Data.Utf8 qualified as Utf8
import Data.Word (Word32, Word64)
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg

-- THE ENCODING MONOID

-- | Every string in a module, as one type.
--
-- 'Utf8.Utf8'\'s phantom parameter keeps 'Data.Name.Name', 'Pkg.Author',
-- 'Pkg.Project' and 'Core.AST.Text' apart in the compiler, which is the point of
-- it — @Core.AST@\'s header explains why putting undecoded JavaScript source in
-- the last of those has to be a type error. The table does not care: they are
-- all UTF-8 bytes and the representation is identical, so a coercion is the
-- whole of the conversion.
data WIRE_STRING

type Str = Utf8.Utf8 WIRE_STRING

str :: Utf8.Utf8 t -> Str
str = Coerce.coerce

-- | The module's string table, or the pass that is still collecting it (D92).
--
-- The encoder runs twice over the same 'Enc': once 'Collecting', where only the
-- strings it reports are read, and once 'Resolved', where only the bytes are.
-- Two passes rather than a separate collecting traversal, because a separate
-- traversal is a second exhaustive walk of @Core.AST@ that can drift from this
-- one — and drift here is a string missing from the table, which is a crash at
-- encode time or, worse, a table that a second frontend would not reproduce.
data Table
  = Collecting
  | Resolved !(Map.Map Str Int)

-- | Bytes and how many of them there are — or the strings they would need, or
-- the reasons there are none.
--
-- The failure case exists for exactly one rule, D91\'s: 'LIntLegacy' carries an
-- unbounded 'Integer' and the wire format carries a @sint64@. Accumulating the
-- messages rather than stopping at the first means a module with three
-- out-of-range literals reports three, which is what a person fixing them wants.
data Piece
  = Piece !Int B.Builder ![Str]
  | Bad [String]

instance Semigroup Piece where
  Bad a <> Bad b = Bad (a ++ b)
  Bad a <> _ = Bad a
  _ <> Bad b = Bad b
  Piece n1 b1 s1 <> Piece n2 b2 s2 = Piece (n1 + n2) (b1 <> b2) (s1 ++ s2)

instance Monoid Piece where
  mempty = Piece 0 mempty []

newtype Enc = Enc {runEnc :: Table -> Piece}

instance Semigroup Enc where
  Enc f <> Enc g = Enc (\t -> f t <> g t)

instance Monoid Enc where
  mempty = Enc (const mempty)

lift :: Piece -> Enc
lift = Enc . const

-- | The bytes, or what stopped them.
--
-- Both passes are here, and the order is forced: the table has to be known
-- before an index can be written, and it cannot be known before the module has
-- been walked.
run :: Enc -> Either [String] B.Builder
run enc =
  case runEnc enc Collecting of
    Bad problems -> Left problems
    Piece _ _ strings ->
      let table = Map.fromList (zip (Set.toAscList (Set.fromList strings)) [1 ..])
       in case runEnc enc (Resolved table) of
            Bad problems -> Left problems
            Piece _ builder _ -> Right builder

-- PRIMITIVES

varintP :: Word64 -> Piece
varintP n = Piece (varintSize n) (go n) []
  where
    go w =
      if w < 0x80
        then B.word8 (fromIntegral w)
        else B.word8 (fromIntegral (w .&. 0x7f) + 0x80) <> go (w `shiftR` 7)

keyP :: Word32 -> WireType -> Piece
keyP tag wire = varintP (tagKey tag wire)

varint :: Word64 -> Enc
varint = lift . varintP

key :: Word32 -> WireType -> Enc
key tag wire = lift (keyP tag wire)

bytes :: Int -> B.Builder -> Enc
bytes n b = lift (Piece n b [])

-- FIELDS
--
-- One function per shape a field can have. The name says what the schema says:
-- `u32` is an implicit-presence `uint32` and skips zero; `optMsg` is an
-- `optional` message and writes exactly when it is `Just`; `oneofText` is a
-- `oneof` member and writes even when its index is zero.

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

-- STRINGS
--
-- D92: a string is a 1-based index into the module's table, and 0 is the empty
-- string. One-based is what keeps rule 5 saying what it said in version 1 --
-- an omitted implicit-presence field reads back as 0, which is the empty
-- string, which is what an omitted `string` used to mean.

-- | The index of a string, given the table. Zero for the empty string, which is
-- never a table entry.
indexOf :: Map.Map Str Int -> Str -> Word32
indexOf table s
  | Utf8.size s == 0 = 0
  | otherwise =
      case Map.lookup s table of
        Just i -> fromIntegral i
        Nothing ->
          -- Unreachable: the collecting pass and the resolving pass are the
          -- same 'Enc' run twice, so every string the second one asks for is
          -- one the first one reported.
          error ("Core.Wire.Encode: " ++ show (Utf8.toChars s) ++ " is not in the string table")

-- | Collect a string on the first pass, and do @what@ with its index on the
-- second.
withIndex :: Utf8.Utf8 t -> (Word32 -> Enc) -> Enc
withIndex s0 what =
  let s = str s0
   in Enc $ \table ->
        case table of
          Collecting ->
            let collected = if Utf8.size s == 0 then [] else [s]
             in case runEnc (what 0) Collecting of
                  Bad problems -> Bad problems
                  Piece _ _ more -> Piece 0 mempty (collected ++ more)
          Resolved m -> runEnc (what (indexOf m s)) table

-- | A string field, implicit presence: index 0 is omitted, exactly as an empty
-- string was in version 1.
text :: Word32 -> Utf8.Utf8 t -> Enc
text tag s = withIndex s (u32 tag)

-- | A @oneof@ member: written whenever selected, index 0 or not.
oneofText :: Word32 -> Utf8.Utf8 t -> Enc
oneofText tag s = withIndex s (\i -> key tag WVarint <> varint (fromIntegral i))

-- | An @optional@ string: explicit presence, so a 'Just' of the empty string is
-- still written, as index 0.
optText :: Word32 -> Maybe (Utf8.Utf8 t) -> Enc
optText _ Nothing = mempty
optText tag (Just s) = withIndex s (\i -> key tag WVarint <> varint (fromIntegral i))

-- | @repeated uint32@, and rule 3\'s first instance in this schema: a repeated
-- numeric scalar is always packed, so this is one length-delimited run of
-- varints and not one record each. An empty list is omitted entirely.
repText :: Word32 -> [Utf8.Utf8 t] -> Enc
repText _ [] = mempty
repText tag ss = go ss mempty
  where
    go [] acc = key tag WBytes <> packed acc
    go (s : rest) acc = withIndex s (\i -> go rest (acc <> varint (fromIntegral i)))

    packed inner =
      Enc $ \table ->
        case runEnc inner table of
          Bad problems -> Bad problems
          Piece n b more -> runEnc (varint (fromIntegral n)) table <> Piece n b more

-- | The table itself, written at tag 1 so that rule 1 puts it on the wire ahead
-- of everything that indexes into it.
stringTable :: Enc
stringTable =
  Enc $ \table ->
    case table of
      Collecting -> mempty
      Resolved m -> runEnc (foldMap rawText (Map.keys m)) table
  where
    rawText s =
      let n = Utf8.size s
       in key 1 WBytes <> varint (fromIntegral n) <> bytes n (Utf8.toBuilder s)

-- MESSAGES

-- | A submessage: always written, because a message field has explicit presence.
msg :: Word32 -> Enc -> Enc
msg tag inner =
  Enc $ \table ->
    case runEnc inner table of
      Bad problems -> Bad problems
      Piece n b more ->
        runEnc (key tag WBytes <> varint (fromIntegral n)) table <> Piece n b more

-- | An @optional@ submessage.
optMsg :: Word32 -> (a -> Enc) -> Maybe a -> Enc
optMsg _ _ Nothing = mempty
optMsg tag f (Just a) = msg tag (f a)

-- | @repeated@ of a message type. Records with one tag, in list order — which
-- is C14\'s order for a binding list, and the schema\'s stated order elsewhere.
rep :: Word32 -> (a -> Enc) -> [a] -> Enc
rep tag f = foldMap (msg tag . f)

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
  stringTable
    <> msg 2 (moduleNameEnc (_moduleName m))
    <> rep 3 fileEntryEnc (Map.toAscList (_moduleFiles m))
    <> rep 4 dataDeclEnc (_moduleData m)
    <> rep 5 classDeclEnc (_moduleClasses m)
    <> rep 6 instanceDeclEnc (_moduleInstances m)
    <> rep 7 bindEnc (_moduleDefs m)
    <> rep 8 recGroupEnc (_moduleDefsRec m)
    <> rep 9 qualEnc (_moduleExports m)
    <> optMsg 10 managerEnc (_moduleManager m)
    <> rep 11 portEnc (_modulePorts m)
    <> optMsg 12 mainEnc (_moduleMain m)

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
      | otherwise -> lift (Bad [legacyProblem n])

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
