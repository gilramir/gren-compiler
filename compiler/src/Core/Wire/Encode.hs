{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoPolyKinds #-}
{-# OPTIONS_GHC -Wall #-}

-- | Core to bytes, against @schema/geng/core/v4.proto@.
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
import Data.List qualified as List
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
  | Resolved !(Map.Map Str Int) !(Map.Map QualName Int) !(Map.Map Type Int)

-- | Bytes and how many of them there are — or the strings they would need, or
-- the reasons there are none.
--
-- The failure case exists for exactly one rule, D91\'s: 'LIntLegacy' carries an
-- unbounded 'Integer' and the wire format carries a @sint64@. Accumulating the
-- messages rather than stopping at the first means a module with three
-- out-of-range literals reports three, which is what a person fixing them wants.
data Piece
  = Piece !Int B.Builder ![Str] ![QualName] ![Type]
  | Bad [String]

instance Semigroup Piece where
  Bad a <> Bad b = Bad (a ++ b)
  Bad a <> _ = Bad a
  _ <> Bad b = Bad b
  Piece n1 b1 s1 q1 t1 <> Piece n2 b2 s2 q2 t2 =
    Piece (n1 + n2) (b1 <> b2) (s1 ++ s2) (q1 ++ q2) (t1 ++ t2)

instance Monoid Piece where
  mempty = Piece 0 mempty [] [] []

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
    Piece _ _ strings quals types ->
      let stringTbl = Map.fromList (zip (Set.toAscList (Set.fromList strings)) [1 ..])
          qualTbl = Map.fromList (zip (List.sortBy qualOrder (Set.toList (Set.fromList quals))) [1 ..])
          typeTbl = buildTypes stringTbl qualTbl types
       in case runEnc enc (Resolved stringTbl qualTbl typeTbl) of
            Bad problems -> Left problems
            Piece _ builder _ _ _ -> Right builder

-- | The order D93 states, and it is __not__ the derived one.
--
-- @Ord QualName@ compares '_qnHome' first, and @Ord ModuleName.Canonical@
-- compares the /module/ before the /package/ — so the derived order is
-- (module, author, project, name), which is a perfectly good total order and a
-- surprising thing for a second frontend to have to reproduce. C6's whole
-- discipline is that an order which is not written down is a dependency on a
-- container's implementation, and this is that hazard in its purest form: the
-- instance is right there, it works, and reading it is the only way to find out
-- what it does.
--
-- Strings got away with the derived instance because @Ord (Utf8 t)@ /is/ UTF-8
-- byte order — checked, not assumed. This one does not, so it is written out.
qualOrder :: QualName -> QualName -> Ordering
qualOrder (QualName (ModuleName.Canonical (Pkg.Name a1 p1) m1) n1) (QualName (ModuleName.Canonical (Pkg.Name a2 p2) m2) n2) =
  compare (str a1) (str a2)
    <> compare (str p1) (str p2)
    <> compare (str m1) (str m2)
    <> compare (str n1) (str n2)

-- | The type table's order, D94's, and the reason it is built one height at a
-- time.
--
-- __By height, then by content: the constructor's tag, then the member's fields
-- left to right, each list compared by its length and then element by element,
-- and every leaf compared as its index in the table it points into.__
--
-- Height first is not a preference, it is what hash-consing needs. A type is
-- taller than every type inside it, so ordering by height puts each entry after
-- everything it references — which is what lets the reader resolve an entry the
-- moment it has read it, and makes a forward reference a hard error rather than
-- a second pass. Within one height, every child already has an index, so the
-- rest of the key is integers and 'typeSortKey' can build it without recursing.
--
-- __Comparing a leaf by its index is still an order stated over the content__,
-- which is what D93 said a sort rule has to be. Index order in the string table
-- /is/ UTF-8 byte order and index order in the name table /is/
-- (author, project, module, name), because each of those tables is itself
-- sorted by its content. The indirection buys the shorter key and costs nothing
-- a second frontend has to know beyond the two orders it already knows.
--
-- The key is injective, which is what stops the sort below leaking the order
-- @Set.toList@ happened to produce: the tag says which constructor, the counted
-- lists say where each field ends, and an index determines its entry, so two
-- types with the same key are the same type.
buildTypes :: Map.Map Str Int -> Map.Map QualName Int -> [Type] -> Map.Map Type Int
buildTypes strings quals types =
  List.foldl' assign Map.empty (Map.elems byHeight)
  where
    byHeight :: Map.Map Int [Type]
    byHeight = Map.fromListWith (++) [(typeHeight t, [t]) | t <- Set.toList (Set.fromList types)]

    assign table group =
      List.foldl'
        (\m (i, t) -> Map.insert t i m)
        table
        (zip [Map.size table + 1 ..] (List.sortOn (typeSortKey strings quals table) group))

-- | One more than the tallest type inside it; a 'TVar' is 1.
typeHeight :: Type -> Int
typeHeight t =
  case t of
    TVar _ -> 1
    TCon _ args -> 1 + tallest args
    TFun args result -> 1 + tallest (result : args)
    TRecord fields _ -> 1 + tallest (map snd fields)
    TForall _ constraints body -> 1 + tallest (body : [c | CClass _ c <- constraints])
  where
    tallest = foldr (max . typeHeight) 0

-- | The rest of 'buildTypes'\' key, over a table that already holds every type
-- shorter than this one.
typeSortKey :: Map.Map Str Int -> Map.Map QualName Int -> Map.Map Type Int -> Type -> [Int]
typeSortKey strings quals table = keyOf
  where
    keyOf t =
      case t of
        TVar name -> [1, strIx name]
        TCon name args -> 2 : qualIx name : counted [[typeIx a] | a <- args]
        TFun args result -> 3 : counted [[typeIx a] | a <- args] ++ [typeIx result]
        TRecord fields row ->
          4 : counted [[strIx f, typeIx ft] | (f, ft) <- fields] ++ maybe [0] (\r -> [1, strIx r]) row
        TForall vars constraints body ->
          5
            : counted [[strIx v] | v <- vars]
            ++ counted [[qualIx c, typeIx ct] | CClass c ct <- constraints]
            ++ [typeIx body]

    counted xs = length xs : concat xs

    strIx s = fromIntegral (indexOf strings (str s))
    qualIx q = Map.findWithDefault 0 q quals
    typeIx t = Map.findWithDefault 0 t table

-- PRIMITIVES

varintP :: Word64 -> Piece
varintP n = Piece (varintSize n) (go n) [] [] []
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
bytes n b = lift (Piece n b [] [] [])

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
                  Piece _ _ more quals types -> Piece 0 mempty (collected ++ more) quals types
          Resolved m _ _ -> runEnc (what (indexOf m s)) table

-- QUALIFIED NAMES
--
-- D93: a `QualName` is a 1-based index into the module's name table, and 0 is
-- absent. Version 2 had already made its strings indices; what was left at every
-- occurrence was the *shape* -- a nested message with a key, a length and three
-- varints -- and that is what this removes.

-- | Collect a qualified name on the first pass, and do @what@ with its index on
-- the second.
withQual :: QualName -> (Word32 -> Enc) -> Enc
withQual q what =
  Enc $ \table ->
    case table of
      Collecting ->
        case runEnc (what 0) Collecting of
          Bad problems -> Bad problems
          Piece _ _ strings more types -> Piece 0 mempty (qualStrings q ++ strings) (q : more) types
      Resolved _ m _ ->
        case Map.lookup q m of
          Just i -> runEnc (what (fromIntegral i)) table
          Nothing ->
            -- Unreachable, for 'indexOf'\'s reason: one 'Enc', run twice.
            Bad ["Core.Wire.Encode: a qualified name is not in the name table"]

-- | The four strings a qualified name is made of.
--
-- 'withQual' has to report these as well as the name itself, and forgetting to
-- was the one bug this change had: the name table's entries index into the
-- __string__ table, so a qualified name that is only ever seen as an index
-- still puts four strings in the table it indexes into. The two tables are not
-- independent, and the collecting pass is where that shows.
qualStrings :: QualName -> [Str]
qualStrings (QualName (ModuleName.Canonical (Pkg.Name author project) modul) name) =
  filter (\s -> Utf8.size s > 0) [str author, str project, str modul, str name]

-- | A qualified-name field. Every one of them is required where it appears, so
-- there is no index 0 to write and rule 5 has nothing to skip.
qual :: Word32 -> QualName -> Enc
qual tag q = withQual q (u32 tag)

-- | An @optional@ qualified name: explicit presence.
optQual :: Word32 -> Maybe QualName -> Enc
optQual _ Nothing = mempty
optQual tag (Just q) = withQual q (\i -> key tag WVarint <> varint (fromIntegral i))

-- | @repeated uint32@ of qualified names, packed like 'repText'.
repQual :: Word32 -> [QualName] -> Enc
repQual _ [] = mempty
repQual tag qs = go qs mempty
  where
    go [] acc = key tag WBytes <> packedRun acc
    go (q : rest) acc = withQual q (\i -> go rest (acc <> varint (fromIntegral i)))

-- TYPES
--
-- D94: a `Type` is a 1-based index into the module's type table, and the table
-- is hash-consed -- a type nested inside another is an index into the same
-- table rather than bytes inside its parent's entry. Version 3 had already made
-- a `TCon`'s head one varint; what was left was that 83,566 type occurrences in
-- the corpus were 4,084 distinct types, each written out at every occurrence.

-- | Collect a type on the first pass, and do @what@ with its index on the
-- second.
--
-- The collecting side runs @typeEnc t@ rather than inspecting the type, which
-- is what makes the recursion free: 'typeEnc' writes a nested type through
-- 'typ' or 'repType', so running it collects every type inside @t@, along with
-- every string and qualified name any of them mentions. That is D93's bug in
-- its deeper form — a table's entries index into the tables before it — and
-- the fix is the same shape: whatever the entry would write, the collecting
-- pass has to have reported.
withType :: Type -> (Word32 -> Enc) -> Enc
withType t what =
  Enc $ \table ->
    case table of
      Collecting ->
        case runEnc (typeEnc t) Collecting of
          Bad problems -> Bad problems
          Piece _ _ strings quals inner ->
            case runEnc (what 0) Collecting of
              Bad problems -> Bad problems
              Piece _ _ strings' quals' more ->
                Piece 0 mempty (strings ++ strings') (quals ++ quals') (t : inner ++ more)
      Resolved _ _ m ->
        case Map.lookup t m of
          Just i -> runEnc (what (fromIntegral i)) table
          Nothing ->
            -- Unreachable, for 'indexOf'\'s reason: one 'Enc', run twice.
            Bad ["Core.Wire.Encode: a type is not in the type table"]

-- | A type field. Every one of them is required where it appears, so there is
-- no index 0 to write and rule 5 has nothing to skip.
typ :: Word32 -> Type -> Enc
typ tag t = withType t (u32 tag)

-- | @repeated uint32@ of types, packed like 'repText'.
repType :: Word32 -> [Type] -> Enc
repType _ [] = mempty
repType tag ts = go ts mempty
  where
    go [] acc = key tag WBytes <> packedRun acc
    go (t : rest) acc = withType t (\i -> go rest (acc <> varint (fromIntegral i)))

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
    go [] acc = key tag WBytes <> packedRun acc
    go (s : rest) acc = withIndex s (\i -> go rest (acc <> varint (fromIntegral i)))

-- | A packed payload: its own length, then the varints.
packedRun :: Enc -> Enc
packedRun inner =
  Enc $ \table ->
    case runEnc inner table of
      Bad problems -> Bad problems
      Piece n b more quals types ->
        runEnc (varint (fromIntegral n)) table <> Piece n b more quals types

-- | The table itself, written at tag 1 so that rule 1 puts it on the wire ahead
-- of everything that indexes into it.
stringTable :: Enc
stringTable =
  Enc $ \table ->
    case table of
      Collecting -> mempty
      Resolved m _ _ -> runEnc (foldMap rawText (Map.keys m)) table
  where
    rawText s =
      let n = Utf8.size s
       in key 1 WBytes <> varint (fromIntegral n) <> bytes n (Utf8.toBuilder s)

-- | The name table at tag 2, in 'qualOrder'. Its entries index into the string
-- table, which is why that one is tag 1.
qualTable :: Enc
qualTable =
  Enc $ \table ->
    case table of
      Collecting -> mempty
      Resolved _ m _ ->
        runEnc
          (foldMap (msg 2 . rawQual) (List.sortBy qualOrder (Map.keys m)))
          table
  where
    rawQual (QualName home name) = msg 1 (moduleNameEnc home) <> text 2 name

-- | The type table at tag 3, in the order 'buildTypes' assigned. Its entries
-- index into both tables before it and into itself, which is why it is last of
-- the three.
typeTable :: Enc
typeTable =
  Enc $ \table ->
    case table of
      Collecting -> mempty
      Resolved _ _ m ->
        runEnc (foldMap (msg 3 . typeEnc) (map fst (List.sortOn snd (Map.toList m)))) table

-- MESSAGES

-- | A submessage: always written, because a message field has explicit presence.
msg :: Word32 -> Enc -> Enc
msg tag inner =
  Enc $ \table ->
    case runEnc inner table of
      Bad problems -> Bad problems
      Piece n b more quals types ->
        runEnc (key tag WBytes <> varint (fromIntegral n)) table <> Piece n b more quals types

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
    TCon name args -> msg 2 (qual 1 name <> repType 2 args)
    TFun args result -> msg 3 (repType 1 args <> typ 2 result)
    TRecord fields row ->
      msg 4 (rep 1 fieldTypeEnc fields <> optText 2 row)
    TForall vars constraints body ->
      msg 5 (repText 1 vars <> rep 2 constraintEnc constraints <> typ 3 body)

fieldTypeEnc :: (Field, Type) -> Enc
fieldTypeEnc (field, t) = text 1 field <> typ 2 t

constraintEnc :: Constraint -> Enc
constraintEnc (CClass cls t) = qual 1 cls <> typ 2 t

-- DECLARATIONS

dataDeclEnc :: DataDecl -> Enc
dataDeclEnc (DataDecl name params transparency ctors classes) =
  qual 1 name
    <> repText 2 params
    <> enum_ 3 (transparencyCode transparency)
    <> rep 4 ctorEnc ctors
    <> repQual 5 classes

ctorEnc :: Ctor -> Enc
ctorEnc (Ctor name tag fields) =
  qual 1 name
    <> u32 2 (fromIntegral tag)
    <> repType 3 fields

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
  qual 1 name
    <> text 2 param
    <> enum_ 3 (opennessCode openness)
    <> rep 4 methodSigEnc methods

methodSigEnc :: (Name.Name, Type) -> Enc
methodSigEnc (name, t) = text 1 name <> typ 2 t

instanceDeclEnc :: InstanceDecl -> Enc
instanceDeclEnc (InstanceDecl cls head_ origin methods) =
  qual 1 cls
    <> typ 2 head_
    <> enum_ 3 (originCode origin)
    <> rep 4 methodImplEnc methods

methodImplEnc :: (Name.Name, Expr) -> Enc
methodImplEnc (name, body) = text 1 name <> msg 2 (exprEnc body)

-- MODULE

moduleEnc :: Module -> Enc
moduleEnc m =
  stringTable
    <> qualTable
    <> typeTable
    <> msg 4 (moduleNameEnc (_moduleName m))
    <> rep 5 fileEntryEnc (Map.toAscList (_moduleFiles m))
    <> rep 6 dataDeclEnc (_moduleData m)
    <> rep 7 classDeclEnc (_moduleClasses m)
    <> rep 8 instanceDeclEnc (_moduleInstances m)
    <> rep 9 bindEnc (_moduleDefs m)
    <> rep 10 recGroupEnc (_moduleDefsRec m)
    <> repQual 11 (_moduleExports m)
    <> optMsg 12 managerEnc (_moduleManager m)
    <> rep 13 portEnc (_modulePorts m)
    <> optMsg 14 mainEnc (_moduleMain m)

recGroupEnc :: [QualName] -> Enc
recGroupEnc names = repQual 1 names

mainEnc :: Main -> Enc
mainEnc main_ =
  case main_ of
    MainString -> enum_ 1 0
    MainHtml -> enum_ 1 1
    MainProgram converter -> enum_ 1 2 <> msg 2 (converterEnc converter)

managerEnc :: Manager -> Enc
managerEnc (Manager kind entries init_ onEffects onSelfMsg cmdMap subMap) =
  enum_ 1 (managerKindCode kind)
    <> repQual 2 entries
    <> qual 3 init_
    <> qual 4 onEffects
    <> qual 5 onSelfMsg
    <> optQual 6 cmdMap
    <> optQual 7 subMap

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
  typ 1 t
    <> msg 2 (spanEnc s)
    <> nodeEnc node

nodeEnc :: Expr_ -> Enc
nodeEnc node =
  case node of
    EVar n -> oneofText 3 n
    EGlobal q -> withQual q (\i -> key 4 WVarint <> varint (fromIntegral i))
    ELit l -> msg 5 (literalEnc l)
    ELam binders body -> msg 6 (absEnc binders body)
    EApp fn args -> msg 7 (appEnc fn args)
    ELet binds body -> msg 8 (bindsEnc binds body)
    ELetRec binds body -> msg 9 (bindsEnc binds body)
    ECase scrut alts fallback ->
      msg 10 (msg 1 (exprEnc scrut) <> rep 2 altEnc alts <> optMsg 3 exprEnc fallback)
    ECtor name tag args ->
      msg 11 (qual 1 name <> u32 2 (fromIntegral tag) <> rep 3 exprEnc args)
    ERecord fields -> msg 12 (rep 1 fieldExprEnc fields)
    EUpdate base fields -> msg 13 (msg 1 (exprEnc base) <> rep 2 fieldExprEnc fields)
    EAccess base field -> msg 14 (msg 1 (exprEnc base) <> text 2 field)
    EArray items -> msg 15 (rep 1 exprEnc items)
    EPrim op args ->
      msg 16 (u32 1 (fromIntegral (Prim.primCode op)) <> rep 2 exprEnc args)
    EJoin binds body -> msg 17 (bindsEnc binds body)
    EJump j args -> msg 18 (text 1 j <> rep 2 exprEnc args)
    ETyLam vars body -> msg 19 (repText 1 vars <> msg 2 (exprEnc body))
    ETyApp fn args -> msg 20 (msg 1 (exprEnc fn) <> repType 2 args)
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
    <> typ 2 t
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
      msg 4 (qual 1 name <> u32 2 (fromIntegral tag) <> rep 3 patternEnc args)
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
