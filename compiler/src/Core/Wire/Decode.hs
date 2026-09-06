{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoPolyKinds #-}
{-# OPTIONS_GHC -Wall #-}

-- | Bytes to Core, against @schema/geng/core/v2.proto@.
--
-- __The reader enforces the canonical profile__ (§B7). C10 writes its seven
-- rules as properties of the writer; making them properties of the reader too
-- is what turns them from a convention into something checkable, and it is what
-- makes a subtle encoder bug — a field at the wrong position, a repeated field
-- that should have been singular — a loud failure at the next read rather than a
-- byte difference discovered at M4.
--
-- __The profile is why this module is short.__ Rule 1 says fields arrive in
-- ascending tag order, so a message is read by walking the schema's fields in
-- order and taking each one if it is next. That walk *is* rule 1's check: a
-- field out of position is simply not there when its turn comes, and is then an
-- unexpected tag at the end of the message. There is no field dispatch table, no
-- accumulator record and no post-hoc ordering check anywhere below.
--
-- What each rule costs here:
--
--   1. ascending order — free, as above
--   2. minimal varints — 'varint' refuses a redundant continuation byte
--   3. packed repeated scalars — /vacuous/. Only numeric scalars can be packed
--      and this schema has no repeated numeric scalar field at all.
--   4. no maps — 'fileTable' refuses entries that are not strictly ascending
--   5. absent, never present-with-default — 'defaulted' refuses the default
--   6. unknown fields — 'end' refuses anything left over
--   7. no @Any@, no extensions — nothing to do
module Core.Wire.Decode
  ( P,
    runP,
    moduleP,
  )
where

import Control.Monad (unless, when)
import Core.AST
import Core.Prim qualified as Prim
import Core.Wire.Protobuf
import Data.Bits (shiftL, testBit, (.&.), (.|.))
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe qualified as BS
import Data.Coerce qualified as Coerce
import Data.Map qualified as Map
import Data.Name qualified as Name
import Data.Utf8 qualified as Utf8
import Data.Word (Word32, Word64, Word8)
import GHC.Float (castWord32ToFloat, castWord64ToDouble)
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg

-- THE PARSER

-- | A slice of the file, and where in the file it starts. Submessage parsing is
-- slicing, which on a strict 'BS.ByteString' costs nothing, and the base keeps
-- an error's offset meaningful in the whole file rather than in the slice.
data Input = Input
  { _buf :: !BS.ByteString,
    _base :: !Int
  }

-- | The path an error will name, and the module's string table (D92).
--
-- The table is in the environment rather than threaded as an argument because
-- every string in the module is an index into it and there are thirty fields
-- that hold one; it is empty until 'withTable' sets it, which 'moduleP' does
-- the moment it has read tag 1.
data Env = Env
  { _path :: ![String],
    _strings :: !(Map.Map Int Str)
  }

-- | Every string in a module, as one type. 'Core.Wire.Encode' says why the
-- phantom parameter is coerced away here and nowhere else.
data WIRE_STRING

type Str = Utf8.Utf8 WIRE_STRING

unStr :: Str -> Utf8.Utf8 t
unStr = Coerce.coerce

newtype P a = P {unP :: Env -> Input -> Either Error (a, Input)}

instance Functor P where
  fmap f (P g) = P (\env i -> fmap (\(a, i') -> (f a, i')) (g env i))

instance Applicative P where
  pure a = P (\_ i -> Right (a, i))
  P f <*> P g =
    P
      ( \env i -> do
          (h, i1) <- f env i
          (a, i2) <- g env i1
          Right (h a, i2)
      )

instance Monad P where
  P g >>= f =
    P
      ( \env i -> do
          (a, i1) <- g env i
          unP (f a) env i1
      )

runP :: P a -> BS.ByteString -> Int -> Either Error a
runP p buf base =
  fmap fst (unP p (Env [] Map.empty) (Input buf base))

-- | Push a field name onto the path an error will name.
inField :: String -> P a -> P a
inField name (P g) = P (\env i -> g env {_path = name : _path env} i)

failAt :: Int -> String -> P a
failAt at why = P (\env _ -> Left (Error at (_path env) why))

failP :: String -> P a
failP why = P (\env i -> Left (Error (_base i) (_path env) why))

-- BYTES

takeByte :: P Word8
takeByte =
  P
    ( \env i ->
        case BS.uncons (_buf i) of
          Nothing -> Left (Error (_base i) (_path env) "ran off the end of the message")
          Just (w, rest) -> Right (w, Input rest (_base i + 1))
    )

takeBytes :: Int -> P BS.ByteString
takeBytes n =
  P
    ( \env i ->
        if BS.length (_buf i) < n
          then Left (Error (_base i) (_path env) ("wanted " ++ show n ++ " bytes and the message has " ++ show (BS.length (_buf i))))
          else Right (BS.unsafeTake n (_buf i), Input (BS.unsafeDrop n (_buf i)) (_base i + n))
    )

isEnd :: P Bool
isEnd = P (\_ i -> Right (BS.null (_buf i), i))

offset :: P Int
offset = P (\_ i -> Right (_base i, i))

-- | Rule 2. A varint whose last byte is @0x00@ and which is longer than one
-- byte has a redundant group; ten bytes is the most any 64-bit value takes, and
-- the tenth may only carry the single bit that is left.
varint :: P Word64
varint =
  do
    start <- offset
    go start 0 0
  where
    go start !shift !acc =
      do
        w <- takeByte
        let acc' = acc .|. (fromIntegral (w .&. 0x7f) `shiftL` shift)
        if testBit w 7
          then
            if shift >= 63
              then failAt start "varint is longer than ten bytes"
              else go start (shift + 7) acc'
          else
            if shift > 0 && (w .&. 0x7f) == 0
              then failAt start "varint is not minimally encoded"
              else
                if shift == 63 && w > 1
                  then failAt start "varint overflows 64 bits"
                  else pure acc'

-- FIELDS

-- | Look at the next field's key without consuming it.
peekKey :: P (Maybe Word64)
peekKey =
  P
    ( \env i ->
        if BS.null (_buf i)
          then Right (Nothing, i)
          else case unP varint env i of
            Left e -> Left e
            Right (k, _) -> Right (Just k, i)
    )

-- | Take the field with this tag if it is the next one, and check its wire type.
next :: String -> Word32 -> WireType -> P a -> P (Maybe a)
next name tag wire body =
  do
    peeked <- peekKey
    case peeked of
      Just k | keyTag k == tag ->
        inField name $
          do
            here <- offset
            _ <- varint
            case keyWire k of
              Just w | w == wire -> Just <$> body
              _ -> failAt here ("field " ++ show tag ++ " has the wrong wire type")
      _ -> pure Nothing

-- | A length-delimited payload, read by a parser that must consume all of it.
submessage :: P a -> P a
submessage body =
  do
    n <- varint
    slice <- takeBytes (fromIntegral n)
    P
      ( \env i ->
          case unP body env (Input slice (_base i - fromIntegral n)) of
            Left e -> Left e
            Right (a, _) -> Right (a, i)
      )

-- | A message: its fields in order, then nothing left over.
--
-- @highest@ is the largest tag the message has, and it is the whole of what
-- distinguishes rule 1's failure from rule 6's in the error text.
message :: String -> Word32 -> P a -> P a
message name highest body =
  inField name $
    do
      a <- body
      done <- isEnd
      unless done $
        do
          here <- offset
          k <- peekKey
          case k of
            Nothing -> pure ()
            Just key ->
              let tag = keyTag key
               in failAt
                    here
                    ( if tag <= highest
                        then "field " ++ show tag ++ " is out of order or repeated"
                        else "unknown field " ++ show tag
                    )
      pure a

-- | An implicit-presence field: absent means the default, and the default
-- written out is rule 5's violation.
defaulted :: (Eq a, Show a) => String -> Word32 -> WireType -> a -> P a -> P a
defaulted name tag wire dflt body =
  do
    here <- offset
    got <- next name tag wire body
    case got of
      Nothing -> pure dflt
      Just a
        | a == dflt -> failAt here ("field " ++ show tag ++ " is present holding its default " ++ show a)
        | otherwise -> pure a

u32 :: String -> Word32 -> P Word32
u32 name tag = fromIntegral <$> defaulted name tag WVarint (0 :: Word64) varint

-- | @bool@, implicit presence. Absent is 'False'; @False@ written out is rule
-- 5's violation, and anything but 0 or 1 is not a boolean at all.
bool_ :: String -> Word32 -> P Bool
bool_ name tag =
  do
    here <- offset
    got <- next name tag WVarint varint
    case got of
      Nothing -> pure False
      Just 1 -> pure True
      Just 0 -> failAt here ("field " ++ show tag ++ " is present holding its default False")
      Just n -> failAt here ("field " ++ show tag ++ " is " ++ show n ++ " and not a boolean")

-- | An enum, implicit presence. Absent means code 0, and code 0 written out is
-- rule 5's violation, so the zero constructor is reached only by absence.
enum_ :: String -> Word32 -> (Word32 -> Maybe a) -> P a
enum_ name tag from =
  do
    here <- offset
    code <- defaulted name tag WVarint (0 :: Word64) varint
    case from (fromIntegral code) of
      Just a -> pure a
      Nothing -> failAt here ("field " ++ show tag ++ " has no such enum value: " ++ show code)

-- | A length-delimited run of UTF-8 bytes. Only the string table holds these
-- now; everywhere else a string is an index into it (D92).
utf8 :: P Str
utf8 =
  do
    here <- offset
    n <- varint
    raw <- takeBytes (fromIntegral n)
    if validUtf8 raw
      then pure (Utf8.fromByteString raw)
      else failAt here "string is not valid UTF-8"

-- | A 1-based index into the module's string table; 0 is the empty string and
-- is not an entry.
resolve :: Word64 -> P (Utf8.Utf8 t)
resolve 0 = pure (Utf8.fromByteString BS.empty)
resolve i =
  do
    table <- P (\env input -> Right (_strings env, input))
    case Map.lookup (fromIntegral i) table of
      Just s -> pure (unStr s)
      Nothing -> failP ("string index " ++ show i ++ " is past the end of the table")

-- | A string field, implicit presence. Absent is index 0 is the empty string,
-- which is what an absent `string` meant in version 1, and index 0 written out
-- is rule 5's violation.
text :: String -> Word32 -> P (Utf8.Utf8 t)
text name tag = resolve =<< defaulted name tag WVarint (0 :: Word64) varint

-- | A @oneof@ member of string type: always written, so index 0 is legitimate.
indexText :: P (Utf8.Utf8 t)
indexText = resolve =<< varint

-- | An @optional@ string: explicit presence, so index 0 is a legitimate value.
optText :: String -> Word32 -> P (Maybe (Utf8.Utf8 t))
optText name tag =
  do
    got <- next name tag WVarint varint
    case got of
      Nothing -> pure Nothing
      Just i -> Just <$> resolve i

msg :: String -> Word32 -> P a -> P a
msg name tag body =
  do
    got <- next name tag WBytes (submessage body)
    case got of
      Just a -> pure a
      Nothing -> failP ("field " ++ show tag ++ " (" ++ name ++ ") is missing")

optMsg :: String -> Word32 -> P a -> P (Maybe a)
optMsg name tag body = next name tag WBytes (submessage body)

rep :: String -> Word32 -> P a -> P [a]
rep name tag body = go id
  where
    go acc =
      do
        got <- next name tag WBytes (submessage body)
        case got of
          Nothing -> pure (acc [])
          Just a -> go (acc . (a :))

-- | @repeated uint32@, packed — rule 3\'s first instance in this schema, since
-- version 2 turned a list of names into a list of indices. An absent field is
-- the empty list, and a present-but-empty one is rule 5\'s violation.
repText :: String -> Word32 -> P [Utf8.Utf8 t]
repText name tag =
  do
    here <- offset
    got <- next name tag WBytes (submessage packedVarints)
    case got of
      Nothing -> pure []
      Just [] -> failAt here ("field " ++ show tag ++ " is present holding its default []")
      Just indices -> mapM resolve indices

-- | Varints to the end of a packed payload.
packedVarints :: P [Word64]
packedVarints = go id
  where
    go acc =
      do
        done <- isEnd
        if done
          then pure (acc [])
          else do
            n <- varint
            go (acc . (n :))

-- | The table, and the two things about it a second frontend has to reproduce:
-- every entry non-empty, and the whole in strictly ascending UTF-8 byte order.
-- Checked rather than assumed, for C10\'s reason — two frontends that disagreed
-- about the order would produce two files with the same meaning and different
-- bytes.
stringTable :: P [Str]
stringTable = go id
  where
    go acc =
      do
        got <- next "strings" 1 WBytes utf8
        case got of
          Nothing -> pure (acc [])
          Just s -> go (acc . (s :))

withTable :: [Str] -> P a -> P a
withTable strings body =
  do
    unless (all ((> 0) . Utf8.size) strings) $
      failP "the string table has an empty entry"
    unless (and (zipWith (<) strings (drop 1 strings))) $
      failP "the string table is not in strictly ascending UTF-8 byte order"
    let table = Map.fromList (zip [1 ..] strings)
    P (\env input -> unP body env {_strings = table} input)

-- | A @oneof@: exactly one member, and it is written even when it holds its
-- type's default, so there is no rule 5 here.
oneof :: String -> [(Word32, WireType, P a)] -> P a
oneof name members =
  inField name $
    do
      here <- offset
      peeked <- peekKey
      case peeked of
        Nothing -> failAt here (name ++ " has no member set")
        Just key ->
          case lookupMember (keyTag key) members of
            Nothing -> failAt here (name ++ " has no member " ++ show (keyTag key))
            Just (wire, body) ->
              do
                _ <- varint
                case keyWire key of
                  Just w | w == wire -> body
                  _ -> failAt here (name ++ " member " ++ show (keyTag key) ++ " has the wrong wire type")

lookupMember :: Word32 -> [(Word32, WireType, P a)] -> Maybe (WireType, P a)
lookupMember _ [] = Nothing
lookupMember tag ((t, w, p) : rest)
  | t == tag = Just (w, p)
  | otherwise = lookupMember tag rest

-- | Rule 3 is vacuous and this is where it would go: nothing in the schema is a
-- repeated numeric scalar, so nothing is ever packed, and a length-delimited
-- payload on a varint field is caught as a wire-type mismatch by 'next'.

-- UTF-8

-- | Whether the bytes are well-formed UTF-8, by the Unicode table: no
-- overlongs, no surrogates, nothing above U+10FFFF. 'Utf8.fromByteString' takes
-- bytes as they stand, so this is where the question is asked — the alternative
-- is a 'Core.AST.Text' that is not text, which is exactly what C10's
-- byte-identical gate cannot rest on.
validUtf8 :: BS.ByteString -> Bool
validUtf8 = go . BS.unpack
  where
    go [] = True
    go (b : rest)
      | b < 0x80 = go rest
      | b < 0xc2 = False
      | b < 0xe0 = cont 1 rest
      | b == 0xe0 = range 0xa0 0xbf 1 rest
      | b < 0xed = cont 2 rest
      | b == 0xed = range 0x80 0x9f 1 rest
      | b < 0xf0 = cont 2 rest
      | b == 0xf0 = range 0x90 0xbf 2 rest
      | b < 0xf4 = cont 3 rest
      | b == 0xf4 = range 0x80 0x8f 2 rest
      | otherwise = False

    cont 0 rest = go rest
    cont n (b : rest) | b >= 0x80 && b <= 0xbf = cont (n - 1 :: Int) rest
    cont _ _ = False

    range lo hi n (b : rest) | b >= lo && b <= hi = cont n rest
    range _ _ _ _ = False

-- NAMES

moduleNameP :: P ModuleName.Canonical
moduleNameP =
  message "ModuleName" 3 $
    do
      author <- text "author" 1
      project <- text "project" 2
      modul <- text "module" 3
      pure (ModuleName.Canonical (Pkg.Name author project) modul)

qualP :: P QualName
qualP =
  message "QualName" 2 $
    do
      home <- msg "home" 1 moduleNameP
      name <- text "name" 2
      pure (QualName home name)

-- SPANS

spanP :: P Span
spanP =
  message "Span" 5 $
    do
      file <- u32 "file" 1
      sr <- u32 "start_row" 2
      sc <- u32 "start_col" 3
      er <- u32 "end_row" 4
      ec <- u32 "end_col" 5
      pure (Span (FileId (fromIntegral file)) sr sc er ec)

-- | Rule 4: a map is a repeated key-value message sorted by key, and "sorted"
-- is checked rather than assumed. Two frontends that disagreed about the order
-- would produce two files with the same meaning and different bytes, which is
-- the one thing C10 exists to prevent.
fileTable :: [(FileId, ModuleName.Canonical)] -> P FileTable
fileTable entries =
  do
    let keys = map fst entries
    unless (and (zipWith (<) keys (drop 1 keys))) $
      failP "the file table is not in strictly ascending key order"
    pure (Map.fromList entries)

fileEntryP :: P (FileId, ModuleName.Canonical)
fileEntryP =
  message "FileEntry" 2 $
    do
      i <- u32 "id" 1
      home <- msg "name" 2 moduleNameP
      pure (FileId (fromIntegral i), home)

-- TYPES

typeP :: P Type
typeP =
  message "Type" 5 $
    oneof
      "type"
      [ (1, WVarint, TVar <$> indexText),
        (2, WBytes, submessage tconP),
        (3, WBytes, submessage tfunP),
        (4, WBytes, submessage trecordP),
        (5, WBytes, submessage tforallP)
      ]

tconP :: P Type
tconP =
  message "TCon" 2 $
    do
      name <- msg "name" 1 qualP
      args <- rep "args" 2 typeP
      pure (TCon name args)

tfunP :: P Type
tfunP =
  message "TFun" 2 $
    do
      args <- rep "args" 1 typeP
      result <- msg "result" 2 typeP
      pure (TFun args result)

trecordP :: P Type
trecordP =
  message "TRecord" 2 $
    do
      fields <- rep "fields" 1 fieldTypeP
      row <- optText "row" 2
      pure (TRecord fields row)

fieldTypeP :: P (Field, Type)
fieldTypeP =
  message "FieldType" 2 $
    do
      field <- text "field" 1
      t <- msg "type" 2 typeP
      pure (field, t)

tforallP :: P Type
tforallP =
  message "TForall" 3 $
    do
      vars <- repText "vars" 1
      constraints <- rep "constraints" 2 constraintP
      body <- msg "body" 3 typeP
      pure (TForall vars constraints body)

constraintP :: P Constraint
constraintP =
  message "Constraint" 2 $
    do
      cls <- msg "class_name" 1 qualP
      t <- msg "type" 2 typeP
      pure (CClass cls t)

-- DECLARATIONS

dataDeclP :: P DataDecl
dataDeclP =
  message "DataDecl" 5 $
    do
      name <- msg "name" 1 qualP
      params <- repText "params" 2
      transparency <- enum_ "transparency" 3 transparencyFromCode
      ctors <- rep "ctors" 4 ctorP
      classes <- rep "classes" 5 qualP
      pure (DataDecl name params transparency ctors classes)

ctorP :: P Ctor
ctorP =
  message "Ctor" 3 $
    do
      name <- msg "name" 1 qualP
      tag <- u32 "tag" 2
      fields <- rep "fields" 3 typeP
      pure (Ctor name (fromIntegral tag) fields)

transparencyFromCode :: Word32 -> Maybe Transparency
transparencyFromCode 0 = Just Transparent
transparencyFromCode 1 = Just Abstract
transparencyFromCode _ = Nothing

opennessFromCode :: Word32 -> Maybe Openness
opennessFromCode 0 = Just Open
opennessFromCode 1 = Just Closed
opennessFromCode _ = Nothing

originFromCode :: Word32 -> Maybe Origin
originFromCode 0 = Just Derived
originFromCode 1 = Just Written
originFromCode _ = Nothing

managerKindFromCode :: Word32 -> Maybe ManagerKind
managerKindFromCode 0 = Just ManagerCmd
managerKindFromCode 1 = Just ManagerSub
managerKindFromCode 2 = Just ManagerFx
managerKindFromCode _ = Nothing

classDeclP :: P ClassDecl
classDeclP =
  message "ClassDecl" 4 $
    do
      name <- msg "name" 1 qualP
      param <- text "param" 2
      openness <- enum_ "openness" 3 opennessFromCode
      methods <- rep "methods" 4 methodSigP
      pure (ClassDecl name param openness methods)

methodSigP :: P (Name.Name, Type)
methodSigP =
  message "MethodSig" 2 $
    do
      name <- text "name" 1
      t <- msg "type" 2 typeP
      pure (name, t)

instanceDeclP :: P InstanceDecl
instanceDeclP =
  message "InstanceDecl" 4 $
    do
      cls <- msg "class_name" 1 qualP
      head_ <- msg "head" 2 typeP
      origin <- enum_ "origin" 3 originFromCode
      methods <- rep "methods" 4 methodImplP
      pure (InstanceDecl cls head_ origin methods)

methodImplP :: P (Name.Name, Expr)
methodImplP =
  message "MethodImpl" 2 $
    do
      name <- text "name" 1
      body <- msg "body" 2 exprP
      pure (name, body)

-- MODULE

moduleP :: P Module
moduleP =
  message "Module" 12 $
    do
      strings <- stringTable
      withTable strings $ moduleBodyP

moduleBodyP :: P Module
moduleBodyP =
  do
    name <- msg "name" 2 moduleNameP
    entries <- rep "files" 3 fileEntryP
    files <- fileTable entries
    dataDecls <- rep "data_decls" 4 dataDeclP
    classes <- rep "classes" 5 classDeclP
    instances <- rep "instances" 6 instanceDeclP
    defs <- rep "defs" 7 bindP
    defsRec <- rep "defs_rec" 8 recGroupP
    exports <- rep "exports" 9 qualP
    manager <- optMsg "manager" 10 managerP
    ports <- rep "ports" 11 portP
    main_ <- optMsg "main" 12 mainP
    pure
      Module
        { _moduleName = name,
          _moduleFiles = files,
          _moduleData = dataDecls,
          _moduleClasses = classes,
          _moduleInstances = instances,
          _moduleDefs = defs,
          _moduleDefsRec = defsRec,
          _moduleExports = exports,
          _moduleManager = manager,
          _modulePorts = ports,
          _moduleMain = main_
        }

recGroupP :: P [QualName]
recGroupP = message "RecGroup" 1 (rep "names" 1 qualP)

-- | C19's well-formedness rule, which the schema cannot state: @flags@ is
-- present exactly when the kind is @MAIN_KIND_PROGRAM@.
mainP :: P Main
mainP =
  message "Main" 2 $
    do
      here <- offset
      code <- defaulted "kind" 1 WVarint (0 :: Word64) varint
      flags <- optMsg "flags" 2 converterP
      case (code, flags) of
        (0, Nothing) -> pure MainString
        (1, Nothing) -> pure MainHtml
        (2, Just converter) -> pure (MainProgram converter)
        (2, Nothing) -> failAt here "a Program main has no flags converter"
        (_, Just _) -> failAt here "only a Program main may carry a flags converter"
        _ -> failAt here ("no such main kind: " ++ show code)

-- | C17's: @cmd_map@ is present for CMD and FX, @sub_map@ for SUB and FX.
managerP :: P Manager
managerP =
  message "Manager" 7 $
    do
      here <- offset
      kind <- enum_ "kind" 1 managerKindFromCode
      entries <- rep "entries" 2 qualP
      init_ <- msg "init" 3 qualP
      onEffects <- msg "on_effects" 4 qualP
      onSelfMsg <- msg "on_self_msg" 5 qualP
      cmdMap <- optMsg "cmd_map" 6 qualP
      subMap <- optMsg "sub_map" 7 qualP
      let wantsCmd = kind /= ManagerSub
      let wantsSub = kind /= ManagerCmd
      when (wantsCmd /= isJust' cmdMap) $
        failAt here "cmd_map is present exactly for a cmd or fx manager"
      when (wantsSub /= isJust' subMap) $
        failAt here "sub_map is present exactly for a sub or fx manager"
      pure (Manager kind entries init_ onEffects onSelfMsg cmdMap subMap)

isJust' :: Maybe a -> Bool
isJust' Nothing = False
isJust' (Just _) = True

portP :: P Port
portP =
  message "Port" 2 $
    do
      binder <- msg "binder" 1 binderP
      flow <- msg "flow" 2 portFlowP
      pure (Port binder flow)

portFlowP :: P PortFlow
portFlowP =
  message "PortFlow" 3 $
    oneof
      "flow"
      [ (1, WBytes, PortOut <$> submessage converterP),
        (2, WBytes, PortIn <$> submessage converterP),
        (3, WBytes, submessage portTaskP)
      ]

portTaskP :: P PortFlow
portTaskP =
  message "PortTask" 2 $
    do
      input <- optMsg "input" 1 converterP
      payload <- msg "payload" 2 converterP
      pure (PortTask input payload)

converterP :: P Converter
converterP =
  message "Converter" 2 $
    do
      isBytes <- bool_ "bytes" 1
      code <- msg "code" 2 exprP
      pure (Converter isBytes code)

-- EXPRESSIONS

exprP :: P Expr
exprP =
  message "Expr" 23 $
    do
      t <- msg "type" 1 typeP
      s <- msg "span" 2 spanP
      node <- nodeP
      pure (Expr node t s)

nodeP :: P Expr_
nodeP =
  oneof
    "node"
    [ (3, WVarint, EVar <$> indexText),
      (4, WBytes, EGlobal <$> submessage qualP),
      (5, WBytes, ELit <$> submessage literalP),
      (6, WBytes, submessage (absP ELam)),
      (7, WBytes, submessage (appP EApp)),
      (8, WBytes, submessage (bindsP ELet)),
      (9, WBytes, submessage (bindsP ELetRec)),
      (10, WBytes, submessage caseP),
      (11, WBytes, submessage ctorExprP),
      (12, WBytes, submessage recordP),
      (13, WBytes, submessage updateP),
      (14, WBytes, submessage accessP),
      (15, WBytes, submessage arrayP),
      (16, WBytes, submessage primP),
      (17, WBytes, submessage (bindsP EJoin)),
      (18, WBytes, submessage jumpP),
      (19, WBytes, submessage tyLamP),
      (20, WBytes, submessage tyAppP),
      (21, WBytes, submessage (absP EWitLam)),
      (22, WBytes, submessage (appP EWitApp)),
      (23, WBytes, submessage crashP)
    ]

absP :: ([Binder] -> Expr -> Expr_) -> P Expr_
absP build =
  message "Abs" 2 $
    do
      binders <- rep "binders" 1 binderP
      body <- msg "body" 2 exprP
      pure (build binders body)

appP :: (Expr -> [Expr] -> Expr_) -> P Expr_
appP build =
  message "App" 2 $
    do
      fn <- msg "fn" 1 exprP
      args <- rep "args" 2 exprP
      pure (build fn args)

bindsP :: ([Bind] -> Expr -> Expr_) -> P Expr_
bindsP build =
  message "Binds" 2 $
    do
      binds <- rep "binds" 1 bindP
      body <- msg "body" 2 exprP
      pure (build binds body)

caseP :: P Expr_
caseP =
  message "ECase" 3 $
    do
      scrut <- msg "scrutinee" 1 exprP
      alts <- rep "alts" 2 altP
      fallback <- optMsg "fallback" 3 exprP
      pure (ECase scrut alts fallback)

ctorExprP :: P Expr_
ctorExprP =
  message "ECtor" 3 $
    do
      name <- msg "name" 1 qualP
      tag <- u32 "tag" 2
      args <- rep "args" 3 exprP
      pure (ECtor name (fromIntegral tag) args)

recordP :: P Expr_
recordP = message "ERecord" 1 (ERecord <$> rep "fields" 1 fieldExprP)

updateP :: P Expr_
updateP =
  message "EUpdate" 2 $
    do
      base <- msg "base" 1 exprP
      fields <- rep "fields" 2 fieldExprP
      pure (EUpdate base fields)

fieldExprP :: P (Field, Expr)
fieldExprP =
  message "FieldExpr" 2 $
    do
      field <- text "field" 1
      value <- msg "value" 2 exprP
      pure (field, value)

accessP :: P Expr_
accessP =
  message "EAccess" 2 $
    do
      base <- msg "base" 1 exprP
      field <- text "field" 2
      pure (EAccess base field)

arrayP :: P Expr_
arrayP = message "EArray" 1 (EArray <$> rep "items" 1 exprP)

primP :: P Expr_
primP =
  message "EPrim" 2 $
    do
      here <- offset
      code <- u32 "op" 1
      args <- rep "args" 2 exprP
      case Prim.primFromCode (fromIntegral code) of
        Nothing -> failAt here ("no such primitive: " ++ show code)
        Just op -> pure (EPrim op args)

jumpP :: P Expr_
jumpP =
  message "EJump" 2 $
    do
      j <- text "join" 1
      args <- rep "args" 2 exprP
      pure (EJump j args)

tyLamP :: P Expr_
tyLamP =
  message "ETyLam" 2 $
    do
      vars <- repText "vars" 1
      body <- msg "body" 2 exprP
      pure (ETyLam vars body)

tyAppP :: P Expr_
tyAppP =
  message "ETyApp" 2 $
    do
      fn <- msg "fn" 1 exprP
      args <- rep "args" 2 typeP
      pure (ETyApp fn args)

-- | The third well-formedness rule the schema cannot state: @todo@ is present
-- exactly when the kind is @CRASH_KIND_TODO@.
crashP :: P Expr_
crashP =
  message "Crash" 2 $
    do
      here <- offset
      code <- defaulted "kind" 1 WVarint (0 :: Word64) varint
      todo <- optText "todo" 2
      case (code, todo) of
        (0, Just message_) -> pure (ECrash (Todo message_))
        (0, Nothing) -> failAt here "a Debug.todo crash has no message"
        (1, Nothing) -> pure (ECrash IncompleteMatch)
        (2, Nothing) -> pure (ECrash StackExhausted)
        (3, Nothing) -> pure (ECrash Unreachable)
        (_, Just _) -> failAt here "only a Debug.todo crash may carry a message"
        _ -> failAt here ("no such crash kind: " ++ show code)

binderP :: P Binder
binderP =
  message "Binder" 3 $
    do
      name <- text "name" 1
      t <- msg "type" 2 typeP
      s <- msg "span" 3 spanP
      pure (Binder name t s)

bindP :: P Bind
bindP =
  message "Bind" 2 $
    do
      binder <- msg "binder" 1 binderP
      value <- msg "value" 2 exprP
      pure (Bind binder value)

altP :: P Alt
altP =
  message "Alt" 2 $
    do
      pattern <- msg "pattern" 1 patternP
      body <- msg "body" 2 exprP
      pure (Alt pattern body)

-- PATTERNS

patternP :: P Pattern
patternP =
  message "Pattern" 7 $
    oneof
      "pattern"
      [ (1, WBytes, PVar <$> submessage binderP),
        (2, WBytes, submessage (message "Unit" 0 (pure PWild))),
        (3, WBytes, PLit <$> submessage literalP),
        (4, WBytes, submessage pctorP),
        (5, WBytes, submessage precordP),
        (6, WBytes, submessage parrayP),
        (7, WBytes, submessage pasP)
      ]

pctorP :: P Pattern
pctorP =
  message "PCtor" 3 $
    do
      name <- msg "name" 1 qualP
      tag <- u32 "tag" 2
      args <- rep "args" 3 patternP
      pure (PCtor name (fromIntegral tag) args)

precordP :: P Pattern
precordP = message "PRecord" 1 (PRecord <$> rep "fields" 1 fieldPatternP)

fieldPatternP :: P (Field, Pattern)
fieldPatternP =
  message "FieldPattern" 2 $
    do
      field <- text "field" 1
      p <- msg "pattern" 2 patternP
      pure (field, p)

parrayP :: P Pattern
parrayP =
  message "PArray" 2 $
    do
      items <- rep "items" 1 patternP
      tail_ <- optMsg "tail" 2 binderP
      pure (PArray items tail_)

pasP :: P Pattern
pasP =
  message "PAs" 2 $
    do
      binder <- msg "binder" 1 binderP
      inner <- msg "pattern" 2 patternP
      pure (PAs binder inner)

-- LITERALS

literalP :: P Literal
literalP =
  message "Literal" 9 $
    oneof
      "literal"
      [ (1, WVarint, LInt . unzigzag32 <$> varint),
        (2, WVarint, LInt64 . unzigzag64 <$> varint),
        (3, WVarint, LUInt32 . narrow32 <$> varint),
        (4, WVarint, LUInt64 <$> varint),
        (5, WFixed64, LFloat <$> fixed64AsDouble),
        (6, WFixed32, LFloat32 <$> fixed32AsFloat),
        (7, WVarint, LChar . unzigzag32 <$> varint),
        (8, WVarint, LString <$> indexText),
        (9, WVarint, LIntLegacy . toInteger . unzigzag64 <$> varint)
      ]

narrow32 :: Word64 -> Word32
narrow32 = fromIntegral

fixed64AsDouble :: P Double
fixed64AsDouble = wordToDouble <$> fixed64

fixed32AsFloat :: P Float
fixed32AsFloat = wordToFloat <$> fixed32

fixed64 :: P Word64
fixed64 =
  do
    raw <- takeBytes 8
    pure (foldr (\i acc -> (acc `shiftL` 8) .|. fromIntegral (BS.index raw i)) 0 [0 .. 7])

fixed32 :: P Word32
fixed32 =
  do
    raw <- takeBytes 4
    pure (foldr (\i acc -> (acc `shiftL` 8) .|. fromIntegral (BS.index raw i)) 0 [0 .. 3])

-- | Reinterpretation, not conversion: the bytes are IEEE 754 and both sides
-- have to see the same ones, including @-0.0@.
wordToDouble :: Word64 -> Double
wordToDouble = castWord64ToDouble

wordToFloat :: Word32 -> Float
wordToFloat = castWord32ToFloat
