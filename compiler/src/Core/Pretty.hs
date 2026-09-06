{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | A readable dump of Core.
--
-- C6 chose ordered renumbering over de Bruijn indices precisely so that this
-- would be worth reading: Core feeds error messages, D12's constraint
-- provenance and D19's crash reporting, and all three are materially worse
-- with indices. This module is the payoff — and it is the first consumer of
-- Core, so it is also where the IR gets exercised before the serializer and
-- the backend exist.
--
-- It is __not__ the golden-test artifact. That is the serialized form (C10),
-- byte-compared. This is for humans, and it deliberately elides the types and
-- spans that would drown a reader unless asked for them.
module Core.Pretty
  ( Options (..),
    defaultOptions,
    verboseOptions,
    moduleToBuilder,
    exprToBuilder,
    typeToBuilder,
  )
where

import Core.AST
import Core.Prim qualified as Prim
import Data.ByteString.Builder qualified as B
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Name qualified as Name
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Utf8 qualified as Utf8
import Gren.ModuleName qualified as ModuleName

data Options = Options
  { -- | Annotate each expression with its type. Off by default: every node
    -- carries one, so printing them all turns a readable dump into a wall.
    _showTypes :: !Bool,
    -- | Annotate each expression with its span.
    _showSpans :: !Bool
  }

defaultOptions :: Options
defaultOptions = Options {_showTypes = False, _showSpans = False}

verboseOptions :: Options
verboseOptions = Options {_showTypes = True, _showSpans = True}

-- MODULE

moduleToBuilder :: Options -> Module -> B.Builder
moduleToBuilder opts m =
  mconcat
    [ "module " <> canonical (_moduleName m) <> "\n",
      section "exports" (map qual (_moduleExports m)),
      section "files" (map fileEntry (Map.toList (_moduleFiles m))),
      block (map (dataDecl opts) (_moduleData m)),
      block (map (classDecl opts) (_moduleClasses m)),
      block (map (instanceDecl opts) (_moduleInstances m)),
      block (maybe [] (pure . managerDecl) (_moduleManager m)),
      block (map (topBind opts (recNames m)) (_moduleDefs m))
    ]

-- | An @effect module@'s manager. The entries are also ordinary bindings below,
-- so what this adds is the kind and the four or five names a runtime needs.
managerDecl :: Manager -> B.Builder
managerDecl m =
  mconcat
    [ "manager " <> kind (_managerKind m) <> "\n",
      "  entry " <> commas (map qual (_managerEntries m)) <> "\n",
      "  init " <> qual (_managerInit m) <> "\n",
      "  onEffects " <> qual (_managerOnEffects m) <> "\n",
      "  onSelfMsg " <> qual (_managerOnSelfMsg m) <> "\n",
      maybe "" (\q -> "  cmdMap " <> qual q <> "\n") (_managerCmdMap m),
      maybe "" (\q -> "  subMap " <> qual q <> "\n") (_managerSubMap m)
    ]
  where
    kind ManagerCmd = "cmd"
    kind ManagerSub = "sub"
    kind ManagerFx = "fx"

recNames :: Module -> [QualName]
recNames = concat . _moduleDefsRec

fileEntry :: (FileId, ModuleName.Canonical) -> B.Builder
fileEntry (FileId i, home) = B.intDec i <> " " <> canonical home

section :: B.Builder -> [B.Builder] -> B.Builder
section _ [] = ""
section label items =
  "\n-- " <> label <> "\n" <> mconcat (map (\i -> "  " <> i <> "\n") items)

block :: [B.Builder] -> B.Builder
block [] = ""
block items = "\n" <> mconcat (map (<> "\n") items)

dataDecl :: Options -> DataDecl -> B.Builder
dataDecl opts d =
  mconcat
    [ transparency (_dataTransparency d),
      "data " <> qual (_dataName d),
      mconcat [" " <> name p | p <- _dataParams d],
      classes (_dataClasses d),
      "\n",
      mconcat [ctor opts c | c <- _dataCtors d]
    ]
  where
    transparency Transparent = ""
    transparency Abstract = "abstract "
    classes [] = ""
    classes cs = " deriving (" <> commas (map qual cs) <> ")"

ctor :: Options -> Ctor -> B.Builder
ctor opts c =
  "  | "
    <> B.intDec (_ctorTag c)
    <> " "
    <> qual (_ctorName c)
    <> mconcat [" " <> atomicType opts t | t <- _ctorFields c]
    <> "\n"

classDecl :: Options -> ClassDecl -> B.Builder
classDecl opts c =
  mconcat
    [ openness (_classOpenness c),
      "class " <> qual (_classNameC c) <> " " <> name (_classParam c) <> "\n",
      mconcat
        [ "  " <> name n <> " : " <> typeToBuilder opts t <> "\n"
        | (n, t) <- _classMethods c
        ]
    ]
  where
    openness Open = ""
    openness Closed = "closed "

instanceDecl :: Options -> InstanceDecl -> B.Builder
instanceDecl opts i =
  mconcat
    [ origin (_instOrigin i),
      "instance " <> qual (_instClass i) <> " " <> atomicType opts (_instHead i) <> "\n",
      mconcat
        [ indent 1 <> name n <> " =\n" <> expr opts 2 e <> "\n"
        | (n, e) <- _instMethods i
        ]
    ]
  where
    origin Derived = "derived "
    origin Written = ""

topBind :: Options -> [QualName] -> Bind -> B.Builder
topBind opts recs b =
  mconcat
    [ if isRec then "rec " else "",
      name (_binderName bnd) <> " : " <> typeToBuilder opts (_binderType bnd) <> "\n",
      name (_binderName bnd) <> " =\n",
      expr opts 1 (_bindValue b) <> "\n"
    ]
  where
    bnd = _bindBinder b
    isRec = any (\q -> _qnName q == _binderName bnd) recs

-- TYPES

typeToBuilder :: Options -> Type -> B.Builder
typeToBuilder opts = go
  where
    go t =
      case t of
        TVar n -> name n
        TCon q [] -> qual q
        TCon q args -> qual q <> mconcat [" " <> atomicType opts a | a <- args]
        TFun args result -> "(" <> commas (map go args) <> " -> " <> go result <> ")"
        TRecord fields row ->
          "{ "
            <> maybe "" (\r -> name r <> " | ") row
            <> commas [name f <> " : " <> go ft | (f, ft) <- fields]
            <> " }"
        TForall vars constraints body ->
          "forall"
            <> mconcat [" " <> name v | v <- vars]
            <> ". "
            <> constraintPrefix constraints
            <> go body
    constraintPrefix [] = ""
    constraintPrefix cs = "(" <> commas (map constraint cs) <> ") => "
    constraint (CClass c t) = qual c <> " " <> atomicType opts t

atomicType :: Options -> Type -> B.Builder
atomicType opts t =
  case t of
    TVar _ -> typeToBuilder opts t
    TCon _ [] -> typeToBuilder opts t
    TRecord _ _ -> typeToBuilder opts t
    _ -> "(" <> typeToBuilder opts t <> ")"

-- EXPRESSIONS

exprToBuilder :: Options -> Expr -> B.Builder
exprToBuilder opts = expr opts 0

expr :: Options -> Int -> Expr -> B.Builder
expr opts depth e =
  indent depth <> annotation opts e <> body
  where
    pad = indent depth
    body =
      case _exprValue e of
        EVar n -> name n
        EGlobal q -> qual q
        ELit l -> literal l
        ECrash k -> crash k
        ELam binders inner ->
          "\\"
            <> commas (map (binder opts) binders)
            <> " ->\n"
            <> expr opts (depth + 1) inner
        EApp fn args ->
          "app\n"
            <> expr opts (depth + 1) fn
            <> mconcat ["\n" <> expr opts (depth + 1) a | a <- args]
        ELet binds inner -> letLike opts depth "let" binds inner
        ELetRec binds inner -> letLike opts depth "letrec" binds inner
        EJoin binds inner -> letLike opts depth "join" binds inner
        EJump j args ->
          "jump "
            <> name j
            <> mconcat ["\n" <> expr opts (depth + 1) a | a <- args]
        ECase scrut alts fallback ->
          "case\n"
            <> expr opts (depth + 1) scrut
            <> "\n"
            <> pad
            <> "of\n"
            <> mconcat [alt opts (depth + 1) a | a <- alts]
            <> maybe
              ""
              (\f -> indent (depth + 1) <> "_ ->\n" <> expr opts (depth + 2) f <> "\n")
              fallback
        ECtor q tag args ->
          qual q
            <> "#"
            <> B.intDec tag
            <> mconcat ["\n" <> expr opts (depth + 1) a | a <- args]
        ERecord fields -> "record" <> fieldList opts depth fields
        EUpdate base fields ->
          "update\n" <> expr opts (depth + 1) base <> fieldList opts depth fields
        EAccess base field ->
          "access ." <> name field <> "\n" <> expr opts (depth + 1) base
        EArray elems ->
          "array" <> mconcat ["\n" <> expr opts (depth + 1) el | el <- elems]
        EPrim op args ->
          "prim "
            <> text (Prim.primName op)
            <> mconcat ["\n" <> expr opts (depth + 1) a | a <- args]
        ETyLam vars inner ->
          "/\\" <> commas (map name vars) <> " ->\n" <> expr opts (depth + 1) inner
        ETyApp fn types ->
          "tyapp ["
            <> commas (map (typeToBuilder opts) types)
            <> "]\n"
            <> expr opts (depth + 1) fn
        EWitLam binders inner ->
          "\\wit "
            <> commas (map (binder opts) binders)
            <> " ->\n"
            <> expr opts (depth + 1) inner
        EWitApp fn args ->
          "witapp\n"
            <> expr opts (depth + 1) fn
            <> mconcat ["\n" <> expr opts (depth + 1) a | a <- args]

letLike :: Options -> Int -> B.Builder -> [Bind] -> Expr -> B.Builder
letLike opts depth keyword binds inner =
  keyword
    <> "\n"
    <> mconcat
      [ indent (depth + 1)
          <> binder opts (_bindBinder b)
          <> " =\n"
          <> expr opts (depth + 2) (_bindValue b)
          <> "\n"
      | b <- binds
      ]
    <> indent depth
    <> "in\n"
    <> expr opts (depth + 1) inner

fieldList :: Options -> Int -> [(Field, Expr)] -> B.Builder
fieldList opts depth fields =
  mconcat
    [ "\n" <> indent (depth + 1) <> "." <> name f <> " =\n" <> expr opts (depth + 2) v
    | (f, v) <- fields
    ]

alt :: Options -> Int -> Alt -> B.Builder
alt opts depth a =
  indent depth
    <> pattern_ opts (_altPattern a)
    <> " ->\n"
    <> expr opts (depth + 1) (_altBody a)
    <> "\n"

pattern_ :: Options -> Pattern -> B.Builder
pattern_ opts p =
  case p of
    PVar b -> binder opts b
    PWild -> "_"
    PLit l -> literal l
    PCtor q tag [] -> qual q <> "#" <> B.intDec tag
    PCtor q tag args ->
      "(" <> qual q <> "#" <> B.intDec tag <> mconcat [" " <> pattern_ opts a | a <- args] <> ")"
    PRecord fields ->
      "{ " <> commas [name f <> " = " <> pattern_ opts fp | (f, fp) <- fields] <> " }"
    PArray items tail_ ->
      "["
        <> commas (map (pattern_ opts) items)
        <> maybe "" (\b -> ", .." <> binder opts b) tail_
        <> "]"
    PAs b inner -> "(" <> pattern_ opts inner <> " as " <> binder opts b <> ")"

binder :: Options -> Binder -> B.Builder
binder opts b
  | _showTypes opts = name (_binderName b) <> " : " <> typeToBuilder opts (_binderType b)
  | otherwise = name (_binderName b)

annotation :: Options -> Expr -> B.Builder
annotation opts e =
  types <> spans
  where
    types
      | _showTypes opts = "{" <> typeToBuilder opts (_exprType e) <> "} "
      | otherwise = ""
    spans
      | _showSpans opts = span_ (_exprSpan e) <> " "
      | otherwise = ""

span_ :: Span -> B.Builder
span_ s =
  "@"
    <> (let FileId i = _spanFile s in B.intDec i)
    <> ":"
    <> B.word32Dec (_spanStartRow s)
    <> ":"
    <> B.word32Dec (_spanStartCol s)
    <> "-"
    <> B.word32Dec (_spanEndRow s)
    <> ":"
    <> B.word32Dec (_spanEndCol s)

literal :: Literal -> B.Builder
literal l =
  case l of
    LInt n -> B.int32Dec n <> "i32"
    LInt64 n -> B.int64Dec n <> "i64"
    LUInt32 n -> B.word32Dec n <> "u32"
    LUInt64 n -> B.word64Dec n <> "u64"
    LFloat d -> B.doubleDec d <> "f64"
    LFloat32 f -> B.floatDec f <> "f32"
    LChar c -> "char#" <> B.int32Dec c
    LString s -> "\"" <> B.stringUtf8 (Utf8.toChars s) <> "\""
    LIntLegacy n -> B.stringUtf8 (show n) <> "int"

crash :: CrashKind -> B.Builder
crash k =
  case k of
    Todo msg -> "crash todo \"" <> B.stringUtf8 (Utf8.toChars msg) <> "\""
    IncompleteMatch -> "crash incomplete-match"
    StackExhausted -> "crash stack-exhausted"
    Unreachable -> "crash unreachable"

-- NAMES AND LAYOUT

qual :: QualName -> B.Builder
qual (QualName home n) = canonical home <> "." <> name n

canonical :: ModuleName.Canonical -> B.Builder
canonical (ModuleName.Canonical _ raw) = name raw

name :: Name.Name -> B.Builder
name = Name.toBuilder

text :: Text.Text -> B.Builder
text = B.byteString . Text.encodeUtf8

commas :: [B.Builder] -> B.Builder
commas = mconcat . List.intersperse ", "

indent :: Int -> B.Builder
indent n = mconcat (replicate n "  ")
