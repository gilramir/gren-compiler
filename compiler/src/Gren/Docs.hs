{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnboxedTuples #-}
-- Temporary while implementing gren format
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module Gren.Docs
  ( Documentation,
    Module (..),
    fromModule,
    Union (..),
    Alias (..),
    Value (..),
    Named (..),
    Fact (..),
    factFromToken,
    factKey,
    factWords,
    withFacts,
    Binop (..),
    Binop.Associativity (..),
    Binop.Precedence (..),
    Error (..),
    decoder,
    encode,
  )
where

import AST.Canonical qualified as Can
import AST.Source qualified as Src
import AST.Utils.Binop qualified as Binop
import Data.Coerce qualified as Coerce
import Data.List qualified as List
import Data.Map ((!))
import Data.Map qualified as Map
import Data.Map.Merge.Strict qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name qualified as Name
import Data.NonEmptyList qualified as NE
import Data.OneOrMore qualified as OneOrMore
import Data.Set qualified as Set
import Data.Word (Word8)
import Foreign.Ptr (Ptr, plusPtr)
import Gren.Compiler.Type qualified as Type
import Gren.Compiler.Type.Extract qualified as Extract
import Gren.ModuleName qualified as ModuleName
import Json.Decode qualified as D
import Json.Encode ((==>))
import Json.Encode qualified as E
import Json.String qualified as Json
import Parse.Primitives (Col, Row, word1)
import Parse.Primitives qualified as P
import Parse.Space qualified as Space
import Parse.Symbol qualified as Symbol
import Parse.Variable qualified as Var
import Reporting.Annotation qualified as A
import Reporting.Error.Docs qualified as E
import Reporting.Result qualified as Result

-- DOCUMENTATION

type Documentation =
  Map.Map Name.Name Module

data Module = Module
  { _name :: Name.Name,
    _comment :: Comment,
    _unions :: Map.Map Name.Name Union,
    _aliases :: Map.Map Name.Name Alias,
    _values :: Map.Map Name.Name Value,
    _binops :: Map.Map Name.Name Binop
  }

type Comment = Json.String

-- | A type alias: its comment, variables and body with any name taken off,
-- and the name and predicate of a refined alias (geng-lang @m4-refine.md@
-- §RF35, D867), one 'Named' whose path is empty, the whole body.
data Alias = Alias Comment [Name.Name] Type.Type [Named]

-- | A custom type: its comment, variables and constructors, and whether it is
-- declared @\@affine@ (geng-lang @m4-own.md@ D921).
data Union = Union Comment [Name.Name] [(Name.Name, [Type.Type])] Bool

-- | An exposed value: its comment, its type with every refinement erased, and
-- the names its signature gives, each with its predicate as written, empty when
-- it names nothing (geng-lang @m4-refine.md@ §RF29, D854).
data Value = Value Comment Type.Type [Named] [Fact]

-- | What an exposed function's callers' checks read of it (geng-lang
-- @m4-own.md@ §OW33, D970–D974): the ownership checker's @I@ line, each fact
-- naming a parameter by its index and its name. None until the CLI's
-- ownership checker has given them ('withFacts'); the binary run by itself has
-- none to give. Each restricts what a caller may do, so one a version gains is
-- MAJOR and one it loses is MINOR (D974).
data Fact
  = -- | A function parameter that escapes the call (D929).
    Escapes Int Name.Name
  | -- | The result is a borrow of a parameter, at a field path (D930).
    Borrows Int Name.Name String
  | -- | A value of a type parameter may be kept twice (D935).
    KeepsTwice Name.Name
  | -- | The callback that is a parameter is lent its argument (D936).
    Lends Int Int Name.Name
  | -- | A parameter whose type is affine or holds a type variable is taken
    -- (D920, §OW6).
    Takes Int Name.Name
  | -- | A function parameter may be called or kept more than once (D952).
    UsesMany Int Name.Name
  deriving (Eq)

-- | A fact as the checker's @I@ line writes it: @escapes:0:fn@,
-- @borrows:1:array:path@, @keeps-twice:a@, @lends:0.1:fn@, @takes:1:acc@,
-- @uses-many:0:fn@.
factFromToken :: String -> Maybe Fact
factFromToken token =
  case splitOn ':' token of
    ["escapes", i, n] -> Escapes <$> number i <*> pure (Name.fromChars n)
    ["borrows", i, n, path] -> Borrows <$> number i <*> pure (Name.fromChars n) <*> pure path
    ["keeps-twice", v] -> Just (KeepsTwice (Name.fromChars v))
    ["lends", kj, n] ->
      case splitOn '.' kj of
        [k, j] -> Lends <$> number k <*> number j <*> pure (Name.fromChars n)
        _ -> Nothing
    ["takes", i, n] -> Takes <$> number i <*> pure (Name.fromChars n)
    ["uses-many", i, n] -> UsesMany <$> number i <*> pure (Name.fromChars n)
    _ -> Nothing
  where
    number text =
      if not (null text) && all (`elem` ['0' .. '9']) text then Just (read text) else Nothing

splitOn :: Char -> String -> [String]
splitOn c text =
  case break (== c) text of
    (before, []) -> [before]
    (before, _ : after) -> before : splitOn c after

-- | A fact with its parameter's name left out, so that a parameter renamed in
-- a later version is the same fact (D974). A type parameter is compared by
-- name, after the renaming the type comparison found.
factKey :: Fact -> (String, Int, Int, String)
factKey fact =
  case fact of
    Escapes i _ -> ("escapes", i, 0, "")
    Borrows i _ path -> ("borrows", i, 0, path)
    KeepsTwice v -> ("keeps-twice", 0, 0, Name.toChars v)
    Lends k j _ -> ("lends", k, j, "")
    Takes i _ -> ("takes", i, 0, "")
    UsesMany i _ -> ("uses-many", i, 0, "")

-- | A fact in words, as the documentation and @geng package diff@ print it
-- under a signature (D973): a parameter by its name, or by where it is when it
-- is a pattern.
factWords :: Fact -> String
factWords fact =
  case fact of
    Escapes i n -> "keeps " ++ param i n ++ " after it returns"
    Borrows i n path -> "answers a borrow of " ++ (if null path then param i n else param i n ++ " (at ." ++ path ++ ")")
    KeepsTwice v -> "may keep a value of type " ++ Name.toChars v ++ " twice"
    Lends k j n -> "lends " ++ param k n ++ " its " ++ ordinal (j + 1) ++ " argument to look at"
    Takes i n -> "takes " ++ param i n
    UsesMany i n -> "may call " ++ param i n ++ " more than once"
  where
    param i n =
      case Name.toChars n of
        '$' : _ -> "its " ++ ordinal (i + 1) ++ " argument"
        chars -> "`" ++ chars ++ "`"

    ordinal k =
      show k
        ++ case (k `mod` 100, k `mod` 10) of
          (t, _) | t >= 11 && t <= 13 -> "th"
          (_, 1) -> "st"
          (_, 2) -> "nd"
          (_, 3) -> "rd"
          _ -> "th"

-- | The documentation with each exposed value's facts, from the checker's
-- @I@ lines of the package @package@ (its module column @package:Module@).
withFacts :: String -> [String] -> Documentation -> Documentation
withFacts package lns docs =
  let facts =
        Map.fromListWith
          (flip (++))
          [ ((Name.fromChars modul, Name.fromChars def), Maybe.mapMaybe factFromToken tokens)
          | line <- lns,
            "I" : home : def : tokens <- [splitOn '\t' line],
            (pkg, ':' : modul) <- [break (== ':') home],
            pkg == package
          ]
      addTo home m =
        m {_values = Map.mapWithKey (\name (Value c t n f) -> Value c t n (Map.findWithDefault f (home, name) facts)) (_values m)}
   in Map.mapWithKey addTo docs

-- | A name a signature gives an argument or its result, where in the type it is
-- (as 'Can.Refinement' says it), and the predicate as written (D812), empty
-- when the name has none. The documentation prints the signature with them, so
-- that a precondition is read where the call is written. A moved name is an
-- argument whose value the function takes (geng-lang @m4-own.md@ D920).
data Named = Named
  { _namedPath :: [Can.RefinementStep],
    _namedName :: Name.Name,
    _namedSource :: String,
    _namedMoved :: Bool
  }

data Binop = Binop Comment Type.Type Binop.Associativity Binop.Precedence

-- JSON

encode :: Documentation -> E.Value
encode docs =
  let moduleFolder :: Name.Name -> Module -> [(Json.String, E.Value)] -> [(Json.String, E.Value)]
      moduleFolder name modInfo acc =
        (Name.toChars name ==> encodeModule modInfo) : acc
   in E.object $ Map.foldrWithKey moduleFolder [] docs

encodeModule :: Module -> E.Value
encodeModule (Module name comment unions aliases values binops) =
  E.object $
    [ "name" ==> ModuleName.encode name,
      "comment" ==> E.string comment,
      "unions" ==> E.list encodeUnion (Map.toList unions),
      "aliases" ==> E.list encodeAlias (Map.toList aliases),
      "values" ==> E.list encodeValue (Map.toList values),
      "binops" ==> E.list encodeBinop (Map.toList binops)
    ]

data Error
  = BadAssociativity
  | BadModuleName
  | BadType

decoder :: D.Decoder Error Documentation
decoder =
  D.dict moduleNameKeyDecoder moduleDecoder

moduleNameKeyDecoder :: D.KeyDecoder Error ModuleName.Raw
moduleNameKeyDecoder =
  let keyParser =
        P.specialize (\_ _ _ -> BadModuleName) ModuleName.parser
   in D.KeyDecoder keyParser (\_ _ -> BadModuleName)

moduleDecoder :: D.Decoder Error Module
moduleDecoder =
  Module
    <$> D.field "name" moduleNameDecoder
    <*> D.field "comment" D.string
    <*> D.field "unions" (dictDecoder union)
    <*> D.field "aliases" (dictDecoder alias)
    <*> D.field "values" (dictDecoder value)
    <*> D.field "binops" (dictDecoder binop)

dictDecoder :: D.Decoder Error a -> D.Decoder Error (Map.Map Name.Name a)
dictDecoder entryDecoder =
  Map.fromList <$> D.list (named entryDecoder)

named :: D.Decoder Error a -> D.Decoder Error (Name.Name, a)
named entryDecoder =
  (,)
    <$> D.field "name" nameDecoder
    <*> entryDecoder

nameDecoder :: D.Decoder e Name.Name
nameDecoder =
  fmap Coerce.coerce D.string

moduleNameDecoder :: D.Decoder Error ModuleName.Raw
moduleNameDecoder =
  D.mapError (const BadModuleName) ModuleName.decoder

typeDecoder :: D.Decoder Error Type.Type
typeDecoder =
  D.mapError (const BadType) Type.decoder

-- UNION JSON

encodeUnion :: (Name.Name, Union) -> E.Value
encodeUnion (name, Union comment args cases affine) =
  E.object $
    [ "name" ==> E.name name,
      "comment" ==> E.string comment,
      "args" ==> E.list E.name args,
      "cases" ==> E.list encodeCase cases
    ]
      ++ ["affine" ==> E.bool True | affine]

union :: D.Decoder Error Union
union =
  Union
    <$> D.field "comment" D.string
    <*> D.field "args" (D.list nameDecoder)
    <*> D.field "cases" (D.list caseDecoder)
    <*> D.oneOf [D.field "affine" D.bool, pure False]

encodeCase :: (Name.Name, [Type.Type]) -> E.Value
encodeCase (tag, args) =
  E.list id [E.name tag, E.list Type.encode args]

caseDecoder :: D.Decoder Error (Name.Name, [Type.Type])
caseDecoder =
  D.pair nameDecoder (D.list typeDecoder)

-- ALIAS JSON

encodeAlias :: (Name.Name, Alias) -> E.Value
encodeAlias (name, Alias comment args tipe names) =
  E.object $
    [ "name" ==> E.name name,
      "comment" ==> E.string comment,
      "args" ==> E.list E.name args,
      "type" ==> Type.encode tipe
    ]
      ++ ["named" ==> E.list encodeNamed names | not (null names)]

alias :: D.Decoder Error Alias
alias =
  Alias
    <$> D.field "comment" D.string
    <*> D.field "args" (D.list nameDecoder)
    <*> D.field "type" typeDecoder
    <*> D.oneOf [D.field "named" (D.list namedDecoder), pure []]

-- VALUE JSON

encodeValue :: (Name.Name, Value) -> E.Value
encodeValue (name, Value comment tipe names facts) =
  E.object $
    [ "name" ==> E.name name,
      "comment" ==> E.string comment,
      "type" ==> Type.encode tipe
    ]
      ++ ["named" ==> E.list encodeNamed names | not (null names)]
      ++ ["ownership" ==> E.list encodeFact facts | not (null facts)]

value :: D.Decoder Error Value
value =
  Value
    <$> D.field "comment" D.string
    <*> D.field "type" typeDecoder
    <*> D.oneOf [D.field "named" (D.list namedDecoder), pure []]
    <*> D.oneOf [D.field "ownership" (D.list factDecoder), pure []]

-- | A fact by its parameter's index, @arg@, counted from 0, and the
-- parameter's name; a lent argument's index is @lent@ (D973).
encodeFact :: Fact -> E.Value
encodeFact fact =
  E.object $
    case fact of
      Escapes i n -> [kind "escapes", "arg" ==> E.int i, "name" ==> E.name n]
      Borrows i n path -> [kind "borrows", "arg" ==> E.int i, "name" ==> E.name n] ++ ["path" ==> E.chars path | not (null path)]
      KeepsTwice v -> [kind "keeps-twice", "var" ==> E.name v]
      Lends k j n -> [kind "lends", "arg" ==> E.int k, "name" ==> E.name n, "lent" ==> E.int j]
      Takes i n -> [kind "takes", "arg" ==> E.int i, "name" ==> E.name n]
      UsesMany i n -> [kind "uses-many", "arg" ==> E.int i, "name" ==> E.name n]
  where
    kind k = "fact" ==> E.chars k

factDecoder :: D.Decoder Error Fact
factDecoder =
  do
    kind <- Json.toChars <$> D.field "fact" D.string
    case kind of
      "escapes" -> Escapes <$> D.field "arg" D.int <*> D.field "name" nameDecoder
      "borrows" -> Borrows <$> D.field "arg" D.int <*> D.field "name" nameDecoder <*> D.oneOf [Json.toChars <$> D.field "path" D.string, pure ""]
      "keeps-twice" -> KeepsTwice <$> D.field "var" nameDecoder
      "lends" -> (\k n j -> Lends k j n) <$> D.field "arg" D.int <*> D.field "name" nameDecoder <*> D.field "lent" D.int
      "takes" -> Takes <$> D.field "arg" D.int <*> D.field "name" nameDecoder
      "uses-many" -> UsesMany <$> D.field "arg" D.int <*> D.field "name" nameDecoder
      _ -> D.failure BadType

-- | A name, its path written as steps, @"arg 1"@ for the second argument and
-- @"result"@ for the last arrow's target, outermost first.
encodeNamed :: Named -> E.Value
encodeNamed (Named path name source moved) =
  E.object $
    [ "path" ==> E.list (E.chars . stepText) path,
      "name" ==> E.name name,
      "predicate" ==> E.chars source
    ]
      ++ ["moved" ==> E.bool True | moved]
  where
    stepText step =
      case step of
        Can.Arg i -> "arg " ++ show i
        Can.Result -> "result"

namedDecoder :: D.Decoder Error Named
namedDecoder =
  Named
    <$> D.field "path" (D.list stepDecoder)
    <*> D.field "name" nameDecoder
    <*> D.field "predicate" (Json.toChars <$> D.string)
    <*> D.oneOf [D.field "moved" D.bool, pure False]

stepDecoder :: D.Decoder Error Can.RefinementStep
stepDecoder =
  do
    text <- Json.toChars <$> D.string
    case words text of
      ["result"] -> return Can.Result
      ["arg", n] | not (null n), all (`elem` ['0' .. '9']) n -> return (Can.Arg (read n))
      _ -> D.failure BadType

-- BINOP JSON

encodeBinop :: (Name.Name, Binop) -> E.Value
encodeBinop (name, Binop comment tipe assoc prec) =
  E.object
    [ "name" ==> E.name name,
      "comment" ==> E.string comment,
      "type" ==> Type.encode tipe,
      "associativity" ==> encodeAssoc assoc,
      "precedence" ==> encodePrec prec
    ]

binop :: D.Decoder Error Binop
binop =
  Binop
    <$> D.field "comment" D.string
    <*> D.field "type" typeDecoder
    <*> D.field "associativity" assocDecoder
    <*> D.field "precedence" precDecoder

-- ASSOCIATIVITY JSON

encodeAssoc :: Binop.Associativity -> E.Value
encodeAssoc assoc =
  case assoc of
    Binop.Left -> E.chars "left"
    Binop.Non -> E.chars "non"
    Binop.Right -> E.chars "right"

assocDecoder :: D.Decoder Error Binop.Associativity
assocDecoder =
  let left = Json.fromChars "left"
      non = Json.fromChars "non"
      right = Json.fromChars "right"
   in do
        str <- D.string
        if
          | str == left -> return Binop.Left
          | str == non -> return Binop.Non
          | str == right -> return Binop.Right
          | otherwise -> D.failure BadAssociativity

-- PRECEDENCE JSON

encodePrec :: Binop.Precedence -> E.Value
encodePrec (Binop.Precedence n) =
  E.int n

precDecoder :: D.Decoder Error Binop.Precedence
precDecoder =
  Binop.Precedence <$> D.int

-- FROM MODULE

fromModule :: Can.Module -> Either E.Error Module
fromModule modul@(Can.Module _ exports docs _ _ _ _ _ _ _ _ _ _) =
  case exports of
    Can.ExportEverything region ->
      Left (E.ImplicitExposing region)
    Can.Export exportDict ->
      case docs of
        Src.NoDocs region ->
          Left (E.NoDocs region)
        Src.YesDocs overview comments ->
          do
            names <- parseOverview overview
            checkNames exportDict names
            checkDefs exportDict overview (Map.fromList comments) modul

-- PARSE OVERVIEW

parseOverview :: Src.DocComment -> Either E.Error [A.Located Name.Name]
parseOverview (Src.DocComment snippet) =
  case P.fromSnippet (chompOverview []) E.BadEnd snippet of
    Left err ->
      Left (E.SyntaxProblem err)
    Right names ->
      Right names

type Parser a =
  P.Parser E.SyntaxProblem a

chompOverview :: [A.Located Name.Name] -> Parser [A.Located Name.Name]
chompOverview names =
  do
    isDocs <- chompUntilDocs
    if isDocs
      then do
        Space.chomp E.Space
        chompOverview =<< chompDocs names
      else return names

chompDocs :: [A.Located Name.Name] -> Parser [A.Located Name.Name]
chompDocs names =
  do
    name <-
      P.addLocation $
        P.oneOf
          E.Name
          [ Var.lower E.Name,
            Var.upper E.Name,
            chompOperator
          ]

    Space.chomp E.Space

    P.oneOfWithFallback
      [ do
          pos <- P.getPosition
          Space.checkIndent pos E.Comma
          word1 0x2C {-,-} E.Comma
          Space.chomp E.Space
          chompDocs (name : names)
      ]
      (name : names)

chompOperator :: Parser Name.Name
chompOperator =
  do
    word1 0x28 {-(-} E.Op
    op <- Symbol.operator E.Op E.OpBad
    word1 0x29 {-)-} E.Op
    return op

chompUntilDocs :: Parser Bool
chompUntilDocs =
  P.Parser $ \(P.State src pos end indent row col) cok _ _ _ ->
    let (# isDocs, newPos, newRow, newCol #) = untilDocs pos end row col
        !newState = P.State src newPos end indent newRow newCol
     in cok isDocs newState

untilDocs :: Ptr Word8 -> Ptr Word8 -> Row -> Col -> (# Bool, Ptr Word8, Row, Col #)
untilDocs pos end row col =
  if pos >= end
    then (# False, pos, row, col #)
    else
      let !word = P.unsafeIndex pos
       in if word == 0x0A {-\n-}
            then untilDocs (plusPtr pos 1) end (row + 1) 1
            else
              let !pos5 = plusPtr pos 5
               in if pos5 <= end
                    && P.unsafeIndex (pos) == 0x40 {-@-}
                    && P.unsafeIndex (plusPtr pos 1) == 0x64 {-d-}
                    && P.unsafeIndex (plusPtr pos 2) == 0x6F {-o-}
                    && P.unsafeIndex (plusPtr pos 3) == 0x63 {-c-}
                    && P.unsafeIndex (plusPtr pos 4) == 0x73 {-s-}
                    && Var.getInnerWidth pos5 end == 0
                    then (# True, pos5, row, col + 5 #)
                    else
                      let !newPos = plusPtr pos (P.getCharWidth word)
                       in untilDocs newPos end row (col + 1)

-- CHECK NAMES

checkNames :: Map.Map Name.Name (A.Located Can.Export) -> [A.Located Name.Name] -> Either E.Error ()
checkNames exports names =
  let docs = List.foldl' addName Map.empty names
      loneDoc = Map.traverseMissing onlyInDocs
      loneExport = Map.traverseMissing onlyInExports
      checkBoth = Map.zipWithAMatched (\n _ r -> isUnique n r)
   in case Result.run (Map.mergeA loneExport loneDoc checkBoth exports docs) of
        (_, Right _) -> Right ()
        (_, Left es) -> Left (E.NameProblems (OneOrMore.destruct NE.List es))

type DocNameRegions =
  Map.Map Name.Name (OneOrMore.OneOrMore A.Region)

addName :: DocNameRegions -> A.Located Name.Name -> DocNameRegions
addName dict (A.At region name) =
  Map.insertWith OneOrMore.more name (OneOrMore.one region) dict

isUnique :: Name.Name -> OneOrMore.OneOrMore A.Region -> Result.Result i w E.NameProblem A.Region
isUnique name regions =
  case regions of
    OneOrMore.One region ->
      Result.ok region
    OneOrMore.More left right ->
      let (r1, r2) = OneOrMore.getFirstTwo left right
       in Result.throw (E.NameDuplicate name r1 r2)

onlyInDocs :: Name.Name -> OneOrMore.OneOrMore A.Region -> Result.Result i w E.NameProblem a
onlyInDocs name regions =
  do
    region <- isUnique name regions
    Result.throw $ E.NameOnlyInDocs name region

onlyInExports :: Name.Name -> A.Located Can.Export -> Result.Result i w E.NameProblem a
onlyInExports name (A.At region _) =
  Result.throw $ E.NameOnlyInExports name region

-- CHECK DEFS

checkDefs :: Map.Map Name.Name (A.Located Can.Export) -> Src.DocComment -> Map.Map Name.Name Src.DocComment -> Can.Module -> Either E.Error Module
checkDefs exportDict overview comments (Can.Module name _ _ decls unions aliases _ _ infixes _ _ _ affines) =
  let types = gatherTypes decls Map.empty
      info = Info comments types unions aliases infixes affines
   in case Result.run (Map.traverseWithKey (checkExport info) exportDict) of
        (_, Left problems) -> Left $ E.DefProblems (OneOrMore.destruct NE.List problems)
        (_, Right inserters) -> Right $ foldr ($) (emptyModule name overview) inserters

emptyModule :: ModuleName.Canonical -> Src.DocComment -> Module
emptyModule (ModuleName.Canonical _ name) (Src.DocComment overview) =
  Module name (Json.fromComment overview) Map.empty Map.empty Map.empty Map.empty

data Info = Info
  { _iComments :: Map.Map Name.Name Src.DocComment,
    _iValues :: Map.Map Name.Name (Either A.Region (Can.Type, [Can.Refinement])),
    _iUnions :: Map.Map Name.Name Can.Union,
    _iAliases :: Map.Map Name.Name Can.Alias,
    _iBinops :: Map.Map Name.Name Can.Binop,
    _iAffines :: Set.Set Name.Name
  }

checkExport :: Info -> Name.Name -> A.Located Can.Export -> Result.Result i w E.DefProblem (Module -> Module)
checkExport info name (A.At region export) =
  case export of
    Can.ExportValue ->
      do
        (tipe, names) <- getType name info
        comment <- getComment region name info
        Result.ok $ \m ->
          m {_values = Map.insert name (Value comment tipe names []) (_values m)}
    Can.ExportBinop ->
      do
        let (Can.Binop_ assoc prec realName) = _iBinops info ! name
        (tipe, _) <- getType realName info
        comment <- getComment region realName info
        Result.ok $ \m ->
          m {_binops = Map.insert name (Binop comment tipe assoc prec) (_binops m)}
    Can.ExportClass ->
      Result.throw (E.ClassNotDocumentable name region)
    Can.ExportAlias ->
      do
        let (Can.Alias tvars tipe refinement) = _iAliases info ! name
            names = [Named [] (Can._ar_name r) (Can._ar_source r) False | Just r <- [refinement]]
        comment <- getComment region name info
        Result.ok $ \m ->
          m {_aliases = Map.insert name (Alias comment tvars (Extract.fromType tipe) names) (_aliases m)}
    Can.ExportUnionOpen ->
      do
        let (Can.Union tvars ctors _ _) = _iUnions info ! name
        comment <- getComment region name info
        Result.ok $ \m ->
          m {_unions = Map.insert name (Union comment tvars (map dector ctors) (Set.member name (_iAffines info))) (_unions m)}
    Can.ExportUnionClosed ->
      do
        let (Can.Union tvars _ _ _) = _iUnions info ! name
        comment <- getComment region name info
        Result.ok $ \m ->
          m {_unions = Map.insert name (Union comment tvars [] (Set.member name (_iAffines info))) (_unions m)}

getComment :: A.Region -> Name.Name -> Info -> Result.Result i w E.DefProblem Comment
getComment region name info =
  case Map.lookup name (_iComments info) of
    Nothing ->
      Result.throw (E.NoComment name region)
    Just (Src.DocComment snippet) ->
      Result.ok (Json.fromComment snippet)

getType :: Name.Name -> Info -> Result.Result i w E.DefProblem (Type.Type, [Named])
getType name info =
  case _iValues info ! name of
    Left region ->
      Result.throw (E.NoAnnotation name region)
    Right (tipe, refinements) ->
      Result.ok (Extract.fromType tipe, map toNamed refinements)
  where
    toNamed ref =
      Named (Can._ref_path ref) (A.toValue (Can._ref_name ref)) (Can._ref_source ref) (Can._ref_moved ref)

dector :: Can.Ctor -> (Name.Name, [Type.Type])
dector (Can.Ctor name _ _ args) =
  (name, map Extract.fromType args)

-- GATHER TYPES

type Types =
  Map.Map Name.Name (Either A.Region (Can.Type, [Can.Refinement]))

gatherTypes :: Can.Decls -> Types -> Types
gatherTypes decls types =
  case decls of
    Can.Declare def subDecls ->
      gatherTypes subDecls (addDef types def)
    Can.DeclareRec def defs subDecls ->
      gatherTypes subDecls (List.foldl' addDef (addDef types def) defs)
    Can.SaveTheEnvironment ->
      types

addDef :: Types -> Can.Def -> Types
addDef types def =
  case def of
    Can.Def _ (A.At region name) _ _ ->
      Map.insert name (Left region) types
    Can.TypedDef (A.At _ name) _ typedArgs _ resultType refinements ->
      let tipe = foldr Can.TLambda resultType (map snd typedArgs)
       in Map.insert name (Right (tipe, refinements)) types
