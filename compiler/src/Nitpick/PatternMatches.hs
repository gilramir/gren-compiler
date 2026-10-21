{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

module Nitpick.PatternMatches
  ( check,
    Error (..),
    Context (..),
    Pattern (..),
    Literal (..),
    checkPatterns,
  )
where

{- The algorithm used here comes from "Warnings for Pattern Matching"
by Luc Maranget. Check it out for more information!

http://moscova.inria.fr/~maranget/papers/warn/warn.pdf

-}

import AST.Canonical qualified as Can
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name qualified as Name
import Data.NonEmptyList qualified as NE
import Data.Set (Set)
import Data.Set qualified as Set
import Gren.String qualified as ES
import Reporting.Annotation qualified as A

-- PATTERN

data Pattern
  = Anything
  | Literal Literal
  | Array [Pattern]
  | Record (Map Name.Name Pattern)
  | Ctor Can.Union Name.Name [Pattern]

data Literal
  = Chr ES.String
  | Str ES.String
  | Int Integer
  deriving (Eq, Ord)

-- CREATE SIMPLIFIED PATTERNS

simplify :: Can.Pattern -> Pattern
simplify (A.At _ pattern) =
  case pattern of
    Can.PAnything ->
      Anything
    Can.PVar _ ->
      Anything
    Can.PRecord fields ->
      Record $ List.foldl' insertRecordField Map.empty fields
    Can.PCtor _ _ union name _ args ->
      Ctor union name $
        map (\(Can.PatternCtorArg _ _ arg) -> simplify arg) args
    Can.PArray entries ->
      Array $ map simplify entries
    Can.PAlias subPattern _ ->
      simplify subPattern
    Can.PInt int ->
      Literal (Int int)
    Can.PStr str ->
      Literal (Str str)
    Can.PChr chr ->
      Literal (Chr chr)
    Can.PBool union bool ->
      Ctor union (if bool then Name.true else Name.false) []

insertRecordField :: Map Name.Name Pattern -> Can.PatternRecordField -> Map Name.Name Pattern
insertRecordField fields (A.At _ (Can.PRFieldPattern name pattern)) =
  Map.insert name (simplify pattern) fields

-- ERROR

data Error
  = Incomplete A.Region Context [Pattern]
  | Redundant A.Region A.Region Int

data Context
  = BadArg
  | BadDestruct
  | BadCase

-- CHECK

check :: Can.Module -> Either (NE.List Error) ()
check (Can.Module _ _ _ decls _ _ _ _ _ _ _ _) =
  case checkDecls decls [] of
    [] ->
      Right ()
    e : es ->
      Left (NE.List e es)

-- CHECK DECLS

checkDecls :: Can.Decls -> [Error] -> [Error]
checkDecls decls errors =
  case decls of
    Can.Declare def subDecls ->
      checkDef def $ checkDecls subDecls errors
    Can.DeclareRec def defs subDecls ->
      checkDef def (foldr checkDef (checkDecls subDecls errors) defs)
    Can.SaveTheEnvironment ->
      errors

-- CHECK DEFS

checkDef :: Can.Def -> [Error] -> [Error]
checkDef def errors =
  case def of
    Can.Def _ _ args body ->
      foldr checkArg (checkExpr body errors) args
    Can.TypedDef _ _ args body _ _ ->
      foldr checkTypedArg (checkExpr body errors) args

checkArg :: Can.Pattern -> [Error] -> [Error]
checkArg pattern@(A.At region _) errors =
  checkPatterns region BadArg [pattern] errors

checkTypedArg :: (Can.Pattern, tipe) -> [Error] -> [Error]
checkTypedArg (pattern@(A.At region _), _) errors =
  checkPatterns region BadArg [pattern] errors

-- CHECK EXPRESSIONS

checkExpr :: Can.Expr -> [Error] -> [Error]
checkExpr (Can.Expr _ region expression) errors =
  case expression of
    Can.VarLocal _ ->
      errors
    Can.VarTopLevel _ _ ->
      errors
    Can.VarKernel _ _ ->
      errors
    Can.VarPrim _ _ ->
      errors
    Can.VarExtern _ _ _ _ ->
      errors
    Can.VarForeign _ _ _ ->
      errors
    Can.VarMethod _ _ _ _ ->
      errors
    Can.VarCtor _ _ _ _ _ ->
      errors
    Can.VarDebug _ _ _ ->
      errors
    Can.VarOperator _ _ _ _ ->
      errors
    Can.Chr _ ->
      errors
    Can.Str _ ->
      errors
    Can.Int _ ->
      errors
    Can.Float _ ->
      errors
    Can.Array entries ->
      foldr checkExpr errors entries
    Can.Negate expr ->
      checkExpr expr errors
    Can.Annotated expr _ ->
      checkExpr expr errors
    Can.Binop _ _ _ left right ->
      checkExpr left $
        checkExpr right errors
    Can.Lambda args body ->
      foldr checkArg (checkExpr body errors) args
    Can.Call func args ->
      checkExpr func $ foldr checkExpr errors args
    Can.If branches finally ->
      foldr checkIfBranch (checkExpr finally errors) branches
    Can.Let def body ->
      checkDef def $ checkExpr body errors
    Can.LetRec defs body ->
      foldr checkDef (checkExpr body errors) defs
    Can.LetDestruct pattern@(A.At reg _) expr body ->
      checkPatterns reg BadDestruct [pattern] $
        checkExpr expr $
          checkExpr body errors
    Can.Case expr branches ->
      checkExpr expr $ checkCases region branches errors
    Can.Accessor _ ->
      errors
    Can.Access record _ ->
      checkExpr record errors
    Can.Update record fields ->
      checkExpr record $ Map.foldr checkField errors fields
    Can.Record fields ->
      Map.foldr checkExpr errors fields

-- CHECK FIELD

checkField :: Can.FieldUpdate -> [Error] -> [Error]
checkField (Can.FieldUpdate _ expr) errors =
  checkExpr expr errors

-- CHECK IF BRANCH

checkIfBranch :: (Can.Expr, Can.Expr) -> [Error] -> [Error]
checkIfBranch (condition, branch) errs =
  checkExpr condition $ checkExpr branch errs

-- CHECK CASE EXPRESSION

checkCases :: A.Region -> [Can.CaseBranch] -> [Error] -> [Error]
checkCases region branches errors =
  let (patterns, newErrors) =
        foldr checkCaseBranch ([], errors) branches
   in checkPatterns region BadCase patterns newErrors

checkCaseBranch :: Can.CaseBranch -> ([Can.Pattern], [Error]) -> ([Can.Pattern], [Error])
checkCaseBranch (Can.CaseBranch pattern expr) (patterns, errors) =
  ( pattern : patterns,
    checkExpr expr errors
  )

-- CHECK PATTERNS

checkPatterns :: A.Region -> Context -> [Can.Pattern] -> [Error] -> [Error]
checkPatterns region context patterns errors =
  case toNonRedundantRows region patterns of
    Left err ->
      err : errors
    Right matrix ->
      case isExhaustive matrix 1 of
        [] ->
          errors
        badPatterns ->
          Incomplete region context (map head badPatterns) : errors

-- EXHAUSTIVE PATTERNS

-- INVARIANTS:
--
--   The initial rows "matrix" are all of length 1
--   The initial count of items per row "n" is also 1
--   The resulting rows are examples of missing patterns
--
isExhaustive :: [[Pattern]] -> Int -> [[Pattern]]
isExhaustive matrix n =
  case matrix of
    [] ->
      [replicate n Anything]
    _ ->
      if n == 0
        then []
        else
          let ctors = collectCtors matrix
              numSeen = Map.size ctors
           in if numSeen == 0
                then
                  let maybeBaseRecord = extractRecordPatterns matrix
                   in case maybeBaseRecord of
                        Nothing ->
                          (:) Anything
                            <$> isExhaustive (Maybe.mapMaybe specializeRowByAnything matrix) (n - 1)
                        Just baseRecord ->
                          -- Treat records as a product of fields (cartesian combination),
                          -- not each field independently.
                          let fieldCount = Map.size baseRecord
                              baseFieldsInOrder = Map.keys baseRecord

                              -- Rebuild a record from the first `fieldCount` patterns in a counterexample row
                              recoverRecord :: [Pattern] -> [Pattern]
                              recoverRecord patterns =
                                let (fieldPats, rest) = splitAt fieldCount patterns
                                 in Record (Map.fromList (zip baseFieldsInOrder fieldPats)) : rest
                           in map recoverRecord $
                                isExhaustive
                                  (Maybe.mapMaybe (specializeRowByRecord baseRecord) matrix)
                                  (fieldCount + n - 1)
                else
                  let alts@(Can.Union _ altList numAlts _) = snd (Map.findMin ctors)
                   in if numSeen < numAlts
                        then
                          -- The rest first: when it is covered, which a
                          -- wildcard branch makes it, there is nothing to
                          -- list, and listing the constructors no row names
                          -- walked all of the type's (D694).
                          case isExhaustive (Maybe.mapMaybe specializeRowByAnything matrix) (n - 1) of
                            [] -> []
                            rest -> (:) <$> Maybe.mapMaybe (isMissing alts ctors) altList <*> rest
                        else
                          -- The rows are split by constructor once, where
                          -- specializing all of them for each constructor
                          -- made a when over n constructors n² (D694).
                          let (tested, untested) = splitRows ctorHead (zip [0 ..] matrix)
                              isAltExhaustive (Can.Ctor name _ arity _) =
                                recoverCtor alts name arity
                                  <$> isExhaustive
                                    ( map snd $
                                        mergeByIndex
                                          (Map.findWithDefault [] name tested)
                                          [(i, replicate arity Anything ++ rest) | (i, rest) <- untested]
                                    )
                                    (arity + n - 1)
                           in concatMap isAltExhaustive altList

isMissing :: Can.Union -> Map.Map Name.Name a -> Can.Ctor -> Maybe Pattern
isMissing union ctors (Can.Ctor name _ arity _) =
  if Map.member name ctors
    then Nothing
    else Just (Ctor union name (replicate arity Anything))

recoverCtor :: Can.Union -> Name.Name -> Int -> [Pattern] -> [Pattern]
recoverCtor union name arity patterns =
  let (args, rest) =
        splitAt arity patterns
   in Ctor union name args : rest

-- REDUNDANT PATTERNS

-- INVARIANT: Produces a list of rows where (forall row. length row == 1)
--
-- The first branch no value reaches is the redundant one, as when each was
-- checked against the useful rows before it; 'usefulRows' answers for all of
-- them in one walk, where that check made a @when@ of n branches n²
-- (geng-lang D694, @m3-sweep.md@ §SW30.2 item 6).
toNonRedundantRows :: A.Region -> [Can.Pattern] -> Either Error [[Pattern]]
toNonRedundantRows region patterns =
  let rows = map (\pattern -> [simplify pattern]) patterns
      useful = usefulRows (zip [0 ..] rows)
   in case [(i, r) | (i, A.At r _) <- zip [0 ..] patterns, not (Set.member i useful)] of
        [] -> Right (reverse rows)
        (i, r) : _ -> Left (Redundant region r (i + 1))

-- | The rows that some value matches before it matches any row above them,
-- which is each row's usefulness against the rows before it.
--
-- One walk over the whole matrix: the first column's rows are split by what
-- they test, a row testing a constructor or literal going to its group alone
-- and a row testing nothing going to every group, and a value reaches the
-- first row left when the columns run out. Values a column names no test for
-- reach only the rows testing nothing, the default group; a union whose every
-- constructor is named has none.
usefulRows :: [(Int, [Pattern])] -> Set Int
usefulRows rows =
  case rows of
    [] ->
      Set.empty
    (i, []) : _ ->
      Set.singleton i
    _ ->
      case [pattern | (_, pattern : _) <- rows, not (isAnything pattern)] of
        [] ->
          usefulRows [(i, patterns) | (i, _ : patterns) <- rows]
        Ctor (Can.Union _ _ numAlts _) _ _ : _ ->
          -- Only the constructors the rows name, and not every one the type
          -- has: a when of two branches over a type of n constructors walked
          -- all n.
          let (tested, untested) = splitRows ctorHead rows
              arities = Map.fromList [(name, length args) | (_, Ctor _ name args : _) <- rows]
              group (name, these) =
                let arity = Map.findWithDefault 0 name arities
                 in usefulRows (mergeByIndex these [(i, replicate arity Anything ++ ps) | (i, ps) <- untested])
              defaults = if Map.size tested == numAlts then Set.empty else usefulRows untested
           in Set.unions (defaults : map group (Map.toList tested))
        Literal _ : _ ->
          let (tested, untested) = splitRows litHead rows
              litHead pattern =
                case pattern of
                  Literal literal -> Just (literal, [])
                  _ -> Nothing
           in Set.unions (usefulRows untested : [usefulRows (mergeByIndex these untested) | these <- Map.elems tested])
        Array _ : _ ->
          let (tested, untested) = splitRows arrayHead rows
              arrayHead pattern =
                case pattern of
                  Array items -> Just (length items, items)
                  _ -> Nothing
              group (len, these) = usefulRows (mergeByIndex these [(i, replicate len Anything ++ ps) | (i, ps) <- untested])
           in Set.unions (usefulRows untested : map group (Map.toList tested))
        Record _ : _ ->
          let baseRecord = collectRecordFieldsWithAnyPattern (map snd rows)
           in usefulRows (Maybe.mapMaybe (\(i, row) -> (,) i <$> specializeRowByRecord baseRecord row) rows)
        Anything : _ ->
          error "Compiler error! An Anything survived the filter for a test."

ctorHead :: Pattern -> Maybe (Name.Name, [Pattern])
ctorHead pattern =
  case pattern of
    Ctor _ name args -> Just (name, args)
    _ -> Nothing

isAnything :: Pattern -> Bool
isAnything pattern =
  case pattern of
    Anything -> True
    _ -> False

-- | A column's rows, in order: those that test it, by the test, with the
-- tested pattern's children in its place, and those that do not, without it.
splitRows :: (Ord k) => (Pattern -> Maybe (k, [Pattern])) -> [(Int, [Pattern])] -> (Map k [(Int, [Pattern])], [(Int, [Pattern])])
splitRows testOf rows =
  let classify (i, row) =
        case row of
          Anything : rest -> Right (i, rest)
          pattern : rest ->
            case testOf pattern of
              Just (k, children) -> Left (k, (i, children ++ rest))
              Nothing -> error "Compiler bug! After type checking, a column's patterns test the same kind of value."
          [] -> error "Compiler error! Empty matrices should not get specialized."
      classified = map classify rows
   in ( Map.fromListWith (++) [(k, [r]) | Left (k, r) <- reverse classified],
        [r | Right r <- classified]
      )

mergeByIndex :: [(Int, a)] -> [(Int, a)] -> [(Int, a)]
mergeByIndex xs ys =
  case (xs, ys) of
    ([], _) -> ys
    (_, []) -> xs
    (x@(i, _) : xs', y@(j, _) : ys') ->
      if i < j then x : mergeByIndex xs' ys else y : mergeByIndex xs ys'

-- INVARIANT: (length row == N) ==> (length result == arity + N - 1)
specializeRowByRecord :: Map Name.Name Pattern -> [Pattern] -> Maybe [Pattern]
specializeRowByRecord baseMap row =
  case row of
    Ctor _ _ _ : _ ->
      Nothing
    Array _ : _ ->
      Nothing
    Record namedPatterns : patterns ->
      let specializedMap = Map.union namedPatterns baseMap
       in Just (Map.elems specializedMap ++ patterns)
    Anything : patterns ->
      Just (Map.elems baseMap ++ patterns)
    Literal _ : _ ->
      error $
        "Compiler bug! After type checking, records and literals\
        \ should never align in pattern match exhaustiveness checks."
    [] ->
      error "Compiler error! Empty matrices should not get specialized."

-- INVARIANT: (length row == N) ==> (length result == N-1)
specializeRowByAnything :: [Pattern] -> Maybe [Pattern]
specializeRowByAnything row =
  case row of
    [] ->
      Nothing
    Ctor _ _ _ : _ ->
      Nothing
    Anything : patterns ->
      Just patterns
    Array _ : _ ->
      Nothing
    Record _ : _ ->
      Nothing
    Literal _ : _ ->
      Nothing

-- COLLECT CTORS

collectCtors :: [[Pattern]] -> Map.Map Name.Name Can.Union
collectCtors matrix =
  List.foldl' collectCtorsHelp Map.empty matrix

collectCtorsHelp :: Map.Map Name.Name Can.Union -> [Pattern] -> Map.Map Name.Name Can.Union
collectCtorsHelp ctors row =
  case row of
    Ctor union name _ : _ ->
      Map.insert name union ctors
    _ ->
      ctors

-- COLLECT RECORD FIELDS

extractRecordPatterns :: [[Pattern]] -> Maybe (Map Name.Name Pattern)
extractRecordPatterns matrix =
  if containsRecord matrix
    then Just $ collectRecordFieldsWithAnyPattern matrix
    else Nothing

containsRecord :: [[Pattern]] -> Bool
containsRecord matrix =
  case matrix of
    [] ->
      False
    (Record _ : _) : _ ->
      True
    _ : rest ->
      containsRecord rest

collectRecordFieldsWithAnyPattern :: [[Pattern]] -> Map Name.Name Pattern
collectRecordFieldsWithAnyPattern matrix =
  let fieldNames = List.foldl' collectRecordFields Set.empty matrix
   in Set.foldl' (\fields name -> Map.insert name Anything fields) Map.empty fieldNames

collectRecordFields :: Set Name.Name -> [Pattern] -> Set Name.Name
collectRecordFields nameCollection row =
  case row of
    Record namedPatterns : _ ->
      Set.union
        (Set.fromList (Map.keys namedPatterns))
        nameCollection
    _ ->
      nameCollection
