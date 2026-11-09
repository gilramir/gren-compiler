module Canonicalize.Type
  ( toAnnotation,
    toSignature,
    Signature (..),
    checkBody,
    canonicalize,
    canonicalizeAliasBody,
    canonicalizeVariantArg,
    addFreeVars,
    equatesConditions,
    boolPath,
    measures,
    operators,
  )
where

import AST.Canonical qualified as Can
import AST.Source qualified as Src
import AST.SourceComments qualified as SC
import AST.Utils.Type qualified as Type
import Canonicalize.Binops qualified as Binops
import Canonicalize.Environment qualified as Env
import Canonicalize.Environment.Dups qualified as Dups
import Canonicalize.NodeId qualified as NodeId
import Control.Monad (foldM)
import Data.Char qualified as Char
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name qualified as Name
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Reporting.Annotation qualified as A
import Reporting.Error.Canonicalize qualified as Error
import Reporting.Result qualified as Result

-- RESULT

type Result i w a =
  Result.Result i w Error.Error a

-- TO ANNOTATION

-- | An annotation: the type, the variables it binds, and what each is
-- constrained by (D111).
--
-- The context is taken here rather than checked separately because it is part
-- of what an annotation is — `Src.Annotation` already pairs them — and because
-- a constraint has no meaning apart from the variables the type binds. A port
-- has no context and passes `Nothing`.
toAnnotation :: Error.RefinementPlace -> Env.Env -> Maybe Src.Context -> Src.Type -> Result i w Can.Annotation
toAnnotation place env maybeContext srcType =
  do
    tipe <- canonicalize place env srcType
    freeVars <- addContext env (addFreeVars Map.empty tipe) maybeContext
    Result.ok $ Can.Forall freeVars tipe

-- CONTEXT

-- | `(Eq a, Ord b) =>`, resolved onto the variables the type binds.
--
-- Two things are checked and both are about the annotation rather than about
-- the class. __The variable has to be one the type binds__: `Eq b => a -> a`
-- has nowhere to put the constraint, because D111 keys the constraint list off
-- `FreeVars`, and a promise about a variable that does not occur is a promise
-- about nothing. And __a constraint may not be written twice__ on the same
-- variable; the second one says nothing the first did not.
--
-- The order the author wrote is kept. It is not Core's order — `lowerAnnotation`
-- sorts, because that is where types are compared — and keeping it here is the
-- same split `Can.TRecord` already makes, carrying a source-order index that
-- `lowerType` drops.
addContext :: Env.Env -> Can.FreeVars -> Maybe Src.Context -> Result i w Can.FreeVars
addContext env freeVars maybeContext =
  case maybeContext of
    Nothing ->
      Result.ok freeVars
    Just (Src.Context entries _) ->
      foldM (addConstraint env) freeVars entries

addConstraint :: Env.Env -> Can.FreeVars -> Src.ContextEntry -> Result i w Can.FreeVars
addConstraint env freeVars (A.At region constraint, _) =
  do
    (className, cls, A.At varRegion var) <-
      case constraint of
        Src.Constraint _ name varName ->
          (,,) name <$> Env.findClass region env name <*> pure varName
        Src.ConstraintQual _ home name varName ->
          (,,) name <$> Env.findClassQual region env home name <*> pure varName
    case Map.lookup var freeVars of
      Nothing ->
        Result.throw (Error.ConstraintVarUnbound varRegion className var)
      Just classes ->
        if cls `elem` classes
          then Result.throw (Error.ConstraintDuplicate region className var)
          else Result.ok (Map.insert var (classes ++ [cls]) freeVars)

-- CANONICALIZE TYPES

-- | A type written anywhere but on a signature's arguments and result, where
-- a name or a refinement is refused (geng-lang @m4-refine.md@ D816, §RF17).
-- The place is where the type is written, and it moves inward with the
-- type: an argument of a type is 'Error.InTypeArgument' wherever the type is,
-- and a record's field 'Error.InRecordField'.
canonicalize :: Error.RefinementPlace -> Env.Env -> Src.Type -> Result i w Can.Type
canonicalize place env (A.At typeRegion tipe) =
  case tipe of
    Src.TVar x ->
      Result.ok (Can.TVar x)
    Src.TType region name args ->
      refuseRefined place typeRegion name
        =<< canonicalizeType env typeRegion name (fmap snd args)
        =<< Env.findType region env name
    Src.TTypeQual region home name args ->
      refuseRefined place typeRegion name
        =<< canonicalizeType env typeRegion name (fmap snd args)
        =<< Env.findTypeQual region env home name
    Src.TLambda a b _ ->
      Can.TLambda
        <$> canonicalize place env a
        <*> canonicalize place env b
    Src.TRecord fields ext
      | any hasWhere fields ->
          Result.throw $
            case ext of
              Just _ -> Error.FieldRefinementExtensible typeRegion
              Nothing -> Error.FieldRefinementMisplaced typeRegion place
      | otherwise ->
          do
            cfields <- sequenceA =<< Dups.checkFields (canonicalizeFields env fields)
            return $ Can.TRecord cfields (fmap (A.toValue . fst) ext)
    Src.TParens inner _ ->
      canonicalize place env inner
    Src.TNamed _ _ _ maybePredicate ->
      Result.throw (Error.RefinementMisplaced typeRegion (Maybe.isJust maybePredicate) place)
    Src.TWhere _ _ ->
      Result.throw (Error.RefinementMisplaced typeRegion True place)

-- | A refined alias anywhere a signature does not name a value: in a type's
-- argument, a record's field anywhere but at a signature's position
-- ('recordRefinement'), a variant, another alias's body, an annotation or a
-- method's signature (geng-lang @m4-refine.md@ §RF35, D869, Dnene14). There is
-- no value there for the predicate to be about, and erasing it would promise a
-- reader what nothing checks.
refuseRefined :: Error.RefinementPlace -> A.Region -> Name.Name -> (Can.Type, Maybe Can.AliasRefinement) -> Result i w Can.Type
refuseRefined place region name (tipe, refinement) =
  case (refinement, tipe) of
    (Nothing, _) -> Result.ok tipe
    -- A refined record alias is a type invariant (geng-lang
    -- @m4-refine-t1.md@ TO17, Dnene22): every record of its shape keeps it,
    -- asked where one is built, so it may be anywhere a type may, a `Task`'s
    -- argument among them.
    (Just _, Can.TAlias _ _ [] (Can.Holey (Can.TRecord _ Nothing))) -> Result.ok tipe
    (Just _, _) -> Result.throw (Error.RefinedAliasMisplaced region name place)

-- | A type alias's body (D867): a refined alias is D814's name and predicate as
-- the whole of it, @type alias Nat = (n : Int where 0 <= n)@, the predicate
-- reading only that name. Anything else is an ordinary alias, where a name is
-- refused as it is in any type that is not a signature's.
--
-- The module's aliases are put in scope before its classes, values and
-- operators, which a predicate reads, so the first pass is asked with
-- @readPredicate@ false: it says which aliases are refined, with a predicate of
-- no meaning, and 'Canonicalize.Environment.Local' reads each predicate once
-- the scope is complete.
canonicalizeAliasBody :: Bool -> Env.Env -> Name.Name -> Src.Type -> Result i w (Can.Type, Maybe Can.AliasRefinement)
canonicalizeAliasBody readPredicate env alias srcType =
  do
    -- An alias of a refined alias is that alias, its predicate and its
    -- name: @type alias Term = State.Term@ re-exports it (Dnene21).
    same <- refinedAliasAt env srcType
    nested <- maybe (hasRefinedField env srcType) (const (Result.ok False)) same
    case same of
      Just (ctype, refinement) -> Result.ok (ctype, Just refinement)
      Nothing -> recordOrPlain readPredicate env alias srcType nested

recordOrPlain :: Bool -> Env.Env -> Name.Name -> Src.Type -> Bool -> Result i w (Can.Type, Maybe Can.AliasRefinement)
recordOrPlain readPredicate env alias srcType nested =
  do
    if nested
      then do
        refined <- recordRefinementAs readPredicate (Just (lowerFirst alias)) env srcType
        case refined of
          Just (ctype, refinement) -> Result.ok (ctype, Just refinement)
          Nothing -> aliasBody readPredicate env alias srcType
      else aliasBody readPredicate env alias srcType

-- | Whether an alias's body is a closed record one of whose fields is a
-- refined alias, or a record that is one (geng-lang @m4-refine-t1.md@ TO15,
-- Dnene21): @type alias Term = { screen : Screen, ... }@ is then refined, its
-- predicate each such field's, read through the field, as a signature's
-- record is (Dnene14), named after the alias.
hasRefinedField :: Env.Env -> Src.Type -> Result i w Bool
hasRefinedField env (A.At _ tipe) =
  case tipe of
    Src.TParens inner _ ->
      hasRefinedField env inner
    Src.TRecord fields Nothing ->
      or <$> traverse (\field -> let (_, fieldType, _) = withoutWhere field in Maybe.isJust <$> refinedPositionAt env fieldType) fields
    _ ->
      Result.ok False

aliasBody :: Bool -> Env.Env -> Name.Name -> Src.Type -> Result i w (Can.Type, Maybe Can.AliasRefinement)
aliasBody readPredicate env alias srcType@(A.At region tipe) =
  case tipe of
    Src.TParens inner _
      | isNamed inner ->
          aliasBody readPredicate env alias inner
    -- A record with predicates on its fields (Dnene15) is the whole-record
    -- form: named as the alias names it, lowercased, or as the name written
    -- around it, and its fields' predicates joined to the one written there.
    Src.TNamed takenAt name inner maybePredicate
      | Just (plain, fieldPredicate) <- fieldPredicates (A.toValue name) inner ->
          do
            checkFieldNames inner
            canonicalizeAliasBody readPredicate env alias $
              A.At region (Src.TNamed takenAt name plain (Just (maybe fieldPredicate (\written -> andAlso region written fieldPredicate) maybePredicate)))
    _
      | Just (plain, fieldPredicate) <- fieldPredicates (lowerFirst alias) srcType ->
          do
            checkFieldNames srcType
            canonicalizeAliasBody readPredicate env alias $
              A.At region (Src.TNamed Nothing (A.At region (lowerFirst alias)) plain (Just fieldPredicate))
    Src.TNamed takenAt name@(A.At nameRegion nameValue) inner maybePredicate ->
      do
        maybe (Result.ok ()) (\at -> Result.throw (Error.TakenMisplaced at Error.TakenInAlias)) takenAt
        innerType <- canonicalize Error.InAlias env inner
        case maybePredicate of
          Nothing ->
            Result.throw (Error.RefinementNameUnused nameRegion nameValue)
          Just (predicate, source)
            | readPredicate ->
                do
                  let self = Named region [Can.Result] name innerType (Just predicate) source Nothing False Nothing
                  cpredicate <- canonicalizePredicate env (Scope self [self] []) predicate
                  Result.ok (innerType, Just (Can.AliasRefinement nameValue cpredicate source))
            | otherwise ->
                Result.ok (innerType, Just (Can.AliasRefinement nameValue (Can.at region (Can.Int 0)) source))
    _ ->
      (\t -> (t, Nothing)) <$> canonicalize Error.InAlias env srcType

-- | A variant's argument (geng-lang @m4-refine-t1.md@ TO13, Dnene17): a
-- refined alias, or a record with refined fields, is the constructor's
-- contract, asked where the constructor is applied and known where it is
-- matched, so the refinement comes back with the type. Anything else is
-- canonicalized as any type there is, so a name or a predicate written on the
-- argument itself is still refused, as Dnene17 has it.
canonicalizeVariantArg :: Env.Env -> Src.Type -> Result i w (Can.Type, Maybe Can.AliasRefinement)
canonicalizeVariantArg env srcType =
  do
    refined <- refinedPositionAt env srcType
    case refined of
      Just (tipe, refinement) -> Result.ok (tipe, Just refinement)
      Nothing -> (\tipe -> (tipe, Nothing)) <$> canonicalize Error.InConstructor env srcType

-- | The refined alias a signature's position is written as, when it is one,
-- canonicalized: its type, and its name and predicate (D872).
refinedAliasAt :: Env.Env -> Src.Type -> Result i w (Maybe (Can.Type, Can.AliasRefinement))
refinedAliasAt env (A.At typeRegion tipe) =
  let resolved found =
        case found of
          -- A refined record alias is a type invariant (geng-lang
          -- @m4-refine-t1.md@ TO17, Dnene22): every record of its shape is
          -- asked it where it is built and keeps it everywhere, so where it
          -- is written it is its type, with nothing asked of a caller and no
          -- name to give, and a record holding one is not refined by it.
          Env.Alias 0 _ _ (Can.TRecord _ Nothing) (Just _) -> False
          Env.Alias _ _ _ _ (Just _) -> True
          _ -> False
      expand name args info =
        do
          (ctype, refinement) <- canonicalizeType env typeRegion name (fmap snd args) info
          Result.ok ((,) ctype <$> refinement)
   in case tipe of
        Src.TParens inner _ ->
          refinedAliasAt env inner
        Src.TType region name args ->
          do
            info <- Env.findType region env name
            if resolved info then expand name args info else Result.ok Nothing
        Src.TTypeQual region home name args ->
          do
            info <- Env.findTypeQual region env home name
            if resolved info then expand name args info else Result.ok Nothing
        _ ->
          Result.ok Nothing

canonicalizeFields :: Env.Env -> [Src.TRecordField] -> [(A.Located Name.Name, Result i w Can.FieldType, ())]
canonicalizeFields env fields =
  let len = fromIntegral (length fields)
      canonicalizeField index (name, srcType, _) =
        (name, Can.FieldType index <$> canonicalize Error.InRecordField env srcType, ())
   in zipWith canonicalizeField [0 .. len] fields

-- SIGNATURES

-- | A value's signature, top-level or a @let@'s: its annotation, and the
-- arguments and result it names, each with its predicate if it is refined
-- (geng-lang @m4-refine.md@ D814, §RF17).
--
-- The annotation is the type with every name taken off, so nothing after
-- this sees a signature that names its arguments as different from one that
-- does not. The names are resolved here, each predicate's names against the
-- signature's own and the arguments the signatures around it name (D823),
-- and the type checker then checks each predicate as a @Bool@
-- ("Type.Constrain.Expression").
--
-- A name of this signature may be read by a @let@ inside the definition, so
-- two more things come back with the signature: the environment its body is
-- canonicalized in, which carries its names, and a check of the canonical
-- body, which refuses a name that nothing, nested or not, reads (D821).
toSignature :: Env.Env -> Name.Name -> Maybe Src.Context -> Src.Type -> Result i w Signature
toSignature env defName maybeContext srcType =
  do
    (tipe, named) <- spine env [] srcType
    freeVars <- addContext env (addFreeVars Map.empty tipe) maybeContext
    (refinements, unread) <- refine env named
    let enclosing = [Can.Enclosing defName (_name n) (_path n) (_type n) | n <- named]
    Result.ok $
      Signature
        { _annotation = Can.Forall freeVars tipe,
          _refinements = refinements,
          _bodyEnv = env {Env._signatures = Env._signatures env ++ enclosing},
          _defName = defName,
          _unread = unread
        }

-- | A canonical signature, and what its definition's body needs from it.
data Signature = Signature
  { _annotation :: Can.Annotation,
    _refinements :: [Can.Refinement],
    _bodyEnv :: Env.Env,
    _defName :: Name.Name,
    _unread :: [A.Located Name.Name]
  }

-- | The names no predicate of their own signature reads, refused unless a
-- @let@ in the canonical body reads them (D821, D823).
checkBody :: Signature -> Can.Expr -> Result i w ()
checkBody (Signature _ _ _ defName unread) body =
  if null unread
    then Result.ok ()
    else
      let nestedReads =
            [ A.toValue (Can._enc_name e)
            | r <- NodeId.exprRefinements body,
              e <- Can._ref_enclosing r,
              Can._enc_def e == defName
            ]
       in traverse_
            ( \(A.At region name) ->
                if name `elem` nestedReads
                  then Result.ok ()
                  else Result.throw (Error.RefinementNameUnused region name)
            )
            unread

-- | A name in a signature, before its predicate is canonicalized.
data Named = Named
  { _region :: A.Region,
    _path :: [Can.RefinementStep],
    _name :: A.Located Name.Name,
    _type :: Can.Type,
    _predicate :: Maybe Src.Expr,
    _source :: String,
    -- | The refined alias the position is written as (D872), whose predicate is
    -- the position's too.
    _alias :: Maybe Can.AliasRefinement,
    -- | Written as the alias alone, with no name of its own.
    _bare :: Bool,
    -- | Where @taken@ is written before the name, when it is (geng-lang
    -- @m4-own.md@ D920).
    _taken :: Maybe A.Region
  }

-- | The arrows of a signature, or of a callback inside one: each argument a
-- position, and the last arrow's target the result. Parentheses around the
-- arrows that are left, @a -> (b -> c)@, are the same arrows.
spine :: Env.Env -> [Can.RefinementStep] -> Src.Type -> Result i w (Can.Type, [Named])
spine env prefix =
  go 0
  where
    go index srcType@(A.At _ tipe) =
      case tipe of
        Src.TLambda arg rest _ ->
          do
            (argType, argNamed) <- position env (prefix ++ [Can.Arg index]) arg
            (restType, restNamed) <- go (index + 1) rest
            Result.ok (Can.TLambda argType restType, argNamed ++ restNamed)
        Src.TParens inner _
          | isArrow inner ->
              go index inner
        _ ->
          position env (prefix ++ [Can.Result]) srcType

-- | One argument or the result. It may be named; and when its type is a
-- function, a callback, its own arguments and result are positions too
-- (§RF13.2).
position :: Env.Env -> [Can.RefinementStep] -> Src.Type -> Result i w (Can.Type, [Named])
position env path srcType@(A.At region tipe) =
  case tipe of
    Src.TNamed takenAt name inner maybePredicate ->
      do
        aliased <- refinedPositionAt env inner
        case aliased of
          Just (innerType, refinement) ->
            Result.ok (innerType, [Named region path name innerType (fst <$> maybePredicate) (maybe "" snd maybePredicate) (Just refinement) False takenAt])
          Nothing ->
            do
              (innerType, innerNamed) <- positionType env path inner
              Result.ok (innerType, Named region path name innerType (fst <$> maybePredicate) (maybe "" snd maybePredicate) Nothing False takenAt : innerNamed)
    Src.TParens inner _
      | isNamed inner ->
          position env path inner
    _ ->
      do
        aliased <- refinedPositionAt env srcType
        case aliased of
          -- A refined alias with no name of its own here is the alias's name,
          -- made distinct from the signature's other names in 'refine'.
          Just (innerType, refinement) ->
            Result.ok (innerType, [Named region path (A.At region (Can._ar_name refinement)) innerType Nothing "" (Just refinement) True Nothing])
          Nothing ->
            positionType env path srcType

-- | A position refined by what it is written as: a refined alias (D872), or a
-- record one of whose fields is one.
refinedPositionAt :: Env.Env -> Src.Type -> Result i w (Maybe (Can.Type, Can.AliasRefinement))
refinedPositionAt env srcType =
  do
    aliased <- refinedAliasAt env srcType
    case aliased of
      Just _ -> Result.ok aliased
      Nothing -> recordRefinement env srcType

-- | A record at a signature's position with a refined alias for a field
-- (geng-lang @m4-refine-t1.md@ TO6, Dnene14): the record is the refined
-- position, and its predicate is each such field's alias's, read through the
-- field, so @{ term : Term, replies : Array Bytes }@ asks and knows
-- @Array.length t.term.named == 16@ as @Term@ alone would of @t@. A record's
-- field that is such a record is read the same way, to any depth. The record
-- is named as its first refined field's alias names its value, as a bare
-- alias is.
recordRefinement :: Env.Env -> Src.Type -> Result i w (Maybe (Can.Type, Can.AliasRefinement))
recordRefinement =
  recordRefinementAs True Nothing

-- | 'recordRefinement' with the record's name given, as an alias's body has
-- it (@term@ for @Term@, geng-lang @m4-refine-t1.md@ TO15, Dnene21), and
-- whether the predicates written on its fields are read: an alias's first
-- pass asks only whether it is refined, before a predicate's names are in
-- scope, and is given the fields' own placeholders.
recordRefinementAs :: Bool -> Maybe Name.Name -> Env.Env -> Src.Type -> Result i w (Maybe (Can.Type, Can.AliasRefinement))
recordRefinementAs readOwn named env (A.At region tipe) =
  case tipe of
    Src.TParens inner _ ->
      recordRefinementAs readOwn named env inner
    Src.TRecord fields ext
      | Maybe.isJust ext && any hasWhere fields ->
          -- Refused by 'canonicalize', as 'positionType' reaches it.
          Result.ok Nothing
      | otherwise ->
          do
            checkFieldNames srcRecord
            typedFields <- traverse fieldOf (map withoutWhere fields)
            let refinedFields = [(A.toValue name, r) | (name, _, Just r) <- typedFields]
                -- Named as its first refined field's alias names its value,
                -- or @record@ when only its fields' own predicates refine it.
                base =
                  case (named, refinedFields) of
                    (Just name, _) -> name
                    (Nothing, (_, Can.AliasRefinement first _ _) : _) -> first
                    (Nothing, []) -> Name.fromChars "record"
            case (refinedFields, fieldPredicates base srcRecord) of
              ([], Nothing) ->
                Result.ok Nothing
              (_, written) ->
                do
                  let len = fromIntegral (length fields)
                      typed = zipWith (\index (name, t, _) -> (name, Result.ok (Can.FieldType index t), ())) [0 .. len] typedFields
                  cfields <- sequenceA =<< Dups.checkFields typed
                  let recordType = Can.TRecord cfields (fmap (A.toValue . fst) ext)
                  binop <- predicateOperator env region (Name.fromChars "&&")
                  own <-
                    case written of
                      Nothing ->
                        Result.ok []
                      Just _
                        | not readOwn ->
                            Result.ok [(Can.at region (Can.Int 0), "")]
                      Just (_, (predicate, text)) ->
                        do
                          let self = Named region [Can.Result] (A.At region base) recordType (Just predicate) text Nothing False Nothing
                          cpredicate <- canonicalizePredicate env (Scope self [self] []) predicate
                          Result.ok [(cpredicate, text)]
                  let piece (field, Can.AliasRefinement from fieldPredicate fieldSource) =
                        ( throughField from base field region fieldPredicate,
                          renameSource from (Name.fromChars (Name.toChars base ++ "." ++ Name.toChars field)) fieldSource
                        )
                      grouped (p, text) = (p, if "||" `List.isInfixOf` text then "(" ++ text ++ ")" else text)
                      joined (p1, s1) (p2, s2) =
                        (Can.at region (Can.Binop (Env._op binop) (Env._op_target binop) (Env._op_annotation binop) p1 p2), s1 ++ " && " ++ s2)
                  case map piece refinedFields ++ own of
                    [] ->
                      Result.ok Nothing
                    [one] ->
                      Result.ok (Just (recordType, uncurry (Can.AliasRefinement base) one))
                    first : rest ->
                      Result.ok (Just (recordType, uncurry (Can.AliasRefinement base) (foldl joined (grouped first) (map grouped rest))))
    _ ->
      Result.ok Nothing
  where
    srcRecord = A.At region tipe
    fieldOf (name, srcType, _) =
      do
        aliased <- refinedPositionAt env srcType
        case aliased of
          Just (t, r) -> Result.ok (name, t, Just r)
          Nothing -> (\t -> (name, t, Nothing)) <$> canonicalize Error.InRecordField env srcType

-- | An alias's predicate read of a record's field: the alias's name as
-- @record.field@, every node at the position.
throughField :: Name.Name -> Name.Name -> Name.Name -> A.Region -> Can.Expr -> Can.Expr
throughField from record field region (Can.Expr nid _ expr) =
  let go = throughField from record field region
   in case expr of
        Can.VarLocal name
          | name == from ->
              Can.at region (Can.Access (Can.at region (Can.VarLocal record)) (A.At region field))
        Can.Negate inner -> Can.Expr nid region (Can.Negate (go inner))
        Can.Call func args -> Can.Expr nid region (Can.Call (go func) (map go args))
        Can.Binop op target annotation left right -> Can.Expr nid region (Can.Binop op target annotation (go left) (go right))
        Can.Access inner f -> Can.Expr nid region (Can.Access (go inner) f)
        other -> Can.Expr nid region other

-- FIELD PREDICATES

-- | A closed record type with a predicate written after a field's type
-- (geng-lang @m4-refine-t1.md@ TO8, Dnene15): the record without them, and
-- their conjunction as the predicate of the record named @base@, each field
-- the record has, written bare, read as @base@'s field, so @index <
-- Array.length items@ is @m.index < Array.length m.items@ for @m@. A field's
-- name hides any other in a predicate, as a @let@'s would. Nothing when no
-- field has one, or when the record is extensible, which 'canonicalize'
-- refuses.
fieldPredicates :: Name.Name -> Src.Type -> Maybe (Src.Type, (Src.Expr, String))
fieldPredicates base (A.At region tipe) =
  case tipe of
    Src.TParens inner _ ->
      fieldPredicates base inner
    Src.TRecord fields Nothing ->
      let names = [A.toValue name | (name, _, _) <- fields]
          written = [predicate | (_, A.At _ (Src.TWhere _ predicate), _) <- fields]
          piece (predicate, text) = (throughRecord base names predicate, prefixFields base names text)
       in case map piece written of
            [] -> Nothing
            first : rest -> Just (A.At region (Src.TRecord (map withoutWhere fields) Nothing), foldl (andAlso region) first rest)
    _ ->
      Nothing

-- | Each name a field's predicate reads bare is one of its record's fields;
-- anything else, an argument's name or a value in scope, it may not read.
checkFieldNames :: Src.Type -> Result i w ()
checkFieldNames (A.At _ tipe) =
  case tipe of
    Src.TParens inner _ ->
      checkFieldNames inner
    Src.TRecord fields _ ->
      let names = [A.toValue name | (name, _, _) <- fields]
          written = [predicate | (_, A.At _ (Src.TWhere _ (predicate, _)), _) <- fields]
       in case [at | at@(A.At _ name) <- concatMap bareNames written, name `notElem` names] of
            [] -> Result.ok ()
            A.At region name : _ -> Result.throw (Error.FieldRefinementUnknown region name names)
    _ ->
      Result.ok ()

-- | The lowercase names a predicate reads, each where it is read.
bareNames :: Src.Expr -> [A.Located Name.Name]
bareNames (A.At region expr) =
  case expr of
    Src.Var Src.LowVar name -> [A.At region name]
    Src.Negate inner -> bareNames inner
    Src.Binops segments final -> concatMap (\(e, _, _) -> bareNames e) segments ++ bareNames final
    Src.Call func args -> bareNames func ++ concatMap (bareNames . snd) args
    Src.Access inner _ -> bareNames inner
    Src.Parens _ inner _ -> bareNames inner
    _ -> []

hasWhere :: Src.TRecordField -> Bool
hasWhere (_, A.At _ tipe, _) =
  case tipe of
    Src.TWhere _ _ -> True
    _ -> False

withoutWhere :: Src.TRecordField -> Src.TRecordField
withoutWhere field@(name, A.At _ tipe, comments) =
  case tipe of
    Src.TWhere inner _ -> (name, inner, comments)
    _ -> field

-- | Two predicates joined by @&&@, each grouped when it holds an @||@, in the
-- tree and in the text.
andAlso :: A.Region -> (Src.Expr, String) -> (Src.Expr, String) -> (Src.Expr, String)
andAlso region (left, leftText) (right, rightText) =
  let grouped (e@(A.At at _), text) =
        if "||" `List.isInfixOf` text then (A.At at (Src.Parens [] e []), "(" ++ text ++ ")") else (e, text)
      (l, lt) = grouped (left, leftText)
      (rr, rt) = grouped (right, rightText)
      noComments = SC.BinopsSegmentComments [] []
   in (A.At region (Src.Binops [(l, A.At region (Name.fromChars "&&"), noComments)] rr), lt ++ " && " ++ rt)

-- | A field predicate's bare field names as the record's fields.
throughRecord :: Name.Name -> [Name.Name] -> Src.Expr -> Src.Expr
throughRecord base names (A.At region expr) =
  let go = throughRecord base names
   in A.At region $
        case expr of
          Src.Var Src.LowVar name
            | name `elem` names ->
                Src.Access (A.At region (Src.Var Src.LowVar base)) (A.At region name)
          Src.Negate inner -> Src.Negate (go inner)
          Src.Binops segments final -> Src.Binops [(go e, op, c) | (e, op, c) <- segments] (go final)
          Src.Call func args -> Src.Call (go func) [(c, go a) | (c, a) <- args]
          Src.Access inner field -> Src.Access (go inner) field
          Src.Parens before inner after -> Src.Parens before (go inner) after
          other -> other

-- | The source of a field predicate with each bare field name read through
-- the record, as 'throughRecord' reads the tree.
prefixFields :: Name.Name -> [Name.Name] -> String -> String
prefixFields base names =
  go ' '
  where
    fields = map Name.toChars names
    prefix = Name.toChars base ++ "."
    isNameChar c = Char.isAlphaNum c || c == '_'
    go _ [] = []
    go before text@(c : rest)
      | isNameChar c =
          let (word, after) = span isNameChar text
           in (if word `elem` fields && before /= '.' && not (isNameChar before) then prefix ++ word else word) ++ go (last word) after
      | otherwise = c : go c rest

lowerFirst :: Name.Name -> Name.Name
lowerFirst name =
  case Name.toChars name of
    c : rest -> Name.fromChars (Char.toLower c : rest)
    [] -> name

positionType :: Env.Env -> [Can.RefinementStep] -> Src.Type -> Result i w (Can.Type, [Named])
positionType env path srcType =
  if isArrow srcType
    then spine env path srcType
    else (\tipe -> (tipe, [])) <$> canonicalize Error.InTypeArgument env srcType

isArrow :: Src.Type -> Bool
isArrow (A.At _ tipe) =
  case tipe of
    Src.TLambda {} -> True
    Src.TParens inner _ -> isArrow inner
    _ -> False

isNamed :: Src.Type -> Bool
isNamed (A.At _ tipe) =
  case tipe of
    Src.TNamed {} -> True
    Src.TParens inner _ -> isNamed inner
    _ -> False

-- REFINE

-- | Every name once in a signature and in the signatures around it; each
-- predicate canonicalized against the names it may see; and every name read
-- by some predicate or refined itself. A name that only a @let@ in the body
-- could read, an argument of the signature's own arrows, comes back unread,
-- to be checked against the body; any other is refused here.
refine :: Env.Env -> [Named] -> Result i w ([Can.Refinement], [A.Located Name.Name])
refine env given =
  do
    let named = distinctAliasNames (Env._signatures env) (Map.keys (Env._vars env)) given
    checkDuplicates named
    traverse_ checkTaken named
    traverse_ (checkShadows (Env._signatures env)) named
    refinements <- traverse (refineOne env named) named
    let readNames = concatMap (maybe [] predicateLocals . Can._ref_predicate) refinements
    unread <- concat <$> traverse (checkRead readNames) named
    Result.ok (refinements, unread)

traverse_ :: (a -> Result i w ()) -> [a] -> Result i w ()
traverse_ f xs = () <$ traverse f xs

checkDuplicates :: [Named] -> Result i w ()
checkDuplicates named =
  let byName = Map.fromListWith (flip (++)) [(A.toValue (_name n), [A.toRegion (_name n)]) | n <- named]
   in traverse_
        ( \(name, regions) ->
            case regions of
              first : second : _ -> Result.throw (Error.RefinementNameDuplicate name first second)
              _ -> Result.ok ()
        )
        (Map.toList byName)

-- | @taken@ says the function takes an argument's value (geng-lang
-- @m4-own.md@ D920), so it is written on an argument of the signature's own
-- arrows and nowhere else (D943): the result is the function's to give, and
-- what a callback does with its arguments is inferred and never written
-- (D936).
checkTaken :: Named -> Result i w ()
checkTaken n =
  case _taken n of
    Nothing -> Result.ok ()
    Just at ->
      case _path n of
        [Can.Arg _] -> Result.ok ()
        [Can.Result] -> Result.throw (Error.TakenMisplaced at Error.TakenOnResult)
        _ -> Result.throw (Error.TakenMisplaced at Error.TakenInCallback)

-- | A name that nothing reads and that is not refined is refused, as D819
-- refused it: it would look as if it meant something (D821). One a @let@
-- could still read is handed back. A taken name means something unread
-- (D942).
checkRead :: [Name.Name] -> Named -> Result i w [A.Located Name.Name]
checkRead readNames n =
  case _predicate n of
    Just _ -> Result.ok []
    Nothing
      | Maybe.isJust (_alias n) -> Result.ok []
      | Maybe.isJust (_taken n) -> Result.ok []
    Nothing ->
      let A.At region name = _name n
       in if name `elem` readNames
            then Result.ok []
            else
              if isOutermostArg (_path n)
                then Result.ok [_name n]
                else Result.throw (Error.RefinementNameUnused region name)

-- | An argument of the signature's own arrows, the only names a @let@ inside
-- the definition may read (D823): the result has no value until the body is
-- done, and a callback's arguments none until it is called.
isOutermostArg :: [Can.RefinementStep] -> Bool
isOutermostArg path =
  case path of
    [Can.Arg _] -> True
    _ -> False

-- | No signature gives a name a signature around it gives, as no @let@ may
-- shadow a name in Gren: the predicate's reading of it would depend on which
-- was nearer.
checkShadows :: [Can.Enclosing] -> Named -> Result i w ()
checkShadows enclosing n =
  let A.At region name = _name n
   in case filter ((== name) . A.toValue . Can._enc_name) enclosing of
        outer : _ -> Result.throw (Error.RefinementNameShadows name (A.toRegion (Can._enc_name outer)) region)
        [] -> Result.ok ()

refineOne :: Env.Env -> [Named] -> Named -> Result i w Can.Refinement
refineOne env named n =
  do
    let enclosing = Env._signatures env
    written <- traverse (canonicalizePredicate env (Scope n named enclosing)) (_predicate n)
    (predicate, source) <- withAlias env n written
    let readNames = maybe [] predicateLocals predicate
    Result.ok $
      Can.Refinement
        { Can._ref_region = _region n,
          Can._ref_path = _path n,
          Can._ref_name = _name n,
          Can._ref_type = _type n,
          Can._ref_predicate = predicate,
          Can._ref_source = source,
          Can._ref_taken = Maybe.isJust (_taken n),
          Can._ref_enclosing = filter ((`elem` readNames) . A.toValue . Can._enc_name) enclosing
        }

-- | A position written as a refined alias (D872): the alias's predicate read
-- of the position's name, and with a predicate written there too, both, the
-- alias's first. The source is the alias's with its name replaced, so an
-- error and the documentation say what is asked of this argument.
withAlias :: Env.Env -> Named -> Maybe Can.Expr -> Result i w (Maybe Can.Expr, String)
withAlias env n written =
  case _alias n of
    Nothing ->
      Result.ok (written, _source n)
    Just (Can.AliasRefinement aliasName aliasPredicate aliasSource) ->
      let A.At region name = _name n
          own = renamePredicate aliasName name region aliasPredicate
          ownSource = renameSource aliasName name aliasSource
       in case written of
            Nothing ->
              Result.ok (Just own, ownSource)
            Just more ->
              do
                binop <- predicateOperator env region (Name.fromChars "&&")
                Result.ok
                  ( Just (Can.at region (Can.Binop (Env._op binop) (Env._op_target binop) (Env._op_annotation binop) own more)),
                    grouped ownSource ++ " && " ++ grouped (_source n)
                  )
  where
    grouped text =
      if "||" `List.isInfixOf` text then "(" ++ text ++ ")" else text

-- | The alias's predicate over the position's name, every node at the
-- position, since the alias's own regions are in the module that wrote it.
renamePredicate :: Name.Name -> Name.Name -> A.Region -> Can.Expr -> Can.Expr
renamePredicate from to region (Can.Expr nid _ expr) =
  let go = renamePredicate from to region
   in Can.Expr nid region $
        case expr of
          Can.VarLocal name | name == from -> Can.VarLocal to
          Can.Negate inner -> Can.Negate (go inner)
          Can.Call func args -> Can.Call (go func) (map go args)
          Can.Binop op target annotation left right -> Can.Binop op target annotation (go left) (go right)
          Can.Access record field -> Can.Access (go record) field
          other -> other

-- | The alias's source with its name replaced wherever it is a name of its
-- own, not part of a longer one or a qualified measure's.
renameSource :: Name.Name -> Name.Name -> String -> String
renameSource from to =
  go ' '
  where
    old = Name.toChars from
    new = Name.toChars to
    isNameChar c = Char.isAlphaNum c || c == '_'
    go _ [] = []
    go before text@(c : rest)
      | isNameChar c =
          let (word, after) = span isNameChar text
           in (if word == old && before /= '.' then new else word) ++ go (lastOf word) after
      | otherwise = c : go c rest
    lastOf word = if null word then ' ' else last word

-- | A refined alias written with no name of its own is named as the alias
-- names its value, unless the signature, or one around it, already gives that
-- name, or a value in scope has it; then a number is added until it is one
-- none of them has. A value's name is avoided because a predicate's name is
-- read where the module's values are in scope, and @term@ for a bare @Term@
-- would be read as a function @term@ beside it (Dnene21).
distinctAliasNames :: [Can.Enclosing] -> [Name.Name] -> [Named] -> [Named]
distinctAliasNames enclosing values named =
  let written = [A.toValue (_name n) | n <- named, not (isBare n)] ++ map (A.toValue . Can._enc_name) enclosing ++ values
      isBare = _bare
      fresh taken base =
        let numbered i = if i == (1 :: Int) then base else Name.fromChars (Name.toChars base ++ show i)
            go i = if numbered i `elem` taken then go (i + 1) else numbered i
         in go 1
      step (taken, out) n =
        if isBare n
          then
            let A.At region base = _name n
                name = fresh taken base
             in (name : taken, out ++ [n {_name = A.At region name}])
          else (taken, out ++ [n])
   in snd (foldl step (written, []) named)

predicateLocals :: Can.Expr -> [Name.Name]
predicateLocals (Can.Expr _ _ expr) =
  case expr of
    Can.VarLocal name -> [name]
    Can.Negate inner -> predicateLocals inner
    Can.Binop _ _ _ left right -> predicateLocals left ++ predicateLocals right
    Can.Call func args -> concatMap predicateLocals (func : args)
    Can.Access record _ -> predicateLocals record
    _ -> []

-- SCOPE

-- | The name whose predicate this is, every name in the signature, and every
-- name the signatures around it give.
data Scope = Scope Named [Named] [Can.Enclosing]

-- | What a predicate may name (§RF13.2): every argument of its own arrows and
-- of the arrows around them, before or after it; and a result only in that
-- result's own predicate. A callback's arguments are seen by the callback's
-- predicates and no others, since they exist only for a call of it. Around a
-- @let@, the arguments of the enclosing signatures' own arrows too (D823).
data Seen
  = Seen Can.Type
  | SeenOnlyByResult
  | SeenOnlyInCallback
  | Unknown [Name.Name]

lookupName :: Scope -> Name.Name -> Seen
lookupName scope@(Scope self named enclosing) name =
  case filter ((== name) . A.toValue . _name) named of
    other : _ ->
      let otherPath = _path other
          selfPath = _path self
       in if not (init otherPath `List.isPrefixOf` init selfPath)
            then SeenOnlyInCallback
            else
              if last otherPath == Can.Result && otherPath /= selfPath
                then SeenOnlyByResult
                else Seen (_type other)
    [] ->
      case filter ((== name) . A.toValue . Can._enc_name) enclosing of
        outer : _
          | isOutermostArg (Can._enc_path outer) -> Seen (Can._enc_type outer)
          | last (Can._enc_path outer) == Can.Result -> SeenOnlyByResult
          | otherwise -> SeenOnlyInCallback
        [] ->
          let candidates = map (A.toValue . _name) named ++ map (A.toValue . Can._enc_name) enclosing
           in Unknown [other | other <- candidates, isSeen (lookupName scope other)]

isSeen :: Seen -> Bool
isSeen seen =
  case seen of
    Seen _ -> True
    _ -> False

-- PREDICATES

-- | A predicate as the parser builds it (D815): literals, names, a measure
-- applied to a name, @not@, @True@, @False@, unary @-@, parentheses and
-- D808's operators, made into the expression it is.
--
-- Every name it reads is the signature's, never a value in scope: a local or a
-- top-level value of the same name is not what the predicate means, and D808
-- allows nothing else. A name read directly must be an 'Int', the checker's
-- only number (D799), or a 'Bool', a condition (geng-lang
-- @m4-refine-t1.md@ TO20, Dnene29); any other is read only through a
-- measure. The type
-- checker reads the operators at 'Int' signatures in place of their classes',
-- so @x < y@ on two 'Float's is a type error rather than a predicate the
-- checker cannot read, and a @*@ needs a literal on one side, the arithmetic
-- being linear (§RF9).
canonicalizePredicate :: Env.Env -> Scope -> Src.Expr -> Result i w Can.Expr
canonicalizePredicate env scope (A.At region expression) =
  case expression of
    Src.Int int _ ->
      Result.ok (Can.at region (Can.Int int))
    Src.Negate inner ->
      Can.at region . Can.Negate <$> canonicalizePredicate env scope inner
    Src.Parens _ inner _ ->
      canonicalizePredicate env scope inner
    Src.Var Src.LowVar _ ->
      intPath
    Src.Access _ _ ->
      intPath
    Src.Var Src.CapVar name ->
      do
        ctor <- Env.findCtor region env name
        case ctor of
          Env.Ctor home typeName (Can.Union vars _ _ opts) index args
            | home == ModuleName.basics && typeName == Name.bool ->
                let tipe = foldr Can.TLambda (Can.TType home typeName (map Can.TVar vars)) args
                    freeVars = Map.fromList (map (\v -> (v, [])) vars)
                 in Result.ok (Can.at region (Can.VarCtor opts home name index (Can.Forall freeVars tipe)))
          _ ->
            Result.throw (Error.RefinementNotCore region name)
    Src.Call (A.At funcRegion (Src.VarQual Src.LowVar prefix name)) [(_, arg)]
      | isPath arg,
        ModuleName.Canonical _ own <- Env._home env,
        prefix == own,
        Just (Env.TopLevel _) <- Map.lookup name (Env._vars env),
        (Env._home env, name) `elem` measures ->
          -- A measure's own module names it by its own name, which no import
          -- gives it, so that @core@'s primitives can be refined with the
          -- predicate every other module writes (@m4-refine.md@ §RF27, D846).
          --
          -- It is made a foreign reference typed from its argument, which must
          -- be of the module's own container type. A top-level reference would
          -- need the measure in scope where the signature is solved, and a
          -- predicate is no dependency of its definition, so @unsafeGet@ can
          -- be solved before @length@ is.
          do
            (carg, argType) <- predicatePath scope arg
            case Type.iteratedDealias argType of
              Can.TType typeHome _ typeArgs
                | ownsType (Env._home env) typeHome ->
                    let vars = Map.fromList [(v, []) | Can.TVar v <- typeArgs]
                        answer = if (Env._home env, name) `elem` boolMeasures then Name.bool else Name.int
                        annotation = Can.Forall vars (Can.TLambda argType (Can.TType ModuleName.basics answer []))
                     in Result.ok (Can.at region (Can.Call (Can.at funcRegion (Can.VarForeign (Env._home env) name annotation)) [carg]))
              _ ->
                Result.throw (Error.RefinementNotMeasure funcRegion prefix name)
    Src.Call (A.At funcRegion (Src.Var Src.LowVar name)) [(_, arg)]
      | isPath arg,
        Just (Env.TopLevel _) <- Map.lookup name (Env._vars env),
        Just (answersBool, measured) <- Map.lookup (Env._home env, name) (Env._measures env) ->
          -- This module's own measure, by its own name (geng-lang
          -- @m4-refine-t1.md@ TO14), made a foreign reference typed from its
          -- argument as `core`'s own are above, and held to the type it
          -- measures by name, since nothing else checks that type here.
          do
            (carg, argType) <- predicatePath scope arg
            if measures_ (Env._home env) measured argType
              then
                let answer = if answersBool then Name.bool else Name.int
                    annotation = Can.Forall Map.empty (Can.TLambda argType (Can.TType ModuleName.basics answer []))
                 in Result.ok (Can.at region (Can.Call (Can.at funcRegion (Can.VarForeign (Env._home env) name annotation)) [carg]))
              else Result.throw (Error.RefinementNotMeasure funcRegion (Name.fromChars "") name)
    Src.Call (A.At funcRegion (Src.Var Src.LowVar name)) [(_, arg)] ->
      do
        case Map.lookup name (Env._vars env) of
          Just (Env.Foreign home annotation)
            | home == ModuleName.basics ->
                do
                  carg <- canonicalizePredicate env scope arg
                  Result.ok (Can.at region (Can.Call (Can.at funcRegion (Can.VarForeign home name annotation)) [carg]))
            | Map.member (home, name) (Env._measures env),
              isPath arg ->
                -- An imported measure the import exposes (TO14).
                do
                  (carg, _) <- predicatePath scope arg
                  Result.ok (Can.at region (Can.Call (Can.at funcRegion (Can.VarForeign home name annotation)) [carg]))
            | otherwise ->
                -- An imported function that is no measure.
                Result.throw (Error.RefinementNotMeasure funcRegion (ModuleName._module home) name)
          Just (Env.TopLevel _) ->
            -- This module's own function, not declared `@measure` (TO14).
            Result.throw (Error.RefinementNotMeasure funcRegion (Name.fromChars "") name)
          _ ->
            Result.throw (Error.RefinementNotCore funcRegion name)
    Src.Call (A.At funcRegion (Src.VarQual Src.LowVar prefix name)) [(_, arg)]
      | isPath arg ->
          do
            func <-
              case Map.lookup name =<< Map.lookup prefix (Env._q_vars env) of
                Just (Env.Specific home annotation)
                  | (home, name) `elem` measures || Map.member (home, name) (Env._measures env) ->
                      Result.ok (Can.at funcRegion (Can.VarForeign home name annotation))
                _ ->
                  Result.throw (Error.RefinementNotMeasure funcRegion prefix name)
            (carg, _) <- predicatePath scope arg
            Result.ok (Can.at region (Can.Call func [carg]))
    Src.Binops ops final ->
      do
        tree <-
          Binops.run region
            =<< ( Binops.More
                    <$> traverse (\(expr, A.At opRegion op, _) -> (,) <$> canonicalizePredicate env scope expr <*> predicateOperator env opRegion op) ops
                    <*> canonicalizePredicate env scope final
                )
        checkShape (scopeBool scope) tree
        Result.ok tree
    _ ->
      -- The parser builds nothing else (D815).
      Result.throw (Error.RefinementNotCore region (Name.fromChars "?"))
  where
    intPath =
      do
        (cexpr, tipe) <- predicatePath scope (A.At region expression)
        if isInt tipe || isBool tipe
          then Result.ok cexpr
          else Result.throw (Error.RefinementNameNotInt region (Name.fromChars (pathText expression)))

-- | A name, or a name's fields (geng-lang @m4-refine-t1.md@ TO5, Dnene13):
-- the read and its type, each field looked up in its record's type.
predicatePath :: Scope -> Src.Expr -> Result i w (Can.Expr, Can.Type)
predicatePath scope (A.At region expression) =
  case expression of
    Src.Access record (A.At fieldRegion field) ->
      do
        (crecord, recordType) <- predicatePath scope record
        case Type.iteratedDealias recordType of
          Can.TRecord fieldTypes _ ->
            case Map.lookup field fieldTypes of
              Just (Can.FieldType _ tipe) ->
                Result.ok (Can.at region (Can.Access crecord (A.At fieldRegion field)), tipe)
              Nothing ->
                Result.throw (Error.RefinementNoSuchField fieldRegion (Name.fromChars (pathText (A.toValue record))) field (Map.keys fieldTypes))
          _ ->
            Result.throw (Error.RefinementNoSuchField fieldRegion (Name.fromChars (pathText (A.toValue record))) field [])
    Src.Var Src.LowVar name ->
      do
        tipe <- findName region scope name
        Result.ok (Can.at region (Can.VarLocal name), tipe)
    _ ->
      Result.throw (Error.RefinementNotCore region (Name.fromChars "?"))

isPath :: Src.Expr -> Bool
isPath (A.At _ expression) =
  case expression of
    Src.Var Src.LowVar _ -> True
    Src.Access record _ -> isPath record
    _ -> False

pathText :: Src.Expr_ -> String
pathText expression =
  case expression of
    Src.Var _ name -> Name.toChars name
    Src.Access (A.At _ record) (A.At _ field) -> pathText record ++ "." ++ Name.toChars field
    _ -> "?"

findName :: A.Region -> Scope -> Name.Name -> Result i w Can.Type
findName region scope name =
  case lookupName scope name of
    Seen tipe -> Result.ok tipe
    SeenOnlyByResult -> Result.throw (Error.RefinementNameOutOfScope region name True)
    SeenOnlyInCallback -> Result.throw (Error.RefinementNameOutOfScope region name False)
    Unknown seen -> Result.throw (Error.RefinementNameUnknown region name seen)

isInt :: Can.Type -> Bool
isInt tipe =
  case Type.iteratedDealias tipe of
    Can.TType home name [] -> home == ModuleName.basics && name == Name.int
    _ -> False

-- | A 'Bool' read directly is a condition: @not keep || room > 0@ (Dnene29).
isBool :: Can.Type -> Bool
isBool tipe =
  case Type.iteratedDealias tipe of
    Can.TType home name [] -> home == ModuleName.basics && name == Name.bool
    _ -> False

-- | Whether a type is the one a module's own measure measures, by the name
-- its annotation writes (geng-lang @m4-refine-t1.md@ TO14): a custom type or
-- a record alias the module declares.
measures_ :: ModuleName.Canonical -> Maybe Name.Name -> Can.Type -> Bool
measures_ home measured tipe =
  case (measured, tipe) of
    (Just name, Can.TType typeHome typeName _) -> typeHome == home && typeName == name
    (Just name, Can.TAlias typeHome typeName _ _) -> typeHome == home && typeName == name
    _ -> False

-- | Whether a measure's own module may apply it to a type: its own, or, for
-- @Array.Builder@, the transient its @Builder@ is an alias of (geng-lang
-- @m4-refine-t1.md@ TO10).
ownsType :: ModuleName.Canonical -> ModuleName.Canonical -> Bool
ownsType home typeHome =
  typeHome == home
    || ( home == ModuleName.Canonical Pkg.core (Name.fromChars "Array.Builder")
           && typeHome == ModuleName.Canonical Pkg.core (Name.fromChars "Array.Transient")
       )

-- | @core@'s measures (D808): the size of each of its collections.
measures :: [(ModuleName.Canonical, Name.Name)]
measures =
  [ (ModuleName.array, Name.fromChars "length"),
    (ModuleName.bytes, Name.fromChars "length"),
    (ModuleName.string, Name.fromChars "count"),
    (ModuleName.dict, Name.fromChars "count"),
    (ModuleName.Canonical Pkg.core (Name.fromChars "Set"), Name.fromChars "count"),
    -- D1031's owned bytes (geng-lang @m4-owned-pages.md@ §OP13).
    (ModuleName.bytesOwned, Name.fromChars "length"),
    -- Not exposed by @core@, so only @core@'s primitives name it (D846).
    (ModuleName.Canonical Pkg.core (Name.fromChars "Array.Transient"), Name.fromChars "length"),
    -- A builder is the transient, under the name a program may write
    -- (geng-lang @m4-refine-t1.md@ TO10).
    (ModuleName.Canonical Pkg.core (Name.fromChars "Array.Builder"), Name.fromChars "length"),
    -- The same for the bytes transient (D863, @m4-refine.md@ §RF32).
    (ModuleName.Canonical Pkg.core (Name.fromChars "Bytes.Transient"), Name.fromChars "length")
  ]
    ++ boolMeasures

-- | @core@'s measures that answer a 'Bool': which constructor a value is
-- (geng-lang @m4-refine-t1.md@ Dnene17). Each is a condition, not a sum.
boolMeasures :: [(ModuleName.Canonical, Name.Name)]
boolMeasures =
  [ (ModuleName.Canonical Pkg.core (Name.fromChars "Maybe"), Name.fromChars "isJust"),
    (ModuleName.Canonical Pkg.core (Name.fromChars "Result"), Name.fromChars "isOk")
  ]

-- | An operator of D808's, resolved as any operator is.
predicateOperator :: Env.Env -> A.Region -> Name.Name -> Result i w Env.Binop
predicateOperator env region op =
  do
    binop <- Env.findBinop region env op
    let home =
          case Env._op_target binop of
            Can.OpValue h _ -> h
            Can.OpMethod (Can.Class h _) _ _ -> h
    if home == ModuleName.basics && Name.toChars op `elem` operators
      then Result.ok binop
      else Result.throw (Error.RefinementNotCore region op)

-- | D808's operators. The type checker reads them at the 'Int' signatures
-- D822 gives them ("Type.Constrain.Expression"); here each keeps its own
-- annotation, so the elaborator gives it the witness it takes anywhere else
-- and the lowering writes it as a body's operator is written (§RF18).
operators :: [String]
operators =
  ["+", "-", "*", "<", "<=", ">", ">=", "==", "/=", "&&", "||"]

-- | What §RF13.4's layers said that a chain does not: a @*@ multiplies at
-- most two values, @size * stride@ but not @a * b * c@, which the checker
-- reads as an atom of its own (geng-lang @m4-refine-t1.md@ TO19, Dnene21;
-- until then one side was a literal, D808), and a comparison compares
-- two sums, never two conditions, but that @==@ and @/=@ may compare two
-- conditions, as @Maybe.isJust r == (Array.length a > 0)@ does (Dnene17).
checkShape :: (Can.Expr -> Bool) -> Can.Expr -> Result i w ()
checkShape boolAt (Can.Expr _ region expr) =
  case expr of
    Can.Binop op _ _ left right ->
      do
        checkShape boolAt left
        checkShape boolAt right
        if Name.toChars op == "*" && degree left + degree right > 2
          then Result.throw (Error.RefinementNonlinear region)
          else Result.ok ()
        if Name.toChars op `elem` comparisons && not (equatesConditions boolAt op left right)
          then traverse_ checkSum [left, right]
          else Result.ok ()
    Can.Negate inner -> checkShape boolAt inner
    Can.Call _ args -> traverse_ (checkShape boolAt) args
    _ -> Result.ok ()
  where
    checkSum operand =
      if isCondition boolAt operand
        then Result.throw (Error.RefinementComparesConditions (Can.exprRegion operand))
        else Result.ok ()

-- | Whether a predicate's path is a 'Bool', a condition (Dnene29), by the
-- types of the names it starts from.
boolPath :: Map.Map Name.Name Can.Type -> Can.Expr -> Bool
boolPath types e =
  maybe False isBool (pathTypeIn types e)

pathTypeIn :: Map.Map Name.Name Can.Type -> Can.Expr -> Maybe Can.Type
pathTypeIn types (Can.Expr _ _ expr) =
  case expr of
    Can.VarLocal name -> Map.lookup name types
    Can.Access inner (A.At _ field) ->
      case Type.iteratedDealias <$> pathTypeIn types inner of
        Just (Can.TRecord fields _) -> (\(Can.FieldType _ t) -> t) <$> Map.lookup field fields
        _ -> Nothing
    _ -> Nothing

-- | 'boolPath' over the names a predicate's scope sees.
scopeBool :: Scope -> Can.Expr -> Bool
scopeBool scope e =
  case root e of
    Just name | Seen t <- lookupName scope name -> boolPath (Map.singleton name t) e
    _ -> False
  where
    root (Can.Expr _ _ x) =
      case x of
        Can.VarLocal n -> Just n
        Can.Access inner _ -> root inner
        _ -> Nothing

comparisons :: [String]
comparisons =
  ["<", "<=", ">", ">=", "==", "/="]

-- | @==@ or @/=@ between two conditions, which the type checker reads at
-- 'Bool' ("Type.Constrain.Expression").
equatesConditions :: (Can.Expr -> Bool) -> Name.Name -> Can.Expr -> Can.Expr -> Bool
equatesConditions boolAt op left right =
  Name.toChars op `elem` ["==", "/="] && isCondition boolAt left && isCondition boolAt right

-- | A condition: a comparison, @&&@, @||@, a call of @not@ or of a measure
-- answering a 'Bool', @True@ or @False@, or a 'Bool' read directly (Dnene29).
isCondition :: (Can.Expr -> Bool) -> Can.Expr -> Bool
isCondition boolAt e@(Can.Expr _ _ expr) =
  boolAt e ||
  case expr of
    Can.Binop op _ _ _ _ -> Name.toChars op `elem` ("&&" : "||" : comparisons)
    Can.Call (Can.Expr _ _ (Can.VarForeign home name _)) _ -> home == ModuleName.basics || (home, name) `elem` boolMeasures
    Can.VarCtor {} -> True
    _ -> False

-- | How many values a product multiplies: 0 for a literal, 2 for @a * b@.
degree :: Can.Expr -> Int
degree e@(Can.Expr _ _ expr)
  | isLiteral e = 0
  | otherwise =
      case expr of
        Can.Binop op _ _ left right
          | Name.toChars op == "*" -> degree left + degree right
          | Name.toChars op `elem` ["+", "-"] -> max (degree left) (degree right)
        Can.Negate inner -> degree inner
        _ -> 1

isLiteral :: Can.Expr -> Bool
isLiteral (Can.Expr _ _ expr) =
  case expr of
    Can.Int _ -> True
    Can.Negate inner -> isLiteral inner
    _ -> False

-- CANONICALIZE TYPE

-- | A type named with its arguments, and the alias's refinement when it is a
-- refined alias (D872), which the caller places or refuses.
canonicalizeType :: Env.Env -> A.Region -> Name.Name -> [Src.Type] -> Env.Type -> Result i w (Can.Type, Maybe Can.AliasRefinement)
canonicalizeType env region name args info =
  do
    cargs <- traverse (canonicalize Error.InTypeArgument env) args
    case info of
      Env.Alias arity home argNames aliasedType refinement ->
        checkArity arity region name args $
          (Can.TAlias home name (zip argNames cargs) (Can.Holey aliasedType), refinement)
      Env.Union arity home ->
        checkArity arity region name args $
          (Can.TType home name cargs, Nothing)

checkArity :: Int -> A.Region -> Name.Name -> [A.Located arg] -> answer -> Result i w answer
checkArity expected region name args answer =
  let actual = length args
   in if expected == actual
        then Result.ok answer
        else Result.throw (Error.BadArity region Error.TypeArity name expected actual)

-- ADD FREE VARS

-- | The annotation's bound variables, each with an empty constraint list.
--
-- Empty here and filled by `addContext` above, which is the only thing that
-- may fill it: a constraint is written on the annotation, and a variable the
-- author said nothing about is unconstrained.
addFreeVars :: Map.Map Name.Name [Can.Class] -> Can.Type -> Map.Map Name.Name [Can.Class]
addFreeVars freeVars tipe =
  case tipe of
    Can.TLambda arg result ->
      addFreeVars (addFreeVars freeVars result) arg
    Can.TVar var ->
      Map.insert var [] freeVars
    Can.TType _ _ args ->
      List.foldl' addFreeVars freeVars args
    Can.TRecord fields Nothing ->
      Map.foldl addFieldFreeVars freeVars fields
    Can.TRecord fields (Just ext) ->
      Map.foldl addFieldFreeVars (Map.insert ext [] freeVars) fields
    Can.TAlias _ _ args _ ->
      List.foldl' (\fvs (_, arg) -> addFreeVars fvs arg) freeVars args

addFieldFreeVars :: Map.Map Name.Name [Can.Class] -> Can.FieldType -> Map.Map Name.Name [Can.Class]
addFieldFreeVars freeVars (Can.FieldType _ tipe) =
  addFreeVars freeVars tipe
