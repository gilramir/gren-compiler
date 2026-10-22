module Canonicalize.Type
  ( toAnnotation,
    toSignature,
    Signature (..),
    checkBody,
    canonicalize,
    addFreeVars,
  )
where

import AST.Canonical qualified as Can
import AST.Source qualified as Src
import AST.Utils.Type qualified as Type
import Canonicalize.Binops qualified as Binops
import Canonicalize.Environment qualified as Env
import Canonicalize.Environment.Dups qualified as Dups
import Canonicalize.NodeId qualified as NodeId
import Control.Monad (foldM)
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
      canonicalizeType env typeRegion name (fmap snd args)
        =<< Env.findType region env name
    Src.TTypeQual region home name args ->
      canonicalizeType env typeRegion name (fmap snd args)
        =<< Env.findTypeQual region env home name
    Src.TLambda a b _ ->
      Can.TLambda
        <$> canonicalize place env a
        <*> canonicalize place env b
    Src.TRecord fields ext ->
      do
        cfields <- sequenceA =<< Dups.checkFields (canonicalizeFields env fields)
        return $ Can.TRecord cfields (fmap (A.toValue . fst) ext)
    Src.TParens inner _ ->
      canonicalize place env inner
    Src.TNamed _ _ maybePredicate ->
      Result.throw (Error.RefinementMisplaced typeRegion (Maybe.isJust maybePredicate) place)

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
    _source :: String
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
    Src.TNamed name inner maybePredicate ->
      do
        (innerType, innerNamed) <- positionType env path inner
        Result.ok (innerType, Named region path name innerType (fst <$> maybePredicate) (maybe "" snd maybePredicate) : innerNamed)
    Src.TParens inner _
      | isNamed inner ->
          position env path inner
    _ ->
      positionType env path srcType

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
refine env named =
  do
    checkDuplicates named
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

-- | A name that nothing reads and that is not refined is refused, as D819
-- refused it: it would look as if it meant something (D821). One a @let@
-- could still read is handed back.
checkRead :: [Name.Name] -> Named -> Result i w [A.Located Name.Name]
checkRead readNames n =
  case _predicate n of
    Just _ -> Result.ok []
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
    predicate <- traverse (canonicalizePredicate env (Scope n named enclosing)) (_predicate n)
    let readNames = maybe [] predicateLocals predicate
    Result.ok $
      Can.Refinement
        { Can._ref_region = _region n,
          Can._ref_path = _path n,
          Can._ref_name = _name n,
          Can._ref_type = _type n,
          Can._ref_predicate = predicate,
          Can._ref_source = _source n,
          Can._ref_enclosing = filter ((`elem` readNames) . A.toValue . Can._enc_name) enclosing
        }

predicateLocals :: Can.Expr -> [Name.Name]
predicateLocals (Can.Expr _ _ expr) =
  case expr of
    Can.VarLocal name -> [name]
    Can.Negate inner -> predicateLocals inner
    Can.Binop _ _ _ left right -> predicateLocals left ++ predicateLocals right
    Can.Call func args -> concatMap predicateLocals (func : args)
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
-- only number (D799); any other is read only through a measure. The type
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
    Src.Var Src.LowVar name ->
      do
        tipe <- findName region scope name
        if isInt tipe
          then Result.ok (Can.at region (Can.VarLocal name))
          else Result.throw (Error.RefinementNameNotInt region name)
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
    Src.Call (A.At funcRegion (Src.VarQual Src.LowVar prefix name)) [(_, A.At argRegion (Src.Var Src.LowVar argName))]
      | ModuleName.Canonical _ own <- Env._home env,
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
            argType <- findName argRegion scope argName
            case Type.iteratedDealias argType of
              Can.TType typeHome _ typeArgs
                | typeHome == Env._home env ->
                    let vars = Map.fromList [(v, []) | Can.TVar v <- typeArgs]
                        annotation = Can.Forall vars (Can.TLambda argType (Can.TType ModuleName.basics Name.int []))
                     in Result.ok (Can.at region (Can.Call (Can.at funcRegion (Can.VarForeign (Env._home env) name annotation)) [Can.at argRegion (Can.VarLocal argName)]))
              _ ->
                Result.throw (Error.RefinementNotMeasure funcRegion prefix name)
    Src.Call (A.At funcRegion (Src.Var Src.LowVar name)) [(_, arg)] ->
      do
        func <-
          case Map.lookup name (Env._vars env) of
            Just (Env.Foreign home annotation)
              | home == ModuleName.basics ->
                  Result.ok (Can.at funcRegion (Can.VarForeign home name annotation))
            _ ->
              Result.throw (Error.RefinementNotCore funcRegion name)
        carg <- canonicalizePredicate env scope arg
        Result.ok (Can.at region (Can.Call func [carg]))
    Src.Call (A.At funcRegion (Src.VarQual Src.LowVar prefix name)) [(_, A.At argRegion (Src.Var Src.LowVar argName))] ->
      do
        func <-
          case Map.lookup name =<< Map.lookup prefix (Env._q_vars env) of
            Just (Env.Specific home annotation)
              | (home, name) `elem` measures ->
                  Result.ok (Can.at funcRegion (Can.VarForeign home name annotation))
            _ ->
              Result.throw (Error.RefinementNotMeasure funcRegion prefix name)
        _ <- findName argRegion scope argName
        Result.ok (Can.at region (Can.Call func [Can.at argRegion (Can.VarLocal argName)]))
    Src.Binops ops final ->
      do
        tree <-
          Binops.run region
            =<< ( Binops.More
                    <$> traverse (\(expr, A.At opRegion op, _) -> (,) <$> canonicalizePredicate env scope expr <*> predicateOperator env opRegion op) ops
                    <*> canonicalizePredicate env scope final
                )
        checkShape tree
        Result.ok tree
    _ ->
      -- The parser builds nothing else (D815).
      Result.throw (Error.RefinementNotCore region (Name.fromChars "?"))

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

-- | @core@'s measures (D808): the size of each of its collections.
measures :: [(ModuleName.Canonical, Name.Name)]
measures =
  [ (ModuleName.array, Name.fromChars "length"),
    (ModuleName.bytes, Name.fromChars "length"),
    (ModuleName.string, Name.fromChars "count"),
    (ModuleName.dict, Name.fromChars "count"),
    (ModuleName.Canonical Pkg.core (Name.fromChars "Set"), Name.fromChars "count"),
    -- Not exposed by @core@, so only @core@'s primitives name it (D846).
    (ModuleName.Canonical Pkg.core (Name.fromChars "Array.Transient"), Name.fromChars "length")
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

-- | What §RF13.4's layers said that a chain does not: a @*@ has a literal
-- on one side, so that the arithmetic stays linear, and a comparison compares
-- two sums, never two conditions.
checkShape :: Can.Expr -> Result i w ()
checkShape (Can.Expr _ region expr) =
  case expr of
    Can.Binop op _ _ left right ->
      do
        checkShape left
        checkShape right
        if Name.toChars op == "*" && not (isLiteral left || isLiteral right)
          then Result.throw (Error.RefinementNonlinear region)
          else Result.ok ()
        if Name.toChars op `elem` comparisons
          then traverse_ checkSum [left, right]
          else Result.ok ()
    Can.Negate inner -> checkShape inner
    Can.Call _ args -> traverse_ checkShape args
    _ -> Result.ok ()
  where
    checkSum operand =
      if isCondition operand
        then Result.throw (Error.RefinementComparesConditions (Can.exprRegion operand))
        else Result.ok ()

comparisons :: [String]
comparisons =
  ["<", "<=", ">", ">=", "==", "/="]

isCondition :: Can.Expr -> Bool
isCondition (Can.Expr _ _ expr) =
  case expr of
    Can.Binop op _ _ _ _ -> Name.toChars op `elem` ("&&" : "||" : comparisons)
    Can.Call (Can.Expr _ _ (Can.VarForeign home _ _)) _ -> home == ModuleName.basics
    Can.VarCtor {} -> True
    _ -> False

isLiteral :: Can.Expr -> Bool
isLiteral (Can.Expr _ _ expr) =
  case expr of
    Can.Int _ -> True
    Can.Negate inner -> isLiteral inner
    _ -> False

-- CANONICALIZE TYPE

canonicalizeType :: Env.Env -> A.Region -> Name.Name -> [Src.Type] -> Env.Type -> Result i w Can.Type
canonicalizeType env region name args info =
  do
    cargs <- traverse (canonicalize Error.InTypeArgument env) args
    case info of
      Env.Alias arity home argNames aliasedType ->
        checkArity arity region name args $
          Can.TAlias home name (zip argNames cargs) (Can.Holey aliasedType)
      Env.Union arity home ->
        checkArity arity region name args $
          Can.TType home name cargs

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
