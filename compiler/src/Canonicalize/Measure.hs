-- | The rules a @\@measure@ is held to (geng-lang @m4-refine-t1.md@ TO14,
-- Dnene17): a function a refinement's predicate may call, which the
-- refinement checker unfolds where it is called. Each rule broken is refused
-- with the rule, never silently left not a measure.
module Canonicalize.Measure
  ( check,
  )
where

import AST.Canonical qualified as Can
import Data.Name qualified as Name
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName
import Reporting.Annotation qualified as A
import Reporting.Error.Canonicalize qualified as Error
import Reporting.Result qualified as Result

type Result i w a =
  Result.Result i w Error.Error a

-- | Every measure the module declares, against its definition. @known@ is
-- every measure a body may call: @core@'s, the imported modules' and this
-- module's own.
check :: ModuleName.Canonical -> (ModuleName.Canonical -> Name.Name -> Bool) -> [String] -> Set.Set Name.Name -> Can.Decls -> Result i w ()
check home known operators measures decls =
  mapM_ (checkDef home known operators) [def | def <- defs decls, Set.member (defName def) measures]

defs :: Can.Decls -> [Can.Def]
defs decls =
  case decls of
    Can.Declare def rest -> def : defs rest
    Can.DeclareRec def more rest -> def : more ++ defs rest
    Can.SaveTheEnvironment -> []

defName :: Can.Def -> Name.Name
defName def =
  case def of
    Can.Def _ (A.At _ name) _ _ -> name
    Can.TypedDef (A.At _ name) _ _ _ _ _ -> name

checkDef :: ModuleName.Canonical -> (ModuleName.Canonical -> Name.Name -> Bool) -> [String] -> Can.Def -> Result i w ()
checkDef home known operators def =
  case def of
    Can.Def _ (A.At region name) _ _ ->
      Result.throw (Error.MeasureBroken region name Error.MeasureArgument)
    Can.TypedDef (A.At region name) _ args body result _ ->
      case args of
        [(A.At _ (Can.PVar param), argType)] ->
          do
            if measuresOwn home argType
              then Result.ok ()
              else Result.throw (Error.MeasureBroken region name Error.MeasureNotOwnType)
            if isBasics Name.int result || isBasics Name.bool result
              then Result.ok ()
              else Result.throw (Error.MeasureBroken region name Error.MeasureAnswer)
            checkBody home known operators name param body
        _ ->
          Result.throw (Error.MeasureBroken region name Error.MeasureArgument)

-- | The body: one @when@ over the argument, each arm a term over what its
-- pattern binds, or a term over the argument itself.
checkBody :: ModuleName.Canonical -> (ModuleName.Canonical -> Name.Name -> Bool) -> [String] -> Name.Name -> Name.Name -> Can.Expr -> Result i w ()
checkBody home known operators self param body =
  case body of
    Can.Expr _ _ (Can.Case (Can.Expr _ _ (Can.VarLocal subject)) branches)
      | subject == param ->
          mapM_ (\(Can.CaseBranch pattern arm) -> term home known operators self (Set.fromList (bound pattern)) arm) branches
    _ ->
      term home known operators self (Set.singleton param) body

-- | A term of D808's predicate grammar: an `Int`, `True` or `False`, a bound
-- name or its field, a measure applied to one, `not`, and the predicate
-- operators between terms.
term :: ModuleName.Canonical -> (ModuleName.Canonical -> Name.Name -> Bool) -> [String] -> Name.Name -> Set.Set Name.Name -> Can.Expr -> Result i w ()
term home known operators self locals expr@(Can.Expr _ region expression) =
  case expression of
    Can.Int _ -> Result.ok ()
    Can.Negate inner -> term home known operators self locals inner
    Can.VarCtor _ ctorHome ctorName _ _
      | ctorHome == ModuleName.basics && (ctorName == Name.true || ctorName == Name.false) -> Result.ok ()
    Can.Binop op _ _ left right
      | Name.toChars op `elem` operators ->
          term home known operators self locals left >> term home known operators self locals right
    Can.Call (Can.Expr _ _ func) [arg]
      | Just (fnHome, fnName) <- measureName func ->
          if fnHome == home && fnName == self
            then Result.throw (Error.MeasureBroken region self Error.MeasureRecursion)
            else
              if known fnHome fnName && isPath locals arg
                then Result.ok ()
                else broken
      | Can.VarForeign fnHome fnName _ <- func,
        fnHome == ModuleName.basics && fnName == Name.fromChars "not" ->
          term home known operators self locals arg
    _
      | isPath locals expr -> Result.ok ()
      | otherwise -> broken
  where
    broken = Result.throw (Error.MeasureBroken region self Error.MeasureTerm)

measureName :: Can.Expr_ -> Maybe (ModuleName.Canonical, Name.Name)
measureName func =
  case func of
    Can.VarForeign h n _ -> Just (h, n)
    Can.VarTopLevel h n -> Just (h, n)
    _ -> Nothing

isPath :: Set.Set Name.Name -> Can.Expr -> Bool
isPath locals (Can.Expr _ _ expression) =
  case expression of
    Can.VarLocal name -> Set.member name locals
    Can.Access record _ -> isPath locals record
    _ -> False

-- | The names a pattern binds.
bound :: Can.Pattern -> [Name.Name]
bound (A.At _ pattern) =
  case pattern of
    Can.PVar name -> [name]
    Can.PAlias inner name -> name : bound inner
    Can.PRecord fields -> concatMap (\(A.At _ (Can.PRFieldPattern _ p)) -> bound p) fields
    Can.PArray items -> concatMap bound items
    Can.PCtor {Can._p_args = args} -> concatMap (bound . Can._arg) args
    _ -> []

measuresOwn :: ModuleName.Canonical -> Can.Type -> Bool
measuresOwn home tipe =
  case tipe of
    Can.TType typeHome _ _ -> typeHome == home
    Can.TAlias typeHome _ _ _ -> typeHome == home
    _ -> False

isBasics :: Name.Name -> Can.Type -> Bool
isBasics name tipe =
  case tipe of
    Can.TType home n [] -> home == ModuleName.basics && n == name
    Can.TAlias _ _ _ (Can.Filled inner) -> isBasics name inner
    Can.TAlias _ _ _ (Can.Holey inner) -> isBasics name inner
    _ -> False
