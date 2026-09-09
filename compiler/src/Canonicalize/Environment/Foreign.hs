{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module Canonicalize.Environment.Foreign
  ( createInitialEnv,
  )
where

import AST.Canonical qualified as Can
import AST.Source qualified as Src
import Canonicalize.Environment qualified as Env
import Control.Monad (foldM)
import Data.List qualified as List
import Data.Map.Strict ((!))
import Data.Map.Strict qualified as Map
import Data.Name qualified as Name
import Gren.Interface qualified as I
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Reporting.Annotation qualified as A
import Reporting.Error.Canonicalize qualified as Error
import Reporting.Result qualified as Result

-- RESULT

type Result i w a =
  Result.Result i w Error.Error a

createInitialEnv :: ModuleName.Canonical -> Map.Map ModuleName.Raw I.Interface -> [Src.Import] -> Result i w Env.Env
createInitialEnv home ifaces imports =
  do
    (State vs ts cs bs cls ms qvs qts qcs qcls qms) <- foldM (addImport ifaces) emptyState (toSafeImports home imports)
    Result.ok (Env.Env home (Map.map infoToVar vs) ts cs bs cls ms qvs qts qcs qcls qms)

infoToVar :: Env.Info Can.Annotation -> Env.Var
infoToVar info =
  case info of
    Env.Specific home tipe -> Env.Foreign home tipe
    Env.Ambiguous h hs -> Env.Foreigns h hs

-- STATE

data State = State
  { _vars :: Env.Exposed Can.Annotation,
    _types :: Env.Exposed Env.Type,
    _ctors :: Env.Exposed Env.Ctor,
    _binops :: Env.Exposed Env.Binop,
    _classes :: Env.Exposed Can.ClassDecl,
    _methods :: Env.Exposed Env.Method,
    _q_vars :: Env.Qualified Can.Annotation,
    _q_types :: Env.Qualified Env.Type,
    _q_ctors :: Env.Qualified Env.Ctor,
    _q_classes :: Env.Qualified Can.ClassDecl,
    _q_methods :: Env.Qualified Env.Method
  }

emptyState :: State
emptyState =
  State Map.empty emptyTypes Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty

emptyTypes :: Env.Exposed Env.Type
emptyTypes =
  Map.empty

-- TO SAFE IMPORTS

toSafeImports :: ModuleName.Canonical -> [Src.Import] -> [Src.Import]
toSafeImports (ModuleName.Canonical pkg _) imports =
  if Pkg.isKernel pkg
    then filter isNormal imports
    else imports

isNormal :: Src.Import -> Bool
isNormal (Src.Import (A.At _ name) maybeAlias _ _ _) =
  if Name.isKernel name
    then case maybeAlias of
      Nothing -> False
      Just _ -> error "kernel imports cannot use `as`"
    else True

-- ADD IMPORTS

addImport :: Map.Map ModuleName.Raw I.Interface -> State -> Src.Import -> Result i w State
addImport ifaces (State vs ts cs bs cls ms qvs qts qcs qcls qms) (Src.Import (A.At _ name) maybeAlias exposing _ _) =
  let (I.Interface pkg defs unions aliases binops iClasses _) = ifaces ! name
      !prefix = maybe name id (fmap fst maybeAlias)
      !home = ModuleName.Canonical pkg name

      !rawTypeInfo =
        Map.union
          (Map.mapMaybeWithKey (unionToType home) unions)
          (Map.mapMaybeWithKey (aliasToType home) aliases)

      !rawClasses = Map.mapMaybe I.toPublicClass iClasses

      !vars = Map.map (Env.Specific home) defs
      !types = Map.map (Env.Specific home . fst) rawTypeInfo
      !ctors = Map.foldr (addExposed . snd) Map.empty rawTypeInfo
      !classes = Map.map (Env.Specific home) rawClasses
      !methods = methodsOf home rawClasses

      !qvs2 = addQualified prefix vars qvs
      !qts2 = addQualified prefix types qts
      !qcs2 = addQualified prefix ctors qcs
      !qcls2 = addQualified prefix classes qcls
      !qms2 = addQualified prefix methods qms
   in case exposing of
        Src.Open ->
          let !vs2 = addExposed vs vars
              !ts2 = addExposed ts types
              !cs2 = addExposed cs ctors
              !bs2 = addExposed bs (Map.mapWithKey (binopToBinop home) binops)
              !cls2 = addExposed cls classes
              !ms2 = addExposed ms methods
           in Result.ok (State vs2 ts2 cs2 bs2 cls2 ms2 qvs2 qts2 qcs2 qcls2 qms2)
        Src.Explicit exposedList ->
          foldM
            (addExposedValue home vars rawTypeInfo binops rawClasses)
            (State vs ts cs bs cls ms qvs2 qts2 qcs2 qcls2 qms2)
            exposedList

-- CLASS

-- | A module's public classes, indexed by method name rather than class name.
--
-- Both indexes are built here because both are asked for: `Canonicalize.Type`
-- resolves a constraint by class name and `Canonicalize.Expression` resolves a
-- variable by method name, and neither can afford the other's scan. A class
-- that is not public contributes neither, which is what makes a private class
-- private: `I.toPublicClass` is the only door.
methodsOf :: ModuleName.Canonical -> Map.Map Name.Name Can.ClassDecl -> Env.Exposed Env.Method
methodsOf home classes =
  Map.fromList
    [ (methodName, Env.Specific home (Env.Method className param annotation))
    | (className, Can.ClassDecl param methods) <- Map.toList classes,
      (methodName, annotation) <- Map.toList methods
    ]

addExposed :: Env.Exposed a -> Env.Exposed a -> Env.Exposed a
addExposed =
  Map.unionWith Env.mergeInfo

addQualified :: Name.Name -> Env.Exposed a -> Env.Qualified a -> Env.Qualified a
addQualified prefix exposed qualified =
  Map.insertWith addExposed prefix exposed qualified

-- UNION

unionToType :: ModuleName.Canonical -> Name.Name -> I.Union -> Maybe (Env.Type, Env.Exposed Env.Ctor)
unionToType home name union =
  unionToTypeHelp home name <$> I.toPublicUnion union

unionToTypeHelp :: ModuleName.Canonical -> Name.Name -> Can.Union -> (Env.Type, Env.Exposed Env.Ctor)
unionToTypeHelp home name union@(Can.Union vars ctors _ _) =
  let addCtor dict (Can.Ctor ctor index _ args) =
        Map.insert ctor (Env.Specific home (Env.Ctor home name union index args)) dict
   in ( Env.Union (length vars) home,
        List.foldl' addCtor Map.empty ctors
      )

-- ALIAS

aliasToType :: ModuleName.Canonical -> Name.Name -> I.Alias -> Maybe (Env.Type, Env.Exposed Env.Ctor)
aliasToType home name alias =
  aliasToTypeHelp home name <$> I.toPublicAlias alias

aliasToTypeHelp :: ModuleName.Canonical -> Name.Name -> Can.Alias -> (Env.Type, Env.Exposed Env.Ctor)
aliasToTypeHelp home _ (Can.Alias vars tipe) =
  (Env.Alias (length vars) home vars tipe, Map.empty)

-- BINOP

binopToBinop :: ModuleName.Canonical -> Name.Name -> I.Binop -> Env.Info Env.Binop
binopToBinop home op (I.Binop name method annotation associativity precedence) =
  let target =
        case method of
          Nothing -> Can.OpValue home name
          Just (className, param) -> Can.OpMethod (Can.Class home className) param name
   in Env.Specific home (Env.Binop op target annotation associativity precedence)

-- ADD EXPOSED VALUE

addExposedValue ::
  ModuleName.Canonical ->
  Env.Exposed Can.Annotation ->
  Map.Map Name.Name (Env.Type, Env.Exposed Env.Ctor) ->
  Map.Map Name.Name I.Binop ->
  Map.Map Name.Name Can.ClassDecl ->
  State ->
  Src.Exposed ->
  Result i w State
addExposedValue home vars types binops classes (State vs ts cs bs cls ms qvs qts qcs qcls qms) exposed =
  case exposed of
    Src.Lower (A.At region name) ->
      case Map.lookup name vars of
        Just info ->
          Result.ok (State (Map.insertWith Env.mergeInfo name info vs) ts cs bs cls ms qvs qts qcs qcls qms)
        Nothing ->
          case classOf name classes of
            Just className ->
              Result.throw (Error.ImportMethodByName region name className)
            Nothing ->
              Result.throw (Error.ImportExposingNotFound region home name (Map.keys vars))
    Src.Upper (A.At region name) privacy ->
      case privacy of
        Src.Private ->
          case Map.lookup name types of
            Just (tipe, ctors) ->
              case tipe of
                Env.Union _ _ ->
                  let !ts2 = Map.insert name (Env.Specific home tipe) ts
                   in Result.ok (State vs ts2 cs bs cls ms qvs qts qcs qcls qms)
                Env.Alias _ _ _ _ ->
                  let !ts2 = Map.insert name (Env.Specific home tipe) ts
                      !cs2 = addExposed cs ctors
                   in Result.ok (State vs ts2 cs2 bs cls ms qvs qts qcs qcls qms)
            Nothing ->
              case Map.lookup name classes of
                Just decl ->
                  let !cls2 = Map.insert name (Env.Specific home decl) cls
                      !ms2 = addExposed ms (methodsOf home (Map.singleton name decl))
                   in Result.ok (State vs ts cs bs cls2 ms2 qvs qts qcs qcls qms)
                Nothing ->
                  case checkForCtorMistake name types of
                    tipe : _ ->
                      Result.throw $ Error.ImportCtorByName region name tipe
                    [] ->
                      Result.throw $ Error.ImportExposingNotFound region home name (Map.keys types ++ Map.keys classes)
        Src.Public dotDotRegion ->
          case Map.lookup name types of
            Just (tipe, ctors) ->
              case tipe of
                Env.Union _ _ ->
                  let !ts2 = Map.insert name (Env.Specific home tipe) ts
                      !cs2 = addExposed cs ctors
                   in Result.ok (State vs ts2 cs2 bs cls ms qvs qts qcs qcls qms)
                Env.Alias _ _ _ _ ->
                  Result.throw (Error.ImportOpenAlias dotDotRegion name)
            Nothing ->
              if Map.member name classes
                then Result.throw (Error.ImportOpenClass dotDotRegion name)
                else Result.throw (Error.ImportExposingNotFound region home name (Map.keys types ++ Map.keys classes))
    Src.Operator region op ->
      case Map.lookup op binops of
        Just binop ->
          let !bs2 = Map.insert op (binopToBinop home op binop) bs
           in Result.ok (State vs ts cs bs2 cls ms qvs qts qcs qcls qms)
        Nothing ->
          Result.throw (Error.ImportExposingNotFound region home op (Map.keys binops))

-- | The class a method name belongs to, if it is a method at all.
--
-- @import Basics exposing (eq)@ is the mistake this exists for: a method is
-- exposed by its class rather than on its own (D121), and the fix is to name
-- the class. `checkForCtorMistake` is the same shape for the same reason.
classOf :: Name.Name -> Map.Map Name.Name Can.ClassDecl -> Maybe Name.Name
classOf name classes =
  case [className | (className, Can.ClassDecl _ methods) <- Map.toList classes, Map.member name methods] of
    className : _ -> Just className
    [] -> Nothing

checkForCtorMistake :: Name.Name -> Map.Map Name.Name (Env.Type, Env.Exposed Env.Ctor) -> [Name.Name]
checkForCtorMistake givenName types =
  Map.foldr addMatches [] types
  where
    addMatches (_, exposedCtors) matches =
      Map.foldrWithKey addMatch matches exposedCtors

    addMatch ctorName info matches =
      if ctorName /= givenName
        then matches
        else case info of
          Env.Specific _ (Env.Ctor _ tipeName _ _ _) ->
            tipeName : matches
          Env.Ambiguous _ _ ->
            matches
