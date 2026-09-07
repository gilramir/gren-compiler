{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module Canonicalize.Environment
  ( Env (..),
    Exposed,
    Qualified,
    Info (..),
    mergeInfo,
    Var (..),
    Type (..),
    Ctor (..),
    Method (..),
    addLocals,
    findClass,
    findClassQual,
    findClassDecl,
    findClassDeclQual,
    findType,
    findTypeQual,
    findCtor,
    findCtorQual,
    findBinop,
    Binop (..),
  )
where

import AST.Canonical qualified as Can
import AST.Utils.Binop qualified as Binop
import Data.Index qualified as Index
import Data.Map.Merge.Strict qualified as Map
import Data.Map.Strict qualified as Map
import Data.Name qualified as Name
import Data.OneOrMore qualified as OneOrMore
import Gren.ModuleName qualified as ModuleName
import Reporting.Annotation qualified as A
import Reporting.Error.Canonicalize qualified as Error
import Reporting.Result qualified as Result

-- RESULT

type Result i w a =
  Result.Result i w Error.Error a

-- ENVIRONMENT

data Env = Env
  { _home :: ModuleName.Canonical,
    _vars :: Map.Map Name.Name Var,
    _types :: Exposed Type,
    _ctors :: Exposed Ctor,
    _binops :: Exposed Binop,
    -- | The classes a constraint or an instance head may name.
    _classes :: Exposed Can.ClassDecl,
    -- | The class methods in scope, indexed by the __method's__ name.
    --
    -- The same declarations as '_classes', keyed the other way, because the
    -- two questions are asked from opposite ends: a constraint knows the class
    -- and wants the declaration, and an expression knows the method and wants
    -- the class. One index cannot answer both without a scan, and a scan per
    -- variable lookup is not a thing to build.
    _methods :: Exposed Method,
    _q_vars :: Qualified Can.Annotation,
    _q_types :: Qualified Type,
    _q_ctors :: Qualified Ctor,
    _q_classes :: Qualified Can.ClassDecl,
    _q_methods :: Qualified Method
  }

type Exposed a =
  Map.Map Name.Name (Info a)

type Qualified a =
  Map.Map Name.Name (Map.Map Name.Name (Info a))

-- INFO

data Info a
  = Specific ModuleName.Canonical a
  | Ambiguous ModuleName.Canonical (OneOrMore.OneOrMore ModuleName.Canonical)

mergeInfo :: Info a -> Info a -> Info a
mergeInfo info1 info2 =
  case info1 of
    Specific h1 _ ->
      case info2 of
        Specific h2 _ -> if h1 == h2 then info1 else Ambiguous h1 (OneOrMore.one h2)
        Ambiguous h2 hs2 -> Ambiguous h1 (OneOrMore.more (OneOrMore.one h2) hs2)
    Ambiguous h1 hs1 ->
      case info2 of
        Specific h2 _ -> Ambiguous h1 (OneOrMore.more hs1 (OneOrMore.one h2))
        Ambiguous h2 hs2 -> Ambiguous h1 (OneOrMore.more hs1 (OneOrMore.more (OneOrMore.one h2) hs2))

-- VARIABLES

data Var
  = Local A.Region
  | TopLevel A.Region
  | Foreign ModuleName.Canonical Can.Annotation
  | Foreigns ModuleName.Canonical (OneOrMore.OneOrMore ModuleName.Canonical)

-- TYPES

data Type
  = Alias Int ModuleName.Canonical [Name.Name] Can.Type
  | Union Int ModuleName.Canonical

-- METHODS

-- | A class method: the class that declares it, and the method's published
-- signature. The class's home is the 'Info' this is wrapped in.
data Method = Method
  { _m_class :: Name.Name,
    _m_annotation :: Can.Annotation
  }

-- CTORS

data Ctor = Ctor
  { _c_home :: ModuleName.Canonical,
    _c_type :: Name.Name,
    _c_union :: Can.Union,
    _c_index :: Index.ZeroBased,
    _c_args :: [Can.Type]
  }

-- BINOPS

data Binop = Binop
  { _op :: Name.Name,
    _op_home :: ModuleName.Canonical,
    _op_name :: Name.Name,
    _op_annotation :: Can.Annotation,
    _op_associativity :: Binop.Associativity,
    _op_precedence :: Binop.Precedence
  }

-- VARIABLE -- ADD LOCALS

addLocals :: Map.Map Name.Name A.Region -> Env -> Result i w Env
addLocals names (Env home vars ts cs bs cls ms qvs qts qcs qcls qms) =
  do
    newVars <-
      Map.mergeA
        (Map.mapMissing addLocalLeft)
        (Map.mapMissing (\_ homes -> homes))
        (Map.zipWithAMatched addLocalBoth)
        names
        vars

    Result.ok (Env home newVars ts cs bs cls ms qvs qts qcs qcls qms)

addLocalLeft :: Name.Name -> A.Region -> Var
addLocalLeft _ region =
  Local region

addLocalBoth :: Name.Name -> A.Region -> Var -> Result i w Var
addLocalBoth name region var =
  case var of
    Foreign _ _ ->
      Result.ok (Local region)
    Foreigns _ _ ->
      Result.ok (Local region)
    Local parentRegion ->
      Result.throw (Error.Shadowing name parentRegion region)
    TopLevel parentRegion ->
      Result.throw (Error.Shadowing name parentRegion region)

-- FIND CLASS

-- | The class a constraint or an instance head names.
--
-- What comes back is the __reference__ — 'Can.Class', a name and the module
-- that declares it — rather than the declaration, because that is all a
-- constraint carries (D111). The declaration is in the same table for when
-- instances need it.
--
-- A class and a type share the upper-case namespace (`docs/m1b-classes.md`
-- §G20.2) and are stored apart, so a name that is a type here is a specific
-- mistake rather than a missing name, and is reported as one.
findClass :: A.Region -> Env -> Name.Name -> Result i w Can.Class
findClass region env name =
  fst <$> findClassDecl region env name

-- | The same lookup, keeping the declaration.
--
-- An instance needs it and a constraint does not: an instance is checked
-- against the methods the class publishes, so it is the one caller that has to
-- read what is on the other side of the name.
findClassDecl :: A.Region -> Env -> Name.Name -> Result i w (Can.Class, Can.ClassDecl)
findClassDecl region (Env _ _ ts _ _ cls _ _ _ _ qcls _) name =
  case Map.lookup name cls of
    Just (Specific home decl) ->
      Result.ok (Can.Class home name, decl)
    Just (Ambiguous h hs) ->
      Result.throw (Error.AmbiguousClass region Nothing name h hs)
    Nothing ->
      if Map.member name ts
        then Result.throw (Error.ConstraintNotAClass region name)
        else Result.throw (Error.NotFoundClass region Nothing name (toPossibleNames cls qcls))

findClassQual :: A.Region -> Env -> Name.Name -> Name.Name -> Result i w Can.Class
findClassQual region env prefix name =
  fst <$> findClassDeclQual region env prefix name

findClassDeclQual :: A.Region -> Env -> Name.Name -> Name.Name -> Result i w (Can.Class, Can.ClassDecl)
findClassDeclQual region (Env _ _ _ _ _ cls _ _ _ _ qcls _) prefix name =
  case Map.lookup prefix qcls of
    Just qualified ->
      case Map.lookup name qualified of
        Just (Specific home decl) ->
          Result.ok (Can.Class home name, decl)
        Just (Ambiguous h hs) ->
          Result.throw (Error.AmbiguousClass region (Just prefix) name h hs)
        Nothing ->
          Result.throw (Error.NotFoundClass region (Just prefix) name (toPossibleNames cls qcls))
    Nothing ->
      Result.throw (Error.NotFoundClass region (Just prefix) name (toPossibleNames cls qcls))

-- FIND TYPE

findType :: A.Region -> Env -> Name.Name -> Result i w Type
findType region (Env _ _ ts _ _ _ _ _ qts _ _ _) name =
  case Map.lookup name ts of
    Just (Specific _ tipe) ->
      Result.ok tipe
    Just (Ambiguous h hs) ->
      Result.throw (Error.AmbiguousType region Nothing name h hs)
    Nothing ->
      Result.throw (Error.NotFoundType region Nothing name (toPossibleNames ts qts))

findTypeQual :: A.Region -> Env -> Name.Name -> Name.Name -> Result i w Type
findTypeQual region (Env _ _ ts _ _ _ _ _ qts _ _ _) prefix name =
  case Map.lookup prefix qts of
    Just qualified ->
      case Map.lookup name qualified of
        Just (Specific _ tipe) ->
          Result.ok tipe
        Just (Ambiguous h hs) ->
          Result.throw (Error.AmbiguousType region (Just prefix) name h hs)
        Nothing ->
          Result.throw (Error.NotFoundType region (Just prefix) name (toPossibleNames ts qts))
    Nothing ->
      Result.throw (Error.NotFoundType region (Just prefix) name (toPossibleNames ts qts))

-- FIND CTOR

findCtor :: A.Region -> Env -> Name.Name -> Result i w Ctor
findCtor region (Env _ _ _ cs _ _ _ _ _ qcs _ _) name =
  case Map.lookup name cs of
    Just (Specific _ ctor) ->
      Result.ok ctor
    Just (Ambiguous h hs) ->
      Result.throw (Error.AmbiguousVariant region Nothing name h hs)
    Nothing ->
      Result.throw (Error.NotFoundVariant region Nothing name (toPossibleNames cs qcs))

findCtorQual :: A.Region -> Env -> Name.Name -> Name.Name -> Result i w Ctor
findCtorQual region (Env _ _ _ cs _ _ _ _ _ qcs _ _) prefix name =
  case Map.lookup prefix qcs of
    Just qualified ->
      case Map.lookup name qualified of
        Just (Specific _ pattern) ->
          Result.ok pattern
        Just (Ambiguous h hs) ->
          Result.throw (Error.AmbiguousVariant region (Just prefix) name h hs)
        Nothing ->
          Result.throw (Error.NotFoundVariant region (Just prefix) name (toPossibleNames cs qcs))
    Nothing ->
      Result.throw (Error.NotFoundVariant region (Just prefix) name (toPossibleNames cs qcs))

-- FIND BINOP

findBinop :: A.Region -> Env -> Name.Name -> Result i w Binop
findBinop region (Env _ _ _ _ binops _ _ _ _ _ _ _) name =
  case Map.lookup name binops of
    Just (Specific _ binop) ->
      Result.ok binop
    Just (Ambiguous h hs) ->
      Result.throw (Error.AmbiguousBinop region name h hs)
    Nothing ->
      Result.throw (Error.NotFoundBinop region name (Map.keysSet binops))

-- TO POSSIBLE NAMES

toPossibleNames :: Exposed a -> Qualified a -> Error.PossibleNames
toPossibleNames exposed qualified =
  Error.PossibleNames (Map.keysSet exposed) (Map.map Map.keysSet qualified)
