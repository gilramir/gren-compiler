{-# LANGUAGE Rank2Types #-}

module Gren.Compiler.Type.Extract
  ( fromAnnotation,
    fromType,
    Types (..),
    mergeMany,
    merge,
    fromInterface,
    fromDependencyInterface,
    fromMsg,
  )
where

import AST.Canonical qualified as Can
import AST.Utils.Type qualified as Type
import Core.AST qualified as Core
import Data.Map ((!))
import Data.Map qualified as Map
import Data.Name qualified as Name
import Data.Set qualified as Set
import Gren.Compiler.Type qualified as T
import Gren.Interface qualified as I
import Gren.ModuleName qualified as ModuleName

-- EXTRACTION

fromAnnotation :: Can.Annotation -> T.Type
fromAnnotation (Can.Forall _ astType) =
  fromType astType

fromType :: Can.Type -> T.Type
fromType astType =
  snd (run (extract astType))

extract :: Can.Type -> Extractor T.Type
extract astType =
  case astType of
    Can.TLambda arg result ->
      T.Lambda
        <$> extract arg
        <*> extract result
    Can.TVar x ->
      pure (T.Var x)
    Can.TType home name args ->
      addUnion (Core.QualName home name) (T.Type (toPublicName home name))
        <*> traverse extract args
    Can.TRecord fields ext ->
      do
        efields <- traverse (traverse extract) (Can.fieldsToList fields)
        pure (T.Record efields ext)
    Can.TAlias home name args aliasType ->
      do
        addAlias (Core.QualName home name) ()
        _ <- extract (Type.dealias args aliasType)
        T.Type (toPublicName home name)
          <$> traverse (extract . snd) args

toPublicName :: ModuleName.Canonical -> Name.Name -> Name.Name
toPublicName (ModuleName.Canonical _ home) name =
  Name.sepBy 0x2E {- . -} home name

-- TRANSITIVELY AVAILABLE TYPES

newtype Types
  = Types (Map.Map ModuleName.Canonical Types_)

-- PERF profile Core.QualName representation
-- current representation needs less allocation
-- but maybe the lookup is much worse

data Types_ = Types_
  { _union_info :: Map.Map Name.Name Can.Union,
    _alias_info :: Map.Map Name.Name Can.Alias
  }

mergeMany :: [Types] -> Types
mergeMany listOfTypes =
  case listOfTypes of
    [] -> Types Map.empty
    t : ts -> foldr merge t ts

merge :: Types -> Types -> Types
merge (Types types1) (Types types2) =
  Types (Map.union types1 types2)

fromInterface :: ModuleName.Raw -> I.Interface -> Types
fromInterface name (I.Interface pkg _ unions aliases _ _ _) =
  Types $
    Map.singleton (ModuleName.Canonical pkg name) $
      Types_ (Map.map I.extractUnion unions) (Map.map I.extractAlias aliases)

fromDependencyInterface :: ModuleName.Canonical -> I.DependencyInterface -> Types
fromDependencyInterface home di =
  Types $
    Map.singleton home $
      case di of
        I.Public (I.Interface _ _ unions aliases _ _ _) ->
          Types_ (Map.map I.extractUnion unions) (Map.map I.extractAlias aliases)
        I.Private _ unions aliases ->
          Types_ unions aliases

-- EXTRACT MODEL, MSG, AND ANY TRANSITIVE DEPENDENCIES

fromMsg :: Types -> Can.Type -> T.DebugMetadata
fromMsg types message =
  let (msgDeps, msgType) =
        run (extract message)

      (aliases, unions) =
        extractTransitive types noDeps msgDeps
   in T.DebugMetadata msgType aliases unions

extractTransitive :: Types -> Deps -> Deps -> ([T.Alias], [T.Union])
extractTransitive types (Deps seenAliases seenUnions) (Deps nextAliases nextUnions) =
  let aliases = Set.difference nextAliases seenAliases
      unions = Set.difference nextUnions seenUnions
   in if Set.null aliases && Set.null unions
        then ([], [])
        else
          let (newDeps, result) =
                run $
                  (,)
                    <$> traverse (extractAlias types) (Set.toList aliases)
                    <*> traverse (extractUnion types) (Set.toList unions)

              oldDeps =
                Deps (Set.union seenAliases nextAliases) (Set.union seenUnions nextUnions)

              remainingResult =
                extractTransitive types oldDeps newDeps
           in mappend result remainingResult

extractAlias :: Types -> Core.QualName -> Extractor T.Alias
extractAlias (Types dict) (Core.QualName home name) =
  let (Can.Alias args aliasType) = _alias_info (dict ! home) ! name
   in T.Alias (toPublicName home name) args <$> extract aliasType

extractUnion :: Types -> Core.QualName -> Extractor T.Union
extractUnion (Types dict) (Core.QualName home name) =
  let pname = toPublicName home name
      (Can.Union vars ctors _ _) = _union_info (dict ! home) ! name
   in T.Union pname vars <$> traverse extractCtor ctors

extractCtor :: Can.Ctor -> Extractor (Name.Name, [T.Type])
extractCtor (Can.Ctor ctor _ _ args) =
  (,) ctor <$> traverse extract args

-- DEPS

data Deps = Deps
  { _aliases :: Set.Set Core.QualName,
    _unions :: Set.Set Core.QualName
  }

noDeps :: Deps
noDeps =
  Deps Set.empty Set.empty

-- EXTRACTOR

newtype Extractor a
  = Extractor
      ( forall result.
        Set.Set Core.QualName ->
        Set.Set Core.QualName ->
        (Set.Set Core.QualName -> Set.Set Core.QualName -> a -> result) ->
        result
      )

run :: Extractor a -> (Deps, a)
run (Extractor k) =
  k Set.empty Set.empty $ \aliases unions value ->
    (Deps aliases unions, value)

addAlias :: Core.QualName -> a -> Extractor a
addAlias alias value =
  Extractor $ \aliases unions ok ->
    ok (Set.insert alias aliases) unions value

addUnion :: Core.QualName -> a -> Extractor a
addUnion union value =
  Extractor $ \aliases unions ok ->
    ok aliases (Set.insert union unions) value

instance Functor Extractor where
  fmap func (Extractor k) =
    Extractor $ \aliases unions ok ->
      let ok1 a1 u1 value =
            ok a1 u1 (func value)
       in k aliases unions ok1

instance Applicative Extractor where
  pure value =
    Extractor $ \aliases unions ok ->
      ok aliases unions value

  (<*>) (Extractor kf) (Extractor kv) =
    Extractor $ \aliases unions ok ->
      let ok1 a1 u1 func =
            let ok2 a2 u2 value =
                  ok a2 u2 (func value)
             in kv a1 u1 ok2
       in kf aliases unions ok1

instance Monad Extractor where
  return = pure

  (>>=) (Extractor ka) callback =
    Extractor $ \aliases unions ok ->
      let ok1 a1 u1 value =
            case callback value of
              Extractor kb -> kb a1 u1 ok
       in ka aliases unions ok1
