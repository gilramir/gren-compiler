{-# OPTIONS_GHC -Wall #-}

-- | Lower canonical types and datatype declarations to Core.
--
-- The type half of the lowering, separated from the expression half because it
-- is where three of C2's decisions actually bite, and because it is testable on
-- its own — which the expression half is not until a whole module can be built.
--
-- The three:
--
--   * __Functions are n-ary__ (C3). @a -> b -> c@ becomes @TFun [a, b] c@,
--     collapsed maximally. Nothing is lost: Gren's arrow is right-associative
--     with no way to write a distinction between @a -> (b -> c)@ and
--     @a -> b -> c@, so the collapsed form is canonical and two types that are
--     equal are equal on the nose.
--   * __Aliases do not survive__. C2's `Type` has no alias node, so every
--     alias is expanded here. A backend never has to chase one, and structural
--     record types compare without first deciding how deeply to dealias.
--   * __Record fields are alphabetical__ (C2), which is what makes those
--     comparisons canonical and what @classes.md@ §2.2's derived `Ord` agrees
--     with. Canonical stores a source-order index alongside each field; it is
--     dropped, because two modules that write the same record type in a
--     different field order have the same type and must lower to the same Core.
module Core.Lower.Type
  ( lowerType,
    sharedLowering,
    lowerAnnotation,
    lowerUnion,
    lowerAlias,
    lowerClass,
  )
where

import AST.Canonical qualified as Can
import AST.Utils.Type qualified as Type
import Control.Exception (evaluate)
import Core.AST qualified as Core
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.Index qualified as Index
import Data.IntMap.Strict qualified as IntMap
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Name (Name)
import Gren.ModuleName qualified as ModuleName
import System.IO.Unsafe (unsafePerformIO)
import System.Mem.StableName (hashStableName, makeStableName)
import Type.Class qualified as Class

lowerType :: Can.Type -> Core.Type
lowerType = lowerTypeWith lowerType

-- | 'lowerType' one level, with the given function for what is inside.
lowerTypeWith :: (Can.Type -> Core.Type) -> Can.Type -> Core.Type
lowerTypeWith lower tipe =
  case tipe of
    Can.TVar name ->
      Core.TVar name
    Can.TType home name args ->
      Core.TCon (Core.QualName home name) (map lower args)
    Can.TLambda arg result ->
      -- Maximal collapse: a function whose result is itself a function has
      -- one argument list, not two. See C3. The chain is gathered first and
      -- built once: built from its result outwards, each of an n-argument
      -- function's n suffixes would be a type of its own, and since types
      -- are interned (geng-lang @m3-sweep.md@ §SW44, D743) each costs its
      -- arity.
      let (args, final) = arrows result
       in Core.TFun (lower arg : args) final
    Can.TRecord fields ext ->
      -- `Map.toAscList` is the alphabetical order C2 asks for, and the
      -- `Word16` source-order index Canonical carries is deliberately dropped.
      Core.TRecord
        [(name, lower fieldType) | (name, Can.FieldType _ fieldType) <- Map.toAscList fields]
        ext
    Can.TAlias _ _ args aliasType ->
      lower (Type.dealias args aliasType)
  where
    -- The arguments and result of a function's result, collapsed: what
    -- lowering the result would have taken apart, an alias for a function
    -- included.
    arrows t =
      case t of
        Can.TLambda arg result ->
          let (args, final) = arrows result
           in (lower arg : args, final)
        Can.TAlias _ _ args aliasType ->
          arrows (Type.dealias args aliasType)
        _ ->
          ([], lower t)

-- | A 'lowerType' that lowers a `Can.Type` it has seen before, the same heap
-- value, once (D743). For one tree of witnesses: a witness for @Eq@ at a type
-- n deep holds one at each depth, each with its table's type, and those types
-- share their insides; lowered one by one they were n·s. Its memo lives as
-- long as the function does. The argument only keeps it from being floated
-- out and shared between trees.
sharedLowering :: a -> Can.Type -> Core.Type
sharedLowering seed =
  seed `seq` unsafePerformIO (lower <$> newIORef IntMap.empty)
  where
    lower memo t =
      unsafePerformIO $
        do
          t' <- evaluate t
          name <- makeStableName t'
          known <- readIORef memo
          case lookup name (IntMap.findWithDefault [] (hashStableName name) known) of
            Just lowered -> return lowered
            Nothing ->
              do
                let !lowered = lowerTypeWith (lower memo) t'
                modifyIORef' memo (IntMap.insertWith (++) (hashStableName name) [(name, lowered)])
                return lowered
{-# NOINLINE sharedLowering #-}

-- | A top-level definition's generalized type.
--
-- The constraint list is `Can.FreeVars`' payload, carried straight through:
-- D111 makes a constraint qualify the annotation rather than sit inside the
-- type, which is the shape `Core.TForall` already had.
--
-- It is empty on every annotation today, and that is a fact about the front
-- end rather than about this function. Gren's @number@, @comparable@ and
-- @appendable@ still arrive as ordinary type variables whose names happen to
-- be special, and `Type.Class.fromName` reads them; a constraint an author
-- writes is still rejected in `Canonicalize.Type` for want of a class to
-- resolve to. Both go together when `core` declares its classes, and this
-- function does not change again when they do.
--
-- Ordered by variable and then by class, both ascending, which is C2's
-- canonical order rather than the author's. `Can` keeps the order the context
-- was written in, because an error message may want to echo it; Core sorts,
-- because Core is where two types are compared and `(Eq a, Ord a) =>` and
-- `(Ord a, Eq a) =>` are the same type. It is the same split `TRecord` makes,
-- where `Can` carries a source-order index and this module drops it.
lowerAnnotation :: Can.Annotation -> Core.Type
lowerAnnotation (Can.Forall freeVars tipe) =
  case Map.toAscList freeVars of
    [] -> lowerType tipe
    vars ->
      Core.TForall
        (map fst vars)
        [ Core.CClass (Core.QualName home name) (Core.TVar var)
        | (var, classes) <- vars,
          Can.Class home name <- List.sort classes
        ]
        (lowerType tipe)

-- | A class declaration (@docs/m1b-classes.md@ §G20).
--
-- The methods come out alphabetically because `Can.ClassDecl` keeps them in a
-- 'Map.Map', which is C2's requirement met the same way record fields meet it:
-- an order two frontends agree on without having to agree on a traversal.
--
-- __What marks a class 'Core.Closed' is the compiler-known table__, not
-- anything in the source (D135). `classes.md` §1.2 fixes the membership of the
-- numeric classes by construction and there is no syntax that says @closed@, so
-- the declaration `core` writes is an ordinary one and "Type.Class" is what it
-- means. A class a user declares is 'Core.Open' because it is not in that
-- table, which is also the §8.3 gate said in the IR: an instance is the only
-- way into an open class and there is no way at all into a closed one.
lowerClass :: ModuleName.Canonical -> Name -> Can.ClassDecl -> Core.ClassDecl
lowerClass home name (Can.ClassDecl param methods) =
  Core.ClassDecl
    { Core._classNameC = Core.QualName home name,
      Core._classParam = param,
      Core._classOpenness =
        if Class.isClosed home name then Core.Closed else Core.Open,
      Core._classMethods =
        [(methodName, lowerAnnotation annotation) | (methodName, annotation) <- Map.toAscList methods]
    }

-- | A custom type declaration.
--
-- 'Core.Abstract' when its module exposes it without its constructors
-- (@Can.isAbstract@), which a native library's header reads to decide whether
-- a host may look inside one (geng-lang @m3-embed.md@ D631); 'Core.Transparent'
-- otherwise. Every class set is empty: published class sets are @classes.md@
-- §2.5, and recording a guess here would be a fabricated answer. 'Core._dataAffine'
-- is whether the type is declared @\@affine@ (geng-lang @m4-own.md@ D921).
lowerUnion :: Core.Transparency -> Bool -> ModuleName.Canonical -> Name -> Can.Union -> Core.DataDecl
lowerUnion transparency affine home name (Can.Union vars ctors _ _) =
  Core.DataDecl
    { Core._dataName = Core.QualName home name,
      Core._dataParams = vars,
      Core._dataTransparency = transparency,
      Core._dataCtors = map (lowerCtor home) ctors,
      Core._dataClasses = [],
      Core._dataAffine = affine
    }

-- | A type alias whose body is a closed record, for a native library's header
-- to name the record by (geng-lang @m3-embed.md@ D630); any other alias has
-- nothing to name there.
lowerAlias :: ModuleName.Canonical -> Name -> Can.Alias -> Maybe Core.Alias
lowerAlias home name (Can.Alias vars body _) =
  case lowerType body of
    tipe@(Core.TRecord (_ : _) Nothing) ->
      Just (Core.Alias (Core.QualName home name) vars tipe)
    _ ->
      Nothing

lowerCtor :: ModuleName.Canonical -> Can.Ctor -> Core.Ctor
lowerCtor home (Can.Ctor name index _ argTypes) =
  Core.Ctor
    { Core._ctorName = Core.QualName home name,
      Core._ctorTag = Index.toMachine index,
      Core._ctorFields = map lowerType argTypes
    }
