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
    lowerAnnotation,
    lowerUnion,
    lowerClass,
  )
where

import AST.Canonical qualified as Can
import AST.Utils.Type qualified as Type
import Core.AST qualified as Core
import Data.Index qualified as Index
import Data.Map qualified as Map
import Data.Name (Name)
import Gren.ModuleName qualified as ModuleName

lowerType :: Can.Type -> Core.Type
lowerType tipe =
  case tipe of
    Can.TVar name ->
      Core.TVar name
    Can.TType home name args ->
      Core.TCon (Core.QualName home name) (map lowerType args)
    Can.TLambda arg result ->
      case lowerType result of
        -- Maximal collapse: a function whose result is itself a function has
        -- one argument list, not two. See C3.
        Core.TFun moreArgs finalResult ->
          Core.TFun (lowerType arg : moreArgs) finalResult
        loweredResult ->
          Core.TFun [lowerType arg] loweredResult
    Can.TRecord fields ext ->
      -- `Map.toAscList` is the alphabetical order C2 asks for, and the
      -- `Word16` source-order index Canonical carries is deliberately dropped.
      Core.TRecord
        [(name, lowerType fieldType) | (name, Can.FieldType _ fieldType) <- Map.toAscList fields]
        ext
    Can.TAlias _ _ args aliasType ->
      lowerType (Type.dealias args aliasType)

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
-- Ordered by variable, then by the order the constraints were written, so that
-- two compilations of the same source emit the same bytes (`docs/core.md` C2).
lowerAnnotation :: Can.Annotation -> Core.Type
lowerAnnotation (Can.Forall freeVars tipe) =
  case Map.toAscList freeVars of
    [] -> lowerType tipe
    vars ->
      Core.TForall
        (map fst vars)
        [ Core.CClass (Core.QualName home name) (Core.TVar var)
        | (var, classes) <- vars,
          Can.Class home name <- classes
        ]
        (lowerType tipe)

-- | A class declaration (@docs/m1b-classes.md@ §G20).
--
-- The methods come out alphabetically because `Can.ClassDecl` keeps them in a
-- 'Map.Map', which is C2's requirement met the same way record fields meet it:
-- an order two frontends agree on without having to agree on a traversal.
--
-- Every declared class is 'Core.Open'. `classes.md` §1.2's closed four are
-- __compiler-known__ — their membership is a table in "Type.Class" and there is
-- no source syntax that says @closed@ — so nothing a module can write is one.
-- What marks them when `core` declares them is verb 7's question, and guessing
-- at it here would put an answer in the field a backend reads.
lowerClass :: ModuleName.Canonical -> Name -> Can.ClassDecl -> Core.ClassDecl
lowerClass home name (Can.ClassDecl param methods) =
  Core.ClassDecl
    { Core._classNameC = Core.QualName home name,
      Core._classParam = param,
      Core._classOpenness = Core.Open,
      Core._classMethods =
        [(methodName, lowerAnnotation annotation) | (methodName, annotation) <- Map.toAscList methods]
    }

-- | A custom type declaration.
--
-- Everything is `Core.Transparent` and every class set is empty at M1a.
-- Abstract types and published class sets are @classes.md@ §2.5, which lands
-- with the classes themselves at M1b; recording a guess here would be a
-- fabricated answer in a field a backend reads for layout.
lowerUnion :: ModuleName.Canonical -> Name -> Can.Union -> Core.DataDecl
lowerUnion home name (Can.Union vars ctors _ _) =
  Core.DataDecl
    { Core._dataName = Core.QualName home name,
      Core._dataParams = vars,
      Core._dataTransparency = Core.Transparent,
      Core._dataCtors = map (lowerCtor home) ctors,
      Core._dataClasses = []
    }

lowerCtor :: ModuleName.Canonical -> Can.Ctor -> Core.Ctor
lowerCtor home (Can.Ctor name index _ argTypes) =
  Core.Ctor
    { Core._ctorName = Core.QualName home name,
      Core._ctorTag = Index.toMachine index,
      Core._ctorFields = map lowerType argTypes
    }
