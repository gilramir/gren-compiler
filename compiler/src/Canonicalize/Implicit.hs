{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | Implicit structural derivation: the instances a __transparent__ type has
-- without asking (@classes.md@ §2.1, @docs/m1b-classes.md@ §G37).
--
-- §2.1 has two halves and 'Canonicalize.Derive' is the other one. __Explicit__
-- is an abstract type asking with @\@derive(Eq)@, and the answer to a question
-- that was asked can be an error: a component that is a function is
-- @CANNOT DERIVE THIS@ and names the field. __Implicit__ is every transparent
-- type deriving because its structure is already public, and there is nobody to
-- report to — a type with a function in it simply does not derive, and what
-- says so is a missing instance at the place someone tried to use one.
--
-- So the two halves cannot share a code path even though they share a
-- generator: this module __decides__ and 'Canonicalize.Derive' __writes__.
--
-- __The instance environment is the class set §2.4 asks for.__ §G25.4 priced
-- this as an interface change — @Gren.Interface@ publishing a class set per
-- type, and a fixpoint over the import graph — and that was one measurement
-- too few. An instance for @Eq Foo@ published in @Foo@'s module __is__ the
-- statement that @Foo@ derives @Eq@; @Gren.Interface._instances@ already
-- carries it, already transitively (D122), and 'Canonicalize.Module' already
-- has the union of them before it canonicalizes anything. The only fixpoint
-- left is over the module's __own__ types, which is a local SCC and not a
-- graph problem. See §G37.2.
--
-- __The fixpoint is the greatest one__, which is §2.1's word "coinductively":
-- assume every candidate derives, strike out the ones whose components say
-- otherwise, repeat. A recursive type derives, and so does a mutually
-- recursive group, unless something outside the group refuses.
module Canonicalize.Implicit
  ( add,
  )
where

import AST.Canonical qualified as Can
import AST.Utils.Type qualified as Type
import Canonicalize.Derive qualified as Derive
import Canonicalize.Instance qualified as Instance
import Control.Monad (foldM)
import Data.Map.Strict qualified as Map
import Data.Name qualified as Name
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName
import Reporting.Annotation qualified as A
import Reporting.Error.Canonicalize qualified as Error
import Reporting.Result qualified as Result

type Result i w a =
  Result.Result i w Error.Error a

-- | Add the instances this module's transparent types derive without asking.
--
-- Runs __after__ the written and @\@derive@d ones, and skips any key they
-- already answer: a hand-written @instance Eq MyType@ is the module saying the
-- structural answer is not the one it wants (§2.5's reason, at a type whose
-- structure happens to be public), and silently generating a second one would
-- be a duplicate rather than a choice.
add ::
  ModuleName.Canonical ->
  -- | The class to derive and its declaration, when the module can see it.
  -- Nothing while @Basics@ compiles the class itself.
  Maybe (Can.Class, Can.ClassDecl) ->
  -- | @Basics.Bool@, which every generated method answers with.
  Can.Union ->
  Can.Exports ->
  Map.Map Name.Name Can.Union ->
  -- | Where each type was declared, so that anything a generated instance
  -- provokes points at the declaration that made it exist.
  Map.Map Name.Name A.Region ->
  -- | Every instance an import publishes.
  Map.Map Can.InstanceKey Can.InstanceHead ->
  Instance.Instances ->
  Result i w Instance.Instances
add home maybeClass boolDecl exports unions regions imported sofar =
  case maybeClass of
    Nothing ->
      Result.ok sofar
    Just (cls, decl) ->
      let candidates = transparent exports unions
          taken = Set.union (Map.keysSet sofar) (Map.keysSet imported)
          known named = Set.member (keyOf cls named) taken
          deriving_ = Set.filter (\name -> not (known (home, name))) (settle home known candidates)
       in foldM (generate home cls decl boolDecl unions regions) sofar (Set.toAscList deriving_)

-- | The module's types that derive at all: a custom type whose constructors it
-- exposes, or that it does not expose (§2.5 — structure is the meaning when
-- structure is public, and a private type's structure is public to everyone
-- who can name it).
transparent :: Can.Exports -> Map.Map Name.Name Can.Union -> Map.Map Name.Name Can.Union
transparent exports unions =
  Map.filterWithKey (\name _ -> not (Can.isAbstract exports name)) unions

keyOf :: Can.Class -> (ModuleName.Canonical, Name.Name) -> Can.InstanceKey
keyOf cls (home, name) =
  Can.InstanceKey cls home name

-- THE FIXPOINT

-- | Which candidates survive, by striking out until nothing changes.
--
-- The greatest fixpoint, not the least: starting from "all of them derive" is
-- what makes a recursive type derive, and starting from none would make it
-- derive nothing. Each round is O(components); the rounds are bounded by the
-- number of candidates because a struck type never comes back.
settle ::
  ModuleName.Canonical ->
  ((ModuleName.Canonical, Name.Name) -> Bool) ->
  Map.Map Name.Name Can.Union ->
  Set.Set Name.Name
settle home known candidates =
  let go assumed =
        let survives name =
              case Map.lookup name candidates of
                Nothing -> False
                Just (Can.Union _ ctors _ _) ->
                  all (componentDerives home known assumed Component) (concatMap ctorArgs ctors)
            kept = Set.filter survives assumed
         in if kept == assumed then assumed else go kept
   in go (Map.keysSet candidates)

ctorArgs :: Can.Ctor -> [Can.Type]
ctorArgs (Can.Ctor _ _ _ args) =
  args

-- | Where a type sits, which decides what a __record__ there means.
--
-- 'Component' is a constructor's argument, or a field of a record that is one:
-- 'Canonicalize.Derive' compares a record there __inline__, field by field,
-- because a record has no type constructor and so can have no instance.
--
-- 'Argument' is an argument of a type constructor — the @Era@ of
-- @Array Era@ — and there the generated code compares nothing itself: it
-- calls @Array@'s instance, which needs a __witness__ for its element, and a
-- witness is a value that some instance has to supply. So a record derives in
-- one position and not in the other, and §2.1's table, which does not
-- distinguish them, is optimistic by exactly that much (§G37.4).
data Position
  = Component
  | Argument
  deriving (Eq)

-- | Whether one component type derives the class.
--
-- §2.1's table read as a predicate, with 'Position' as the fifth answer it
-- does not have:
--
--   * a __function__ never derives, which is the rule §2.3 calls the single
--     most visible correctness improvement in the spec;
--   * a __variable__ always does, because it becomes the instance's context —
--     @Eq a => Eq (Box a)@ is the head 'Canonicalize.Derive' writes;
--   * a __record__ derives in a 'Component' position when every field does,
--     and never in an 'Argument' one;
--   * a __type constructor__ derives when there is an instance for it — one
--     published by an import, one this module already has, or one this round
--     is still assuming — and when every argument derives in 'Argument'
--     position.
--
-- The argument check is stricter than resolution in one other way: it asks
-- about every argument rather than only the ones the instance's context
-- constrains, so a phantom argument that does not derive strikes the type out.
-- That matches what 'Canonicalize.Derive.instanceHead' writes, which
-- constrains every variable of the type it is deriving for, and the two have
-- to agree or a generated instance would be one nothing can resolve.
componentDerives ::
  ModuleName.Canonical ->
  ((ModuleName.Canonical, Name.Name) -> Bool) ->
  Set.Set Name.Name ->
  Position ->
  Can.Type ->
  Bool
componentDerives home known assumed position tipe =
  case Type.iteratedDealias tipe of
    Can.TLambda _ _ ->
      False
    Can.TVar _ ->
      True
    Can.TRecord fields Nothing ->
      position == Component
        && all (componentDerives home known assumed Component . fieldType) (Map.elems fields)
    Can.TRecord _ (Just _) ->
      -- An extensible record's row variable is a component whose type nothing
      -- knows, which is the same reason `Canonicalize.Derive` refuses one.
      False
    Can.TType tipeHome name args ->
      let here = tipeHome == home && Set.member name assumed
       in (here || known (tipeHome, name))
            && all (componentDerives home known assumed Argument) args
    Can.TAlias _ _ _ _ ->
      -- Unreachable: `iteratedDealias` above removed every alias it could, and
      -- what it leaves is a holey one, which only appears in an annotation.
      False

fieldType :: Can.FieldType -> Can.Type
fieldType (Can.FieldType _ tipe) =
  tipe

-- GENERATING

generate ::
  ModuleName.Canonical ->
  Can.Class ->
  Can.ClassDecl ->
  Can.Union ->
  Map.Map Name.Name Can.Union ->
  Map.Map Name.Name A.Region ->
  Instance.Instances ->
  Name.Name ->
  Result i w Instance.Instances
generate home cls decl boolDecl unions regions sofar typeName =
  case Map.lookup typeName unions of
    Nothing ->
      Result.ok sofar
    Just union ->
      do
        let witness = Instance.witnessNameOf sofar (classNameOf cls) typeName
        let region = Map.findWithDefault A.zero typeName regions
        -- Nothing generated here can fail: 'settle' has already refused every
        -- component 'Canonicalize.Derive' would have reported. The region is
        -- the type declaration's all the same, because a bug in this module
        -- shows up as a type error in code nobody wrote and the declaration is
        -- the only thing a reader can be pointed at.
        instance_ <-
          Derive.derive home boolDecl region typeName union cls decl witness
        Result.ok (Map.insert (Can.InstanceKey cls home typeName) instance_ sofar)

classNameOf :: Can.Class -> Name.Name
classNameOf (Can.Class _ name) =
  name
