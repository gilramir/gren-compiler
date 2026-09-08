{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | Structural derivation: what @\@derive(Eq)@ writes for you
-- (@classes.md@ §2.1, @docs/m1b-classes.md@ §G25).
--
-- __What it produces is an ordinary instance.__ A derived instance is a
-- 'AST.Canonical.Instance' with a real head and real method definitions, sitting
-- in @Can.Module._instances@ beside the written ones. So it is type-checked by
-- the machinery that checks a written one, it resolves by the machinery that
-- resolves to a written one (§G23), and a generator bug is a @TYPE MISMATCH@
-- rather than bad JavaScript. The only thing that distinguishes it is
-- 'AST.Canonical.Derived', which Core carries through as
-- 'Core.AST.Origin'.
--
-- __Only an abstract type asks.__ §8.1: a transparent type's structure is
-- already public, so it derives implicitly and @\@derive@ on one is a
-- redundancy error rather than a no-op. That check needs to know transparent
-- from abstract, which is 'AST.Canonical.isAbstract' and is why §G16.1 could
-- not make it before now.
--
-- __A component is compared by its own instance, not by walking it.__ That is
-- the whole point of §2.5: @Dict@'s structural equality is /wrong/, so a type
-- with a @Dict@ field has to reach @Dict@'s own answer. The exception is a
-- record, which has no type constructor and so can have no instance — its
-- fields are compared inline, in the alphabetical order 'Map.toAscList' gives,
-- which is the same order §2.2 fixes for derived ordering and for the same
-- reason.
module Canonicalize.Derive
  ( derive,
  )
where

import AST.Canonical qualified as Can
import AST.Utils.Type qualified as Type
import Canonicalize.Instance qualified as Instance
import Data.Index qualified as Index
import Data.Map.Strict qualified as Map
import Data.Name qualified as Name
import Gren.ModuleName qualified as ModuleName
import Reporting.Annotation qualified as A
import Reporting.Error.Canonicalize qualified as Error
import Reporting.Result qualified as Result

type Result i w a =
  Result.Result i w Error.Error a

-- | What the generator needs that is not the type or the class.
data Ctx = Ctx
  { _home :: ModuleName.Canonical,
    -- | @Basics.Bool@, for the answers and for the fall-through pattern.
    _bool :: Can.Union,
    -- | The @\@derive@ attribute's, so every generated node has a real one and
    -- an error about generated code points at what asked for it.
    _region :: A.Region,
    _typeName :: Name.Name,
    _class :: Can.Class,
    _param :: Name.Name
  }

-- DERIVE

-- | The instance @\@derive(C)@ asks for, or why there is not one.
derive ::
  ModuleName.Canonical ->
  Can.Union ->
  A.Region ->
  Name.Name ->
  Can.Union ->
  Can.Class ->
  Can.ClassDecl ->
  Name.Name ->
  Result i w Can.Instance
derive home boolDecl region typeName union cls@(Can.Class classHome className) decl witness =
  let Can.ClassDecl param published = decl
      ctx = Ctx home boolDecl region typeName cls param
      head_ = instanceHead ctx decl union witness
   in if classHome /= ModuleName.basics || className /= Name.fromChars "Eq"
        then
          -- §8.3: structural derivation is defined for `Eq`, `Ord` and
          -- `Inspect` and for nothing else, so a user class has no structural
          -- rule to appeal to. `Ord` and `Inspect` are not declared yet
          -- (§G24.2, §G24.3), so today the list is one long.
          Result.throw (Error.DeriveNotStructural region typeName className)
        else do
          eqMethod <- methodDef ctx head_ published nameEq (eqBody ctx union)
          Result.ok (Can.Instance head_ Can.Derived (Map.singleton nameEq eqMethod))

-- | @instance Eq a => Eq (T a)@, for a @T@ of any arity.
--
-- The context is every one of the type's variables constrained by the class
-- being derived, which is exactly §2.1's rule — @T a@ derives @C@ when @a@
-- does — written as the head a resolver reads.
instanceHead :: Ctx -> Can.ClassDecl -> Can.Union -> Name.Name -> Can.InstanceHead
instanceHead ctx (Can.ClassDecl param published) (Can.Union vars _ _ _) witness =
  let withoutMethods =
        Can.InstanceHead
          { Can._ih_home = _home ctx,
            Can._ih_class = _class ctx,
            Can._ih_con = _home ctx,
            Can._ih_conName = _typeName ctx,
            Can._ih_args = map Can.TVar vars,
            Can._ih_witness = witness,
            Can._ih_context = Map.fromList [(v, [_class ctx]) | v <- vars],
            Can._ih_methods = Map.empty
          }
   in withoutMethods
        { Can._ih_methods =
            Map.map
              (\annotation -> let Can.Forall _ tipe = Instance.specialize withoutMethods param annotation in tipe)
              published
        }

-- | A method definition, with the signature the class published for it
-- specialized at this head — the same 'Canonicalize.Instance.specialize' a
-- written method gets, so a derived body is checked against the same type a
-- hand-written one would be.
methodDef ::
  Ctx ->
  Can.InstanceHead ->
  Map.Map Name.Name Can.Annotation ->
  Name.Name ->
  ([Name.Name] -> Result i w Can.Expr) ->
  Result i w Can.Def
methodDef ctx head_ published name build =
  case Map.lookup name published of
    Nothing ->
      Result.throw (Error.DeriveMethodMissing (_region ctx) (_typeName ctx) name)
    Just annotation ->
      do
        let Can.Forall freeVars tipe = Instance.specialize head_ (_param ctx) annotation
        let (args, result) = arguments ctx tipe
        body <- build (map (binderOf . fst) args)
        Result.ok (Can.TypedDef (A.At (_region ctx) name) freeVars args body result)

-- | The argument list a method's specialized type asks for, named @$0@, @$1@.
--
-- The names carry a @$@ so that nothing the author wrote can be captured by
-- one, which is the same guarantee C6 gives the lowering's generated binders
-- and is available for the same reason: a Gren identifier has no @$@ in it.
arguments :: Ctx -> Can.Type -> ([(Can.Pattern, Can.Type)], Can.Type)
arguments ctx tipe =
  argumentsFrom ctx 0 tipe

argumentsFrom :: Ctx -> Int -> Can.Type -> ([(Can.Pattern, Can.Type)], Can.Type)
argumentsFrom ctx index tipe =
  case tipe of
    Can.TLambda arg result ->
      let (rest, final) = argumentsFrom ctx (index + 1) result
          binder = Name.fromChars ("$" ++ show index)
       in ((A.At (_region ctx) (Can.PVar binder), arg) : rest, final)
    _ ->
      ([], tipe)

-- EQ

-- | @eq x y@: the same constructor with equal fields, or 'False'.
--
-- The two arguments are what the class's own signature gives it. A @Basics.Eq@
-- whose @eq@ takes anything but two is not the class §1.1 fixes and this
-- generator has nothing to say about it.
eqBody :: Ctx -> Can.Union -> [Name.Name] -> Result i w Can.Expr
eqBody ctx union@(Can.Union _ ctors _ _) args =
  case args of
    [left, right] ->
      do
        branches <- traverse (eqBranch ctx union) ctors
        Result.ok (at ctx (Can.Case (local ctx left) (map (\branch -> branch right) branches)))
    _ ->
      Result.throw (Error.DeriveMethodShape (_region ctx) (_typeName ctx) nameEq)

-- | One outer branch: this constructor on the left, and a case on the right
-- that answers 'False' for any other.
eqBranch :: Ctx -> Can.Union -> Can.Ctor -> Result i w (Name.Name -> Can.CaseBranch)
eqBranch ctx union ctor@(Can.Ctor _ _ _ argTypes) =
  do
    comparisons <- traverse (eqField ctx) (zip [0 :: Int ..] argTypes)
    Result.ok $ \right ->
      let lefts = [Name.fromChars ("$l" ++ show i) | i <- [0 .. length argTypes - 1]]
          rights = [Name.fromChars ("$r" ++ show i) | i <- [0 .. length argTypes - 1]]
          matched =
            conjunction
              ctx
              [ compare_ (local ctx l) (local ctx r)
              | (compare_, l, r) <- zip3 comparisons lefts rights
              ]
          inner =
            Can.Case
              (local ctx right)
              ( Can.CaseBranch (ctorPattern ctx union ctor rights) matched
                  : [ Can.CaseBranch (A.At (_region ctx) Can.PAnything) (bool ctx False)
                    | numCtors union > 1
                    ]
              )
       in Can.CaseBranch (ctorPattern ctx union ctor lefts) (at ctx inner)

-- | How two values of one component type are compared.
--
-- A type constructor and a type variable both go to the class's method: the
-- constructor resolves to that type's instance (§G23) and the variable is the
-- witness case, which reports itself. A record has no constructor and so no
-- instance, and is compared field by field. A function derives nothing, which
-- §2.3 calls the single most visible correctness improvement in the spec.
eqField :: Ctx -> (Int, Can.Type) -> Result i w (Can.Expr -> Can.Expr -> Can.Expr)
eqField ctx (index, tipe) =
  case Type.iteratedDealias tipe of
    Can.TLambda _ _ ->
      Result.throw $
        Error.DeriveComponentIsFunction (_region ctx) (_typeName ctx) index
    Can.TRecord fields Nothing ->
      do
        comparisons <- traverse (eqField ctx) (zip (repeat index) (map fieldType (Map.elems fields)))
        let names = Map.keys fields
        Result.ok $ \left right ->
          conjunction
            ctx
            [ compare_ (access ctx left field) (access ctx right field)
            | (compare_, field) <- zip comparisons names
            ]
    Can.TRecord _ (Just _) ->
      -- An extensible record reaches here only through an alias, and its row
      -- variable is a component whose type nothing knows.
      Result.throw $
        Error.DeriveComponentIsFunction (_region ctx) (_typeName ctx) index
    _ ->
      -- A component at a type variable is the same call as one at a type:
      -- @Eq a => Eq (Box a)@ is the head 'instanceHead' already writes, the
      -- variable is in its context, and the witness for it is the one the
      -- instance was passed (§G26). Until verb 6 this was
      -- @CANNOT DERIVE THIS YET@.
      Result.ok $ \left right ->
        at ctx (Can.Call (method ctx) [left, right])

fieldType :: Can.FieldType -> Can.Type
fieldType (Can.FieldType _ tipe) =
  tipe

-- BUILDING BLOCKS

at :: Ctx -> Can.Expr_ -> Can.Expr
at ctx =
  Can.at (_region ctx)

local :: Ctx -> Name.Name -> Can.Expr
local ctx name =
  at ctx (Can.VarLocal name)

access :: Ctx -> Can.Expr -> Name.Name -> Can.Expr
access ctx expr field =
  at ctx (Can.Access expr (A.At (_region ctx) field))

-- | The class's method, as the node §G23's resolver reads.
method :: Ctx -> Can.Expr
method ctx =
  at ctx $
    Can.VarMethod
      (_class ctx)
      (_param ctx)
      (Name.fromChars "eq")
      (Can.Forall (Map.singleton (_param ctx) [_class ctx]) (methodType ctx))

methodType :: Ctx -> Can.Type
methodType ctx =
  let a = Can.TVar (_param ctx)
   in Can.TLambda a (Can.TLambda a (boolType ctx))

boolType :: Ctx -> Can.Type
boolType _ =
  Can.TType ModuleName.basics Name.bool []

-- | Every one of them, and 'True' when there are none.
--
-- @&&@ is @if a then b else False@, which needs no operator to be in scope
-- where the generated code lands. The last conjunct is the answer rather than a
-- test against 'True', so a one-field constructor's method is the comparison
-- itself and not the comparison wrapped in a @case@ that returns it.
conjunction :: Ctx -> [Can.Expr] -> Can.Expr
conjunction ctx tests =
  case tests of
    [] -> bool ctx True
    [test] -> test
    test : rest -> at ctx (Can.If [(test, conjunction ctx rest)] (bool ctx False))

bool :: Ctx -> Bool -> Can.Expr
bool ctx value =
  let union@(Can.Union _ _ _ opts) = _bool ctx
      name = if value then Name.fromChars "True" else Name.fromChars "False"
      index = ctorIndex union name
   in at ctx $
        Can.VarCtor
          opts
          ModuleName.basics
          name
          index
          (Can.Forall Map.empty (Can.TType ModuleName.basics Name.bool []))

ctorPattern :: Ctx -> Can.Union -> Can.Ctor -> [Name.Name] -> Can.Pattern
ctorPattern ctx union (Can.Ctor name index _ argTypes) binders =
  A.At (_region ctx) $
    Can.PCtor
      { Can._p_home = _home ctx,
        Can._p_type = _typeName ctx,
        Can._p_union = union,
        Can._p_name = name,
        Can._p_index = index,
        Can._p_args =
          [ Can.PatternCtorArg i tipe (A.At (_region ctx) (Can.PVar binder))
          | (i, tipe, binder) <- zip3 (iterate Index.next Index.first) argTypes binders
          ]
      }

numCtors :: Can.Union -> Int
numCtors (Can.Union _ _ n _) =
  n

ctorIndex :: Can.Union -> Name.Name -> Index.ZeroBased
ctorIndex (Can.Union _ ctors _ _) name =
  case [index | Can.Ctor other index _ _ <- ctors, other == name] of
    index : _ -> index
    [] -> Index.first

nameEq :: Name.Name
nameEq =
  Name.fromChars "eq"

binderOf :: Can.Pattern -> Name.Name
binderOf (A.At _ p) =
  case p of
    Can.PVar name -> name
    _ -> Name.fromChars "$0"
