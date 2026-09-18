{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | Structural derivation: what @\@derive(Eq)@, @\@derive(Ord)@ and
-- @\@derive(Inspect)@ write for you (@classes.md@ §2.1, §2.2,
-- @docs/representation.md@ R5, @docs/m1b-classes.md@ §G25, §G42, §G43).
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
-- __@Inspect@ is a different walk, and deliberately not the same one.__ @eq@
-- and @compare@ are __relations__ — two values in, one answer out — and
-- @inspect@ is a __rendering__: one value in, a string out. Forcing them
-- together would make every field of 'Verb' a @Maybe@ of something. So the
-- binary pair share 'body' and the unary one has 'inspectBody', and what they
-- do share is 'Position''s refusals, which are §2.1's and are the same for all
-- three classes.
--
-- __The format lives in @core@, not here.__ @Inspect.ctor@, @Inspect.record@
-- and @Inspect.arg@ are ordinary functions in the class's own module, and the
-- generated body calls them. So @representation.md@ R5 is one Gren file that
-- can be read against the specification, and this module decides only which
-- components are visited — which is the same question it answers for the other
-- two classes.
--
-- __The two relations share every decision but the leaf.__ @eq@ and @compare@
-- walk the same shapes in the same order and differ in three places: what a
-- pair of components reduces to (a @Bool@ or an @Order@), how a constructor's
-- components are combined (all of them, against the first that is not @EQ@),
-- and what happens when the two constructors are different — @False@ for @eq@,
-- and for @compare@ the answer §2.2 fixes, which is __constructor declaration
-- order__. 'Verb' is that difference, named once so the walk is written once.
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
import Gren.String qualified as ES
import Reporting.Annotation qualified as A
import Reporting.Error.Canonicalize qualified as Error
import Reporting.Result qualified as Result

type Result i w a =
  Result.Result i w Error.Error a

-- | What the generator needs that is not the type or the class.
data Ctx = Ctx
  { _home :: ModuleName.Canonical,
    -- | @Basics.Bool@, for @eq@'s answers and for the fall-through pattern.
    _bool :: Can.Union,
    -- | @Basics.Order@, for @compare@'s.
    _order :: Can.Union,
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
  Can.Union ->
  A.Region ->
  Name.Name ->
  Can.Union ->
  Can.Class ->
  Can.ClassDecl ->
  Name.Name ->
  Result i w Can.Instance
derive home boolDecl orderDecl region typeName union cls@(Can.Class classHome className) decl witness =
  let Can.ClassDecl param published = decl
      ctx = Ctx home boolDecl orderDecl region typeName cls param
      head_ = instanceHead ctx decl union witness
   in case verbOf classHome className of
        Nothing ->
          -- §8.3: structural derivation is defined for `Eq`, `Ord` and
          -- `Inspect` and for nothing else, so a user class has no structural
          -- rule to appeal to. All three are declared now, so the list is
          -- closed rather than partial.
          Result.throw (Error.DeriveNotStructural region typeName className)
        Just (Relation verb) ->
          do
            let name = _v_method verb
            method_ <- methodDef ctx head_ published name (body ctx verb union)
            Result.ok (Can.Instance head_ Can.Derived (Map.singleton name method_))
        Just Rendering ->
          do
            let name = nameInspect
            method_ <- methodDef ctx head_ published name (inspectBody ctx union)
            Result.ok (Can.Instance head_ Can.Derived (Map.singleton name method_))

-- THE TWO VERBS

-- | The three places @eq@ and @compare@ differ, and nothing else does.
--
-- Naming them makes the walk one function rather than two that drift: the
-- structure §2.1 fixes — which components are looked at, in which order, and
-- which shapes refuse — is the same question for both classes and is answered
-- once, in 'body' and 'field'.
data Verb = Verb
  { -- | @eq@ or @compare@, both the method to define and the method to call at
    -- a component.
    _v_method :: Name.Name,
    -- | What a call to it answers with: @Bool@ or @Order@.
    _v_result :: Ctx -> Can.Type,
    -- | One constructor's components, combined. @eq@ wants all of them and
    -- @compare@ the first that is not @EQ@; both answer for a constructor with
    -- no components without looking at anything.
    _v_combine :: Ctx -> [Can.Expr] -> Can.Expr,
    -- | The answer when the two values are different constructors, given how
    -- the right one's index compares with the left one's.
    _v_mismatch :: Ctx -> Ordering -> Can.Expr
  }

-- | Which of §2.1's three classes this is, and therefore which walk it gets.
data Kind
  = Relation Verb
  | Rendering

verbOf :: ModuleName.Canonical -> Name.Name -> Maybe Kind
verbOf classHome className
  | classHome == ModuleName.basics && className == Name.eqClass = Just (Relation eqVerb)
  | classHome == ModuleName.basics && className == Name.ordClass = Just (Relation ordVerb)
  | classHome == ModuleName.inspect && className == Name.inspectClass = Just Rendering
  | otherwise = Nothing

eqVerb :: Verb
eqVerb =
  Verb
    { _v_method = Name.fromChars "eq",
      _v_result = boolType,
      _v_combine = conjunction,
      _v_mismatch = \ctx _ -> bool ctx False
    }

-- | §2.2: a custom type is ordered __by constructor declaration order first__,
-- then by payload order. So the answer for two different constructors is
-- decided before any component is looked at, and it is decided by the index
-- 'Can.Ctor' already carries — no comparison of anything at run time, because
-- the pattern that matched has already established which constructor each side
-- is.
ordVerb :: Verb
ordVerb =
  Verb
    { _v_method = Name.fromChars "compare",
      _v_result = orderType,
      _v_combine = firstUnequal,
      _v_mismatch = \ctx ordering ->
        order ctx (case ordering of LT -> "GT"; EQ -> "EQ"; GT -> "LT")
    }

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
        built <- build (map (binderOf . fst) args)
        Result.ok (Can.TypedDef (A.At (_region ctx) name) freeVars args built result)

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

-- THE WALK

-- | @eq x y@ / @compare x y@: a case on the left, and inside each branch a case
-- on the right.
--
-- The two arguments are what the class's own signature gives it. A @Basics.Eq@
-- whose @eq@ takes anything but two is not the class §1.1 fixes and this
-- generator has nothing to say about it; the same for @Ord@.
body :: Ctx -> Verb -> Can.Union -> [Name.Name] -> Result i w Can.Expr
body ctx verb union@(Can.Union _ ctors _ _) args =
  case args of
    [left, right] ->
      do
        branches <- traverse (branch ctx verb union) ctors
        Result.ok (at ctx (Can.Case (local ctx left) (map (\mk -> mk right) branches)))
    _ ->
      Result.throw (Error.DeriveMethodShape (_region ctx) (_typeName ctx) (_v_method verb))

-- | One outer branch: this constructor on the left, and a case on the right.
--
-- @eq@ needs two inner branches whatever the type looks like — this
-- constructor, and anything else. @compare@ needs to know /which/ other
-- constructor, because §2.2 orders them by declaration, so it lists the ones
-- declared __before__ this one explicitly and lets the wildcard cover the ones
-- declared after. That is @i + 2@ inner branches for the @i@th constructor and
-- so quadratically many for the type, which is the price of deriving an
-- ordering without a primitive that reads a constructor's index. Gren custom
-- types are small and this generator is the only thing that pays it.
branch :: Ctx -> Verb -> Can.Union -> Can.Ctor -> Result i w (Name.Name -> Can.CaseBranch)
branch ctx verb union ctor@(Can.Ctor _ index _ argTypes) =
  do
    comparisons <- traverse (field ctx verb []) (zip [0 :: Int ..] argTypes)
    Result.ok $ \right ->
      let lefts = [Name.fromChars ("$l" ++ show i) | i <- [0 .. length argTypes - 1]]
          rights = [Name.fromChars ("$r" ++ show i) | i <- [0 .. length argTypes - 1]]
          matched =
            _v_combine
              verb
              ctx
              [ compare_ (local ctx l) (local ctx r)
              | (compare_, l, r) <- recursiveLast ctx verb (zip argTypes (zip3 comparisons lefts rights))
              ]
          earlier =
            [ Can.CaseBranch (anonymousPattern ctx union other) (_v_mismatch verb ctx LT)
            | other@(Can.Ctor _ otherIndex _ _) <- namedCtors union,
              Index.toMachine otherIndex < Index.toMachine index,
              distinguishesCtors verb
            ]
          wildcard =
            [ Can.CaseBranch (A.At (_region ctx) Can.PAnything) (_v_mismatch verb ctx GT)
            | Index.toMachine index < numCtors union - 1 || not (distinguishesCtors verb),
              numCtors union > 1
            ]
          inner =
            Can.Case
              (local ctx right)
              (Can.CaseBranch (ctorPattern ctx union ctor rights) matched : earlier ++ wildcard)
       in Can.CaseBranch (ctorPattern ctx union ctor lefts) (at ctx inner)

-- | Whether the mismatch answer depends on /which/ other constructor it is.
--
-- @eq@'s does not — every other constructor is @False@ — so it keeps the two
-- branches it always had and the quadratic listing above is skipped entirely.
distinguishesCtors :: Verb -> Bool
distinguishesCtors verb =
  _v_method verb /= nameEq

namedCtors :: Can.Union -> [Can.Ctor]
namedCtors (Can.Union _ ctors _ _) =
  ctors

-- | How two values of one component type are compared.
--
-- A type constructor and a type variable both go to the class's method — @eq@
-- or @compare@, whichever is being derived: the
-- constructor resolves to that type's instance (§G23) and the variable is the
-- witness case, which reports itself. A record has no constructor and so no
-- instance, and is compared field by field. A function derives nothing, which
-- §2.3 calls the single most visible correctness improvement in the spec.
--
-- The path is the record fields walked to reach this component, so that the
-- error for a function can name the field (§7) and not only the argument.
field :: Ctx -> Verb -> [Name.Name] -> (Int, Can.Type) -> Result i w (Can.Expr -> Can.Expr -> Can.Expr)
field ctx verb path (index, tipe) =
  case Type.iteratedDealias tipe of
    Can.TLambda _ _ ->
      Result.throw $
        Error.DeriveComponentIsFunction (_region ctx) (_typeName ctx) index path
    Can.TRecord fields Nothing ->
      do
        comparisons <- traverse (\(name, t) -> field ctx verb (path ++ [name]) (index, t)) (Map.toList (Map.map fieldType fields))
        let names = Map.keys fields
        let types = map fieldType (Map.elems fields)
        Result.ok $ \left right ->
          _v_combine
            verb
            ctx
            [ compare_ (access ctx left name) (access ctx right name)
            | (compare_, name) <- recursiveLast ctx verb (zip types (zip comparisons names))
            ]
    Can.TRecord _ (Just _) ->
      -- An extensible record reaches here only through an alias, and its row
      -- variable is a component whose type nothing knows.
      Result.throw $
        Error.DeriveComponentIsFunction (_region ctx) (_typeName ctx) index path
    _ ->
      -- A component at a type variable is the same call as one at a type:
      -- @Eq a => Eq (Box a)@ is the head 'instanceHead' already writes, the
      -- variable is in its context, and the witness for it is the one the
      -- instance was passed (§G26). Until verb 6 this was
      -- @CANNOT DERIVE THIS YET@.
      Result.ok $ \left right ->
        at ctx (Can.Call (method ctx verb) [left, right])

-- | @eq@'s components with the ones that mention the type being derived moved
-- to the end, keeping their order otherwise (D333, @m1b-classes.md@ §G51).
--
-- 'conjunction' makes its last test the answer rather than a test, so the last
-- component is compared by a call in tail position. When that call is the
-- instance's own @eq@ the tail-call pass turns it into a loop, and a chain of
-- @Link { rest : Chain, value : Int }@ is compared in constant stack — which it
-- was not while @rest@ sorted before @value@ and the recursion sat under an
-- @if@. @eq@ is a conjunction of pure tests, so the order they run in is not
-- observable.
--
-- @compare@ keeps the order it was given, because that order is the answer:
-- §2.2 orders by payload position and a record by its fields alphabetically,
-- and moving a component would change which one decides.
recursiveLast :: Ctx -> Verb -> [(Can.Type, a)] -> [a]
recursiveLast ctx verb components
  | distinguishesCtors verb = map snd components
  | otherwise =
      [c | (t, c) <- components, not (mentionsSelf ctx t)]
        ++ [c | (t, c) <- components, mentionsSelf ctx t]

-- | Whether a component's type names the type being derived anywhere in it.
mentionsSelf :: Ctx -> Can.Type -> Bool
mentionsSelf ctx tipe =
  case tipe of
    Can.TLambda a b -> mentionsSelf ctx a || mentionsSelf ctx b
    Can.TVar _ -> False
    Can.TType home name args ->
      (home == _home ctx && name == _typeName ctx) || any (mentionsSelf ctx) args
    Can.TRecord fields _ -> any (mentionsSelf ctx . fieldType) (Map.elems fields)
    Can.TAlias _ _ args aliased ->
      any (mentionsSelf ctx . snd) args
        || case aliased of
          Can.Holey t -> mentionsSelf ctx t
          Can.Filled t -> mentionsSelf ctx t

fieldType :: Can.FieldType -> Can.Type
fieldType (Can.FieldType _ tipe) =
  tipe

-- THE RENDERING

-- | @inspect x@: one @case@, one branch per constructor, and each branch is a
-- call to @Inspect.ctor@ with the constructor's own name and its components
-- rendered.
--
-- R5's shapes come out of @core@ rather than out of this function: a
-- constructor with no payload is @ctor "Nothing" []@ and reduces to
-- @"Nothing"@ there, and a nested one is parenthesized by @Inspect.arg@,
-- which decides from the rendered string because @inspect : a -> String@ gives
-- an instance no way to be told it is in an argument position.
inspectBody :: Ctx -> Can.Union -> [Name.Name] -> Result i w Can.Expr
inspectBody ctx union@(Can.Union _ ctors _ _) args =
  case args of
    [subject] ->
      do
        branches <- traverse (inspectBranch ctx union) ctors
        Result.ok (at ctx (Can.Case (local ctx subject) branches))
    _ ->
      Result.throw (Error.DeriveMethodShape (_region ctx) (_typeName ctx) nameInspect)

inspectBranch :: Ctx -> Can.Union -> Can.Ctor -> Result i w Can.CaseBranch
inspectBranch ctx union ctor@(Can.Ctor name _ _ argTypes) =
  do
    renderings <- traverse (inspectField ctx []) (zip [0 :: Int ..] argTypes)
    let binders = [Name.fromChars ("$c" ++ show i) | i <- [0 .. length argTypes - 1]]
    let rendered =
          [ call ctx (foreign_ ctx nameArg oneString) [render (local ctx binder)]
          | (render, binder) <- zip renderings binders
          ]
    Result.ok $
      Can.CaseBranch
        (ctorPattern ctx union ctor binders)
        ( call
            ctx
            (foreign_ ctx nameCtor ctorType)
            [str ctx (ES.fromChars (Name.toChars name)), at ctx (Can.Array rendered)]
        )

-- | How one component is rendered.
--
-- The same three answers 'field' gives, for the same reasons: a function
-- refuses, a record has no instance and is rendered field by field in the
-- alphabetical order 'Map.toAscList' gives, and everything else goes to the
-- class's own method.
inspectField :: Ctx -> [Name.Name] -> (Int, Can.Type) -> Result i w (Can.Expr -> Can.Expr)
inspectField ctx path (index, tipe) =
  case Type.iteratedDealias tipe of
    Can.TLambda _ _ ->
      Result.throw $
        Error.DeriveComponentIsFunction (_region ctx) (_typeName ctx) index path
    Can.TRecord fields Nothing ->
      do
        renderings <- traverse (\(name, t) -> inspectField ctx (path ++ [name]) (index, t)) (Map.toList (Map.map fieldType fields))
        let names = Map.keys fields
        Result.ok $ \subject ->
          call
            ctx
            (foreign_ ctx nameRecord recordType)
            [ at ctx $
                Can.Array
                  [ at ctx $
                      Can.Record
                        ( Map.fromList
                            [ (A.At (_region ctx) nameName, str ctx (ES.fromChars (Name.toChars name))),
                              (A.At (_region ctx) nameValue, render (access ctx subject name))
                            ]
                        )
                  | (render, name) <- zip renderings names
                  ]
            ]
    Can.TRecord _ (Just _) ->
      Result.throw $
        Error.DeriveComponentIsFunction (_region ctx) (_typeName ctx) index path
    _ ->
      Result.ok $ \subject ->
        call ctx (inspectMethod ctx) [subject]

-- | @Inspect.inspect@ at this instance's own class parameter, which is the
-- same node 'method' writes for the other two.
inspectMethod :: Ctx -> Can.Expr
inspectMethod ctx =
  at ctx $
    Can.VarMethod
      (_class ctx)
      (_param ctx)
      nameInspect
      (Can.Forall (Map.singleton (_param ctx) [_class ctx]) (Can.TLambda (Can.TVar (_param ctx)) stringType))

-- | One of @Inspect@'s ordinary functions, named with its home rather than
-- looked up, because generated code must not depend on what the author
-- imported.
foreign_ :: Ctx -> Name.Name -> Can.Type -> Can.Expr
foreign_ ctx name tipe =
  at ctx (Can.VarForeign ModuleName.inspect name (Can.Forall Map.empty tipe))

stringType :: Can.Type
stringType =
  Can.TType ModuleName.string Name.string []

arrayOf :: Can.Type -> Can.Type
arrayOf tipe =
  Can.TType ModuleName.array Name.array [tipe]

-- | @ctor : String -> Array String -> String@
ctorType :: Can.Type
ctorType =
  Can.TLambda stringType (Can.TLambda (arrayOf stringType) stringType)

-- | @record : Array { name : String, value : String } -> String@
recordType :: Can.Type
recordType =
  Can.TLambda
    ( arrayOf
        ( Can.TRecord
            ( Map.fromList
                [ (nameName, Can.FieldType 0 stringType),
                  (nameValue, Can.FieldType 1 stringType)
                ]
            )
            Nothing
        )
    )
    stringType

-- | @arg : String -> String@
oneString :: Can.Type
oneString =
  Can.TLambda stringType stringType

str :: Ctx -> ES.String -> Can.Expr
str ctx value =
  at ctx (Can.Str value)

call :: Ctx -> Can.Expr -> [Can.Expr] -> Can.Expr
call ctx fn args =
  at ctx (Can.Call fn args)

nameInspect :: Name.Name
nameInspect =
  Name.fromChars "inspect"

nameCtor :: Name.Name
nameCtor =
  Name.fromChars "ctor"

nameRecord :: Name.Name
nameRecord =
  Name.fromChars "record"

nameArg :: Name.Name
nameArg =
  Name.fromChars "arg"

nameName :: Name.Name
nameName =
  Name.fromChars "name"

nameValue :: Name.Name
nameValue =
  Name.fromChars "value"

-- BUILDING BLOCKS

at :: Ctx -> Can.Expr_ -> Can.Expr
at ctx =
  Can.at (_region ctx)

local :: Ctx -> Name.Name -> Can.Expr
local ctx name =
  at ctx (Can.VarLocal name)

access :: Ctx -> Can.Expr -> Name.Name -> Can.Expr
access ctx expr name =
  at ctx (Can.Access expr (A.At (_region ctx) name))

-- | The class's method, as the node §G23's resolver reads.
method :: Ctx -> Verb -> Can.Expr
method ctx verb =
  at ctx $
    Can.VarMethod
      (_class ctx)
      (_param ctx)
      (_v_method verb)
      (Can.Forall (Map.singleton (_param ctx) [_class ctx]) (methodType ctx verb))

methodType :: Ctx -> Verb -> Can.Type
methodType ctx verb =
  let a = Can.TVar (_param ctx)
   in Can.TLambda a (Can.TLambda a (_v_result verb ctx))

boolType :: Ctx -> Can.Type
boolType _ =
  Can.TType ModuleName.basics Name.bool []

orderType :: Ctx -> Can.Type
orderType _ =
  Can.TType ModuleName.basics Name.order []

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

-- | The first component that is not @EQ@, and @EQ@ when there are none.
--
-- @case c of EQ -> rest; $o -> $o@ — the fall-through binds rather than
-- repeating @c@, because @c@ is a call and repeating it would compare the
-- component twice on the unequal path, which is the common one. The last
-- component is the answer rather than a test, for the reason 'conjunction'
-- gives.
firstUnequal :: Ctx -> [Can.Expr] -> Can.Expr
firstUnequal ctx tests =
  case tests of
    [] -> order ctx "EQ"
    [test] -> test
    test : rest ->
      let carried = Name.fromChars "$o"
       in at ctx $
            Can.Case
              test
              [ Can.CaseBranch (orderPattern ctx "EQ") (firstUnequal ctx rest),
                Can.CaseBranch (A.At (_region ctx) (Can.PVar carried)) (local ctx carried)
              ]

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

-- | @LT@, @EQ@ or @GT@, read out of @Basics.Order@'s own declaration for the
-- reason 'Canonicalize.Module.boolUnion' gives: generated code must not depend
-- on what the author imported or shadowed.
order :: Ctx -> String -> Can.Expr
order ctx chars =
  let union@(Can.Union _ _ _ opts) = _order ctx
      name = Name.fromChars chars
   in at ctx $
        Can.VarCtor
          opts
          ModuleName.basics
          name
          (ctorIndex union name)
          (Can.Forall Map.empty (Can.TType ModuleName.basics Name.order []))

orderPattern :: Ctx -> String -> Can.Pattern
orderPattern ctx chars =
  let union = _order ctx
      name = Name.fromChars chars
   in A.At (_region ctx) $
        Can.PCtor
          { Can._p_home = ModuleName.basics,
            Can._p_type = Name.order,
            Can._p_union = union,
            Can._p_name = name,
            Can._p_index = ctorIndex union name,
            Can._p_args = []
          }

-- | The same constructor pattern 'ctorPattern' writes, with every argument
-- ignored: @compare@'s @earlier@ branches match to learn which constructor the
-- right-hand value is and never look inside it.
anonymousPattern :: Ctx -> Can.Union -> Can.Ctor -> Can.Pattern
anonymousPattern ctx union ctor@(Can.Ctor _ _ _ argTypes) =
  ctorPattern ctx union ctor [Name.fromChars ("$_" ++ show i) | i <- [0 .. length argTypes - 1]]

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
