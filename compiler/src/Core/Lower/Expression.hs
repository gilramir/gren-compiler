{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | Lower canonical expressions, definitions and patterns to Core.
--
-- The expression half of the lowering. @docs/core.md@ §C2 is the grammar and
-- this module is meant to be read beside it; what follows is only the places
-- where the two languages do not line up.
--
-- __Every node's type comes from the solver__, by node id
-- (@docs/m1a-node-types.md@). A missing one is an `error` rather than a
-- `Maybe`: `Type.Constrain.Expression` records at the single point every node
-- passes through, so a gap is a broken invariant, not an unusual program.
--
-- __Canonical binds patterns where Core binds names.__ A lambda argument, a
-- definition argument and a destructuring @let@ can all be a pattern in
-- Canonical; Core's 'Core.AST.ELam' and 'Core.AST.Bind' take a 'Core.AST.Binder',
-- which is a name. So a pattern argument becomes a generated binder plus an
-- 'Core.AST.ECase' around the body, and a destructuring @let@ becomes an
-- 'Core.AST.ECase' with one alternative. Generated binders are named @$0@, @$1@
-- and @$r@ — @$@ cannot appear in a Gren name, so they cannot collide, and the
-- numbering is positional rather than a counter, so it is deterministic
-- without one (C6).
--
-- __Constructors are saturated in Core__ (C2), so @Just x@ is an
-- 'Core.AST.ECtor' but a bare @Just@ is an 'Core.AST.ELam' around one. The
-- saturated case is recognized here rather than left to a pass, because
-- otherwise 'Core.AST.ECtor' would hardly ever be produced and the node would
-- be describing the AST's shape rather than the program's meaning.
--
-- Three things this pass deliberately does not do, each because doing it would
-- mean inventing an answer M1b has to give properly:
--
--   * __No 'Core.AST.ETyLam' or 'Core.AST.ETyApp'.__ Type abstraction pairs
--     with witness abstraction and both are the elaborator's, at M1b (D10).
--     Introducing type application alone would mean computing an
--     instantiation at every use site for a node nothing reads yet, and
--     binder types are correspondingly left unquantified: a 'Core.AST.TForall'
--     with no 'Core.AST.ETyLam' to bind is decoration, and an inconsistently
--     applied one is worse.
--   * __No partial application made explicit.__ C3 wants a partial
--     application to be a visible 'Core.AST.ELam'; deciding that an
--     application is partial needs the callee's arity, which for an imported
--     function is not in this module. It is a Core→Core pass, and C11 gives
--     M1a no passes.
--   * __No 'Core.AST.EPrim' and no @'Core.AST.ECrash' 'Core.AST.Todo'.__ Both
--     wait on @core@ being rewritten with C13's @\@prim@ table at M1b.
--     @Debug.log@ and @Debug.todo@ lower as the ordinary @Debug@ functions
--     they still are.
module Core.Lower.Expression
  ( Env (..),
    expr,
    def,
    pattern,
    span,
  )
where

import AST.Canonical qualified as Can
import Core.AST qualified as Core
import Core.Lower.Literal qualified as Literal
import Core.Lower.Type (lowerAnnotation, lowerType)
import Core.Order qualified as Order
import Core.Prim qualified as Prim
import Core.Refs qualified as Refs
import Data.Index qualified as Index
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set qualified as Set
import Data.Utf8 qualified as Utf8
import Data.Word (Word32)
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Reporting.Annotation qualified as A
import Type.Resolve qualified as Resolve
import Prelude hiding (span)

-- ENVIRONMENT

data Env = Env
  { -- | The file this module's spans point into. C5 keeps a file id on every
    -- node rather than assuming the enclosing module's, so that a Core→Core
    -- pass can inline across a module boundary without losing where the code
    -- came from.
    _file :: !Core.FileId,
    -- | One entry per node, from the solver.
    _types :: Map.Map Can.NodeId Can.Type,
    -- | What each use of a constrained name elaborates to, from
    -- `Type.Resolve` (§G23, §G26). Total for the same reason '_types' is:
    -- every use elaborated or the module did not get here.
    _uses :: Resolve.Uses,
    -- | The witness parameters each definition binds, keyed by the node id of
    -- its body.
    _params :: Resolve.Params,
    -- | The context inferred for each unannotated definition (§G33), keyed by
    -- the node id of the definition. A definition with an entry here is
    -- constrained, and is quantified in Core exactly as a written one is.
    _inferred :: Resolve.Inferred
  }

-- | The type recorded for a node.
canTypeOf :: Env -> Can.NodeId -> Can.Type
canTypeOf env nid =
  case Map.lookup nid (_types env) of
    Just tipe -> tipe
    Nothing ->
      error $
        "Core.Lower.Expression: node "
          ++ show nid
          ++ " has no recorded type. See docs/m1a-node-types.md."

-- | The Core type recorded for a node.
typeOf :: Env -> Can.NodeId -> Core.Type
typeOf env nid =
  lowerType (canTypeOf env nid)

-- | What a use of a constrained name elaborates to, or nothing if the name is
-- not constrained.
useOf :: Env -> Can.NodeId -> Maybe Resolve.Use
useOf env nid = Map.lookup nid (_uses env)

-- | The witness parameters a definition binds, found by its body's node id.
paramsOf :: Env -> Can.NodeId -> [(Name, Can.Type)]
paramsOf env nid = Map.findWithDefault [] nid (_params env)

-- WITNESSES

-- | A witness, as the value it is (§G26).
--
-- A witness for @C t@ is a record with one field per method of @C@; the one an
-- instance supplies is the binding D125 gives that instance, applied to
-- witnesses for its own context. So the two nodes R1 keeps for the semantics —
-- 'Core.AST.EWitLam' and 'Core.AST.EWitApp' — are a lambda and a call that
-- specialization is allowed to erase, and every other node here is one a
-- backend already emits.
witness :: Core.Span -> Resolve.Witness -> Core.Expr
witness sp w =
  case w of
    Resolve.FromParam name tipe ->
      Core.Expr (Core.EVar name) (lowerType tipe) sp
    Resolve.FromInstance home name args tipe ->
      let table = lowerType tipe
          global = Core.Expr (Core.EGlobal (Core.QualName home name)) table sp
       in case args of
            [] -> global
            _ -> Core.Expr (Core.EWitApp global (map (witness sp) args)) table sp
    Resolve.FromRecord cls fields subject tipe ->
      recordWitness sp cls fields (lowerType subject) (lowerType tipe)

-- | The method table for a record type, built where it is needed (§G38).
--
-- Every other witness names something: a parameter the definition was handed,
-- or an instance's binding. A record has no instance to name, because an
-- instance head is a type constructor applied to arguments and a record has no
-- constructor — so this is the one witness that is a value written out rather
-- than a reference, and it is written out at each use.
--
-- What it holds is `classes.md` §2.1's rule for a record, which
-- 'Canonicalize.Derive.eqField' already writes for a record that is a
-- __component__ of a type that does have a constructor. The two say the same
-- thing about the same shape, in two IRs, because the two shapes reach the
-- comparison by different routes; §G38.3 is the argument for not unifying them.
recordWitness :: Core.Span -> Can.Class -> [(Name, Resolve.Witness)] -> Core.Type -> Core.Type -> Core.Expr
recordWitness sp cls@(Can.Class _ className) fields subject tipe
  | className == Name.ordClass = Core.Expr (Core.ERecord [(nameCompare, ordMethod sp cls fields subject)]) tipe sp
  | className == Name.inspectClass = Core.Expr (Core.ERecord [(nameInspect, inspectMethod sp cls fields subject)]) tipe sp
  | otherwise = Core.Expr (Core.ERecord [(nameEq, eqMethod sp cls fields subject)]) tipe sp

-- | @\$el $er -> $el.a == $er.a && …@, and 'True' for the empty record.
eqMethod :: Core.Span -> Can.Class -> [(Name, Resolve.Witness)] -> Core.Type -> Core.Expr
eqMethod sp cls fields subject =
  let compare_ (field, w) =
        Core.Expr
          (Core.EApp (method sp cls nameEq w) [access sp subject witLeft field, access sp subject witRight field])
          boolType
          sp
   in lambda2 sp subject boolType (conjunction sp (map compare_ fields))

-- | @\$el $er -> case compare $el.a $er.a of EQ -> …; $o -> $o@, and @EQ@ for
-- the empty record.
--
-- The fall-through binds rather than repeating the call, which is the same
-- choice 'Canonicalize.Derive.firstUnequal' makes and for the same reason: the
-- unequal path is the common one and the component would otherwise be compared
-- twice.
ordMethod :: Core.Span -> Can.Class -> [(Name, Resolve.Witness)] -> Core.Type -> Core.Expr
ordMethod sp cls fields subject =
  let compare_ (field, w) =
        Core.Expr
          (Core.EApp (method sp cls nameCompare w) [access sp subject witLeft field, access sp subject witRight field])
          orderType
          sp
   in lambda2 sp subject orderType (firstUnequal sp (map compare_ fields))

-- | @\$el -> Inspect.record [ { name = "a", value = inspect $el.a }, … ]@.
--
-- `representation.md` R5's record shape, built by the same @Inspect.record@
-- that a derived instance calls, so the two routes to a record produce one
-- format (§G43.3).
inspectMethod :: Core.Span -> Can.Class -> [(Name, Resolve.Witness)] -> Core.Type -> Core.Expr
inspectMethod sp cls fields subject =
  let entry (field, w) =
        Core.Expr
          ( Core.ERecord
              [ (nameName, Core.Expr (Core.ELit (Core.LString (Utf8.fromChars (Name.toChars field)))) stringType sp),
                ( nameValue,
                  Core.Expr
                    (Core.EApp (method sp cls nameInspect w) [access sp subject witLeft field])
                    stringType
                    sp
                )
              ]
          )
          entryType
          sp
      entries = Core.Expr (Core.EArray (map entry fields)) (arrayOf entryType) sp
      called =
        Core.Expr
          ( Core.EApp
              (Core.Expr (Core.EGlobal (Core.QualName ModuleName.inspect nameRecord)) recordFnType sp)
              [entries]
          )
          stringType
          sp
   in Core.Expr
        (Core.ELam [Core.Binder witLeft subject sp] called)
        (Core.TFun [subject] stringType)
        sp

witLeft :: Name
witLeft = Name.fromChars "$el"

witRight :: Name
witRight = Name.fromChars "$er"

access :: Core.Span -> Core.Type -> Name -> Name -> Core.Expr
access sp subject side field =
  Core.Expr (Core.EAccess (Core.Expr (Core.EVar side) subject sp) field) (fieldType subject field) sp

lambda2 :: Core.Span -> Core.Type -> Core.Type -> Core.Expr -> Core.Expr
lambda2 sp subject result body =
  Core.Expr
    (Core.ELam [Core.Binder witLeft subject sp, Core.Binder witRight subject sp] body)
    (Core.TFun [subject, subject] result)
    sp

-- | One method out of a witness, which is what a witness is a record of.
method :: Core.Span -> Can.Class -> Name -> Resolve.Witness -> Core.Expr
method sp _ name w =
  let table = witness sp w
   in Core.Expr (Core.EAccess table name) (fieldType (Core.typeOf table) name) sp

-- | @a && b && …@, as the nested `case` `Canonicalize.Derive` writes for the
-- same rule. `True` for the empty record, which is the right answer and the
-- only one available.
conjunction :: Core.Span -> [Core.Expr] -> Core.Expr
conjunction sp conditions =
  case conditions of
    [] ->
      Core.Expr (Core.ECtor (Core.QualName ModuleName.basics Name.true) (boolTag True) []) boolType sp
    [one] ->
      one
    first : rest ->
      Core.Expr
        ( Core.ECase
            first
            [ Core.Alt (boolPattern True) (conjunction sp rest),
              Core.Alt (boolPattern False) (Core.Expr (Core.ECtor (Core.QualName ModuleName.basics Name.false) (boolTag False) []) boolType sp)
            ]
            Nothing
        )
        boolType
        sp

-- | The first field that is not @EQ@, and @EQ@ when there are none.
firstUnequal :: Core.Span -> [Core.Expr] -> Core.Expr
firstUnequal sp comparisons =
  case comparisons of
    [] ->
      orderCtor sp "EQ"
    [one] ->
      one
    first : rest ->
      let carried = Name.fromChars "$o"
       in Core.Expr
            ( Core.ECase
                first
                [ Core.Alt (orderPattern "EQ") (firstUnequal sp rest),
                  Core.Alt
                    (Core.PVar (Core.Binder carried orderType sp))
                    (Core.Expr (Core.EVar carried) orderType sp)
                ]
                Nothing
            )
            orderType
            sp

orderTag :: String -> Int
orderTag chars =
  case chars of
    "LT" -> 0
    "EQ" -> 1
    _ -> 2

orderCtor :: Core.Span -> String -> Core.Expr
orderCtor sp chars =
  Core.Expr
    (Core.ECtor (Core.QualName ModuleName.basics (Name.fromChars chars)) (orderTag chars) [])
    orderType
    sp

orderPattern :: String -> Core.Pattern
orderPattern chars =
  Core.PCtor (Core.QualName ModuleName.basics (Name.fromChars chars)) (orderTag chars) []

boolType :: Core.Type
boolType =
  Core.TCon (Core.QualName ModuleName.basics Name.bool) []

orderType :: Core.Type
orderType =
  Core.TCon (Core.QualName ModuleName.basics Name.order) []

stringType :: Core.Type
stringType =
  Core.TCon (Core.QualName ModuleName.string Name.string) []

arrayOf :: Core.Type -> Core.Type
arrayOf element =
  Core.TCon (Core.QualName ModuleName.array Name.array) [element]

-- | @{ name : String, value : String }@, the entry `Inspect.record` takes.
entryType :: Core.Type
entryType =
  Core.TRecord [(nameName, stringType), (nameValue, stringType)] Nothing

-- | @Array { name : String, value : String } -> String@
recordFnType :: Core.Type
recordFnType =
  Core.TFun [arrayOf entryType] stringType

nameEq :: Name
nameEq = Name.fromChars "eq"

nameCompare :: Name
nameCompare = Name.fromChars "compare"

nameInspect :: Name
nameInspect = Name.fromChars "inspect"

nameRecord :: Name
nameRecord = Name.fromChars "record"

nameName :: Name
nameName = Name.fromChars "name"

nameValue :: Name
nameValue = Name.fromChars "value"

-- | A use of a constrained name, applied to the witnesses it needs.
applied :: Env -> Can.NodeId -> Core.Span -> Core.Expr -> Core.Expr
applied env nid sp fn =
  case useOf env nid of
    Just (Resolve.Applied args) -> witnessApp sp fn args
    _ -> fn

-- | Apply a constrained name to the witnesses its constraints need.
witnessApp :: Core.Span -> Core.Expr -> [Resolve.Witness] -> Core.Expr
witnessApp sp fn args =
  case args of
    [] -> fn
    _ -> Core.Expr (Core.EWitApp fn (map (witness sp) args)) (Core.typeOf fn) sp

-- | Bind a definition's witness parameters around its body.
witnessLam :: Env -> Core.Span -> Can.NodeId -> Core.Expr -> Core.Expr
witnessLam env sp bodyNid body =
  case paramsOf env bodyNid of
    [] -> body
    params ->
      Core.Expr
        (Core.EWitLam [Core.Binder name (lowerType tipe) sp | (name, tipe) <- params] body)
        (Core.typeOf body)
        sp

span :: Env -> A.Region -> Core.Span
span env (A.Region (A.Position startRow startCol) (A.Position endRow endCol)) =
  Core.Span
    (_file env)
    (fromIntegral startRow)
    (fromIntegral startCol)
    (fromIntegral endRow)
    (fromIntegral endCol)

-- EXPRESSIONS

expr :: Env -> Can.Expr -> Core.Expr
expr env (Can.Expr nid region value) =
  let tipe = typeOf env nid
      sp = span env region
      node v = Core.Expr v tipe sp
   in case value of
        Can.VarLocal name ->
          applied env nid sp (node (Core.EVar name))
        Can.VarTopLevel home name ->
          applied env nid sp (node (Core.EGlobal (Core.QualName home name)))
        Can.VarForeign home name _ ->
          applied env nid sp (node (Core.EGlobal (Core.QualName home name)))
        Can.VarMethod _ _ _ _ ->
          -- The instance was picked before the lowering ran, because picking
          -- it needs the solved type and reporting that there is none needs a
          -- phase that reports (§G23). What is left here is the reference, or
          -- — when the class parameter is a variable the definition is
          -- constrained on — the method taken out of the witness it was
          -- handed (§G26).
          case useOf env nid of
            Just (Resolve.Instantiated home name args) ->
              witnessApp sp (Core.Expr (Core.EGlobal (Core.QualName home name)) tipe sp) args
            Just (Resolve.Projected w name) ->
              node (Core.EAccess (witness sp w) name)
            _ ->
              error $
                "Core.Lower.Expression: class-method node "
                  ++ show nid
                  ++ " was not resolved. See docs/m1b-classes.md §G23."
        Can.VarOperator _ home name _ ->
          applied env nid sp (node (Core.EGlobal (Core.QualName home name)))
        Can.VarPrim op _ ->
          primValue tipe sp op
        Can.VarKernel home name ->
          -- @AST.Optimized.toKernelGlobal@ already gave a kernel function a
          -- module: the `gren/kernel` pseudo-package, one module per kernel
          -- prefix. Core reuses it rather than inventing a second encoding.
          -- Kernel references stop existing when `ffi.md` F7 retires the
          -- splicer at M1b.
          node (Core.EGlobal (Core.QualName (ModuleName.Canonical Pkg.kernel home) name))
        Can.VarDebug _ name _ ->
          -- The module on the node is the one doing the referring, not the one
          -- being referred to.
          --
          -- Witnessed like a foreign reference, because `Debug.log` is one in
          -- every way that matters here: it is `core`'s binding, and since D158
          -- its type carries `Inspect a =>`.
          applied env nid sp (node (Core.EGlobal (Core.QualName ModuleName.debug name)))
        Can.VarCtor _ home name index _ ->
          ctorValue tipe sp (Core.QualName home name) (Index.toMachine index)
        Can.Chr c ->
          node (Core.ELit (Literal.chr c))
        Can.Str s ->
          node (Core.ELit (Literal.str s))
        Can.Int n _ ->
          literal env nid sp tipe Name.int (Literal.int tipe n)
        Can.Float f _ ->
          literal env nid sp tipe Name.float (Literal.float tipe f)
        Can.Array items ->
          node (Core.EArray (map (expr env) items))
        -- A negative literal is one literal (`syntax.md` S5,
        -- `docs/m1b-int.md` §I20). Gren parses `-1` as `Negate (Int 1)`, so
        -- without this the Core for every negative number is a call, and
        -- `-9223372036854775808` is a call that arrives at the right answer by
        -- wrapping twice — the literal is one past the signed width's top,
        -- `fromIntegral` wraps it to the bottom, and `negate` wraps it back
        -- (§I16.4). The range check has already folded the sign to decide the
        -- literal is legal; this folds it to decide what it *is*, and the two
        -- agree because they fold the same way.
        --
        -- Integers only. A float carries its digits as text, so folding one
        -- means negating the `Double` after reading it rather than choosing a
        -- constructor, and `negate` at a float is exact anyway.
        Can.Negate (Can.Expr _ _ (Can.Int value _)) ->
          literal env nid sp tipe Name.int (Literal.int tipe (negate value))
        Can.Negate inner ->
          -- `-x` is `Basics.negate` at `x`'s type, and since D144 that is a
          -- method rather than a binding, so this resolves the way an operator
          -- does (§I11). What used to be here — a global named outright —
          -- worked only while `Num` had no methods.
          let negType = negateType tipe
              call1 fn = node (Core.EApp fn [expr env inner])
           in case useOf env nid of
                Just (Resolve.Instantiated home instanceName args) ->
                  call1 (witnessApp sp (Core.Expr (Core.EGlobal (Core.QualName home instanceName)) negType sp) args)
                Just (Resolve.Projected w methodName) ->
                  call1 (Core.Expr (Core.EAccess (witness sp w) methodName) negType sp)
                _ ->
                  error $
                    "Core.Lower.Expression: negation at node "
                      ++ show nid
                      ++ " was not resolved to an instance of Basics.Num."
        Can.Binop _ target _ left right ->
          let opType = binopType env left right tipe
              global home name = Core.Expr (Core.EGlobal (Core.QualName home name)) opType sp
              call2 fn = node (Core.EApp fn [expr env left, expr env right])
           in case target of
                Can.OpValue home name ->
                  call2 (applied env nid sp (global home name))
                Can.OpMethod _ _ name ->
                  -- The three answers 'Can.VarMethod' has, at an operator
                  -- (D138, §G35). The node id the instance was recorded
                  -- against is the binop's own, which is why 'Type.Resolve'
                  -- asks 'methodUse' about it.
                  case useOf env nid of
                    Just (Resolve.Instantiated home instanceName args) ->
                      call2 (witnessApp sp (global home instanceName) args)
                    Just (Resolve.Projected w methodName) ->
                      call2 (Core.Expr (Core.EAccess (witness sp w) methodName) opType sp)
                    _ ->
                      error $
                        "Core.Lower.Expression: operator node "
                          ++ show nid
                          ++ " names the method "
                          ++ show name
                          ++ " and was not resolved. See docs/m1b-classes.md §G23."
        Can.Lambda args body ->
          node (lambda env tipe sp args (expr env body))
        Can.Call func args ->
          node (call env func args)
        Can.If branches final ->
          node (ifChain env tipe sp branches final)
        Can.Let _ _ ->
          letRun env tipe sp value
        Can.LetRec _ _ ->
          letRun env tipe sp value
        Can.LetDestruct _ _ _ ->
          letRun env tipe sp value
        Can.Case scrutinee branches ->
          let scrutineeType = typeOfExpr env scrutinee
              branch (Can.CaseBranch p body) =
                Core.Alt (pattern env scrutineeType p) (expr env body)
           in -- No fallback: `Nitpick.PatternMatches` rejects a `when` that
              -- does not cover its scrutinee, so every alternative set that
              -- reaches here is exhaustive. C4's fallback is for the pass that
              -- builds decision trees, which is M1b.
              node (Core.ECase (expr env scrutinee) (map branch branches) Nothing)
        Can.Accessor field ->
          node (accessor tipe sp field)
        Can.Access record (A.At _ field) ->
          node (Core.EAccess (expr env record) field)
        Can.Update record fields ->
          node $
            Core.EUpdate
              (expr env record)
              [(name, expr env value') | (A.At _ name, Can.FieldUpdate _ value') <- Map.toAscList fields]
        Can.Record fields ->
          node
            (Core.ERecord [(name, expr env value') | (A.At _ name, value') <- Map.toAscList fields])

-- | A numeric literal: the value, or @fromInt@ / @fromFloat@ applied to it
-- (D170, @docs/m1b-classes.md@ §G49).
--
-- 'Type.Resolve.literal' records a use only where the literal's type is a
-- variable, and then the literal is lowered at the argument's type — @Int@ or
-- @Float@, which is exactly the value 'Literal.int' and 'Literal.float' give a
-- variable — and handed to the method. Specialization folds the call back into
-- a literal wherever it learns the instance (@Core.Pass.Specialize@).
--
-- __The method is checked by name, and it has to be.__ A negative literal's
-- node is a @Negate@, and at a known type 'Type.Resolve.negation' has already
-- recorded @negate@'s instance against it, which the fold above ignores. Taking
-- any use found there as the conversion turned every @-1@ at an @Int@ into
-- @negate -1@; the front end's own path handling was what showed it. A variable's
-- witness is always a parameter, so a conversion is always a projection.
literal :: Env -> Can.NodeId -> Core.Span -> Core.Type -> Name -> Core.Literal -> Core.Expr
literal env nid sp tipe argName value =
  let argType = Core.TCon (Core.QualName ModuleName.basics argName) []
      methodType = Core.TFun [argType] tipe
   in case useOf env nid of
        Just (Resolve.Projected w methodName)
          | methodName == Name.fromInt || methodName == Name.fromFloat ->
              Core.Expr
                ( Core.EApp
                    (Core.Expr (Core.EAccess (witness sp w) methodName) methodType sp)
                    [Core.Expr (Core.ELit value) argType sp]
                )
                tipe
                sp
        _ ->
          Core.Expr (Core.ELit value) tipe sp

typeOfExpr :: Env -> Can.Expr -> Core.Type
typeOfExpr env (Can.Expr nid _ _) = typeOf env nid

-- APPLICATION

-- | A call, with the one shape that is not an 'Core.AST.EApp'.
call :: Env -> Can.Expr -> [Can.Expr] -> Core.Expr_
call env func args =
  case func of
    Can.Expr nid _ (Can.VarCtor _ home name index _)
      | arity (typeOf env nid) == length args ->
          Core.ECtor (Core.QualName home name) (Index.toMachine index) (map (expr env) args)
    _ ->
      Core.EApp (expr env func) (map (expr env) args)

-- | A primitive, which is only ever the whole body of a @\@prim@ declaration
-- (`core.md` C13) and so is only ever a value.
--
-- Eta-expanded, for the reason 'ctorValue' is: 'Core.AST.EPrim' is saturated
-- everywhere it appears. The wrapper costs nothing that survives — the
-- declaration it is the body of is @core@'s own one-line wrapper around the
-- primitive, and inlining that is what the backend's specialization does with
-- every other one.
--
-- The types come from the /node/ rather than from the primitive table, because
-- they are the same types: this node was inferred against the table's
-- annotation, so what the solver came back with is the table's type at this
-- declaration.
primValue :: Core.Type -> Core.Span -> Prim.PrimOp -> Core.Expr
primValue tipe sp op =
  case tipe of
    Core.TFun argTypes result ->
      let binders = zipWith (\i t -> Core.Binder (generated i) t sp) [0 ..] argTypes
          built = Core.Expr (Core.EPrim op (map (variable sp) binders)) result sp
       in Core.Expr (Core.ELam binders built) tipe sp
    _ ->
      -- Unreachable: every primitive takes at least one argument
      -- ('Core.Prim.primArity'), so its type is a function type.
      error ("Core.Lower.Expression: the " ++ show op ++ " primitive is not a function: " ++ show tipe)

-- | A constructor used as a value rather than applied.
--
-- Nullary is already a value; anything else is eta-expanded, which is what
-- keeps 'Core.AST.ECtor' saturated everywhere it appears.
ctorValue :: Core.Type -> Core.Span -> Core.QualName -> Int -> Core.Expr
ctorValue tipe sp name tag =
  case tipe of
    Core.TFun argTypes result ->
      let binders = zipWith (\i t -> Core.Binder (generated i) t sp) [0 ..] argTypes
          built = Core.Expr (Core.ECtor name tag (map (variable sp) binders)) result sp
       in Core.Expr (Core.ELam binders built) tipe sp
    _ ->
      Core.Expr (Core.ECtor name tag []) tipe sp

-- | @.field@, which Core has no node for: it is the function it stands for.
accessor :: Core.Type -> Core.Span -> Name -> Core.Expr_
accessor tipe sp field =
  case tipe of
    Core.TFun [recordType] result ->
      let binder = Core.Binder recordArg recordType sp
       in Core.ELam
            [binder]
            (Core.Expr (Core.EAccess (variable sp binder) field) result sp)
    _ ->
      error ("Core.Lower.Expression: an accessor is not a one-argument function: " ++ show tipe)

-- LET RUNS

-- | A run of @let@ bindings, lowered and put in C14's order.
--
-- Canonical hands the bindings over one at a time — @Can.Let@ for a plain one,
-- @Can.LetRec@ for a mutually recursive group, @Can.LetDestruct@ for a
-- destructuring — nested one inside the next, and the nesting is the order
-- @Data.Graph.stronglyConnComp@ happened to produce. C14 replaces it: the run's
-- items are grouped by mutual recursion and the groups come out in dependency
-- order, least-named ready group first, exactly as a module's definitions and a
-- linked program's bindings do.
--
-- __A destructuring is an item like any other__, rather than a wall the
-- reordering stops at. It has to be: where Canonical put it in the chain is the
-- same unspecified choice, so leaving it in place would leave the order half
-- specified. It is named by the least name its pattern binds; one that binds
-- nothing — @_ = Debug.log "here" x@ — has only its source position to be known
-- by, and sorts before named items that are equally ready, which is where a
-- reader writes it.
--
-- Every frame in a run carries the same type and the same span: @detectCycles@
-- builds all of them with @Can.at letRegion@, so the whole run is one region and
-- nothing moves when the items do.
letRun :: Env -> Core.Type -> Core.Span -> Can.Expr_ -> Core.Expr
letRun env tipe sp value =
  let (items, body) = collect value
   in List.foldr (frame tipe sp) body (arrange items)
  where
    collect v =
      case v of
        Can.Let d rest -> prepend (bindsItem [def env d]) (continue rest)
        Can.LetRec ds rest -> prepend (bindsItem (map (def env) ds)) (continue rest)
        Can.LetDestruct p scrutinee rest ->
          -- A destructuring `let` binds no single name, so it is an `ECase` with
          -- one alternative. It is irrefutable: the frontend rejects a
          -- destructuring that does not cover its type, which is why there is no
          -- fallback.
          prepend
            (destructItem env (pattern env (typeOfExpr env scrutinee) p) (A.toRegion p) (expr env scrutinee))
            (continue rest)
        _ -> ([], error "Core.Lower.Expression.letRun: not a let")

    continue e@(Can.Expr _ _ v) =
      case v of
        Can.Let _ _ -> collect v
        Can.LetRec _ _ -> collect v
        Can.LetDestruct _ _ _ -> collect v
        _ -> ([], expr env e)

    prepend item (items, body) = (item : items, body)

-- | One step of a @let@ run: a group of bindings, or a destructuring.
data Item = Item
  { -- | What orders it: the least name it binds, and where it is written. The
    -- position only decides between two items that bind no names at all, since
    -- shadowing is forbidden (D63) and a run's names are therefore distinct.
    _itemKey :: !(Maybe Name, (Word32, Word32)),
    _itemNames :: !(Set.Set Name),
    _itemUses :: !(Set.Set Name),
    _itemWhat :: !What
  }

data What
  = Binds ![Core.Bind]
  | Destructure !Core.Pattern !Core.Expr

bindsItem :: [Core.Bind] -> Item
bindsItem binds =
  Item
    { _itemKey = minimum [(Just (bindName b), position (Core._binderSpan (Core._bindBinder b))) | b <- binds],
      _itemNames = Set.fromList (map bindName binds),
      _itemUses = Set.unions (map (Refs.freeLocals . Core._bindValue) binds),
      _itemWhat = Binds binds
    }

destructItem :: Env -> Core.Pattern -> A.Region -> Core.Expr -> Item
destructItem env p region scrutinee =
  let names = Refs.patternBinders p
   in Item
        { _itemKey = (fst <$> Set.minView names, position (span env region)),
          _itemNames = names,
          _itemUses = Refs.freeLocals scrutinee,
          _itemWhat = Destructure p scrutinee
        }

position :: Core.Span -> (Word32, Word32)
position s = (Core._spanStartRow s, Core._spanStartCol s)

-- | The run's items, grouped and ordered by C14.
--
-- A group of more than one item is a mutual recursion Canonical did not see —
-- its edges for a @let@ are each binding's free variables, which is this same
-- relation, so the two only disagree if one of them is wrong. Bindings that end
-- up together become one recursive frame; a destructuring cannot be part of a
-- recursive group at all (@checkCycle@ rejects it before this pass runs), so if
-- one ever arrives in a group the items are emitted separately, in the group's
-- own order, rather than merged into a frame that could not hold them.
arrange :: [Item] -> [[Item]]
arrange items =
  let byKey = Map.fromList [(_itemKey item, item) | item <- items]
      owner = Map.fromList [(n, _itemKey item) | item <- items, n <- Set.toList (_itemNames item)]
      deps =
        Map.fromList
          [ ( _itemKey item,
              Set.fromList (Maybe.mapMaybe (`Map.lookup` owner) (Set.toList (_itemUses item)))
            )
          | item <- items
          ]
   in [ [byKey Map.! k | k <- group]
      | group <- Order.groups (map _itemKey items) deps
      ]

-- | One group of items as one frame — or as several, when they cannot be one.
frame :: Core.Type -> Core.Span -> [Item] -> Core.Expr -> Core.Expr
frame tipe sp group inner =
  case group of
    [Item _ _ _ (Destructure p scrutinee)] ->
      Core.Expr (Core.ECase scrutinee [Core.Alt p inner] Nothing) tipe sp
    _
      | Just binds <- allBinds group ->
          let recursive =
                length binds > 1
                  || or [Set.member (bindName b) (Refs.freeLocals (Core._bindValue b)) | b <- binds]
              node = if recursive then Core.ELetRec else Core.ELet
           in Core.Expr (node (List.sortOn bindName binds) inner) tipe sp
      | otherwise ->
          List.foldr (\item acc -> frame tipe sp [item] acc) inner group

allBinds :: [Item] -> Maybe [Core.Bind]
allBinds group =
  concat
    <$> traverse
      ( \item ->
          case _itemWhat item of
            Binds binds -> Just binds
            Destructure _ _ -> Nothing
      )
      group

bindName :: Core.Bind -> Name
bindName = Core._binderName . Core._bindBinder

-- LAMBDAS AND DEFINITIONS

-- | @\\p1 p2 -> body@, where each @p@ may be a pattern rather than a name.
lambda :: Env -> Core.Type -> Core.Span -> [Can.Pattern] -> Core.Expr -> Core.Expr_
lambda env tipe sp args body =
  let (argTypes, _) = arguments (length args) tipe
      (binders, wrap) = binderList env sp argTypes args
   in Core.ELam binders (wrap body)

def :: Env -> Can.Def -> Core.Bind
def env d =
  case d of
    Can.Def nid (A.At region name) args body ->
      -- An unannotated definition's context is the elaborator's answer rather
      -- than the author's (§G33), and everything after that is the same: the
      -- context it has is the context it binds. It has none unless something
      -- was attributed to it, which is what keeps every unconstrained
      -- definition's Core exactly what it was.
      quantified env (span env region) name (Map.findWithDefault Map.empty nid (_inferred env)) (canTypeOf env nid) args body
    Can.TypedDef (A.At region name) freeVars args body result ->
      quantified env (span env region) name freeVars (foldr (Can.TLambda . snd) result args) (map fst args) body

-- | Bind a definition under the context it carries.
--
-- __A definition is quantified in Core exactly when it is constrained__
-- (§G26). The witness parameters are real binders and the 'Core.TForall' that
-- names them is a real type; an unconstrained definition keeps L2's
-- unquantified type, because a `TForall` with nothing to bind it is decoration
-- and type abstraction is specialization's half of verb 6.
quantified :: Env -> Core.Span -> Name -> Can.FreeVars -> Can.Type -> [Can.Pattern] -> Can.Expr -> Core.Bind
quantified env sp name freeVars declared args body =
  let value = bindValue env sp (lowerType declared) args (expr env body)
   in case Can.contextOrder freeVars of
        [] ->
          Core.Bind (Core.Binder name (lowerType declared) sp) value
        _ ->
          -- Every constraint binds a witness since D144, closed ones included:
          -- the middle case that bound none — a definition constrained only by
          -- `Num`, which had no methods to project — went with the list that
          -- named it (@docs\/m1b-int.md@ §I11).
          Core.Bind
            (Core.Binder name (lowerAnnotation (Can.Forall freeVars declared)) sp)
            (witnessLam env sp (nodeIdOf body) value)

bindValue :: Env -> Core.Span -> Core.Type -> [Can.Pattern] -> Core.Expr -> Core.Expr
bindValue env sp tipe args body =
  case args of
    [] -> body
    _ ->
      let (argTypes, result) = arguments (length args) tipe
          (binders, wrap) = binderList env sp argTypes args
       in Core.Expr (Core.ELam binders (wrap body)) (Core.TFun argTypes result) sp

nodeIdOf :: Can.Expr -> Can.NodeId
nodeIdOf (Can.Expr nid _ _) = nid

-- | Turn argument patterns into binders, plus the wrapping the ones that are
-- not simply names need.
--
-- The binders are built first and the destructuring is nested inside-out, so
-- that @\\{ x } { y } -> body@ destructures the first argument outermost — the
-- order it is written in.
binderList :: Env -> Core.Span -> [Core.Type] -> [Can.Pattern] -> ([Core.Binder], Core.Expr -> Core.Expr)
binderList env sp argTypes args =
  let one index tipe arg@(A.At region p) =
        case p of
          Can.PVar name ->
            (Core.Binder name tipe (span env region), id)
          Can.PAnything ->
            (Core.Binder (generated index) tipe (span env region), id)
          _ ->
            let binder = Core.Binder (generated index) tipe (span env region)
                wrap body =
                  Core.Expr
                    (Core.ECase (variable sp binder) [Core.Alt (pattern env tipe arg) body] Nothing)
                    (Core.typeOf body)
                    sp
             in (binder, wrap)
      parts = zipWith3 one [0 ..] argTypes args
   in (map fst parts, foldr ((.) . snd) id parts)

-- CONDITIONALS

-- | Core has no conditional: an @if@ is a @when@ on a `Bool`.
--
-- @else if@ chains are one Canonical node with several branches, and they nest
-- here. The nested nodes take the whole @if@'s type and span, which are the
-- only ones they could have: the source has no separate expression for them.
ifChain :: Env -> Core.Type -> Core.Span -> [(Can.Expr, Can.Expr)] -> Can.Expr -> Core.Expr_
ifChain env tipe sp branches final =
  case branches of
    [] ->
      -- The parser will not build one; `Can.If` is the shape of `if`/`else`.
      error "Core.Lower.Expression: an `if` with no branches"
    (condition, body) : rest ->
      Core.ECase
        (expr env condition)
        [ Core.Alt (boolPattern True) (expr env body),
          Core.Alt (boolPattern False) $
            case rest of
              [] -> expr env final
              _ -> Core.Expr (ifChain env tipe sp rest final) tipe sp
        ]
        Nothing

-- PATTERNS

-- | Lower a pattern, given the type of the value it destructures.
--
-- Types come down rather than up (@docs/m1a-node-types.md@ §N9): a pattern has
-- no node id and no recorded type, but every place one appears knows the type
-- of the thing being taken apart, and every step inwards is mechanical. The
-- type is already Core's, so aliases are gone and record fields are in order
-- before this is ever asked to look inside one.
pattern :: Env -> Core.Type -> Can.Pattern -> Core.Pattern
pattern env tipe (A.At region p) =
  let sp = span env region
      binder name = Core.Binder name tipe sp
   in case p of
        Can.PAnything ->
          Core.PWild
        Can.PVar name ->
          Core.PVar (binder name)
        Can.PAlias inner name ->
          Core.PAs (binder name) (pattern env tipe inner)
        Can.PRecord fields ->
          -- Alphabetical, like every other field list in Core (C2). Canonical
          -- keeps them in source order.
          Core.PRecord $
            List.sortOn
              fst
              [ (name, pattern env (fieldType tipe name) sub)
              | A.At _ (Can.PRFieldPattern name sub) <- fields
              ]
        Can.PArray entries ->
          -- No tail binder: Canonical has no array pattern that binds one.
          -- Core's is for the @[ a, b, ..rest ]@ form the surface language
          -- does not have yet.
          Core.PArray (map (pattern env (elementType tipe)) entries) Nothing
        Can.PBool union b ->
          checkedBoolPattern union b
        Can.PChr c ->
          Core.PLit (Literal.chr c)
        Can.PStr s ->
          Core.PLit (Literal.str s)
        Can.PInt n _ ->
          Core.PLit (Literal.int tipe n)
        Can.PCtor home _ union name index args ->
          -- The type Canonical caches on a constructor argument is the one the
          -- constructor was *declared* with, so `Just`'s argument is `a` and
          -- not the `Int` this pattern is matching. The pattern's own type
          -- carries the arguments the datatype was applied to, so instantiating
          -- is a substitution of the union's parameters.
          let instantiate = substitution (Can._u_vars union) tipe
           in Core.PCtor
                (Core.QualName home name)
                (Index.toMachine index)
                [ pattern env (instantiate (lowerType argType)) arg
                | Can.PatternCtorArg _ argType arg <- args
                ]

-- | Instantiate a datatype's parameters from the type a pattern is matching.
substitution :: [Name] -> Core.Type -> (Core.Type -> Core.Type)
substitution params tipe =
  case tipe of
    Core.TCon _ args
      | length args == length params ->
          substitute (Map.fromList (zip params args))
    _ ->
      error ("Core.Lower.Expression: a constructor pattern on " ++ show tipe)

substitute :: Map.Map Name Core.Type -> Core.Type -> Core.Type
substitute bindings tipe =
  case tipe of
    Core.TVar name ->
      Map.findWithDefault tipe name bindings
    Core.TCon name args ->
      Core.TCon name (map (substitute bindings) args)
    Core.TFun args result ->
      Core.TFun (map (substitute bindings) args) (substitute bindings result)
    Core.TRecord fields ext ->
      Core.TRecord [(name, substitute bindings t) | (name, t) <- fields] ext
    Core.TForall vars constraints body ->
      -- Not produced by this pass, but a substitution that ignored shadowing
      -- would be a trap for whoever adds one.
      let inner = foldr Map.delete bindings vars
       in Core.TForall vars constraints (substitute inner body)

fieldType :: Core.Type -> Name -> Core.Type
fieldType tipe name =
  case tipe of
    Core.TRecord fields _
      | Just found <- lookup name fields ->
          found
    _ ->
      error ("Core.Lower.Expression: no field " ++ show name ++ " in " ++ show tipe)

elementType :: Core.Type -> Core.Type
elementType tipe =
  case tipe of
    Core.TCon _ [element] -> element
    _ -> error ("Core.Lower.Expression: an array pattern on " ++ show tipe)

-- BOOLEANS

-- | @Basics@ declares @type Bool = True | False@, in that order.
--
-- An `if` carries no union to read the tags off, so they are written down
-- here — once, and checked against the union every time a `True` or `False`
-- pattern is lowered, so that a reordering in @core@ is a loud failure rather
-- than silently swapped branches.
boolTag :: Bool -> Int
boolTag b = if b then 0 else 1

boolPattern :: Bool -> Core.Pattern
boolPattern b =
  Core.PCtor
    (Core.QualName ModuleName.basics (if b then Name.true else Name.false))
    (boolTag b)
    []

checkedBoolPattern :: Can.Union -> Bool -> Core.Pattern
checkedBoolPattern (Can.Union _ ctors _ _) b =
  let wanted = if b then Name.true else Name.false
      declared = [Index.toMachine index | Can.Ctor name index _ _ <- ctors, name == wanted]
   in if declared == [boolTag b]
        then boolPattern b
        else
          error $
            "Core.Lower.Expression: Basics declares "
              ++ show wanted
              ++ " at "
              ++ show declared
              ++ ", not "
              ++ show (boolTag b)

-- TYPES

-- | Peel @n@ argument types off a function type.
--
-- Core function types are collapsed maximally (C3), so a two-argument lambda
-- whose body is another lambda has a type with three arguments in one list.
-- The ones this binder does not take stay a function, which is what the body's
-- type is.
arguments :: Int -> Core.Type -> ([Core.Type], Core.Type)
arguments n tipe =
  case tipe of
    Core.TFun args result
      | n <= length args ->
          case splitAt n args of
            (taken, []) -> (taken, result)
            (taken, left) -> (taken, Core.TFun left result)
    _ ->
      error ("Core.Lower.Expression: " ++ show n ++ " arguments taken from " ++ show tipe)

arity :: Core.Type -> Int
arity tipe =
  case tipe of
    Core.TFun args _ -> length args
    _ -> 0

-- | The type of `Basics.negate` at this use.
negateType :: Core.Type -> Core.Type
negateType result = Core.TFun [result] result

-- | The type of an operator at this use, which Canonical caches only as the
-- operator's general annotation.
binopType :: Env -> Can.Expr -> Can.Expr -> Core.Type -> Core.Type
binopType env left right result =
  Core.TFun [typeOfExpr env left, typeOfExpr env right] result

-- GENERATED NAMES

-- | A binder the lowering introduces. @$@ cannot appear in a Gren name, so
-- these cannot collide with a source one; the index is the argument's
-- position, so no counter is threaded and the result is the same on every run
-- (C6).
generated :: Int -> Name
generated index = Name.fromChars ('$' : show index)

recordArg :: Name
recordArg = Name.fromChars "$r"

variable :: Core.Span -> Core.Binder -> Core.Expr
variable sp (Core.Binder name tipe _) = Core.Expr (Core.EVar name) tipe sp
