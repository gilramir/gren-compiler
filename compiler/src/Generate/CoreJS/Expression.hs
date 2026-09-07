{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | Core expressions as JavaScript (@docs/m1a-js-on-core.md@ §J15).
--
-- This is @Generate.JavaScript.Expression@ written against 'Core.AST' instead of
-- @AST.Optimized@, and most of it is a translation with nothing to decide: the
-- calling convention, the currying helpers, the constructor representation and
-- the operator table are the JS backend's and are unchanged, because a program
-- has to answer the same.
--
-- __Three places it is not a translation__, and they are why dropping the @Opt@
-- hop was worth doing rather than only tidy:
--
--   * __A join point is a jump__ (C15). @Opt@ has no general labelled block —
--     @Opt.Jump@ existed only inside a decider — so @Generate.FromCore@ compiled
--     a 'Core.AST.EJoin' to a function and an 'Core.AST.EJump' to a call, which
--     costs a closure. Here a join is a labelled loop and a jump is a @break@ or
--     a @continue@; see 'joins'.
--   * __A pattern is compiled here__, from 'Core.AST.ECase', rather than by
--     `Optimize.DecisionTree` before it. Alternatives are tested in source order
--     and no branch body is duplicated, which is the same naive matcher §J8
--     describes and the same reason: decision trees are C4's optional Core→Core
--     pass, and "Core.Pass.Case" is where they live.
--   * __A literal is written, not pasted__ (§J4). C2 keeps Core's text as
--     characters, so "Generate.JavaScript.Literal" writes the JavaScript.
module Generate.CoreJS.Expression
  ( Env (..),
    Ctor (..),
    Shape (..),
    Code (..),
    codeToExpr,
    codeToStmtList,
    generate,
    generateField,
    ctorArity,
    ctorDefinition,
    isBool,
  )
where

import Core.AST qualified as Core
import Data.ByteString.Builder qualified as B
import Data.Index qualified as Index
import Data.IntMap qualified as IntMap
import Data.List qualified as List
import Data.Map (Map, (!))
import Data.Map qualified as Map
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Utf8 qualified as Utf8
import Generate.JavaScript.Builder qualified as JS
import Generate.JavaScript.Literal qualified as Literal
import Generate.JavaScript.Name qualified as JsName
import Generate.Mode qualified as Mode
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Reporting.Annotation qualified as A

-- ENVIRONMENT

-- | What generating one expression needs to know beyond the expression.
data Env = Env
  { _mode :: Mode.Mode,
    -- | Every reachable constructor, by name. A constructor's /shape/ is not on
    -- the `Core.AST.ECtor` node — the node carries a tag, and whether that tag
    -- is a JavaScript integer, a field of a record or nothing at all depends on
    -- the whole datatype (C9: the representation is backend-local).
    _ctors :: Map Core.QualName Ctor,
    -- | The arity of every top-level binding that is a function, so that a
    -- saturated call can go straight to the uncurried @name$@ rather than
    -- through @A2@. `Generate.JavaScript.makeArgLookup` reads the same thing off
    -- the graph.
    _arities :: Map Core.QualName Int,
    -- | The joins in scope, and how to enter each one. See 'joins'.
    _tails :: Map Name Join,
    -- | The module being generated, which is what the source map records as the
    -- origin of every position in it.
    _home :: ModuleName.Canonical,
    -- | How many @case@ scrutinees are already bound to a temporary above this
    -- point, which is what names the next one.
    --
    -- A JavaScript @var@ is function-scoped, so two @case@ expressions in one
    -- function must not name their scrutinee the same way unless one is finished
    -- with it before the other starts. Nesting is the only way they overlap —
    -- siblings in a chain each assign before they read — so the nesting depth is
    -- a sufficient and deterministic name. The old pipeline gets the same thing
    -- from @Optimize.Names@' @_v0@ counter.
    _depth :: Int
  }

-- | What a constructor compiles to, which the datatype decides and not the
-- constructor: one constructor with one field is unboxed, all-nullary
-- constructors are an enum, anything else is a tagged record.
data Ctor = Ctor
  { _ctorShape :: !Shape,
    _ctorTag :: !Int,
    -- | How many arguments this constructor takes.
    _ctorFields :: !Int,
    -- | How many constructors the datatype has. A one-constructor type is
    -- irrefutable and gets no test at all, which is what keeps a record-shaped
    -- @type@ from being compared against itself.
    _ctorAlts :: !Int,
    _ctorHome :: !ModuleName.Canonical,
    _ctorShort :: !Name
  }

data Shape = Normal | Enum | Unbox
  deriving (Eq)

-- | Where an 'Core.AST.EJump' goes.
--
-- @_joinLabel@ is the JavaScript label; @_joinParams@ are the variables a jump
-- assigns before transferring. 'JumpBreak' leaves the block the join's body
-- follows, 'JumpContinue' goes back to the top of the join's own body.
data Join = Join
  { _joinLabel :: !JsName.Name,
    _joinParams :: ![Name],
    _joinKind :: !JumpKind
  }

data JumpKind = JumpBreak | JumpContinue

-- CODE CHUNKS

-- | An expression, or the statements that produce one. The same distinction
-- `Generate.JavaScript.Expression` makes, and for the same reason: a @let@ and a
-- @case@ are statements in JavaScript, and wrapping every one of them in an
-- immediately-invoked function would be both slower and unreadable.
data Code
  = JsExpr JS.Expr
  | JsBlock [JS.Stmt]

codeToExpr :: Code -> JS.Expr
codeToExpr code =
  case code of
    JsExpr expr -> expr
    JsBlock [JS.Return expr] -> expr
    JsBlock stmts -> JS.Call (JS.Function Nothing [] stmts) []

codeToStmtList :: Code -> [JS.Stmt]
codeToStmtList code =
  case code of
    JsExpr (JS.Call (JS.Function Nothing [] stmts) []) -> stmts
    JsExpr expr -> [JS.Return expr]
    JsBlock stmts -> stmts

-- EXPRESSIONS

jsExpr :: Env -> Core.Expr -> JS.Expr
jsExpr env = codeToExpr . generate env

generate :: Env -> Core.Expr -> Code
generate env (Core.Expr value _ sp) =
  let pos = start sp
   in case value of
        Core.EVar name ->
          JsExpr (JS.TrackedRef (_home env) pos (JsName.fromLocalHumanReadable name) (JsName.fromLocal name))
        Core.EGlobal q ->
          JsExpr (globalRef env pos q)
        Core.ELit lit ->
          JsExpr (literal env pos lit)
        Core.ELam binders body ->
          function env pos (map Core._binderName binders) (generate env body)
        Core.EApp fn args ->
          JsExpr (call env pos fn args)
        Core.ELet binds body ->
          JsBlock (map (localBind env) binds ++ codeToStmtList (generate env body))
        Core.ELetRec binds body ->
          -- A `var` is hoisted and a function body does not run until it is
          -- called, so a recursive group needs no more than the same statements:
          -- Canonical rejects value cycles, which is the argument §J8 makes for
          -- the same shortcut at the top level.
          JsBlock (map (localBind env) binds ++ codeToStmtList (generate env body))
        Core.EJoin binds body ->
          JsBlock (joins env binds body)
        Core.EJump join args ->
          JsBlock (jump env join args)
        Core.ECase scrutinee alts fallback ->
          JsBlock (caseOf env scrutinee alts fallback)
        Core.ECtor name tag args ->
          JsExpr (ctor env pos name tag args)
        Core.ERecord fields ->
          JsExpr (record env sp fields)
        Core.EUpdate base fields ->
          JsExpr $
            JS.Call
              (JS.Ref (JsName.fromKernel Name.utils "update"))
              [jsExpr env base, record env sp fields]
        Core.EAccess base name ->
          JsExpr (JS.TrackedAccess (jsExpr env base) (_home env) pos (generateField (_mode env) name))
        Core.EArray items ->
          JsExpr (JS.TrackedArray (_home env) (region sp) (map (jsExpr env) items))
        Core.EPrim _ _ ->
          error "Generate.CoreJS: EPrim — `core` has no @prim declarations yet (docs/m1a-lowering.md §L4)"
        Core.ECrash _ ->
          error "Generate.CoreJS: ECrash — the lowering does not produce one yet (docs/m1a-lowering.md §L4)"
        Core.ETyLam _ _ ->
          error "Generate.CoreJS: ETyLam — specialization is M1b (docs/m1a-lowering.md §L2)"
        Core.ETyApp _ _ ->
          error "Generate.CoreJS: ETyApp — specialization is M1b (docs/m1a-lowering.md §L2)"
        Core.EWitLam _ _ ->
          error "Generate.CoreJS: EWitLam — classes are M1b"
        Core.EWitApp _ _ ->
          error "Generate.CoreJS: EWitApp — classes are M1b"

-- | A reference to a top-level name.
--
-- A kernel function is spelled the way `Gren.Kernel` splices it; a @Debug@ value
-- goes to the @Debug@ module the frontend routes it through. Neither is ever a
-- constructor: a constructor reaches the generator as `Core.AST.ECtor`, and a
-- bare one is an @ELam@ around a saturated application of it.
globalRef :: Env -> A.Position -> Core.QualName -> JS.Expr
globalRef env pos (Core.QualName home@(ModuleName.Canonical pkg raw) name)
  | pkg == Pkg.kernel = JS.Ref (JsName.fromKernel raw name)
  | otherwise =
      JS.TrackedRef (_home env) pos (JsName.fromGlobalHumanReadable home name) (JsName.fromGlobal home name)

localBind :: Env -> Core.Bind -> JS.Stmt
localBind env (Core.Bind binder body) =
  let name = Core._binderName binder
   in JS.TrackedVar
        (_home env)
        (start (Core._binderSpan binder))
        (JsName.fromLocalHumanReadable name)
        (JsName.fromLocal name)
        (jsExpr env body)

-- LITERALS

literal :: Env -> A.Position -> Core.Literal -> JS.Expr
literal env pos lit =
  case lit of
    Core.LIntLegacy n -> JS.TrackedInt (_home env) pos (fromInteger n)
    Core.LInt n -> JS.TrackedInt (_home env) pos (fromIntegral n)
    Core.LInt64 n -> JS.TrackedInt (_home env) pos (fromIntegral n)
    Core.LUInt32 n -> JS.TrackedInt (_home env) pos (fromIntegral n)
    Core.LUInt64 n -> JS.TrackedInt (_home env) pos (fromIntegral n)
    Core.LFloat d -> JS.TrackedFloat (_home env) pos (Utf8.toBuilder (Literal.float d))
    Core.LFloat32 f -> JS.TrackedFloat (_home env) pos (Utf8.toBuilder (Literal.float (realToFrac f)))
    Core.LString text -> JS.TrackedString (_home env) pos (text_ (Utf8.toChars text))
    -- A `Char` is a one-character string, wrapped in dev mode by the kernel
    -- `_Utils_chr` so that `Debug.toString` can tell one from a string.
    Core.LChar code ->
      let one = JS.TrackedString (_home env) pos (text_ [toEnum (fromIntegral code)])
       in case _mode env of
            Mode.Dev -> JS.Call (JS.Ref (JsName.fromKernel Name.utils "chr")) [one]
            Mode.Prod _ -> one

text_ :: [Char] -> B.Builder
text_ = Utf8.toBuilder . Literal.string

-- RECORDS

record :: Env -> Core.Span -> [(Core.Field, Core.Expr)] -> JS.Expr
record env sp fields =
  JS.TrackedObject
    (_home env)
    (region sp)
    [ (A.At (region sp) (generateField (_mode env) name), jsExpr env value)
    | (name, value) <- fields
    ]

generateField :: Mode.Mode -> Name -> JsName.Name
generateField mode name =
  case mode of
    Mode.Dev -> JsName.fromLocal name
    Mode.Prod fields -> fields ! name

-- CONSTRUCTORS

-- | A saturated constructor application, which is the only shape Core has:
-- `Core.Lower.Expression` eta-expands a constructor used as a value, so a bare
-- one is an @ELam@ around one of these.
--
-- __A constructor with arguments is built inline__ rather than called, which the
-- old pipeline could not do: it reached a constructor through @Opt.VarGlobal@
-- and so had to call the function it emitted. Saturation is on the Core node, so the
-- record can be written where it is used.
--
-- __A nullary one is a reference__ to the @var@ 'ctorDefinition' emits, so that
-- @Nothing@ is one object in dev mode rather than one per mention.
-- The tag is not read: 'lookupCtor' already has it, from the env's ctor table,
-- and taking the caller's would be a second source for one fact.
ctor :: Env -> A.Position -> Core.QualName -> Int -> [Core.Expr] -> JS.Expr
ctor env pos name@(Core.QualName _ short) _tag args
  | isBool name = JS.TrackedBool (_home env) pos (short == Name.true)
  | otherwise =
      let c = lookupCtor env name
          built = map (jsExpr env) args
       in case (_ctorShape c, built) of
            (Enum, _) -> ctorRef c
            (_, []) -> ctorRef c
            (Unbox, [one]) | Mode.Prod _ <- _mode env -> one
            _ -> object env c built

ctorRef :: Ctor -> JS.Expr
ctorRef c = JS.Ref (JsName.fromGlobal (_ctorHome c) (_ctorShort c))

-- | The tagged record a constructor builds: the tag under @$@, then one field
-- per argument named @a@, @b@, … in order.
object :: Env -> Ctor -> [JS.Expr] -> JS.Expr
object env c built =
  JS.Object $
    (JsName.dollar, tagValue env c)
      : Index.indexedMap (\i value -> (JsName.fromIndex i, value)) built

tagValue :: Env -> Ctor -> JS.Expr
tagValue env c =
  case _mode env of
    Mode.Dev -> JS.String (Name.toBuilder (_ctorShort c))
    Mode.Prod _ -> JS.Int (tagToInt c)

-- | A nullary constructor of an all-nullary datatype: the tag itself under
-- @--optimize@, and the one-field record in dev so that `Debug.toString` can
-- still print a name.
enumValue :: Env -> Ctor -> JS.Expr
enumValue env c =
  case _mode env of
    Mode.Dev -> JS.Object [(JsName.dollar, JS.String (Name.toBuilder (_ctorShort c)))]
    Mode.Prod _ -> JS.Int (tagToInt c)

-- | `Dict`'s two constructors are numbered from the other end, which is
-- `Generate.JavaScript.Expression.ctorToInt`'s rule and has to stay: the kernel
-- JavaScript compares against those integers.
tagToInt :: Ctor -> Int
tagToInt c =
  if _ctorHome c == ModuleName.dict && _ctorShort c == "RBNode_gren_builtin" || _ctorShort c == "RBEmpty_gren_builtin"
    then negate (_ctorTag c + 1)
    else _ctorTag c

-- | The @var@ a constructor needs.
--
-- Core itself needs none: every 'Core.AST.ECtor' is saturated and is built where
-- it stands. __Kernel JavaScript__ is what needs them, and it is not a corner
-- case — @_Utils_compare@ returns @__Basics_LT@, @__Basics_EQ@ or @__Basics_GT@,
-- so the three constructors of @Order@ are read by the function every @compare@
-- in every program goes through. @Maybe.Just@ and @Result.Ok@ are two more of
-- §J7's eighteen. So one is emitted for every constructor, as the old pipeline
-- does, and 'ctor' uses it for the nullary case where sharing is worth more than
-- inlining.
--
-- @True@ and @False@ are the exception: both paths compile them to JavaScript
-- literals, and no kernel file names either.
--
-- __The unboxed case differs from the old pipeline on purpose.__ @Opt.Box@ under
-- @--optimize@ is a reference to @Basics.identity@, which makes a constructor
-- depend on a /binding/ and so gives it a place in the link order. Writing the
-- function out instead costs a few bytes once and means a constructor depends on
-- nothing at all, which is what lets 'Generate.CoreJS' emit them ahead of
-- everything else without a fourth kind of thing in the order.
ctorDefinition :: Env -> Core.QualName -> Maybe JS.Stmt
ctorDefinition env name
  | isBool name = Nothing
  | otherwise =
      let c = lookupCtor env name
          arity = _ctorFields c
          argNames = Index.indexedMap (\i _ -> JsName.fromIndex i) [1 .. arity]
          global = JsName.fromGlobal (_ctorHome c) (_ctorShort c)
          direct = JsName.fromGlobalDirectFn (_ctorHome c) (_ctorShort c)
          body = JS.Object ((JsName.dollar, tagValue env c) : map (\n -> (n, JS.Ref n)) argNames)
       in case (_ctorShape c, arity) of
            (Enum, _) -> Just (JS.Var global (enumValue env c))
            (_, 0) -> Just (JS.Var global body)
            (Unbox, _) ->
              -- `function ($) { return $; }` in `--optimize`, and the tagged
              -- record in dev, where the tag is what `Debug.toString` prints.
              Just $
                JS.Var global $
                  case _mode env of
                    Mode.Prod _ -> JS.Function Nothing [JsName.dollar] [JS.Return (JS.Ref JsName.dollar)]
                    Mode.Dev -> JS.Function Nothing argNames [JS.Return body]
            (Normal, 1) ->
              Just (JS.Var global (JS.Function Nothing argNames [JS.Return body]))
            (Normal, _) ->
              Just $
                JS.Block
                  [ JS.Var direct (JS.Function Nothing argNames [JS.Return body]),
                    JS.Var global (codeToExpr (curriedRef argNames direct))
                  ]

-- | How many arguments a constructor takes, so that a saturated application of
-- one can be called directly.
ctorArity :: Env -> Core.QualName -> Maybe Int
ctorArity env name =
  case Map.lookup name (_ctors env) of
    Just c | _ctorShape c == Normal -> Just (_ctorFields c)
    _ -> Nothing

lookupCtor :: Env -> Core.QualName -> Ctor
lookupCtor env name@(Core.QualName _ short) =
  case Map.lookup name (_ctors env) of
    Just c -> c
    Nothing -> error ("Generate.CoreJS: no datatype declares " ++ Name.toChars short)

isBool :: Core.QualName -> Bool
isBool (Core.QualName home short) =
  home == ModuleName.basics && (short == Name.true || short == Name.false)

-- FUNCTIONS

-- | A curried function: the uncurried body wrapped in @F2@ … @F9@.
function :: Env -> A.Position -> [Name] -> Code -> Code
function env pos params body =
  let args = [A.At (A.Region pos pos) (JsName.fromLocal p) | p <- params]
   in case IntMap.lookup (length params) funcHelpers of
        Just helper ->
          JsExpr (JS.Call helper [JS.TrackedFunction (_home env) pos args (codeToStmtList body)])
        Nothing ->
          case args of
            [_] -> JsExpr (JS.TrackedFunction (_home env) pos args (codeToStmtList body))
            _ -> foldr addArg body (map A.toValue args)
  where
    addArg arg code = JsExpr (JS.Function Nothing [arg] (codeToStmtList code))

curriedRef :: [JsName.Name] -> JsName.Name -> Code
curriedRef args ref =
  case IntMap.lookup (length args) funcHelpers of
    Just helper -> JsExpr (JS.Call helper [JS.Ref ref])
    Nothing ->
      let addArg arg code = JsExpr (JS.Function Nothing [arg] (codeToStmtList code))
       in foldr addArg (JsExpr (JS.Call (JS.Ref ref) (map JS.Ref args))) args

funcHelpers :: IntMap.IntMap JS.Expr
funcHelpers =
  IntMap.fromList (map (\n -> (n, JS.Ref (JsName.makeF n))) [2 .. 9])

callHelpers :: IntMap.IntMap JS.Expr
callHelpers =
  IntMap.fromList (map (\n -> (n, JS.Ref (JsName.makeA n))) [2 .. 9])

-- CALLS

call :: Env -> A.Position -> Core.Expr -> [Core.Expr] -> JS.Expr
call env pos fn args =
  case Core._exprValue fn of
    Core.EGlobal q@(Core.QualName (ModuleName.Canonical pkg raw) name)
      | pkg == Pkg.core && raw == Name.basics -> basicsCall env pos q name args
      | pkg == Pkg.core && raw == Name.bitwise -> bitwiseCall env pos q name (map (jsExpr env) args)
      | pkg == Pkg.core && raw == Name.math -> mathCall env pos q name (map (jsExpr env) args)
      | otherwise -> globalCall env pos q (map (jsExpr env) args)
    _ ->
      normalCall env pos (jsExpr env fn) (map (jsExpr env) args)

-- | A call to a name whose arity is known and matched goes straight to the
-- uncurried @name$@; anything else goes through @A2@ … @A9@.
globalCall :: Env -> A.Position -> Core.QualName -> [JS.Expr] -> JS.Expr
globalCall env pos q@(Core.QualName home name) args =
  case Map.lookup q (_arities env) of
    Just n
      | n > 1 && n == length args ->
          JS.Call
            (JS.TrackedRef (_home env) pos (JsName.fromGlobalHumanReadable home name) (JsName.fromGlobalDirectFn home name))
            args
    _ -> normalCall env pos (globalRef env pos q) args

normalCall :: Env -> A.Position -> JS.Expr -> [JS.Expr] -> JS.Expr
normalCall env pos fn args =
  case IntMap.lookup (length args) callHelpers of
    Just helper -> JS.TrackedNormalCall (_home env) pos helper fn args
    Nothing -> List.foldl' (\f a -> JS.Call f [a]) fn args

-- | The operators. `Generate.JavaScript.Expression`'s table, unchanged: `core`
-- has no @\@prim@ declarations yet (C13 is M1b), so these names arrive as
-- ordinary applications and the backend is where they become JavaScript.
basicsCall :: Env -> A.Position -> Core.QualName -> Name -> [Core.Expr] -> JS.Expr
basicsCall env pos q name args =
  case args of
    [one] ->
      let arg = jsExpr env one
       in case name of
            "not" -> JS.Prefix JS.PrefixNot arg
            "negate" -> JS.Prefix JS.PrefixNegate arg
            "toFloat" -> arg
            _ -> globalCall env pos q [arg]
    [leftE, rightE] ->
      case name of
        "append" -> append env leftE rightE
        "apL" -> jsExpr env (apply leftE rightE)
        "apR" -> jsExpr env (apply rightE leftE)
        _ ->
          let left = jsExpr env leftE
              right = jsExpr env rightE
           in case name of
                "add" -> JS.Infix JS.OpAdd left right
                "sub" -> JS.Infix JS.OpSub left right
                "mul" -> JS.Infix JS.OpMul left right
                "fdiv" -> JS.Infix JS.OpDiv left right
                "idiv" -> JS.Infix JS.OpBitwiseOr (JS.Infix JS.OpDiv left right) (JS.Int 0)
                "eq" -> equal left right
                "neq" -> notEqual left right
                "lt" -> cmp JS.OpLt JS.OpLt 0 left right
                "gt" -> cmp JS.OpGt JS.OpGt 0 left right
                "le" -> cmp JS.OpLe JS.OpLt 1 left right
                "ge" -> cmp JS.OpGe JS.OpGt (-1) left right
                "or" -> JS.Infix JS.OpOr left right
                "and" -> JS.Infix JS.OpAnd left right
                "xor" -> JS.Infix JS.OpNe left right
                _ -> globalCall env pos q [left, right]
    _ -> globalCall env pos q (map (jsExpr env) args)

bitwiseCall :: Env -> A.Position -> Core.QualName -> Name -> [JS.Expr] -> JS.Expr
bitwiseCall env pos q name args =
  case args of
    [arg] ->
      case name of
        "complement" -> JS.Prefix JS.PrefixComplement arg
        _ -> globalCall env pos q args
    [left, right] ->
      case name of
        "and" -> JS.Infix JS.OpBitwiseAnd left right
        "or" -> JS.Infix JS.OpBitwiseOr left right
        "xor" -> JS.Infix JS.OpBitwiseXor left right
        "shiftLeftBy" -> JS.Infix JS.OpLShift right left
        "shiftRightBy" -> JS.Infix JS.OpSpRShift right left
        "shiftRightZfBy" -> JS.Infix JS.OpZfRShift right left
        _ -> globalCall env pos q args
    _ -> globalCall env pos q args

mathCall :: Env -> A.Position -> Core.QualName -> Name -> [JS.Expr] -> JS.Expr
mathCall env pos q name args =
  case args of
    [left, right] ->
      case name of
        "remainderBy" -> JS.Infix JS.OpMod right left
        _ -> globalCall env pos q args
    _ -> globalCall env pos q args

-- | @a |> f@ and @f <| a@ are the application they spell, built in Core rather
-- than in JavaScript so that the arity and operator tables see through them.
apply :: Core.Expr -> Core.Expr -> Core.Expr
apply fn value =
  case Core._exprValue fn of
    Core.EApp f args -> fn {Core._exprValue = Core.EApp f (args ++ [value])}
    _ -> fn {Core._exprValue = Core.EApp fn [value]}

-- | A run of @++@ is flattened, so that a literal anywhere in it makes the whole
-- run a JavaScript @+@ rather than a chain of `_Utils_ap` calls.
append :: Env -> Core.Expr -> Core.Expr -> JS.Expr
append env left right =
  let parts = jsExpr env left : flatten env right
   in if any isStringLiteral parts
        then foldr1 (JS.Infix JS.OpAdd) parts
        else foldr1 (\a b -> JS.Call (JS.Ref (JsName.fromKernel Name.utils "ap")) [a, b]) parts

flatten :: Env -> Core.Expr -> [JS.Expr]
flatten env expr =
  case Core._exprValue expr of
    Core.EApp fn [left, right]
      | Core.EGlobal (Core.QualName (ModuleName.Canonical pkg raw) "append") <- Core._exprValue fn,
        pkg == Pkg.core,
        raw == Name.basics ->
          jsExpr env left : flatten env right
    _ -> [jsExpr env expr]

isStringLiteral :: JS.Expr -> Bool
isStringLiteral expr =
  case expr of
    JS.String _ -> True
    JS.TrackedString _ _ _ -> True
    _ -> False

-- COMPARISON

equal :: JS.Expr -> JS.Expr -> JS.Expr
equal left right =
  if isLiteral left || isLiteral right
    then strictEq left right
    else JS.Call (JS.Ref (JsName.fromKernel Name.utils "eq")) [left, right]

notEqual :: JS.Expr -> JS.Expr -> JS.Expr
notEqual left right =
  if isLiteral left || isLiteral right
    then strictNEq left right
    else JS.Prefix JS.PrefixNot (JS.Call (JS.Ref (JsName.fromKernel Name.utils "eq")) [left, right])

cmp :: JS.InfixOp -> JS.InfixOp -> Int -> JS.Expr -> JS.Expr -> JS.Expr
cmp idealOp backupOp backupInt left right =
  if isLiteral left || isLiteral right
    then JS.Infix idealOp left right
    else
      JS.Infix
        backupOp
        (JS.Call (JS.Ref (JsName.fromKernel Name.utils "cmp")) [left, right])
        (JS.Int backupInt)

strictEq :: JS.Expr -> JS.Expr -> JS.Expr
strictEq left right =
  case left of
    JS.Int 0 -> JS.Prefix JS.PrefixNot right
    JS.Bool b -> if b then right else JS.Prefix JS.PrefixNot right
    _ ->
      case right of
        JS.Int 0 -> JS.Prefix JS.PrefixNot left
        JS.Bool b -> if b then left else JS.Prefix JS.PrefixNot left
        _ -> JS.Infix JS.OpEq left right

strictNEq :: JS.Expr -> JS.Expr -> JS.Expr
strictNEq left right =
  case left of
    JS.Int 0 -> JS.Prefix JS.PrefixNot (JS.Prefix JS.PrefixNot right)
    JS.Bool b -> if b then JS.Prefix JS.PrefixNot right else right
    _ ->
      case right of
        JS.Int 0 -> JS.Prefix JS.PrefixNot (JS.Prefix JS.PrefixNot left)
        JS.Bool b -> if b then JS.Prefix JS.PrefixNot left else left
        _ -> JS.Infix JS.OpNe left right

isLiteral :: JS.Expr -> Bool
isLiteral expr =
  case expr of
    JS.String _ -> True
    JS.TrackedString _ _ _ -> True
    JS.Float _ -> True
    JS.TrackedFloat _ _ _ -> True
    JS.Int _ -> True
    JS.TrackedInt _ _ _ -> True
    JS.Bool _ -> True
    JS.TrackedBool _ _ _ -> True
    _ -> False

-- JOINS

-- | A join is a labelled block and a jump is a @break@ or a @continue@ (C15).
--
-- A join is entered from two different places and they are not the same jump.
-- From the __scope body__ a jump goes /forward/, to the code after the block;
-- from the join's __own body__ it goes /backward/, to the top of the loop. So a
-- join gets two labels, and which one a jump names depends on which of the two
-- regions it is in:
--
-- @
-- var p1, p2;                  -- the join's parameters, if it has any
-- j: while (true) {            -- entered from the body
--     \<body\>                   -- EJump j args  =>  p = args; break j;
-- }
-- j$0: while (true) {          -- only if the join's own body jumps to j
--     \<join body\>              -- EJump j args  =>  p = args; continue j$0;
-- }
-- @
--
-- One label for both is an infinite loop, which is how this was found: a
-- function's entry jump became a @continue@ of the loop it was supposed to fall
-- into.
--
-- The outer @while (true)@ never loops. An 'Core.AST.EJump' is in tail position
-- by construction, so the body either returns or breaks; it is a loop rather
-- than a bare labelled block only because `Generate.JavaScript.Builder` has
-- @While@ and not one, which is also how `Optimize.DecisionTree`'s shared
-- branches are emitted today.
--
-- Both halves collapse in the shapes that occur. "Core.Pass.Case" produces
-- parameterless joins entered only from the body, so there is no inner loop and
-- no parameter to declare; "Core.Pass.TailCall" produces one join whose body
-- /is/ the entry jump with the parameters as its arguments, so the outer block
-- disappears entirely and what is left is the @label: while (true)@ the old
-- pipeline emits for a tail-recursive function.
joins :: Env -> [Core.Bind] -> Core.Expr -> [JS.Stmt]
joins env binds body =
  case binds of
    [] -> codeToStmtList (generate env body)
    bind : rest ->
      let (name, params, joinBody) = split bind
          enterLabel = JsName.fromLocal name
          loopLabel = JsName.makeLabel name 0
          selfJumps = jumpsTo name joinBody
          bodyEnv = withJoin name (Join enterLabel params JumpBreak) env
          joinEnv = withJoin name (Join loopLabel params JumpContinue) env
          joinStmts = codeToStmtList (generate joinEnv joinBody)
          loop
            | selfJumps = JS.Labelled loopLabel (JS.While (JS.Bool True) (JS.Block joinStmts))
            | otherwise = JS.Block joinStmts
       in case entryJump name rest body of
            -- The body is nothing but the jump that enters the join, so there is
            -- nothing to break out of: bind the parameters and fall in.
            Just args -> assign bodyEnv params args ++ [loop]
            Nothing ->
              declare params
                ++ [JS.Labelled enterLabel (JS.While (JS.Bool True) (JS.Block (joins bodyEnv rest body)))]
                ++ [loop]
  where
    split (Core.Bind binder value) =
      case Core._exprValue value of
        Core.ELam ps inner -> (Core._binderName binder, map Core._binderName ps, inner)
        _ -> (Core._binderName binder, [], value)

withJoin :: Name -> Join -> Env -> Env
withJoin name join env =
  env {_tails = Map.insert name join (_tails env)}

-- | Is the whole scope body one jump into this join, with nothing else in it?
--
-- That is what "Core.Pass.TailCall" builds, and it is worth recognising because
-- the block it would otherwise need is entered once and left immediately.
entryJump :: Name -> [Core.Bind] -> Core.Expr -> Maybe [Core.Expr]
entryJump name rest body =
  case (rest, Core._exprValue body) of
    ([], Core.EJump j args) | j == name -> Just args
    _ -> Nothing

-- | @var p1, p2;@ — hoisted so that the jumps that assign them and the loop that
-- reads them are talking about the same variables. They are always assigned
-- before they are read, because a jump is the only way into the loop.
declare :: [Name] -> [JS.Stmt]
declare params =
  case params of
    [] -> []
    _ -> [JS.Vars [(JsName.fromLocal p, JS.Null) | p <- params]]

-- | Binding a join's parameters where no transfer of control is needed.
--
-- Nothing at all when the arguments /are/ the parameters, which is what a
-- function's own entry join makes them: they are the function's arguments and
-- are bound already.
assign :: Env -> [Name] -> [Core.Expr] -> [JS.Stmt]
assign env params args
  | map Just params == map varName args = []
  | otherwise = [JS.Vars [(JsName.fromLocal p, jsExpr env a) | (p, a) <- zip params args]]

varName :: Core.Expr -> Maybe Name
varName expr =
  case Core._exprValue expr of
    Core.EVar n -> Just n
    _ -> Nothing

-- | Does this expression jump to the named join?
--
-- It answers whether the join's own body is a loop, which is the only thing
-- that decides between the two labels. A jump inside a lambda would be a
-- violation of C15's rule — a join is not a value and cannot be captured — so
-- there is no scope to stop at.
jumpsTo :: Name -> Core.Expr -> Bool
jumpsTo name = go
  where
    go (Core.Expr value _ _) =
      case value of
        Core.EJump j args -> j == name || any go args
        Core.ELam _ b -> go b
        Core.EApp f as -> go f || any go as
        Core.ELet bs b -> any bindGo bs || go b
        Core.ELetRec bs b -> any bindGo bs || go b
        -- A nested join may shadow the name, in which case a jump inside it is
        -- the inner one's. Shadowing does not happen — the passes take fresh
        -- names — and treating it as a jump here would only cost an unused
        -- label, never a wrong one.
        Core.EJoin bs b -> any bindGo bs || go b
        Core.ECase s as f -> go s || any altGo as || maybe False go f
        Core.ECtor _ _ as -> any go as
        Core.ERecord fs -> any (go . snd) fs
        Core.EUpdate b fs -> go b || any (go . snd) fs
        Core.EAccess b _ -> go b
        Core.EArray as -> any go as
        Core.EPrim _ as -> any go as
        Core.ETyLam _ b -> go b
        Core.ETyApp b _ -> go b
        Core.EWitLam _ b -> go b
        Core.EWitApp b as -> go b || any go as
        Core.EVar _ -> False
        Core.EGlobal _ -> False
        Core.ELit _ -> False
        Core.ECrash _ -> False
    bindGo = go . Core._bindValue
    altGo (Core.Alt _ b) = go b

-- | Entering a join: assign its parameters, then transfer.
--
-- Through temporaries, because an argument may read the parameter it is about to
-- overwrite — @loop (b) (a)@ — which is exactly why
-- `Generate.JavaScript.Expression.generateTailCall` does the same.
jump :: Env -> Name -> [Core.Expr] -> [JS.Stmt]
jump env name args =
  case Map.lookup name (_tails env) of
    Nothing ->
      error ("Generate.CoreJS: jump to a join that is not in scope: " ++ Name.toChars name)
    Just (Join label params kind) ->
      let pairs = zip params (map (jsExpr env) args)
          transfer =
            case kind of
              JumpBreak -> JS.Break (Just label)
              JumpContinue -> JS.Continue (Just label)
       in case pairs of
            [] -> [transfer]
            _ ->
              JS.Vars [(JsName.makeTemp p, value) | (p, value) <- pairs]
                : [ JS.ExprStmt (JS.Assign (JS.LRef (JsName.fromLocal p)) (JS.Ref (JsName.makeTemp p)))
                  | (p, _) <- pairs
                  ]
                ++ [transfer]

-- CASE

-- | Alternatives tested in source order, as a chain of @if@ statements.
--
-- A shared test is repeated and __no branch body is ever duplicated__, which is
-- what makes this correct without a decision tree. `Core.Pass.Case` is where
-- decision trees live, and after it has run the chain this builds is one test
-- deep per alternative — which is why the same emitter serves both.
caseOf :: Env -> Core.Expr -> [Core.Alt] -> Maybe Core.Expr -> [JS.Stmt]
caseOf env scrutinee alts fallback =
  case Core._exprValue scrutinee of
    -- A scrutinee that is already a variable is tested where it stands, which is
    -- the shortcut @Optimize.Expression@ took and `Core.Pass.Case` relies on.
    Core.EVar name ->
      chain env (JS.Ref (JsName.fromLocal name)) alts fallback
    _ ->
      let root = JsName.makeTemp (Name.fromVarIndex (_depth env))
          inner = env {_depth = _depth env + 1}
       in JS.Var root (jsExpr env scrutinee)
            : chain inner (JS.Ref root) alts fallback

chain :: Env -> JS.Expr -> [Core.Alt] -> Maybe Core.Expr -> [JS.Stmt]
chain env root alts fallback =
  case alts of
    [] ->
      case fallback of
        Just f -> codeToStmtList (generate env f)
        Nothing -> error "Generate.CoreJS: a case with no alternatives"
    [alt]
      | Nothing <- fallback ->
          -- The last alternative is the fallback when there is no other: every
          -- `ECase` the lowering produces is exhaustive, which is why
          -- `Core.AST.ECase`'s own fallback is a `Maybe`.
          branch env root alt
    alt@(Core.Alt pattern _) : rest ->
      let (tests, _) = match env root pattern
       in if null tests
            then branch env root alt
            else
              [ JS.IfStmt
                  (List.foldl1' (JS.Infix JS.OpAnd) tests)
                  (JS.Block (branch env root alt))
                  (JS.Block (chain env root rest fallback))
              ]

branch :: Env -> JS.Expr -> Core.Alt -> [JS.Stmt]
branch env root (Core.Alt pattern body) =
  let (_, binds) = match env root pattern
   in binds ++ codeToStmtList (generate env body)

-- | What a pattern tests, and what it binds, against a value already in hand.
--
-- One walk, two answers: a naive matcher needs the tests without the bindings,
-- to decide whether to take the branch, and the bindings without the tests
-- inside it.
match :: Env -> JS.Expr -> Core.Pattern -> ([JS.Expr], [JS.Stmt])
match env value pattern =
  case pattern of
    Core.PWild -> ([], [])
    Core.PVar binder -> ([], [JS.Var (JsName.fromLocal (Core._binderName binder)) value])
    Core.PAs binder inner ->
      let (tests, binds) = match env value inner
       in (tests, JS.Var (JsName.fromLocal (Core._binderName binder)) value : binds)
    Core.PLit lit -> ([strictEq (scrutinised env lit value) (patternLiteral lit)], [])
    Core.PRecord fields ->
      collect [match env (JS.Access value (generateField (_mode env) f)) p | (f, p) <- fields]
    Core.PArray items Nothing ->
      let subs = Index.indexedMap (\i p -> match env (JS.Index value (JS.Int (Index.toMachine i))) p) items
          (tests, binds) = collect subs
       in (JS.Infix JS.OpEq (JS.Access value (JsName.fromLocal "length")) (JS.Int (length items)) : tests, binds)
    Core.PArray _ (Just _) ->
      error "Generate.CoreJS: an array pattern with a tail — the frontend has no syntax for one"
    Core.PCtor name _ args
      | isBool name ->
          let Core.QualName _ short = name
           in ([if short == Name.true then value else JS.Prefix JS.PrefixNot value], [])
      | otherwise ->
          let c = lookupCtor env name
              subs =
                case _ctorShape c of
                  Unbox -> [match env (unboxed env value) p | p <- args]
                  _ -> Index.indexedMap (\i p -> match env (JS.Access value (JsName.fromIndex i)) p) args
              (tests, binds) = collect subs
           in (ctorTest env c value ++ tests, binds)
  where
    collect subs = (concatMap fst subs, concatMap snd subs)

-- | A datatype with one constructor is irrefutable, so it gets no test — which
-- is also what keeps an unboxed constructor from being compared against its own
-- payload. `Optimize.DecisionTree` drops the same tests.
ctorTest :: Env -> Ctor -> JS.Expr -> [JS.Expr]
ctorTest env c value
  | _ctorAlts c <= 1 = []
  | otherwise =
      let seen =
            case (_mode env, _ctorShape c) of
              (Mode.Prod _, Enum) -> value
              (Mode.Prod _, Unbox) -> value
              _ -> JS.Access value JsName.dollar
       in [strictEq seen (tagValue env c)]

unboxed :: Env -> JS.Expr -> JS.Expr
unboxed env value =
  case _mode env of
    Mode.Dev -> JS.Access value (JsName.fromIndex Index.first)
    Mode.Prod _ -> value

-- | A `Char` value is @_Utils_chr('a')@ in dev mode, which is a @String@
-- __object__ and not a primitive: @===@ against a string literal is false for
-- it whatever the characters are. `Optimize.DecisionTree` unwraps it the same
-- way, and this is where the naive matcher has to.
scrutinised :: Env -> Core.Literal -> JS.Expr -> JS.Expr
scrutinised env lit value =
  case (lit, _mode env) of
    (Core.LChar _, Mode.Dev) -> JS.Call (JS.Access value (JsName.fromLocal "valueOf")) []
    _ -> value

patternLiteral :: Core.Literal -> JS.Expr
patternLiteral lit =
  case lit of
    Core.LIntLegacy n -> JS.Int (fromInteger n)
    Core.LInt n -> JS.Int (fromIntegral n)
    Core.LInt64 n -> JS.Int (fromIntegral n)
    Core.LUInt32 n -> JS.Int (fromIntegral n)
    Core.LUInt64 n -> JS.Int (fromIntegral n)
    Core.LString text -> JS.String (text_ (Utf8.toChars text))
    -- A character pattern tests the one-character string, not the dev-mode
    -- `_Utils_chr` wrapper: `_Utils_chr` returns a `String` object in dev, and
    -- `Optimize.DecisionTree` compares against the bare string for that reason.
    Core.LChar code -> JS.String (text_ [toEnum (fromIntegral code)])
    Core.LFloat _ -> error "Generate.CoreJS: a float pattern — the frontend rejects one"
    Core.LFloat32 _ -> error "Generate.CoreJS: a float pattern — the frontend rejects one"

-- SPANS

start :: Core.Span -> A.Position
start (Core.Span _ row col _ _) = A.Position (fromIntegral row) (fromIntegral col)

region :: Core.Span -> A.Region
region (Core.Span _ r1 c1 r2 c2) =
  A.Region (A.Position (fromIntegral r1) (fromIntegral c1)) (A.Position (fromIntegral r2) (fromIntegral c2))
