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
import Core.Lower.Type (lowerType)
import Core.Order qualified as Order
import Core.Refs qualified as Refs
import Data.Index qualified as Index
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set qualified as Set
import Data.Word (Word32)
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Reporting.Annotation qualified as A
import Prelude hiding (span)

-- ENVIRONMENT

data Env = Env
  { -- | The file this module's spans point into. C5 keeps a file id on every
    -- node rather than assuming the enclosing module's, so that a Core→Core
    -- pass can inline across a module boundary without losing where the code
    -- came from.
    _file :: !Core.FileId,
    -- | One entry per node, from the solver.
    _types :: Map.Map Can.NodeId Can.Type
  }

-- | The Core type recorded for a node.
typeOf :: Env -> Can.NodeId -> Core.Type
typeOf env nid =
  case Map.lookup nid (_types env) of
    Just tipe -> lowerType tipe
    Nothing ->
      error $
        "Core.Lower.Expression: node "
          ++ show nid
          ++ " has no recorded type. See docs/m1a-node-types.md."

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
          node (Core.EVar name)
        Can.VarTopLevel home name ->
          node (Core.EGlobal (Core.QualName home name))
        Can.VarForeign home name _ ->
          node (Core.EGlobal (Core.QualName home name))
        Can.VarOperator _ home name _ ->
          node (Core.EGlobal (Core.QualName home name))
        Can.VarKernel home name ->
          -- `AST.Optimized.toKernelGlobal` already gives a kernel function a
          -- module: the `gren/kernel` pseudo-package, one module per kernel
          -- prefix. Core reuses it rather than inventing a second encoding.
          -- Kernel references stop existing when `ffi.md` F7 retires the
          -- splicer at M1b.
          node (Core.EGlobal (Core.QualName (ModuleName.Canonical Pkg.kernel home) name))
        Can.VarDebug _ name _ ->
          -- The module on the node is the one doing the referring, not the one
          -- being referred to.
          node (Core.EGlobal (Core.QualName ModuleName.debug name))
        Can.VarCtor _ home name index _ ->
          ctorValue tipe sp (Core.QualName home name) (Index.toMachine index)
        Can.Chr c ->
          node (Core.ELit (Literal.chr c))
        Can.Str s ->
          node (Core.ELit (Literal.str s))
        Can.Int n ->
          node (Core.ELit (Literal.int n))
        Can.Float f ->
          node (Core.ELit (Literal.float f))
        Can.Array items ->
          node (Core.EArray (map (expr env) items))
        Can.Negate inner ->
          node $
            Core.EApp
              (Core.Expr (Core.EGlobal (Core.QualName ModuleName.basics Name.negate)) (negateType tipe) sp)
              [expr env inner]
        Can.Binop _ home name _ left right ->
          node $
            Core.EApp
              (Core.Expr (Core.EGlobal (Core.QualName home name)) (binopType env left right tipe) sp)
              [expr env left, expr env right]
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
      bind env (span env region) name (typeOf env nid) args (expr env body)
    Can.TypedDef (A.At region name) _ args body result ->
      let tipe = lowerType (foldr (Can.TLambda . snd) result args)
       in bind env (span env region) name tipe (map fst args) (expr env body)

bind :: Env -> Core.Span -> Name -> Core.Type -> [Can.Pattern] -> Core.Expr -> Core.Bind
bind env sp name tipe args body =
  Core.Bind
    (Core.Binder name tipe sp)
    ( case args of
        [] -> body
        _ ->
          let (argTypes, result) = arguments (length args) tipe
              (binders, wrap) = binderList env sp argTypes args
           in Core.Expr (Core.ELam binders (wrap body)) (Core.TFun argTypes result) sp
    )

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
        Can.PInt n ->
          Core.PLit (Literal.int n)
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
