{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | A JavaScript program from a linked Core program (@docs/m1a-js-on-core.md@
-- §J15).
--
-- The Core-native emitter: §J3 item 6's successor, and the end of the @Opt@ hop.
-- @Generate.FromCore@ built an @AST.Optimized.GlobalGraph@ out of Core and let
-- @Generate.JavaScript@ walk it; this reads 'Core.Program.Program' and writes
-- JavaScript, and the only thing it is handed besides Core is the kernel chunks,
-- which C16 (D81) put in the build system on purpose.
--
-- __There is no graph walk here.__ @Generate.JavaScript@ is a depth-first
-- traversal from each root's @main@, emitting a node the first time it is
-- reached; the order that produces is a property of the traversal, and
-- @compiler#387@ is what it costs when it goes wrong. The linker has already
-- answered both questions — what is reachable and in what order (C14) — so this
-- is a fold over '_progLinked' and nothing else.
module Generate.CoreJS
  ( GeneratedResult (..),
    generate,
    shortenFieldNames,
  )
where

import Core.AST qualified as Core
import Core.Prim qualified as Prim
import Core.Program (Linked (..), Program (..))
import Data.ByteString qualified as BS
import Data.ByteString.Builder qualified as B
import Data.ByteString.Lazy.Char8 qualified as BLazy
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set qualified as Set
import Data.Utf8 qualified as Utf8
import Generate.CoreJS.Expression qualified as Expr
import Generate.CoreJS.Extern qualified as Extern
import Generate.CoreJS.Prim qualified as JsPrim
import Generate.JavaScript.Builder qualified as JS
import Generate.JavaScript.Functions qualified as Functions
import Generate.JavaScript.Name qualified as JsName
import Generate.Mode qualified as Mode
import Generate.SourceMap qualified as SourceMap
import Gren.Kernel qualified as K
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Reporting.Annotation qualified as A

-- ENTRY

-- | What a backend hands "Make": the JavaScript, and the source map for it.
data GeneratedResult = GeneratedResult
  { _source :: B.Builder,
    _sourceMap :: SourceMap.SourceMap
  }

-- | The whole program, in one pass over the link order.
--
-- @kernels@ is the chunk list per kernel module, which the builder reads off the
-- graph `Gren.Kernel` already filled in. Only the modules '_progKernels' names
-- are spliced, and each one lands where the linker put it.
generate :: Mode.Mode -> Program -> Map Name [K.Chunk] -> Map (Pkg.Name, Name) BS.ByteString -> GeneratedResult
generate mode program kernels exts =
  let env = envFor mode program
      started =
        JS.addByteString (taskHelpers env program <> JsPrim.recordHelpers <> JsPrim.crashHelpers <> JsPrim.exportHelpers <> stringHelpers env <> floatBitsHelpers env <> bytesHelpers env <> arrayHelpers env <> sourceHelpers env <> Extern.files exts (_progExterns program)) $
          List.foldl'
            (flip JS.stmtToBuilder)
            (JS.emptyBuilder firstGeneratedLineNumber)
            (constructors env program)
      builder = List.foldl' (item env kernels) started (_progLinked program)
   in GeneratedResult
        { _source =
            prelude
              <> JS._code builder
              <> exports env (_progMains program)
              <> "}(this.module ? this.module.exports : this));",
          _sourceMap = SourceMap.wrap (JS._mappings builder)
        }

prelude :: B.Builder
prelude =
  "(function(scope){\n'use strict';" <> Functions.functions

firstGeneratedLineNumber :: Int
firstGeneratedLineNumber =
  fromIntegral (BLazy.count '\n' (B.toLazyByteString prelude)) + 1

-- | Constructors, ahead of everything else and in no particular order.
--
-- They can be: a constructor definition refers to nothing. That is not free —
-- @Opt.Box@ under @--optimize@ is a reference to @Basics.identity@, which would
-- make a constructor depend on a binding and so need a place in the link order —
-- and `Generate.CoreJS.Expression.ctorDefinition` pays for it by writing the
-- identity function out instead. A few bytes once, against a fourth kind of
-- thing in the order.
--
-- __Why they are emitted at all__, when Core never refers to one as a value:
-- `Core.Lower.Expression` eta-expands a constructor used as a value, so every
-- 'Core.AST.ECtor' is saturated and is built inline. __Kernel JavaScript__ is
-- the caller that remains — @__Maybe_Just@, @__Result_Ok@ and the rest of §J7's
-- eighteen — and it reaches them by name.
constructors :: Expr.Env -> Program -> [JS.Stmt]
constructors env program =
  [ stmt
  | d <- _progData program,
    c <- Core._dataCtors d,
    Just stmt <- [Expr.ctorDefinition env (Core._ctorName c)]
  ]

item :: Expr.Env -> Map Name [K.Chunk] -> JS.Builder -> Linked -> JS.Builder
item env kernels builder linked =
  case linked of
    LBind name bind ->
      JS.stmtToBuilder (definition env name bind) builder
    LKernel short ->
      case Map.lookup short kernels of
        Nothing -> error ("Generate.CoreJS: no chunks for kernel module " ++ Name.toChars short)
        Just chunks -> JS.addByteString (kernel (Expr._mode env) chunks) builder
    LExtern home e ->
      JS.addByteString (Extern.wrapper home e) builder

-- DEFINITIONS

-- | One top-level binding.
--
-- A function of more than one argument gets the pair the JS backend has always
-- emitted: the uncurried @name$@ that a saturated call goes straight to, and the
-- curried @name@ that everything else uses.
definition :: Expr.Env -> Core.QualName -> Core.Bind -> JS.Stmt
definition env q@(Core.QualName home name) (Core.Bind binder body) =
  let pos = position (Core._binderSpan binder)
      readable = JsName.fromGlobalHumanReadable home name
      global = JsName.fromGlobal home name
   in case Core._exprValue body of
        Core.ELam params inner
          | length params > 1 ->
              let argNames = map (JsName.fromLocal . Core._binderName) params
                  direct = JsName.fromGlobalDirectFn home name
                  located = [A.At (A.Region pos pos) n | n <- argNames]
               in JS.Block
                    [ JS.TrackedVar home pos readable direct $
                        JS.TrackedFunction home pos located $
                          Expr.codeToStmtList (Expr.generate (inside env q) inner),
                      JS.Var global (curried argNames direct)
                    ]
        _ ->
          JS.TrackedVar home pos readable global $
            Expr.codeToExpr (Expr.generate (inside env q) body)

-- | The module a definition belongs to is the module its positions are in.
inside :: Expr.Env -> Core.QualName -> Expr.Env
inside env (Core.QualName home _) =
  env {Expr._home = home}

curried :: [JsName.Name] -> JsName.Name -> JS.Expr
curried argNames direct =
  case length argNames of
    n | n >= 2 && n <= 9 -> JS.Call (JS.Ref (JsName.makeF n)) [JS.Ref direct]
    _ ->
      let addArg arg body = JS.Function Nothing [arg] [JS.Return body]
       in foldr addArg (JS.Call (JS.Ref direct) (map JS.Ref argNames)) argNames

-- KERNEL

kernel :: Mode.Mode -> [K.Chunk] -> B.Builder
kernel mode chunks =
  List.foldr (addChunk mode) mempty chunks

addChunk :: Mode.Mode -> K.Chunk -> B.Builder -> B.Builder
addChunk mode chunk builder =
  case chunk of
    K.JS javascript -> B.byteString javascript <> builder
    K.GrenVar home name -> JsName.toBuilder (JsName.fromGlobal home name) <> builder
    K.JsVar home name -> JsName.toBuilder (JsName.fromKernel home name) <> builder
    K.GrenField name -> JsName.toBuilder (Expr.generateField mode name) <> builder
    K.JsField int -> JsName.toBuilder (JsName.fromInt int) <> builder
    K.JsEnum int -> B.intDec int <> builder
    K.Debug -> case mode of Mode.Dev -> builder; Mode.Prod _ -> "_UNUSED" <> builder
    K.Prod -> case mode of Mode.Dev -> "_UNUSED" <> builder; Mode.Prod _ -> builder

-- EXPORTS

exports :: Expr.Env -> [(ModuleName.Canonical, Core.Main)] -> B.Builder
exports env mains =
  "_Program_export(" <> trieToBuilder env (foldr addToTrie emptyTrie mains) <> ");"

-- | What a runtime is handed for one @main@ (C19).
entry :: ModuleName.Canonical -> Core.Main -> JS.Expr
entry home main =
  let value = JS.Ref (JsName.fromGlobal home Name._main)
   in case main of
        Core.MainTask -> JS.Call (JS.Ref (JsName.fromLocalHumanReadable "_TaskPrim_runMain")) [value]

data Trie = Trie
  { _main :: Maybe (ModuleName.Canonical, Core.Main),
    _subs :: Map Name Trie
  }

emptyTrie :: Trie
emptyTrie = Trie Nothing Map.empty

addToTrie :: (ModuleName.Canonical, Core.Main) -> Trie -> Trie
addToTrie (home@(ModuleName.Canonical _ raw), main) trie =
  merge trie (segments home (Name.splitDots raw) main)

segments :: ModuleName.Canonical -> [Name] -> Core.Main -> Trie
segments home parts main =
  case parts of
    [] -> Trie (Just (home, main)) Map.empty
    part : rest -> Trie Nothing (Map.singleton part (segments home rest main))

merge :: Trie -> Trie -> Trie
merge (Trie main1 subs1) (Trie main2 subs2) =
  Trie (pick main1 main2) (Map.unionWith merge subs1 subs2)
  where
    pick Nothing b = b
    pick a Nothing = a
    pick _ _ = error "Generate.CoreJS: two root modules with the same name"

trieToBuilder :: Expr.Env -> Trie -> B.Builder
trieToBuilder env (Trie maybeMain subs) =
  let starter end =
        case maybeMain of
          Nothing -> "{"
          Just (home, main) ->
            "{'init':" <> JS._code (JS.exprToBuilder (entry home main) (JS.emptyBuilder 0)) <> end
   in case Map.toList subs of
        [] -> starter "" <> "}"
        (name, sub) : rest ->
          starter ","
            <> "'"
            <> Utf8.toBuilder name
            <> "':"
            <> trieToBuilder env sub
            <> List.foldl' (\end (n, t) -> ",'" <> Utf8.toBuilder n <> "':" <> trieToBuilder env t <> end) "}" rest

-- ENVIRONMENT

envFor :: Mode.Mode -> Program -> Expr.Env
envFor mode program =
  Expr.Env
    { Expr._mode = mode,
      Expr._ctors = Map.fromList (concatMap ctorEntries (_progData program)),
      Expr._arities =
        Map.fromList $
          [ (q, length params)
          | (q, Core.Bind _ body) <- _progBindings program,
            Core.ELam params _ <- [Core._exprValue body]
          ]
            ++ [ (Core.QualName home (Core._binderName (Core._externBinder e)), Extern.arity e)
               | (home, e) <- _progExterns program
               ],
      Expr._prims =
        Map.fromList
          [ (q, op)
          | (q, Core.Bind _ body) <- _progBindings program,
            Just op <- [primBody body]
          ],
      Expr._tails = Map.empty,
      Expr._home = ModuleName.basics,
      Expr._depth = 0
    }

-- | The scheduler (D246, @m1b-source.md@ §SO24), when the program can run a
-- task at all: it has a @main@, reaches a @task_@ or @source_@ primitive, or
-- links an extern whose result is a @Task@, whose wrapper is a binding node.
-- It is emitted before every other helper, since the @source_@ helpers and a
-- zero-argument extern build a node when the program loads.
taskHelpers :: Expr.Env -> Program -> B.Builder
taskHelpers env program
  | not (null (_progMains program))
      || any JsPrim.isTask (Map.elems (Expr._prims env))
      || any (not . Core._externPure . snd) (_progExterns program) =
      JsPrim.taskHelpers
  | otherwise = mempty

-- | D206's string helpers, when the program reaches a @str_@ primitive at all
-- (@docs/m1b-str-prim.md@ §Z3). Every primitive is a binding's whole body in
-- @core@, so 'Expr._prims' has one for each that is reachable.
stringHelpers :: Expr.Env -> B.Builder
stringHelpers env
  | any isStr (Map.elems (Expr._prims env)) = JsPrim.helpers
  | otherwise = mempty
  where
    isStr op =
      case op of
        Prim.StrOp _ -> True
        _ -> False

-- | The float bits helpers, when the program reaches @f64_bits@,
-- @f64_from_bits@, @f32_bits@, @f32_from_bits@ or one of D391's three word
-- primitives (@docs/m1b-bytes-prim.md@ §BY3).
floatBitsHelpers :: Expr.Env -> B.Builder
floatBitsHelpers env
  | any JsPrim.isFloatBits (Map.elems (Expr._prims env)) = JsPrim.bitsHelpers
  | otherwise = mempty

-- | The @bytes_@ and @bt_@ helpers, when the program reaches one of that group
-- (@docs/m1b-bytes-prim.md@ §BY4).
bytesHelpers :: Expr.Env -> B.Builder
bytesHelpers env
  | any JsPrim.isBytes (Map.elems (Expr._prims env)) = JsPrim.bytesHelpers
  | otherwise = mempty

-- | The @arr_@ and @tr_@ helpers, when the program reaches one of that group
-- (@docs/m1b-arr-prim.md@ §AR2).
sourceHelpers :: Expr.Env -> B.Builder
sourceHelpers env
  | any JsPrim.isSource (Map.elems (Expr._prims env)) = JsPrim.sourceHelpers
  | otherwise = mempty

arrayHelpers :: Expr.Env -> B.Builder
arrayHelpers env
  | any JsPrim.isArray (Map.elems (Expr._prims env)) = JsPrim.arrayHelpers
  | otherwise = mempty

-- | The primitive a binding /is/, when its whole body is one applied to its own
-- parameters in order.
--
-- That is what a @\@prim@ declaration lowers to — @Core.Lower.Expression@\'s
-- @primValue@ eta-expands the table entry — so this recognizes the shape rather
-- than the attribute, and a binding written that way by hand is treated the
-- same. Nothing else has to be checked: an argument that is a parameter used
-- once is substitutable at a saturated call site by construction.
primBody :: Core.Expr -> Maybe Prim.PrimOp
primBody body =
  case Core._exprValue body of
    Core.ELam binders inner ->
      case Core._exprValue inner of
        Core.EPrim op args
          | map Core._binderName binders == [name | Core.EVar name <- map Core._exprValue args],
            length args == length binders ->
              Just op
        _ -> Nothing
    _ -> Nothing

ctorEntries :: Core.DataDecl -> [(Core.QualName, Expr.Ctor)]
ctorEntries d =
  [ ( Core._ctorName c,
      Expr.Ctor
        { Expr._ctorShape = shapeOf d,
          Expr._ctorTag = Core._ctorTag c,
          Expr._ctorFields = length (Core._ctorFields c),
          Expr._ctorAlts = length (Core._dataCtors d),
          Expr._ctorHome = home,
          Expr._ctorShort = short
        }
    )
  | c <- Core._dataCtors d,
    let Core.QualName home short = Core._ctorName c
  ]

-- | The representation choice, derived the way `Canonicalize.Environment.Local`
-- derives it from source and @Generate.FromCore.ctorOpts@ derived it from Core.
shapeOf :: Core.DataDecl -> Expr.Shape
shapeOf d =
  case Core._dataCtors d of
    [c] | length (Core._ctorFields c) == 1 -> Expr.Unbox
    cs | all (null . Core._ctorFields) cs -> Expr.Enum
    _ -> Expr.Normal

-- FIELD NAMES

-- | The @--optimize@ field table, from the program's field set.
--
-- `Generate.Mode.shortenFieldNames` reads a frequency map and gives the shortest
-- names to the commonest fields. The linker's '_progFields' is a set: C6 wants a
-- specified order and a set has one, and a count is a property of the JavaScript
-- rather than of the program. So the assignment here is alphabetical instead —
-- correct either way, since all that is required is a bijection, and measurably
-- a little larger. §J15 says how much.
shortenFieldNames :: Set.Set Name -> Mode.ShortFieldNames
shortenFieldNames fields =
  Map.fromList (zipWith (\i f -> (f, JsName.fromInt i)) [0 ..] (Set.toAscList fields))

-- SPANS

position :: Core.Span -> A.Position
position (Core.Span _ row col _ _) =
  A.Position (fromIntegral row) (fromIntegral col)
