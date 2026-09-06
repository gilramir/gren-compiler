{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | A JavaScript program from a linked Core program (@docs/m1a-js-on-core.md@
-- §J15).
--
-- The Core-native emitter: §J3 item 6's successor, and the end of the @Opt@ hop.
-- `Generate.FromCore` builds an 'AST.Optimized.GlobalGraph' out of Core and lets
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
  ( generate,
    generateForRepl,
    shortenFieldNames,
  )
where

import AST.Canonical qualified as Can
import Core.AST qualified as Core
import Core.Program (Linked (..), Program (..))
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
import Generate.JavaScript (GeneratedResult (..), printForRepl)
import Generate.JavaScript.Builder qualified as JS
import Generate.JavaScript.Functions qualified as Functions
import Generate.JavaScript.Name qualified as JsName
import Generate.Mode qualified as Mode
import Generate.SourceMap qualified as SourceMap
import Gren.Kernel qualified as K
import Gren.ModuleName qualified as ModuleName
import Reporting.Annotation qualified as A
import Reporting.Render.Type.Localizer qualified as L

-- ENTRY

-- | The whole program, in one pass over the link order.
--
-- @kernels@ is the chunk list per kernel module, which the builder reads off the
-- graph `Gren.Kernel` already filled in. Only the modules '_progKernels' names
-- are spliced, and each one lands where the linker put it.
generate :: Mode.Mode -> Program -> Map Name [K.Chunk] -> GeneratedResult
generate mode program kernels =
  let env = envFor mode program
      started =
        List.foldl'
          (flip JS.stmtToBuilder)
          (JS.emptyBuilder firstGeneratedLineNumber)
          (constructors env program)
      linked = List.foldl' (item env kernels) started (_progLinked program)
      builder = List.foldl' (flip JS.stmtToBuilder) linked (managers program)
   in GeneratedResult
        { _source =
            prelude
              <> JS._code builder
              <> exports env (_progMains program)
              <> "}(this.module ? this.module.exports : this));",
          _sourceMap = SourceMap.wrap (JS._mappings builder)
        }

-- | One REPL entry, as a script that prints the value and its type (§J17).
--
-- The same fold over the link order that 'generate' performs, with the two ends
-- swapped for the REPL's: no module wrapper, because the script is piped
-- straight into @node@ and nothing imports it; and no @_Platform_export@,
-- because a REPL entry has no @main@. What replaces the export is
-- `Generate.JavaScript.printForRepl`, which both REPLs share.
--
-- The value being printed is a root, and so is @Debug.toString@ — not because
-- the printer calls it (it calls kernel @Debug@\'s @_Debug_toAnsiString@
-- directly) but because that binding is what reaches the kernel module the
-- function is in. Rooting the kernel module instead would work here, where the
-- printer runs last and no order can be wrong, but it would make the two REPLs
-- reach different sets and a differential comparison between them worth less.
-- 'Generate.replRoots' is where that choice is written down.
generateForRepl :: Bool -> L.Localizer -> Program -> Map Name [K.Chunk] -> ModuleName.Canonical -> Name -> Can.Annotation -> B.Builder
generateForRepl ansi localizer program kernels home name (Can.Forall _ tipe) =
  let mode = Mode.Dev
      env = envFor mode program
      started =
        List.foldl'
          (flip JS.stmtToBuilder)
          (JS.emptyBuilder 0)
          (constructors env program)
      linked = List.foldl' (item env kernels) started (_progLinked program)
      builder = List.foldl' (flip JS.stmtToBuilder) linked (managers program)
   in "process.on('uncaughtException', function(err) { process.stderr.write(err.toString() + '\\n'); process.exit(1); });"
        <> Functions.functions
        <> JS._code builder
        <> printForRepl ansi localizer home name tipe

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
    LPort home port_ ->
      JS.stmtToBuilder (portDefinition env home port_) builder
    LKernel short ->
      case Map.lookup short kernels of
        Nothing -> error ("Generate.CoreJS: no chunks for kernel module " ++ Name.toChars short)
        Just chunks -> JS.addByteString (kernel (Expr._mode env) chunks) builder

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

-- PORTS

-- | The runtime call a @port@ declaration stands for (C18).
--
-- Core names the pieces and this assembles the call, which is the half of a port
-- that is not a value: @_Platform_incomingPort@ and its two siblings are raw
-- uncurried JavaScript functions with no @F3@ wrapper, and an input-less task
-- port passes a JavaScript @null@ where the encoder goes and another where the
-- input goes. Neither is anything Core could have written.
portDefinition :: Expr.Env -> ModuleName.Canonical -> Core.Port -> JS.Stmt
portDefinition env home (Core.Port binder flow) =
  let name = Core._binderName binder
      inner = env {Expr._home = home}
      converter (Core.Converter _ code) = Expr.codeToExpr (Expr.generate inner code)
      bytes (Core.Converter b _) = JS.Bool b
      platform fn = JS.Ref (JsName.fromKernel Name.platform fn)
      wire = JS.String (Name.toBuilder name)
   in JS.Var (JsName.fromGlobal home name) $
        case flow of
          Core.PortOut c -> JS.Call (platform "outgoingPort") [wire, converter c, bytes c]
          Core.PortIn c -> JS.Call (platform "incomingPort") [wire, converter c, bytes c]
          Core.PortTask input output ->
            let made =
                  JS.Call
                    (platform "taskPort")
                    [ wire,
                      maybe JS.Null converter input,
                      converter output,
                      maybe (JS.Bool False) bytes input,
                      bytes output
                    ]
             in case input of
                  Just _ -> made
                  -- No input: the port is a `Task` rather than a function to
                  -- one, so the runtime's curried constructor is applied to the
                  -- `null` that stands for the input it will never be given.
                  -- The second `null` Core cannot write; this is the first.
                  Nothing -> JS.Call made [JS.Null]

-- MANAGERS

-- | Registering each @effect module@'s manager with the runtime (C17).
--
-- Last, and it can be: an assignment into @_Platform_effectManagers@ is read
-- when effects are dispatched and never at load, so all it needs is for the
-- five functions to be defined by the time it runs — which the linker has
-- already arranged, because it puts an edge from each entry binding to all five.
--
-- What is __not__ here is @command@ and @subscription@. The old pipeline emits
-- them as part of this node and reaches them through an @Opt.Link@; in Core they
-- are ordinary bindings holding @Platform.leaf \"<module>\"@, so they are already
-- in the link order and the shortcut §J11 left behind goes with the hop.
managers :: Program -> [JS.Stmt]
managers program =
  [ JS.ExprStmt $
      JS.Assign
        (JS.LBracket (JS.Ref (JsName.fromKernel Name.platform "effectManagers")) (JS.String (Name.toBuilder raw)))
        (JS.Call (JS.Ref (JsName.fromKernel Name.platform "createManager")) (managerArgs home m))
  | (home@(ModuleName.Canonical _ raw), m) <- _progManagers program
  ]

-- | The five slots @_Platform_createManager@ takes, in its order. A @sub@-only
-- manager has no @cmdMap@, and the runtime reads a @0@ in that position.
managerArgs :: ModuleName.Canonical -> Core.Manager -> [JS.Expr]
managerArgs home m =
  let ref (Core.QualName h n) = JS.Ref (JsName.fromGlobal h n)
      three = [ref (Core._managerInit m), ref (Core._managerOnEffects m), ref (Core._managerOnSelfMsg m)]
   in case (Core._managerCmdMap m, Core._managerSubMap m) of
        (Just cmdMap, Nothing) -> three ++ [ref cmdMap]
        (Nothing, Just subMap) -> three ++ [JS.Int 0, ref subMap]
        (Just cmdMap, Just subMap) -> three ++ [ref cmdMap, ref subMap]
        (Nothing, Nothing) ->
          error ("Generate.CoreJS: a manager with neither map: " ++ ModuleName.toChars (ModuleName._module home))

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
  let export = JsName.fromKernel Name.platform "export"
   in JsName.toBuilder export <> "(" <> trieToBuilder env (foldr addToTrie emptyTrie mains) <> ");"

-- | What a runtime is handed for one @main@ (C19).
entry :: Expr.Env -> ModuleName.Canonical -> Core.Main -> JS.Expr
entry env home main =
  let value = JS.Ref (JsName.fromGlobal home Name._main)
   in case main of
        Core.MainString -> JS.Call (JS.Ref (JsName.fromKernel Name.node "log")) [value]
        Core.MainHtml -> JS.Call (JS.Ref (JsName.fromKernel Name.virtualDom "init")) [value]
        Core.MainProgram (Core.Converter True _) -> JS.Call value [JS.Null]
        Core.MainProgram (Core.Converter False code) ->
          JS.Call value [Expr.codeToExpr (Expr.generate (env {Expr._home = home}) code)]

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
            "{'init':" <> JS._code (JS.exprToBuilder (entry env home main) (JS.emptyBuilder 0)) <> end
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
        Map.fromList
          [ (q, length params)
          | (q, Core.Bind _ body) <- _progBindings program,
            Core.ELam params _ <- [Core._exprValue body]
          ],
      Expr._tails = Map.empty,
      Expr._home = ModuleName.basics,
      Expr._depth = 0
    }

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
-- derives it from source and `Generate.FromCore.ctorOpts` derives it from Core.
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
