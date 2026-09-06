{-# OPTIONS_GHC -Wall #-}

-- | Lower a canonical module to Core.
--
-- The declaration half: definitions, datatypes and exports. It is the
-- assembling step — "Core.Lower.Expression" and "Core.Lower.Type" do the
-- translating — and its own decisions are these.
--
-- __The file table names modules, not files__ (C5). C2 writes the table as
-- @FileId -> FilePath@, but a path is where a machine happened to keep the
-- source: absolute on one machine, package-relative on another, and different
-- again when the same package is built from a tarball. C10's gate is that two
-- frontends produce byte-identical Core, and a path cannot survive it. A
-- canonical module name is stable, identifies the source exactly as precisely,
-- and is already on the module being lowered. Resolving one to a path for an
-- error message is the build system's job and it already does it.
--
-- __The definitions are in C14's order__, not the one `Canonical` arrived at.
-- Canonical's is @Data.Graph.stronglyConnComp@'s, which is deterministic and
-- unwritten — @docs/m1a-determinism.md@ §T2 — so it is replaced here by the
-- order "Core.Order" specifies and the linker already used: dependency order,
-- least-named ready group first, a group's members by name. The binds are one
-- flat list and 'Core.AST._moduleDefsRec' names the groups of more than one, so
-- a backend that has to emit a mutually recursive group together still can.
--
-- __Ports and effect managers are not lowered.__ A @port@ becomes a generated
-- JSON encoder or decoder in @Optimize/Port.hs@, and an @effect module@ becomes
-- a manager node with no Core counterpart; neither has a place in Core until
-- @core@ stops needing them, which is @portable-core.md@ P3 and @ffi.md@ F4 at
-- M1b. 'unloweredEffects' is what a module still declares that this pass drops,
-- so that the gap is visible rather than a shorter list of definitions.
module Core.Lower.Module
  ( lower,
    unloweredEffects,
  )
where

import AST.Canonical qualified as Can
import Core.AST qualified as Core
import Core.Lower.Expression qualified as Expr
import Core.Lower.Type (lowerUnion)
import Core.Order qualified as Order
import Core.Refs qualified as Refs
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set qualified as Set
import Data.Utf8 qualified as Utf8
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Reporting.Annotation qualified as A

lower :: Map.Map Can.NodeId Can.Type -> Can.Module -> Core.Module
lower types modul =
  let home = Can._name modul
      env = Expr.Env selfFile types
      defs =
        definitions home $
          map (Expr.def env) (concatMap group (declGroups (Can._decls modul)))
            ++ entries home (Can._effects modul)
   in Core.Module
        { Core._moduleName = home,
          Core._moduleFiles = Map.singleton selfFile home,
          Core._moduleData =
            [lowerUnion home name union | (name, union) <- Map.toAscList (Can._unions modul)],
          -- Classes and instances are M1b; there is no syntax for either yet.
          Core._moduleClasses = [],
          Core._moduleInstances = [],
          Core._moduleDefs = concat defs,
          Core._moduleDefsRec =
            [map (Core.QualName home . bindName) g | g <- defs, length g > 1],
          Core._moduleExports = map (Core.QualName home) (exports modul),
          Core._moduleManager = manager home (Can._effects modul)
        }

-- | The module's definitions, grouped and ordered by C14.
--
-- The dependency relation is the one "Core.Program" links with — every global
-- a definition's body refers to, from inside a lambda as much as beside it —
-- restricted to this module's own names. Canonical's relation is narrower: a
-- definition that takes arguments is given no edges at all (@toNodeTwo@),
-- because a function body does not run when the definition is elaborated. That
-- is the right relation for deciding *evaluation* order and the wrong one for a
-- specified *emission* order, and using the linker's here is what makes linking
-- a single module reproduce the order the module already has.
definitions :: ModuleName.Canonical -> [Core.Bind] -> [[Core.Bind]]
definitions home binds =
  let byName = Map.fromList [(bindName b, b) | b <- binds]
      deps =
        Map.fromList
          [ ( bindName b,
              Set.fromList
                [ n
                | Core.QualName h n <- Set.toList (Refs._refGlobals (Refs.refsIn (Core._bindValue b))),
                  h == home
                ]
            )
          | b <- binds
          ]
   in [[byName Map.! n | n <- g] | g <- Order.groups (map bindName binds) deps]

bindName :: Core.Bind -> Name
bindName = Core._binderName . Core._bindBinder

-- | The one file a module's spans point into: itself.
--
-- A Core→Core pass that inlines across a module boundary adds the other
-- module's entry as it does so; nothing at M1a moves a node between modules.
selfFile :: Core.FileId
selfFile = Core.FileId 0

-- DECLARATIONS

data Group
  = Single Can.Def
  | Recursive [Can.Def]

group :: Group -> [Can.Def]
group g =
  case g of
    Single d -> [d]
    Recursive ds -> ds

declGroups :: Can.Decls -> [Group]
declGroups decls =
  case decls of
    Can.Declare d rest -> Single d : declGroups rest
    Can.DeclareRec d others rest -> Recursive (d : others) : declGroups rest
    Can.SaveTheEnvironment -> []

defName :: Can.Def -> Name
defName d =
  case d of
    Can.Def _ (A.At _ name) _ _ -> name
    Can.TypedDef (A.At _ name) _ _ _ _ -> name

-- EXPORTS

-- | The module's exported __values__, sorted by name (C6).
--
-- Types and aliases are not values: an alias does not survive lowering at all,
-- and a datatype is in 'Core.AST._moduleData' whether or not it is exposed.
-- What is left is definitions and operators, and an operator is exported under
-- its symbol while the value it names is an ordinary function, so it is that
-- function that goes in the list.
--
-- Sorted rather than taken in the order the two branches produce: @exposing (..)@
-- would otherwise inherit the declaration order, and an explicit @exposing@ list
-- is ascending by /exposed/ name, which is not the same list when an operator
-- exports a differently named function.
exports :: Can.Module -> [Name]
exports modul =
  List.sort $
    case Can._exports modul of
      Can.ExportEverything _ ->
        concatMap (map defName . group) (declGroups (Can._decls modul))
          ++ map binopTarget (Map.elems (Can._binops modul))
      Can.Export exposed ->
        concat
          [ case entry of
              Can.ExportValue -> [name]
              Can.ExportBinop -> maybe [] (pure . binopTarget) (Map.lookup name (Can._binops modul))
              _ -> []
          | (name, A.At _ entry) <- Map.toAscList exposed
          ]

binopTarget :: Can.Binop -> Name
binopTarget (Can.Binop_ _ _ name) = name

-- EFFECTS

-- | What a module declares that Core does not carry yet.
--
-- Ports only, since §J10a: a manager is lowered (see 'manager' and 'entries'),
-- and no package M1a builds against declares a port. @Optimize/Port.hs@ turns
-- one into a generated JSON encoder or decoder, which is a subsystem rather
-- than a shape, and @portable-core.md@ P3 rebuilds the whole port mechanism on
-- @ffi.md@ F4 at M1b. Lowering it now would be writing something to delete
-- with nothing exercising it in between.
unloweredEffects :: Can.Module -> [Name]
unloweredEffects modul =
  case Can._effects modul of
    Can.NoEffects -> []
    Can.Ports ports -> Map.keys ports
    Can.Manager {} -> []

-- | An @effect module@'s manager, as a Core declaration.
--
-- The five functions are named rather than referred to: what a runtime does
-- with them is the runtime's business, and the record @_Platform_createManager@
-- builds has that runtime's field names rather than Gren's.
manager :: ModuleName.Canonical -> Can.Effects -> Maybe Core.Manager
manager home effects =
  case effects of
    Can.NoEffects -> Nothing
    Can.Ports _ -> Nothing
    Can.Manager _ _ _ m ->
      let here = Core.QualName home
          entry name = here (Name.fromChars name)
       in Just $
            Core.Manager
              { Core._managerKind =
                  case m of
                    Can.Cmd _ -> Core.ManagerCmd
                    Can.Sub _ -> Core.ManagerSub
                    Can.Fx _ _ -> Core.ManagerFx,
                Core._managerEntries = map entry (entryNames m),
                Core._managerInit = here (Name.fromChars "init"),
                Core._managerOnEffects = here (Name.fromChars "onEffects"),
                Core._managerOnSelfMsg = here (Name.fromChars "onSelfMsg"),
                Core._managerCmdMap =
                  case m of
                    Can.Sub _ -> Nothing
                    _ -> Just (here (Name.fromChars "cmdMap")),
                Core._managerSubMap =
                  case m of
                    Can.Cmd _ -> Nothing
                    _ -> Just (here (Name.fromChars "subMap"))
              }

-- | Which of @command@ and @subscription@ a manager declares.
entryNames :: Can.Manager -> [String]
entryNames m =
  case m of
    Can.Cmd _ -> ["command"]
    Can.Sub _ -> ["subscription"]
    Can.Fx _ _ -> ["command", "subscription"]

-- | @command@ and @subscription@ as ordinary bindings.
--
-- @_Platform_leaf(home)@ closes over the module name and reads nothing else, so
-- this really is what the value is: a partial application of a kernel function
-- to a string. `Optimize.Module` gets the same JavaScript from a graph edge —
-- an @Opt.Link@ to the manager node, which emits the @var@ as one of its own
-- statements — which is why the old pipeline needs no binding here and a
-- Core-only program representation does.
--
-- The type is the one @Type.Constrain.Module.letCmd@ gives it, with @msg@ for
-- the variable a fresh one stands for there: a manager's effect type applied to
-- a message, to that runtime's @Cmd@ or @Sub@ of the same message.
entries :: ModuleName.Canonical -> Can.Effects -> [Core.Bind]
entries home effects =
  case effects of
    Can.NoEffects -> []
    Can.Ports _ -> []
    Can.Manager _ _ _ m ->
      [ leaf home name (effectType home m name)
      | name <- entryNames m
      ]

leaf :: ModuleName.Canonical -> String -> Core.Type -> Core.Bind
leaf (ModuleName.Canonical _ raw) name tipe =
  let sp = Core.Span selfFile 0 0 0 0
      string = Core.TCon (Core.QualName ModuleName.string Name.string) []
      platformLeaf =
        Core.Expr
          (Core.EGlobal (Core.QualName kernelPlatform (Name.fromChars "leaf")))
          (Core.TFun [string] tipe)
          sp
      home_ = Core.Expr (Core.ELit (Core.LString (Utf8.fromChars (ModuleName.toChars raw)))) string sp
   in Core.Bind
        (Core.Binder (Name.fromChars name) (generalize tipe) sp)
        (Core.Expr (Core.EApp platformLeaf [home_]) tipe sp)

-- | @Foo.MyCmd msg -> Platform.Cmd.Cmd msg@, or the @Sub@ of the same shape.
effectType :: ModuleName.Canonical -> Can.Manager -> String -> Core.Type
effectType home m name =
  let msg = Core.TVar msgVar
      effect tipe = Core.TCon (Core.QualName home tipe) [msg]
      wrapper modul tipe = Core.TCon (Core.QualName modul tipe) [msg]
   in case (m, name) of
        (Can.Cmd cmd, _) -> Core.TFun [effect cmd] (wrapper ModuleName.cmd Name.cmd)
        (Can.Sub sub, _) -> Core.TFun [effect sub] (wrapper ModuleName.sub Name.sub)
        (Can.Fx cmd _, "command") -> Core.TFun [effect cmd] (wrapper ModuleName.cmd Name.cmd)
        (Can.Fx _ sub, _) -> Core.TFun [effect sub] (wrapper ModuleName.sub Name.sub)

generalize :: Core.Type -> Core.Type
generalize = Core.TForall [msgVar] []

-- | The message variable's name. `Type.Constrain.Module` uses a fresh
-- unification variable and never names it; Core needs a name and C6 needs it to
-- be the same one every time.
msgVar :: Name
msgVar = Name.fromChars "msg"

kernelPlatform :: ModuleName.Canonical
kernelPlatform = ModuleName.Canonical Pkg.kernel Name.platform
