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
-- __Recursive groups keep their shape.__ `Canonical` distinguishes a plain
-- declaration from a mutually recursive one, and Core keeps both: the binds are
-- one flat list, and 'Core.AST._moduleDefsRec' names the groups so a backend
-- that has to emit them together can. The order is the one `Canonical` gives,
-- which is the frontend's dependency sort rather than source order — C6's
-- traversal audit is what makes it reproducible, and that audit is still open.
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
import Data.Map qualified as Map
import Data.Name (Name)
import Data.Name qualified as Name
import Reporting.Annotation qualified as A

lower :: Map.Map Can.NodeId Can.Type -> Can.Module -> Core.Module
lower types modul =
  let home = Can._name modul
      env = Expr.Env selfFile types
      groups = declGroups (Can._decls modul)
   in Core.Module
        { Core._moduleName = home,
          Core._moduleFiles = Map.singleton selfFile home,
          Core._moduleData =
            [lowerUnion home name union | (name, union) <- Map.toAscList (Can._unions modul)],
          -- Classes and instances are M1b; there is no syntax for either yet.
          Core._moduleClasses = [],
          Core._moduleInstances = [],
          Core._moduleDefs = map (Expr.def env) (concatMap group groups),
          Core._moduleDefsRec =
            [map (Core.QualName home) (map defName g) | Recursive g <- groups],
          Core._moduleExports = map (Core.QualName home) (exports modul)
        }

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

-- | The module's exported __values__, in a fixed order (C6).
--
-- Types and aliases are not values: an alias does not survive lowering at all,
-- and a datatype is in 'Core.AST._moduleData' whether or not it is exposed.
-- What is left is definitions and operators, and an operator is exported under
-- its symbol while the value it names is an ordinary function, so it is that
-- function that goes in the list.
exports :: Can.Module -> [Name]
exports modul =
  case Can._exports modul of
    Can.ExportEverything _ ->
      concatMap (map defName . group) (declGroups (Can._decls modul))
        ++ map binopTarget (Map.elems (Can._binops modul))
    Can.Export entries ->
      concat
        [ case entry of
            Can.ExportValue -> [name]
            Can.ExportBinop -> maybe [] (pure . binopTarget) (Map.lookup name (Can._binops modul))
            _ -> []
          | (name, A.At _ entry) <- Map.toAscList entries
        ]

binopTarget :: Can.Binop -> Name
binopTarget (Can.Binop_ _ _ name) = name

-- EFFECTS

-- | What a module declares that Core does not carry yet.
unloweredEffects :: Can.Module -> [Name]
unloweredEffects modul =
  case Can._effects modul of
    Can.NoEffects -> []
    Can.Ports ports -> Map.keys ports
    Can.Manager _ _ _ _ -> [Name.fromChars "$fx$"]
