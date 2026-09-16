{-# OPTIONS_GHC -Wall #-}

-- | May this module refer to the capabilities it refers to? (D258,
-- @m1b-source.md@ §SO12.4)
--
-- A value declared under @\@capability@ mints a capability — a @Permission@, an
-- @Environment@ — and minting one is the application's decision: a dependency
-- that wants the filesystem takes a permission from its caller, and its type
-- says so. @Init.Task@ enforced that by being a type only a program's @init@
-- could run; once @main@ is a @Task Never {}@ nothing about a type can, so it is
-- enforced here instead.
--
-- The rule: a reference to a capability declared in package @p@ is allowed from
-- a module of @p@ itself — a package builds on its own capabilities — and from
-- a module of the application being built. From a module of any other package
-- it is refused, wherever in the module it is.
--
-- It is a walk over the canonical module rather than a check in name
-- resolution, because a reference's region is still there and nothing about the
-- environment has to change to carry one more fact per name.
module Nitpick.Capability
  ( Error (..),
    check,
  )
where

import AST.Canonical qualified as Can
import Data.Map qualified as Map
import Data.Name (Name)
import Data.Set qualified as Set
import Gren.Interface qualified as I
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Reporting.Annotation qualified as A

-- | A reference to a capability from a package that did not declare it.
data Error
  = MintedByDependency A.Region ModuleName.Canonical Name Pkg.Name

-- | Whether the module is the application's, its package, its imports'
-- interfaces, and the module.
check :: Bool -> Pkg.Name -> Map.Map ModuleName.Raw I.Interface -> Can.Module -> [Error]
check application pkg ifaces modul
  | application = []
  | otherwise =
      [ MintedByDependency region home name pkg
      | (region, home@(ModuleName.Canonical declaring raw), name) <- references modul,
        declaring /= pkg,
        Just iface <- [Map.lookup raw ifaces],
        Set.member name (I._capabilities iface)
      ]

-- | Every reference to another module's value, with where it is.
references :: Can.Module -> [(A.Region, ModuleName.Canonical, Name)]
references modul =
  decls (Can._decls modul)
    ++ concatMap (concatMap def . Map.elems . Can._in_methods) (Map.elems (Can._instances modul))

decls :: Can.Decls -> [(A.Region, ModuleName.Canonical, Name)]
decls ds =
  case ds of
    Can.Declare d rest -> def d ++ decls rest
    Can.DeclareRec d others rest -> def d ++ concatMap def others ++ decls rest
    Can.SaveTheEnvironment -> []

def :: Can.Def -> [(A.Region, ModuleName.Canonical, Name)]
def d =
  case d of
    Can.Def _ _ _ body -> expr body
    Can.TypedDef _ _ _ body _ -> expr body

expr :: Can.Expr -> [(A.Region, ModuleName.Canonical, Name)]
expr (Can.Expr _ region value) =
  case value of
    Can.VarForeign home name _ -> [(region, home, name)]
    Can.VarOperator _ home name _ -> [(region, home, name)]
    Can.Array items -> concatMap expr items
    Can.Negate inner -> expr inner
    Can.Binop _ target _ left right ->
      ( case target of
          Can.OpValue home name -> [(region, home, name)]
          Can.OpMethod {} -> []
      )
        ++ expr left
        ++ expr right
    Can.Lambda _ body -> expr body
    Can.Call func args -> concatMap expr (func : args)
    Can.If branches final ->
      concatMap (\(c, b) -> expr c ++ expr b) branches ++ expr final
    Can.Let d body -> def d ++ expr body
    Can.LetRec ds body -> concatMap def ds ++ expr body
    Can.LetDestruct _ bound body -> expr bound ++ expr body
    Can.Case scrutinee branches ->
      expr scrutinee ++ concatMap (\(Can.CaseBranch _ b) -> expr b) branches
    Can.Access record _ -> expr record
    Can.Update record fields ->
      expr record ++ concatMap (\(Can.FieldUpdate _ v) -> expr v) (Map.elems fields)
    Can.Record fields -> concatMap expr (Map.elems fields)
    _ -> []
