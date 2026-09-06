{-# OPTIONS_GHC -Wall #-}

-- | Is this module's @main@ one the compiler can generate an entry point for?
--
-- Three rejections, all of them @Reporting.Error.Main@'s, and all three used to
-- be made on the way past by @Optimize.Module@ — the only user-facing check the
-- old pipeline owned. Retiring that pipeline meant giving them a home that is
-- about the question rather than about the graph, which is this one, beside
-- `Nitpick.PatternMatches` and `Nitpick.Debug`.
--
-- The classification is not repeated here. `Core.Lower.Module.mainOf` is the one
-- statement of what a @main@ may be (C19); this reads its answer and supplies
-- the region, which a type alone does not have.
module Nitpick.Main
  ( check,
  )
where

import AST.Canonical qualified as Can
import Core.Lower.Module qualified as Lower
import Data.Map qualified as Map
import Data.Name (Name)
import Data.Name qualified as Name
import Gren.Platform qualified as P
import Reporting.Annotation qualified as A
import Reporting.Error.Main qualified as E

-- | The module's declarations, in the order they are elaborated in.
--
-- The order matters for exactly one pair of answers: a @main@ inside a recursive
-- group is a 'E.BadCycle' and is never asked what its type is, so
-- @main : String -> String@ in a cycle reports the cycle rather than the type.
-- @Optimize.Module.addDecls@ chose the same way, by reaching @DeclareRec@ before
-- it reached the definition.
check :: P.Platform -> Map.Map Name Can.Annotation -> Can.Module -> Either E.Error ()
check platform annotations modul =
  go (Can._decls modul)
  where
    go decls =
      case decls of
        Can.Declare def subDecls ->
          case defName def of
            name
              | name == Name._main -> mainType (defRegion def) >> go subDecls
              | otherwise -> go subDecls
        Can.DeclareRec d ds subDecls ->
          case filter ((== Name._main) . defName) (d : ds) of
            [] -> go subDecls
            main : _ ->
              Left (E.BadCycle (defRegion main) (defName d) (map defName ds))
        Can.SaveTheEnvironment ->
          Right ()

    mainType region =
      case Lower.mainOf platform annotations of
        Lower.NoMain -> Right ()
        Lower.IsMain _ -> Right ()
        Lower.NotRunnable tipe allowed -> Left (E.BadType region tipe allowed)
        Lower.BadFlags subType invalidPayload ->
          Left (E.BadFlags region subType invalidPayload)

defName :: Can.Def -> Name
defName def =
  case def of
    Can.Def _ (A.At _ name) _ _ -> name
    Can.TypedDef (A.At _ name) _ _ _ _ -> name

defRegion :: Can.Def -> A.Region
defRegion def =
  case def of
    Can.Def _ (A.At region _) _ _ -> region
    Can.TypedDef (A.At region _) _ _ _ _ -> region
