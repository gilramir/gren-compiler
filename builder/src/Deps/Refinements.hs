-- | The refinement half of comparing two versions of a package (geng-lang
-- @m4-refine.md@ §RF29, D810, D855).
--
-- The type comparison is 'Deps.Diff''s. A value whose erased type is the same
-- in both versions and whose signature's names or predicates are not is
-- decided by the refinement checker, which is a Geng package the CLI runs
-- (D826), so @geng package diff@, @bump@ and @validate@ are run in two
-- processes as a refined build is (D833). The CLI's first asks with
-- @GENG_REFINE_STAGE=dir@: each version's Core of the modules those values are
-- in goes to @dir/old@ and @dir/new@, the values to @dir/values@, a line each,
-- and the command stops with nothing printed. The CLI decides each value and
-- asks again with @GENG_REFINE_VERDICTS@ naming the file it wrote, and that run
-- is the command. With no such value the first run is the command, except
-- @bump@'s, which stops anyway: its question reads our input, and only the
-- last run is given it.
--
-- __Neither variable set__, the binary run by itself, leaves each such value
-- MAJOR, with a line saying it was not compared.
module Deps.Refinements
  ( Outcome (..),
    decide,
  )
where

import Core.AST qualified as Core
import Core.Dump qualified as Dump
import Core.Wire qualified as Wire
import Data.ByteString.Builder qualified as B
import Data.Char qualified as Char
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Name qualified as Name
import Data.Set qualified as Set
import Deps.Diff qualified as Diff
import Gren.Docs qualified as Docs
import Gren.Magnitude qualified as M
import Gren.ModuleName qualified as ModuleName
import System.Environment qualified as Env
import System.FilePath ((</>))

-- | Whether the command goes on, and with which verdicts.
data Outcome
  = Stopped
  | Decided Diff.Verdicts

-- | The verdicts for comparing @old@ with @new@, or a stop for the checker.
-- @alwaysStop@ is @bump@'s, and @validate@'s when its first run stopped for the
-- version's own goals (D858).
decide :: Bool -> (Docs.Documentation, [Core.Module]) -> (Docs.Documentation, [Core.Module]) -> IO Outcome
decide alwaysStop (oldDocs, oldCores) (newDocs, newCores) =
  do
    let candidates = Diff.refinementCandidates oldDocs newDocs
    stage <- nonEmpty "GENG_REFINE_STAGE"
    given <- nonEmpty "GENG_REFINE_VERDICTS"
    case (given, stage) of
      (Just file, _) ->
        Decided . parseVerdicts <$> readFile file
      (Nothing, Just dir)
        | alwaysStop || not (null candidates) ->
            do
              let homes = Set.fromList (map fst candidates)
              writeCores (dir </> "old") homes oldCores
              writeCores (dir </> "new") homes newCores
              writeFile (dir </> "values") (unlines [Name.toChars home ++ " " ++ Name.toChars name | (home, name) <- candidates])
              return Stopped
      _ ->
        return (Decided Map.empty)

nonEmpty :: String -> IO (Maybe String)
nonEmpty name =
  do
    value <- Env.lookupEnv name
    return $ case value of
      Just v | v /= "" -> Just v
      _ -> Nothing

-- | The Core of each module in @homes@, as @GENG_DUMP_WIRE@ writes it.
writeCores :: FilePath -> Set.Set ModuleName.Raw -> [Core.Module] -> IO ()
writeCores dir homes cores =
  mapM_ write [m | m <- cores, Set.member (ModuleName._module (Core._moduleName m)) homes]
  where
    write m =
      case Wire.encode m of
        Left problems ->
          error (unlines ("Core.Wire:" : problems))
        Right encoded ->
          Dump.writeWire dir (Core._moduleName m) (B.byteString encoded)

-- | The CLI's verdicts: a line @Module value MAGNITUDE@ for each value, and
-- under it, indented, each line of why.
parseVerdicts :: String -> Diff.Verdicts
parseVerdicts text =
  Map.fromList (go (lines text))
  where
    go ls =
      case ls of
        [] -> []
        l : rest ->
          let (why, after) = List.span (\x -> take 1 x == " ") rest
           in case words l of
                [home, name, magnitude] ->
                  ((Name.fromChars home, Name.fromChars name), Diff.Verdict (toMagnitude magnitude) (map (dropWhile Char.isSpace) why)) : go after
                _ ->
                  go after

    toMagnitude m =
      case m of
        "PATCH" -> M.PATCH
        "MINOR" -> M.MINOR
        _ -> M.MAJOR
