{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module Type.Solve
  ( run,
    Solved (..),
  )
where

import AST.Canonical qualified as Can
import Control.Monad
import Data.Map.Strict ((!))
import Data.Map.Strict qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name qualified as Name
import Data.NonEmptyList qualified as NE
import Data.Vector qualified as Vector
import Data.Vector.Mutable qualified as MVector
import Reporting.Annotation qualified as A
import Reporting.Error.Type qualified as Error
import Reporting.Render.Type qualified as RT
import Reporting.Render.Type.Localizer qualified as L
import Type.Class qualified as Class
import Type.Error qualified as ET
import Type.Occurs qualified as Occurs
import Type.Type as Type
import Type.Unify qualified as Unify
import Type.UnionFind qualified as UF

-- RUN SOLVER

run :: Constraint -> IO (Either (NE.List Error.Error) Solved)
run constraint =
  do
    pools <- MVector.replicate 8 []

    (State env mark errors nodes) <-
      solve Map.empty outermostRank pools emptyState constraint

    case errors of
      [] ->
        do
          -- The second of defaulting's two moments; see 'defaultAmbiguous'.
          defaultStuck (nextMark mark) (Map.elems env) (Map.elems nodes)
          annotations <- traverse Type.toAnnotation env
          nodeTypes <- Type.toNodeTypes nodes
          return (Right (Solved annotations nodeTypes))
      e : es ->
        return $ Left (NE.List e es)

-- | What a successful solve produces.
--
-- The annotations are the generalized types of the module's top-level
-- definitions, which is all anything before Core wanted. The node types are
-- one entry per expression node, which is what a typed Core needs and what
-- nothing used to compute (`docs/m1a-node-types.md`).
data Solved = Solved
  { _annotations :: Map.Map Name.Name Can.Annotation,
    _nodeTypes :: Map.Map Can.NodeId Can.Type
  }

emptyState :: State
emptyState =
  State Map.empty (nextMark noMark) [] Map.empty

-- SOLVER

type Env =
  Map.Map Name.Name Variable

type Pools =
  MVector.IOVector [Variable]

data State = State
  { _env :: Env,
    _mark :: Mark,
    _errors :: [Error.Error],
    -- | The constraint-level type recorded for each expression node, zonked
    -- once at the end of the solve rather than as it is recorded — a node's
    -- type is not final until everything that can unify with it has run.
    _nodes :: Map.Map Can.NodeId Type
  }

solve :: Env -> Int -> Pools -> State -> Constraint -> IO State
solve env rank pools state constraint =
  case constraint of
    CTrue ->
      return state
    CSaveTheEnvironment ->
      return (state {_env = env})
    CEqual region category tipe expectation ->
      do
        actual <- typeToVariable rank pools tipe
        expected <- expectedToVariable rank pools expectation
        answer <- Unify.unify actual expected
        case answer of
          Unify.Ok vars ->
            do
              introduce rank pools vars
              return state
          Unify.Err vars actualType expectedType ->
            do
              introduce rank pools vars
              return $
                addError state $
                  Error.BadExpr region category actualType $
                    Error.typeReplace expectation expectedType
    CLocal region name expectation ->
      do
        actual <- makeCopy rank pools (env ! name)
        expected <- expectedToVariable rank pools expectation
        answer <- Unify.unify actual expected
        case answer of
          Unify.Ok vars ->
            do
              introduce rank pools vars
              return state
          Unify.Err vars actualType expectedType ->
            do
              introduce rank pools vars
              return $
                addError state $
                  Error.BadExpr region (Error.Local name) actualType $
                    Error.typeReplace expectation expectedType
    CForeign region name (Can.Forall freeVars srcType) expectation ->
      do
        actual <- srcTypeToVariable rank pools freeVars srcType
        expected <- expectedToVariable rank pools expectation
        answer <- Unify.unify actual expected
        case answer of
          Unify.Ok vars ->
            do
              introduce rank pools vars
              return state
          Unify.Err vars actualType expectedType ->
            do
              introduce rank pools vars
              return $
                addError state $
                  Error.BadExpr region (Error.Foreign name) actualType $
                    Error.typeReplace expectation expectedType
    CPattern region category tipe expectation ->
      do
        actual <- typeToVariable rank pools tipe
        expected <- patternExpectationToVariable rank pools expectation
        answer <- Unify.unify actual expected
        case answer of
          Unify.Ok vars ->
            do
              introduce rank pools vars
              return state
          Unify.Err vars actualType expectedType ->
            do
              introduce rank pools vars
              return $
                addError state $
                  Error.BadPattern
                    region
                    category
                    actualType
                    (Error.ptypeReplace expectation expectedType)
    CNode nid tipe ->
      -- Recording only. Nothing is unified and no variable is allocated, so a
      -- CNode cannot change what typechecks or what generalizes.
      return state {_nodes = Map.insert nid tipe (_nodes state)}
    CAnd constraints ->
      foldM (solve env rank pools) state constraints
    CLet [] flexs _ headerCon CTrue ->
      do
        introduce rank pools flexs
        solve env rank pools state headerCon
    CLet [] [] header headerCon subCon ->
      do
        state1 <- solve env rank pools state headerCon
        locals <- traverse (A.traverse (typeToVariable rank pools)) header
        let newEnv = Map.union env (Map.map A.toValue locals)
        state2 <- solve newEnv rank pools state1 subCon
        foldM occurs state2 $ Map.toList locals
    CLet rigids flexs header headerCon subCon ->
      do
        -- work in the next pool to localize header
        let nextRank = rank + 1
        let poolsLength = MVector.length pools
        nextPools <-
          if nextRank < poolsLength
            then return pools
            else MVector.grow pools poolsLength

        -- introduce variables
        let vars = rigids ++ flexs
        forM_ vars $ \var ->
          UF.modify var $ \(Descriptor content _ mark copy) ->
            Descriptor content nextRank mark copy
        MVector.write nextPools nextRank vars

        -- run solver in next pool
        locals <- traverse (A.traverse (typeToVariable nextRank nextPools)) header
        (State savedEnv mark errors nodes) <-
          solve env nextRank nextPools state headerCon

        let youngMark = mark
        let visitMark = nextMark youngMark
        let headerMark = nextMark visitMark
        let finalMark = nextMark headerMark

        -- pop pool
        generalized <- generalize youngMark visitMark nextRank nextPools
        MVector.write nextPools nextRank []

        -- close the ambiguous constrained variables (`classes.md` §0)
        defaultAmbiguous headerMark (map A.toValue (Map.elems locals)) generalized

        -- check that things went well
        mapM_ isGeneric rigids

        let newEnv = Map.union env (Map.map A.toValue locals)
        let tempState = State savedEnv finalMark errors nodes
        newState <- solve newEnv rank nextPools tempState subCon

        foldM occurs newState (Map.toList locals)

-- Check that a variable has rank == noRank, meaning that it can be generalized.
isGeneric :: Variable -> IO ()
isGeneric var =
  do
    (Descriptor _ rank _ _) <- UF.get var
    if rank == noRank
      then return ()
      else do
        tipe <- Type.toErrorType var
        error $
          "You ran into a compiler bug. Here are some details for the developers:\n\n"
            ++ "    "
            ++ show (ET.toDoc L.empty RT.None tipe)
            ++ " [rank = "
            ++ show rank
            ++ "]\n\n"
            ++ "Please create an <http://sscce.org/> and then report it\n\
               \at <https://github.com/gren-lang/compiler/issues>\n\n"

-- EXPECTATIONS TO VARIABLE

expectedToVariable :: Int -> Pools -> Error.Expected Type -> IO Variable
expectedToVariable rank pools expectation =
  typeToVariable rank pools $
    case expectation of
      Error.NoExpectation tipe ->
        tipe
      Error.FromContext _ _ tipe ->
        tipe
      Error.FromAnnotation _ _ _ tipe ->
        tipe

patternExpectationToVariable :: Int -> Pools -> Error.PExpected Type -> IO Variable
patternExpectationToVariable rank pools expectation =
  typeToVariable rank pools $
    case expectation of
      Error.PNoExpectation tipe ->
        tipe
      Error.PFromContext _ _ tipe ->
        tipe

-- ERROR HELPERS

addError :: State -> Error.Error -> State
addError (State savedEnv rank errors nodes) err =
  State savedEnv rank (err : errors) nodes

-- OCCURS CHECK

occurs :: State -> (Name.Name, A.Located Variable) -> IO State
occurs state (name, A.At region variable) =
  do
    hasOccurred <- Occurs.occurs variable
    if hasOccurred
      then do
        errorType <- Type.toErrorType variable
        (Descriptor _ rank mark copy) <- UF.get variable
        UF.set variable (Descriptor Error rank mark copy)
        return $ addError state (Error.InfiniteType region name errorType)
      else return state

-- GENERALIZE

-- | Every variable has rank less than or equal to the maxRank of the pool.
-- This sorts variables into the young and old pools accordingly.
--
-- __Returns the variables it generalized__, which is what 'defaultAmbiguous'
-- needs and the only reason this is not @IO ()@. They are the candidates and
-- not the answer: a generalized variable is ambiguous only if the header does
-- not mention it, which is a question this function has no way to ask.
generalize :: Mark -> Mark -> Int -> Pools -> IO [Variable]
generalize youngMark visitMark youngRank pools =
  do
    youngVars <- MVector.read pools youngRank
    rankTable <- poolToRankTable youngMark youngRank youngVars

    -- get the ranks right for each entry.
    -- start at low ranks so that we only have to pass
    -- over the information once.
    Vector.imapM_
      (\rank table -> mapM_ (adjustRank youngMark visitMark rank) table)
      rankTable

    -- For variables that have rank lowerer than youngRank, register them in
    -- the appropriate old pool if they are not redundant.
    Vector.forM_ (Vector.unsafeInit rankTable) $ \vars ->
      forM_ vars $ \var ->
        do
          isRedundant <- UF.redundant var
          if isRedundant
            then return ()
            else do
              (Descriptor _ rank _ _) <- UF.get var
              MVector.modify pools (var :) rank

    -- For variables with rank youngRank
    --   If rank < youngRank: register in oldPool
    --   otherwise generalize
    fmap Maybe.catMaybes $
      forM (Vector.unsafeLast rankTable) $ \var ->
        do
          isRedundant <- UF.redundant var
          if isRedundant
            then return Nothing
            else do
              (Descriptor content rank mark copy) <- UF.get var
              if rank < youngRank
                then do
                  MVector.modify pools (var :) rank
                  return Nothing
                else do
                  UF.set var $ Descriptor content noRank mark copy
                  return (Just var)

-- DEFAULTING

-- | `classes.md` §0: an ambiguous constrained variable takes the default.
--
-- __What ambiguous means here.__ A variable this generalization made generic
-- and the header does not mention is one nothing will ever instantiate: it is
-- not part of any definition's type, so no use site can pin it down and no
-- later constraint can reach it. If it carries classes, it is stuck at
-- @number@ forever, which is the state §G23.5 measured — `same 3 3` reports
-- `UNCONSTRAINED TYPE VARIABLE` naming `number`, because a variable is not
-- something an instance can be picked by.
--
-- __Why the header is the whole test.__ Reachability from the header is what
-- separates the ambiguous case from the legitimately polymorphic one, and the
-- difference is not academic: an unannotated @zero = 0@ generalizes to
-- @number@, its variable /is/ the header's, and defaulting it would make
-- @zero@ an @Int@ and @zero + 1.5@ an error. §0 says an exported polymorphic
-- numeric constant is not an ambiguity case; this is that sentence, and it is
-- also why a __rigid__ variable is not a candidate. A rigid one is the
-- annotation's, so `zero : Num a => a` keeps its @a@ by construction rather
-- than by a rule about annotations.
--
-- __Marks, not a set.__ The reachable variables are marked, exactly as
-- 'adjustRank' marks the ones it has visited, because 'Variable' is a
-- union-find point with no ordering to put in a set and because the mark
-- doubles as the cycle guard a recursive type needs.
defaultAmbiguous :: Mark -> [Variable] -> [Variable] -> IO ()
defaultAmbiguous headerMark headerVars generalized =
  do
    mapM_ (markReachable headerMark) headerVars
    forM_ generalized $ \var ->
      do
        (Descriptor content _ mark copy) <- UF.get var
        case content of
          FlexSuper classes _
            | mark /= headerMark,
              Just (home, name) <- Class.defaultsTo classes ->
                -- `outermostRank`, not the `noRank` it was just given: the
                -- variable is a closed type now, so 'makeCopyHelp' should share
                -- it rather than copy one per use, which is the rank a concrete
                -- nullary type has anyway ('adjustRankContent' on an `App1` with
                -- no arguments).
                UF.set var $ Descriptor (Structure (App1 home name [])) outermostRank mark copy
          _ ->
            return ()

-- | The other moment: a constrained variable the whole solve left stuck.
--
-- __Why one moment is not enough.__ 'defaultAmbiguous' fires where a rank is
-- popped, and the most ordinary program in the language never pops one. An
-- annotated definition whose type has no variables — @main : String@ — is a
-- @CLet [] [] header ...@, which solves its body at the /current/ rank and
-- generalizes nothing. So the @number@ in @same 3 3@ inside such a definition
-- is never young, never generalized, and never seen by the other moment. This
-- was measured before it was written down: with only the generalization-time
-- rule in place, `same 3 3` still reported `UNCONSTRAINED TYPE VARIABLE`, and
-- not one 'FlexSuper' reached 'generalize' in the whole module.
--
-- __One rule, two witnesses that nothing can reach a variable.__ At a
-- generalization it is that the header does not mention it. Here it is that the
-- module's environment does not mention it and generalization never made it
-- generic — the solve is over, so a variable no published type contains is one
-- nothing can unify with and nothing can instantiate.
--
-- __The @noRank@ half of that test is what protects a local polymorphic
-- binding.__ @let n = 1 in …@ generalizes @n@ to @number@ and each use
-- instantiates a copy; the generic variable is in no top-level type, so the
-- environment test alone would default it and leave a binder typed @Int@ under
-- uses typed @Float@. It was already generalized, so it is somebody's, and it
-- is left alone.
--
-- The sweep is over the recorded node types because that — with the annotations,
-- which come out of the same environment — is everything anything downstream
-- reads. A variable in neither is one no one asks about.
defaultStuck :: Mark -> [Variable] -> [Type] -> IO ()
defaultStuck mark envVars nodeTypes =
  do
    mapM_ (markReachable mark) envVars
    mapM_ (sweepType mark) nodeTypes

-- | Walk a recorded node type down to its variables.
sweepType :: Mark -> Type -> IO ()
sweepType mark tipe =
  case tipe of
    PlaceHolder _ -> return ()
    AliasN _ _ args realType ->
      mapM_ (sweepType mark . snd) args >> sweepType mark realType
    VarN var -> sweepVar mark var
    AppN _ _ args -> mapM_ (sweepType mark) args
    FunN arg result -> sweepType mark arg >> sweepType mark result
    EmptyRecordN -> return ()
    RecordN fields ext ->
      mapM_ (sweepType mark) (Map.elems fields) >> sweepType mark ext

-- | Default one variable if it is stuck, and walk what is under it.
--
-- The mark does double duty, as it does in 'adjustRank': a variable the
-- environment reached carries it already and is skipped, and a variable this
-- sweep has handled carries it afterwards. Both mean "not a candidate", so one
-- mark says both and the walk terminates on a recursive type.
sweepVar :: Mark -> Variable -> IO ()
sweepVar mark var =
  do
    (Descriptor content rank varMark copy) <- UF.get var
    if varMark == mark
      then return ()
      else do
        UF.set var (Descriptor content rank mark copy)
        case content of
          FlexSuper classes _
            | rank /= noRank,
              Just (home, name) <- Class.defaultsTo classes ->
                UF.set var $ Descriptor (Structure (App1 home name [])) outermostRank mark copy
          Structure flatType ->
            () <$ traverseFlatType (\v -> sweepVar mark v >> return v) flatType
          Alias _ _ args realType ->
            do
              mapM_ (sweepVar mark . snd) args
              sweepVar mark realType
          _ ->
            return ()

-- | Mark a variable and everything under it, for 'defaultAmbiguous'.
markReachable :: Mark -> Variable -> IO ()
markReachable headerMark var =
  do
    (Descriptor content rank mark copy) <- UF.get var
    if mark == headerMark
      then return ()
      else do
        UF.set var (Descriptor content rank headerMark copy)
        case content of
          Structure flatType ->
            () <$ traverseFlatType (\v -> markReachable headerMark v >> return v) flatType
          Alias _ _ args realType ->
            do
              mapM_ (markReachable headerMark . snd) args
              markReachable headerMark realType
          _ ->
            return ()

poolToRankTable :: Mark -> Int -> [Variable] -> IO (Vector.Vector [Variable])
poolToRankTable youngMark youngRank youngInhabitants =
  do
    mutableTable <- MVector.replicate (youngRank + 1) []

    -- Sort the youngPool variables into buckets by rank.
    forM_ youngInhabitants $ \var ->
      do
        (Descriptor content rank _ copy) <- UF.get var
        UF.set var (Descriptor content rank youngMark copy)
        MVector.modify mutableTable (var :) rank

    Vector.unsafeFreeze mutableTable

-- ADJUST RANK

--
-- Adjust variable ranks such that ranks never increase as you move deeper.
-- This way the outermost rank is representative of the entire structure.
--
adjustRank :: Mark -> Mark -> Int -> Variable -> IO Int
adjustRank youngMark visitMark groupRank var =
  do
    (Descriptor content rank mark copy) <- UF.get var
    if mark == youngMark
      then do
        -- Set the variable as marked first because it may be cyclic.
        UF.set var $ Descriptor content rank visitMark copy
        maxRank <- adjustRankContent youngMark visitMark groupRank content
        UF.set var $ Descriptor content maxRank visitMark copy
        return maxRank
      else
        if mark == visitMark
          then return rank
          else do
            let minRank = min groupRank rank
            -- TODO how can minRank ever be groupRank?
            UF.set var $ Descriptor content minRank visitMark copy
            return minRank

adjustRankContent :: Mark -> Mark -> Int -> Content -> IO Int
adjustRankContent youngMark visitMark groupRank content =
  let go = adjustRank youngMark visitMark groupRank
   in case content of
        FlexVar _ ->
          return groupRank
        FlexSuper _ _ ->
          return groupRank
        RigidVar _ ->
          return groupRank
        RigidSuper _ _ ->
          return groupRank
        Structure flatType ->
          case flatType of
            App1 _ _ args ->
              foldM (\rank arg -> max rank <$> go arg) outermostRank args
            Fun1 arg result ->
              max <$> go arg <*> go result
            EmptyRecord1 ->
              -- THEORY: an empty record never needs to get generalized
              return outermostRank
            Record1 fields extension ->
              do
                extRank <- go extension
                foldM (\rank field -> max rank <$> go field) extRank fields
        Alias _ _ args _ ->
          -- THEORY: anything in the realVar would be outermostRank
          foldM (\rank (_, argVar) -> max rank <$> go argVar) outermostRank args
        Error ->
          return groupRank

-- REGISTER VARIABLES

introduce :: Int -> Pools -> [Variable] -> IO ()
introduce rank pools variables =
  do
    MVector.modify pools (variables ++) rank
    forM_ variables $ \var ->
      UF.modify var $ \(Descriptor content _ mark copy) ->
        Descriptor content rank mark copy

-- TYPE TO VARIABLE

typeToVariable :: Int -> Pools -> Type -> IO Variable
typeToVariable rank pools tipe =
  typeToVar rank pools Map.empty tipe

-- PERF working with @mgriffith we noticed that a 784 line entry in a `let` was
-- causing a ~1.5 second slowdown. Moving it to the top-level to be a function
-- saved all that time. The slowdown seems to manifest in `typeToVar` and in
-- `register` in particular. Have not explored further yet. Top-level definitions
-- are recommended in cases like this anyway, so there is at least a safety
-- valve for now.
--
typeToVar :: Int -> Pools -> Map.Map Name.Name Variable -> Type -> IO Variable
typeToVar rank pools aliasDict tipe =
  let go = typeToVar rank pools aliasDict
   in case tipe of
        VarN v ->
          return v
        AppN home name args ->
          do
            argVars <- traverse go args
            register rank pools (Structure (App1 home name argVars))
        FunN a b ->
          do
            aVar <- go a
            bVar <- go b
            register rank pools (Structure (Fun1 aVar bVar))
        AliasN home name args aliasType ->
          do
            argVars <- traverse (traverse go) args
            aliasVar <- typeToVar rank pools (Map.fromList argVars) aliasType
            register rank pools (Alias home name argVars aliasVar)
        PlaceHolder name ->
          return (aliasDict ! name)
        RecordN fields ext ->
          do
            fieldVars <- traverse go fields
            extVar <- go ext
            register rank pools (Structure (Record1 fieldVars extVar))
        EmptyRecordN ->
          register rank pools emptyRecord1

register :: Int -> Pools -> Content -> IO Variable
register rank pools content =
  do
    var <- UF.fresh (Descriptor content rank noMark Nothing)
    MVector.modify pools (var :) rank
    return var

emptyRecord1 :: Content
emptyRecord1 =
  Structure EmptyRecord1

-- SOURCE TYPE TO VARIABLE

-- | An annotation's bound variables become unification variables, under the
-- constraints the annotation was written with.
--
-- __This is where §G21.3's unenforced promise is spent__ (D135). It read the
-- variable's *name* through verbs 3 to 6, because `Class.Class` was an enum of
-- names no module declared; `Basics` declares the closed ones now, so
-- `Class.fromContext` reads the resolved constraint list and `Num a =>` is
-- enforced here, by unification, at the definition and at every use of it.
--
-- An /open/ class in the list leaves the variable flexible on purpose. It is
-- `Type.Resolve`'s to discharge and D130 is the rule: the two mechanisms divide
-- here and nowhere else.
srcTypeToVariable :: Int -> Pools -> Can.FreeVars -> Can.Type -> IO Variable
srcTypeToVariable rank pools freeVars srcType =
  let nameToContent name constraints =
        maybe (FlexVar (Just name)) (\classes -> FlexSuper classes (Just name)) (classesOf constraints)

      makeVar name constraints =
        UF.fresh (Descriptor (nameToContent name constraints) rank noMark Nothing)
   in do
        flexVars <- Map.traverseWithKey makeVar freeVars
        MVector.modify pools (Map.elems flexVars ++) rank
        srcTypeToVar rank pools flexVars srcType

srcTypeToVar :: Int -> Pools -> Map.Map Name.Name Variable -> Can.Type -> IO Variable
srcTypeToVar rank pools flexVars srcType =
  let go = srcTypeToVar rank pools flexVars
   in case srcType of
        Can.TLambda argument result ->
          do
            argVar <- go argument
            resultVar <- go result
            register rank pools (Structure (Fun1 argVar resultVar))
        Can.TVar name ->
          return (flexVars ! name)
        Can.TType home name args ->
          do
            argVars <- traverse go args
            register rank pools (Structure (App1 home name argVars))
        Can.TRecord fields maybeExt ->
          do
            fieldVars <- traverse (srcFieldTypeToVar rank pools flexVars) fields
            extVar <-
              case maybeExt of
                Nothing -> register rank pools emptyRecord1
                Just ext -> return (flexVars ! ext)
            register rank pools (Structure (Record1 fieldVars extVar))
        Can.TAlias home name args aliasType ->
          do
            argVars <- traverse (traverse go) args
            aliasVar <-
              case aliasType of
                Can.Holey tipe ->
                  srcTypeToVar rank pools (Map.fromList argVars) tipe
                Can.Filled tipe ->
                  go tipe

            register rank pools (Alias home name argVars aliasVar)

srcFieldTypeToVar :: Int -> Pools -> Map.Map Name.Name Variable -> Can.FieldType -> IO Variable
srcFieldTypeToVar rank pools flexVars (Can.FieldType _ srcTipe) =
  srcTypeToVar rank pools flexVars srcTipe

-- COPY

makeCopy :: Int -> Pools -> Variable -> IO Variable
makeCopy rank pools var =
  do
    copy <- makeCopyHelp rank pools var
    restore var
    return copy

makeCopyHelp :: Int -> Pools -> Variable -> IO Variable
makeCopyHelp maxRank pools variable =
  do
    (Descriptor content rank _ maybeCopy) <- UF.get variable

    case maybeCopy of
      Just copy ->
        return copy
      Nothing ->
        if rank /= noRank
          then return variable
          else do
            let makeDescriptor c = Descriptor c maxRank noMark Nothing
            copy <- UF.fresh $ makeDescriptor content
            MVector.modify pools (copy :) maxRank

            -- Link the original variable to the new variable. This lets us
            -- avoid making multiple copies of the variable we are instantiating.
            --
            -- Need to do this before recursively copying to avoid looping.
            UF.set variable $
              Descriptor content rank noMark (Just copy)

            -- Now we recursively copy the content of the variable.
            -- We have already marked the variable as copied, so we
            -- will not repeat this work or crawl this variable again.
            case content of
              Structure term ->
                do
                  newTerm <- traverseFlatType (makeCopyHelp maxRank pools) term
                  UF.set copy $ makeDescriptor (Structure newTerm)
                  return copy
              FlexVar _ ->
                return copy
              FlexSuper _ _ ->
                return copy
              RigidVar name ->
                do
                  UF.set copy $ makeDescriptor $ FlexVar (Just name)
                  return copy
              RigidSuper super name ->
                do
                  UF.set copy $ makeDescriptor $ FlexSuper super (Just name)
                  return copy
              Alias home name args realType ->
                do
                  newArgs <- mapM (traverse (makeCopyHelp maxRank pools)) args
                  newRealType <- makeCopyHelp maxRank pools realType
                  UF.set copy $ makeDescriptor (Alias home name newArgs newRealType)
                  return copy
              Error ->
                return copy

-- RESTORE

restore :: Variable -> IO ()
restore variable =
  do
    (Descriptor content _ _ maybeCopy) <- UF.get variable
    case maybeCopy of
      Nothing ->
        return ()
      Just _ ->
        do
          UF.set variable $ Descriptor content noRank noMark Nothing
          restoreContent content

restoreContent :: Content -> IO ()
restoreContent content =
  case content of
    FlexVar _ ->
      return ()
    FlexSuper _ _ ->
      return ()
    RigidVar _ ->
      return ()
    RigidSuper _ _ ->
      return ()
    Structure term ->
      case term of
        App1 _ _ args ->
          mapM_ restore args
        Fun1 arg result ->
          do
            restore arg
            restore result
        EmptyRecord1 ->
          return ()
        Record1 fields ext ->
          do
            mapM_ restore fields
            restore ext
    Alias _ _ args var ->
      do
        mapM_ (traverse restore) args
        restore var
    Error ->
      return ()

-- TRAVERSE FLAT TYPE

traverseFlatType :: (Variable -> IO Variable) -> FlatType -> IO FlatType
traverseFlatType f flatType =
  case flatType of
    App1 home name args ->
      liftM (App1 home name) (traverse f args)
    Fun1 a b ->
      liftM2 Fun1 (f a) (f b)
    EmptyRecord1 ->
      pure EmptyRecord1
    Record1 fields ext ->
      liftM2 Record1 (traverse f fields) (f ext)
