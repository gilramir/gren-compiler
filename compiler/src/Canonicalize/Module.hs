{-# OPTIONS_GHC -Wall #-}

module Canonicalize.Module
  ( canonicalize,
    importedInstances,
  )
where

import AST.Canonical qualified as Can
import AST.Source qualified as Src
import Canonicalize.Derive qualified as Derive
import Canonicalize.Effects qualified as Effects
import Canonicalize.Environment qualified as Env
import Canonicalize.Environment.Dups qualified as Dups
import Canonicalize.Environment.Foreign qualified as Foreign
import Canonicalize.Environment.Local qualified as Local
import Canonicalize.Expression qualified as Expr
import Canonicalize.Implicit qualified as Implicit
import Canonicalize.Instance qualified as Instance
import Canonicalize.Pattern qualified as Pattern
import Canonicalize.Type qualified as Type
import Control.Monad (foldM)
import Core.Extern qualified as Extern
import Core.Lower.Type qualified as LowerType
import Data.Char qualified as Char
import Data.Graph qualified as Graph
import Data.Index qualified as Index
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name qualified as Name
import Gren.Interface qualified as I
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Gren.String qualified as ES
import Reporting.Annotation qualified as A
import Reporting.Error.Canonicalize qualified as Error
import Reporting.Result qualified as Result
import Reporting.Warning qualified as W
import Type.Class qualified as Class

-- RESULT

type Result i w a =
  Result.Result i w Error.Error a

-- MODULES

canonicalize :: Pkg.Name -> Map.Map ModuleName.Raw I.Interface -> Src.Module -> Result i [W.Warning] Can.Module
canonicalize pkg ifaces modul@(Src.Module _ exports docs imports valuesWithSourceOrder classes instances unions _ (_, binops) _ _ effects) =
  do
    checkClassesAreFirstParty pkg (fmap snd classes)

    let values = fmap snd valuesWithSourceOrder
    let home = ModuleName.Canonical pkg (Src.getName modul)
    let cbinops = Map.fromList (map canonicalizeBinop binops)

    (env, cunions, caliases, cclasses) <-
      Local.add modul
        =<< Foreign.createInitialEnv home ifaces (fmap snd imports)

    cvalues <- canonicalizeValues env values
    ceffects <- Effects.canonicalize env values cunions effects
    cexports <- canonicalizeExports values cunions caliases cclasses cbinops ceffects exports

    -- Derived instances first, so that a hand-written one for the same type and
    -- class is the duplicate: the author wrote that one, so the error can point
    -- at code they can see.
    derived <- deriveInstances home ifaces env cexports cunions (fmap snd unions)
    written <- Instance.canonicalizeInto pkg (importedInstances ifaces) env derived (fmap snd instances)

    -- Last, so that a written or `@derive`d instance is already in the map and
    -- the implicit rule can see that this type is spoken for (§G37).
    cinstances <-
      Implicit.add
        home
        (structuralClasses home ifaces cclasses)
        (boolUnion home ifaces cunions)
        (orderUnion home ifaces cunions)
        cexports
        cunions
        (Map.fromList [(name, region) | A.At region (Src.Union (A.At _ name) _ _ _ _) <- fmap snd unions])
        (importedInstances ifaces)
        written

    checkClosedClassesCovered home (fmap snd classes) cclasses cinstances

    return $ Can.Module home cexports docs cvalues cunions caliases cclasses cinstances cbinops ceffects (externBodies values)

-- | Every member of a closed class this module declares has an instance here.
--
-- §I3's third rule, and §G43.3's lesson applied before it costs anything. A
-- closed class is two statements of the same fact: the membership table in
-- "Type.Class", which the unifier and `classes.md` §0's defaulting read, and
-- the instances `core` writes, which is where the methods actually are. Nothing
-- makes them agree, and the last pair of lists that said the same thing twice
-- came apart for a whole checkpoint.
--
-- The direction checked is the one that breaks a program: a member with no
-- instance is a type the unifier admits and the elaborator cannot find a
-- witness for, which is a `NO INSTANCE` at whatever unlucky call site reaches
-- it first. The other direction cannot happen — an instance whose head is not a
-- member would have to be written in `core`, and 'Type.Class.members' is the
-- list its author was reading.
checkClosedClassesCovered ::
  ModuleName.Canonical ->
  [A.Located Src.Class] ->
  Map.Map Name.Name Can.ClassDecl ->
  Map.Map Can.InstanceKey Can.Instance ->
  Result i w ()
checkClosedClassesCovered home classes cclasses cinstances =
  let regionOf name =
        Maybe.listToMaybe
          [region | A.At _ (Src.Class (A.At region declared) _ _ _) <- classes, declared == name]
      missing =
        [ (region, className, memberName)
        | (className, _) <- Map.toList cclasses,
          Just cls <- [Class.fromDeclared home className],
          Just region <- [regionOf className],
          (memberHome, memberName) <- Class.members cls,
          not (Map.member (Can.InstanceKey (Can.Class home className) memberHome memberName) cinstances)
        ]
   in case missing of
        [] -> Result.ok ()
        (region, className, memberName) : _ ->
          Result.throw (Error.ClosedClassMissingInstance region className memberName)

-- | The instances this module's imports make visible.
--
-- A plain union of what each import publishes, because each of those is
-- already the closure of its own imports (D122) — which is what makes an
-- instance environment assembled from direct imports the transitive one D114
-- asks for, with nothing in the build graph having to know about instances.
importedInstances :: Map.Map ModuleName.Raw I.Interface -> Map.Map Can.InstanceKey Can.InstanceHead
importedInstances ifaces =
  Map.unions (map I._instances (Map.elems ifaces))

-- CLASS DECLARATIONS

-- | `classes.md` §8.3's gate: only a first-party package may declare a class.
--
-- Not a temporary rejection like the two below it, but the restriction §8.4
-- decided M1b ships with, and it lifts when D10 opens rather than when the
-- next verb lands. Classes and instances are gated __together__ and always
-- will be: structural derivation is defined for `Eq`, `Ord` and `Inspect`
-- only, so a user class nobody may write an instance for has no instances at
-- all and is inert.
checkClassesAreFirstParty :: Pkg.Name -> [A.Located Src.Class] -> Result i w ()
checkClassesAreFirstParty pkg classes
  | Pkg.isFirstParty pkg = Result.ok ()
  | otherwise =
      case classes of
        [] ->
          Result.ok ()
        A.At region (Src.Class (A.At _ name) _ _ _) : _ ->
          Result.throw (Error.ClassDeclThirdParty region name)

-- | The instances `@derive` asks for (`classes.md` §2.1, §G25).
--
-- Three things are checked before anything is generated, and they are in this
-- order because each makes the next one meaningful: the type has to be
-- __abstract__, because a transparent one already derives and §8.1 calls
-- asking a redundancy error; a class named twice has one answer written twice;
-- and the class has to resolve, which is `Canonicalize.Type`'s lookup and
-- reports what it reports for a constraint.
deriveInstances ::
  ModuleName.Canonical ->
  Map.Map ModuleName.Raw I.Interface ->
  Env.Env ->
  Can.Exports ->
  Map.Map Name.Name Can.Union ->
  [A.Located Src.Union] ->
  Result i w (Map.Map Can.InstanceKey Can.Instance)
deriveInstances home ifaces env exports cunions unions =
  foldM (deriveOne home ifaces env exports cunions) Map.empty $
    [ (region, name, classes)
    | A.At region (Src.Union (A.At _ name) _ _ classes@(_ : _) _) <- unions
    ]

deriveOne ::
  ModuleName.Canonical ->
  Map.Map ModuleName.Raw I.Interface ->
  Env.Env ->
  Can.Exports ->
  Map.Map Name.Name Can.Union ->
  Map.Map Can.InstanceKey Can.Instance ->
  (A.Region, Name.Name, [A.Located Name.Name]) ->
  Result i w (Map.Map Can.InstanceKey Can.Instance)
deriveOne home ifaces env exports cunions sofar (_, typeName, classNames) =
  case Map.lookup typeName cunions of
    Nothing ->
      -- The union is in `cunions` by construction: both come from the same
      -- declarations, and a duplicate name was reported before this ran.
      Result.ok sofar
    Just union ->
      foldM (deriveClass home ifaces env exports cunions typeName union) sofar classNames

deriveClass ::
  ModuleName.Canonical ->
  Map.Map ModuleName.Raw I.Interface ->
  Env.Env ->
  Can.Exports ->
  Map.Map Name.Name Can.Union ->
  Name.Name ->
  Can.Union ->
  Map.Map Can.InstanceKey Can.Instance ->
  A.Located Name.Name ->
  Result i w (Map.Map Can.InstanceKey Can.Instance)
deriveClass home ifaces env exports cunions typeName union sofar (A.At region className) =
  if not (Can.isAbstract exports typeName)
    then Result.throw (Error.DeriveOnTransparent region typeName className)
    else do
      (cls, decl) <- Env.findClassDecl region env className
      let key = Can.InstanceKey cls home typeName
      if Map.member key sofar
        then Result.throw (Error.DeriveTwice region typeName className)
        else do
          let witness = Instance.witnessNameOf sofar className typeName
          instance_ <-
            Derive.derive home (boolUnion home ifaces cunions) (orderUnion home ifaces cunions) region typeName union cls decl witness
          Result.ok (Map.insert key instance_ sofar)

-- | `Basics.Bool`, which a derived `eq` answers with, and `Basics.Order`,
-- which a derived `compare` answers with.
--
-- Read from the interface rather than from this module's environment, because
-- the generated code is not the author's and must not depend on what they
-- imported or shadowed. `Basics` is compiling itself in the one case the
-- interface is absent, and then its own declarations are where to look — which
-- they had to become with implicit derivation (§G37), because `Basics`'
-- transparent types derive too and `Order` is one of them.
boolUnion :: ModuleName.Canonical -> Map.Map ModuleName.Raw I.Interface -> Map.Map Name.Name Can.Union -> Can.Union
boolUnion =
  basicsUnion Name.bool

orderUnion :: ModuleName.Canonical -> Map.Map ModuleName.Raw I.Interface -> Map.Map Name.Name Can.Union -> Can.Union
orderUnion =
  basicsUnion Name.order

basicsUnion :: Name.Name -> ModuleName.Canonical -> Map.Map ModuleName.Raw I.Interface -> Map.Map Name.Name Can.Union -> Can.Union
basicsUnion name home ifaces localUnions =
  case I._unions <$> Map.lookup Name.basics ifaces of
    Just unions ->
      case Map.lookup name unions >>= I.toPublicUnion of
        Just union -> union
        Nothing -> emptyUnion
    Nothing ->
      if home == ModuleName.basics
        then Map.findWithDefault emptyUnion name localUnions
        else emptyUnion

-- | The stand-in when the union cannot be found at all, which nothing reaches:
-- `Basics` declares both and every other module imports `Basics`.
emptyUnion :: Can.Union
emptyUnion =
  Can.Union [] [] 0 Can.Enum

-- | The classes implicit derivation writes instances for, found the same way
-- `Bool` is and for the same reason.
--
-- Two of `classes.md` §2.1's three, because `Canonicalize.Derive` writes two:
-- `Inspect` joins them when it has a module to be declared in (§G24.3). A
-- class that is absent contributes nothing rather than failing, which is what
-- a `core` that removed one would do and is why this returns a list rather
-- than insisting on both.
structuralClasses ::
  ModuleName.Canonical ->
  Map.Map ModuleName.Raw I.Interface ->
  Map.Map Name.Name Can.ClassDecl ->
  [(Can.Class, Can.ClassDecl)]
structuralClasses home ifaces localClasses =
  [ (Can.Class classHome name, decl)
  | (classHome, moduleName, name) <-
      [ (ModuleName.basics, Name.basics, Name.eqClass),
        (ModuleName.basics, Name.basics, Name.ordClass),
        (ModuleName.inspect, Name.inspectModule, Name.inspectClass)
      ],
    Just decl <- [structuralClassDecl home ifaces localClasses moduleName name]
  ]

-- | One class, from the interface of the module that declares it.
--
-- `Eq` and `Ord` are `Basics`'s and every module imports `Basics`, so they are
-- always found. `Inspect` is its own module's (§G43) and is found only where
-- that module is imported — which is every module outside `core`, because it is
-- a default import, and inside `core` only the modules that ask. That is the
-- rule rather than an accident: `Inspect` names `String`, so everything
-- `String` imports is beneath it and cannot import back, and those types'
-- instances are written in `Inspect` itself.
structuralClassDecl ::
  ModuleName.Canonical ->
  Map.Map ModuleName.Raw I.Interface ->
  Map.Map Name.Name Can.ClassDecl ->
  Name.Name ->
  Name.Name ->
  Maybe Can.ClassDecl
structuralClassDecl home ifaces localClasses moduleName name =
  case I._classes <$> Map.lookup moduleName ifaces of
    Just classes ->
      Map.lookup name classes >>= I.toPublicClass
    Nothing ->
      if ModuleName._module home == moduleName
        then Map.lookup name localClasses
        else Nothing

-- CANONICALIZE BINOP

canonicalizeBinop :: A.Located Src.Infix -> (Name.Name, Can.Binop)
canonicalizeBinop (A.At _ (Src.Infix op associativity precedence func)) =
  (op, Can.Binop_ associativity precedence func)

-- DECLARATIONS / CYCLE DETECTION
--
-- There are two phases of cycle detection:
--
-- 1. Detect cycles using ALL dependencies => needed for type inference
-- 2. Detect cycles using DIRECT dependencies => nonterminating recursion
--

canonicalizeValues :: Env.Env -> [A.Located Src.Value] -> Result i [W.Warning] Can.Decls
canonicalizeValues env values =
  do
    nodes <- traverse (toNodeOne env) values
    detectCycles (Graph.stronglyConnComp nodes)

detectCycles :: [Graph.SCC NodeTwo] -> Result i w Can.Decls
detectCycles sccs =
  case sccs of
    [] ->
      Result.ok Can.SaveTheEnvironment
    scc : otherSccs ->
      case scc of
        Graph.AcyclicSCC (def, _, _) ->
          Can.Declare def <$> detectCycles otherSccs
        Graph.CyclicSCC subNodes ->
          do
            defs <- traverse detectBadCycles (Graph.stronglyConnComp subNodes)
            case defs of
              [] -> detectCycles otherSccs
              d : ds -> Can.DeclareRec d ds <$> detectCycles otherSccs

detectBadCycles :: Graph.SCC Can.Def -> Result i w Can.Def
detectBadCycles scc =
  case scc of
    Graph.AcyclicSCC def ->
      Result.ok def
    Graph.CyclicSCC [] ->
      error "The definition of Data.Graph.SCC should not allow empty CyclicSCC!"
    Graph.CyclicSCC (def : defs) ->
      let (A.At region name) = extractDefName def
          names = map (A.toValue . extractDefName) defs
       in Result.throw (Error.RecursiveDecl region name names)

extractDefName :: Can.Def -> A.Located Name.Name
extractDefName def =
  case def of
    Can.Def _ name _ _ -> name
    Can.TypedDef name _ _ _ _ -> name

-- DECLARATIONS / CYCLE DETECTION SETUP
--
-- toNodeOne and toNodeTwo set up nodes for the two cycle detection phases.
--

-- Phase one nodes track ALL dependencies.
-- This allows us to find cyclic values for type inference.
type NodeOne =
  (NodeTwo, Name.Name, [Name.Name])

-- Phase two nodes track DIRECT dependencies.
-- This allows us to detect cycles that definitely do not terminate.
type NodeTwo =
  (Can.Def, Name.Name, [Name.Name])

toNodeOne :: Env.Env -> A.Located Src.Value -> Result i [W.Warning] NodeOne
toNodeOne env (A.At _ (Src.Value aname@(A.At _ name) srcArgs body maybeType _)) =
  case maybeType of
    Nothing ->
      do
        (args, argBindings) <-
          Pattern.verify (Error.DPFuncArgs name) $
            traverse (Pattern.canonicalize env . snd) srcArgs

        newEnv <-
          Env.addLocals argBindings env

        (cbody, freeLocals) <-
          Expr.verifyBindings W.Pattern argBindings (Expr.canonicalize newEnv body)

        let def = Can.Def Can.unnumbered aname args cbody
        return
          ( toNodeTwo name srcArgs def freeLocals,
            name,
            Map.keys freeLocals
          )
    Just (Src.Annotation maybeContext srcType _)
      | A.At bodyRegion (Src.Extern impls Nothing) <- body ->
          do
            annotation@(Can.Forall freeVars tipe) <- Type.toAnnotation env maybeContext srcType
            checkExtern aname impls tipe
            checkJsExtern aname impls tipe
            let canImpls = List.sortOn (\(Can.ExternImpl language _) -> language) (map canonicalImpl impls)
            let isPure = any (\(Src.ExternImpl p _ _) -> p) impls
            let cbody = Can.at bodyRegion (Can.VarExtern name canImpls isPure annotation)
            let def = Can.TypedDef aname freeVars [] cbody tipe
            return (toNodeTwo name srcArgs def Map.empty, name, [])
    Just (Src.Annotation maybeContext srcType _) ->
      do
        (Can.Forall freeVars tipe) <- Type.toAnnotation env maybeContext srcType

        -- An extern with a Geng body (D222) is held to every rule a bodiless
        -- one is, and is then an ordinary definition of that body.
        -- 'externBodies' records that it is an extern as well.
        geng <-
          case body of
            A.At _ (Src.Extern impls (Just geng)) ->
              do
                checkExtern aname impls tipe
                checkJsExtern aname impls tipe
                return geng
            _ ->
              return body

        ((args, resultType), argBindings) <-
          Pattern.verify (Error.DPFuncArgs name) $
            Expr.gatherTypedArgs env name (fmap snd srcArgs) tipe Index.first []

        newEnv <-
          Env.addLocals argBindings env

        (cbody, freeLocals) <-
          Expr.verifyBindings W.Pattern argBindings (Expr.canonicalize newEnv geng)

        let def = Can.TypedDef aname freeVars args cbody resultType
        return
          ( toNodeTwo name srcArgs def freeLocals,
            name,
            Map.keys freeLocals
          )

-- EXTERNS

-- | Every extern declaration with a Geng body, by name, with its
-- implementations sorted by language and whether it is pure (D222). The
-- definition itself is among the module's values; 'toNodeOne' has already
-- checked the rows.
externBodies :: [A.Located Src.Value] -> Map.Map Name.Name Can.ExternBody
externBodies values =
  Map.fromList
    [ ( name,
        Can.ExternBody
          (List.sortOn (\(Can.ExternImpl language _) -> language) (map canonicalImpl impls))
          (any (\(Src.ExternImpl p _ _) -> p) impls)
      )
    | A.At _ (Src.Value (A.At _ name) _ (A.At _ (Src.Extern impls (Just _))) _ _) <- values
    ]

-- | `ffi.md` F1 and D77, checked on a declaration's attributes and its type.
--
-- In the order an author would fix them: each attribute on its own (a language
-- in the table, with the names that language takes), then the attributes
-- against each other (one per language, and all of one purity), and last the
-- declared type, which must end in a `Task` unless the extern is pure (F1,
-- `syntax.md` S2).
checkExtern :: A.Located Name.Name -> [Src.ExternImpl] -> Can.Type -> Result i w ()
checkExtern (A.At nameRegion name) impls tipe =
  do
    mapM_ checkImpl impls
    _ <- foldM checkDuplicate Map.empty impls
    case impls of
      Src.ExternImpl isPure _ _ : rest
        | Just (Src.ExternImpl _ (A.At region _) _) <- List.find (\(Src.ExternImpl p _ _) -> p /= isPure) rest ->
            Result.throw (Error.ExternMixedPurity region name)
      Src.ExternImpl False _ _ : _
        | not (endsInTask tipe) ->
            Result.throw (Error.ExternNotTask nameRegion name tipe)
      _ ->
        Result.ok ()
  where
    checkImpl (Src.ExternImpl _ (A.At region language) names) =
      case lookup (Name.toChars language) externLanguages of
        Nothing ->
          Result.throw (Error.ExternUnknownLanguage region language)
        Just wanted
          | length names /= wanted ->
              Result.throw (Error.ExternNames region language wanted (length names))
          | otherwise ->
              Result.ok ()

    checkDuplicate seen (Src.ExternImpl _ (A.At region language) _) =
      case Map.lookup language seen of
        Just first -> Result.throw (Error.ExternDuplicateLanguage region language first)
        Nothing -> Result.ok (Map.insert language region seen)

-- | What a @js@ row asks of its names and of the declared type, once
-- 'checkExtern' has held (@m1b-extern.md@ §H13, D192, D198–D203).
--
-- The module names the file, @src/Ext/<Module>.js@, so it is a module name's
-- segment, which is also what the front end reads a file under @src@ as. The
-- function is looked up among that file's declarations, so it is a JavaScript
-- identifier. And the type has to be one the boundary can carry, which
-- "Core.Extern" decides for this check and for the wrapper the backend writes.
checkJsExtern :: A.Located Name.Name -> [Src.ExternImpl] -> Can.Type -> Result i w ()
checkJsExtern (A.At nameRegion name) impls tipe =
  case [names | Src.ExternImpl _ (A.At _ language) names <- impls, Name.toChars language == "js"] of
    [[A.At moduleRegion modul, A.At functionRegion function]] ->
      do
        let moduleChars = ES.toChars modul
        let functionChars = ES.toChars function
        if isModuleSegment moduleChars
          then Result.ok ()
          else Result.throw (Error.ExternJsModule moduleRegion moduleChars)
        if isIdentifier functionChars
          then Result.ok ()
          else Result.throw (Error.ExternJsFunction functionRegion functionChars)
        let isPure = any (\(Src.ExternImpl p _ _) -> p) impls
        case Extern.classify isPure (LowerType.lowerType tipe) of
          Right _ -> Result.ok ()
          Left problem -> Result.throw (Error.ExternDoesNotCross nameRegion name problem)
    _ ->
      Result.ok ()
  where
    isModuleSegment chars =
      case chars of
        first : rest -> Char.isAsciiUpper first && all isAsciiAlphaNum rest
        [] -> False

    isIdentifier chars =
      case chars of
        first : rest -> (Char.isAsciiUpper first || Char.isAsciiLower first || first == '_' || first == '$') && all (\c -> isAsciiAlphaNum c || c == '_' || c == '$') rest
        [] -> False

    isAsciiAlphaNum c =
      Char.isAsciiUpper c || Char.isAsciiLower c || Char.isDigit c

-- | D77's table: the extern languages, and how many quoted names each takes.
externLanguages :: [(String, Int)]
externLanguages =
  [ ("js", 2),
    ("erlang", 2),
    ("c", 1)
  ]

-- | An attribute row after 'checkExtern' has held, so its language is one of
-- the table's three.
canonicalImpl :: Src.ExternImpl -> Can.ExternImpl
canonicalImpl (Src.ExternImpl _ (A.At _ language) names) =
  Can.ExternImpl
    ( case Name.toChars language of
        "erlang" -> Can.ExternErlang
        "c" -> Can.ExternC
        _ -> Can.ExternJs
    )
    (map A.toValue names)

-- | Whether a type, past its arguments and through its aliases, is a @Task@,
-- which both `Task.Task` and `Platform.Task` are aliases of. The type itself is
-- declared in the unexposed `Task.Internal` (@m1b-source.md@ §SO11), because
-- `Platform` — which declared it until close-out item 4 — and `Task` import each
-- other.
endsInTask :: Can.Type -> Bool
endsInTask tipe =
  case tipe of
    Can.TLambda _ result -> endsInTask result
    Can.TType home typeName _ -> home == ModuleName.taskInternal && typeName == Name.task
    Can.TAlias _ _ _ (Can.Holey aliased) -> endsInTask aliased
    Can.TAlias _ _ _ (Can.Filled aliased) -> endsInTask aliased
    _ -> False

toNodeTwo :: Name.Name -> [arg] -> Can.Def -> Expr.FreeLocals -> NodeTwo
toNodeTwo name args def freeLocals =
  case args of
    [] ->
      (def, name, Map.foldrWithKey addDirects [] freeLocals)
    _ ->
      (def, name, [])

addDirects :: Name.Name -> Expr.Uses -> [Name.Name] -> [Name.Name]
addDirects name (Expr.Uses directUses _) directDeps =
  if directUses > 0
    then name : directDeps
    else directDeps

-- CANONICALIZE EXPORTS

canonicalizeExports ::
  [A.Located Src.Value] ->
  Map.Map Name.Name union ->
  Map.Map Name.Name alias ->
  Map.Map Name.Name Can.ClassDecl ->
  Map.Map Name.Name binop ->
  Can.Effects ->
  A.Located Src.Exposing ->
  Result i w Can.Exports
canonicalizeExports values unions aliases classes binops effects (A.At region exposing) =
  case exposing of
    Src.Open ->
      Result.ok (Can.ExportEverything region)
    Src.Explicit exposeds ->
      do
        let names = Map.fromList (map valueToName values)
        infos <- traverse (checkExposed names unions aliases classes binops effects) exposeds
        Can.Export <$> Dups.detect Error.ExportDuplicate (Dups.unions infos)

valueToName :: A.Located Src.Value -> (Name.Name, ())
valueToName (A.At _ (Src.Value (A.At _ name) _ _ _ _)) =
  (name, ())

checkExposed ::
  Map.Map Name.Name value ->
  Map.Map Name.Name union ->
  Map.Map Name.Name alias ->
  Map.Map Name.Name Can.ClassDecl ->
  Map.Map Name.Name binop ->
  Can.Effects ->
  Src.Exposed ->
  Result i w (Dups.Dict (A.Located Can.Export))
checkExposed values unions aliases classes binops effects exposed =
  case exposed of
    Src.Lower (A.At region name) ->
      if Map.member name values
        then ok name region Can.ExportValue
        else case checkPorts effects name of
          Nothing ->
            ok name region Can.ExportPort
          Just ports ->
            case classOf name classes of
              Just className ->
                Result.throw (Error.ExportMethodByName region name className)
              Nothing ->
                Result.throw $
                  Error.ExportNotFound region Error.BadVar name $
                    ports ++ Map.keys values
    Src.Operator region name ->
      if Map.member name binops
        then ok name region Can.ExportBinop
        else
          Result.throw $
            Error.ExportNotFound region Error.BadOp name $
              Map.keys binops
    Src.Upper (A.At region name) (Src.Public dotDotRegion) ->
      if Map.member name unions
        then ok name region Can.ExportUnionOpen
        else
          if Map.member name aliases
            then Result.throw $ Error.ExportOpenAlias dotDotRegion name
            else
              if Map.member name classes
                then Result.throw $ Error.ExportOpenClass dotDotRegion name
                else
                  Result.throw $
                    Error.ExportNotFound region Error.BadType name $
                      Map.keys unions ++ Map.keys aliases ++ Map.keys classes
    Src.Upper (A.At region name) Src.Private ->
      if Map.member name unions
        then ok name region Can.ExportUnionClosed
        else
          if Map.member name aliases
            then ok name region Can.ExportAlias
            else
              if Map.member name classes
                then ok name region Can.ExportClass
                else
                  Result.throw $
                    Error.ExportNotFound region Error.BadType name $
                      Map.keys unions ++ Map.keys aliases ++ Map.keys classes

-- | The class a method name belongs to, if it is a method at all.
--
-- @exposing (eq)@ where `eq` is a method is the mistake this exists for: a
-- method travels with its class (D121), so the fix is to name the class rather
-- than the method.
classOf :: Name.Name -> Map.Map Name.Name Can.ClassDecl -> Maybe Name.Name
classOf name classes =
  case [className | (className, Can.ClassDecl _ methods) <- Map.toList classes, Map.member name methods] of
    className : _ -> Just className
    [] -> Nothing

checkPorts :: Can.Effects -> Name.Name -> Maybe [Name.Name]
checkPorts effects name =
  case effects of
    Can.NoEffects ->
      Just []
    Can.Ports ports ->
      if Map.member name ports then Nothing else Just (Map.keys ports)
    Can.Manager _ _ _ _ ->
      Just []

ok :: Name.Name -> A.Region -> Can.Export -> Result i w (Dups.Dict (A.Located Can.Export))
ok name region export =
  Result.ok $ Dups.one name region (A.At region export)
