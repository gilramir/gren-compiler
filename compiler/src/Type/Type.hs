{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module Type.Type
  ( Constraint (..),
    exists,
    Variable,
    FlatType (..),
    Type (..),
    Descriptor (Descriptor),
    Content (..),
    noRank,
    outermostRank,
    Mark,
    noMark,
    nextMark,
    (==>),
    int,
    float,
    char,
    string,
    bool,
    never,
    mkFlexVar,
    mkFlexNumber,
    unnamedFlexVar,
    unnamedFlexSuper,
    nameToFlex,
    classesOf,
    nameToRigid,
    toAnnotation,
    toNodeTypes,
    toErrorType,
    toErrorTypePair,
  )
where

import AST.Canonical qualified as Can
import AST.Utils.Type qualified as Type
import Control.Monad.State.Strict (StateT, liftIO)
import Control.Monad.State.Strict qualified as State
import Data.Foldable (foldrM)
import Data.Map.Strict qualified as Map
import Data.Name qualified as Name
import Data.Word (Word32)
import Gren.ModuleName qualified as ModuleName
import Reporting.Annotation qualified as A
import Reporting.Error.Type qualified as E
import Type.Class qualified as Class
import Type.Error qualified as ET
import Type.UnionFind qualified as UF

-- CONSTRAINTS

data Constraint
  = CTrue
  | CSaveTheEnvironment
  | CEqual A.Region E.Category Type (E.Expected Type)
  | CLocal A.Region Name.Name (E.Expected Type)
  | CForeign A.Region Name.Name Can.Annotation (E.Expected Type)
  | CPattern A.Region E.PCategory Type (E.PExpected Type)
  | -- | Record the type of one expression node, for the Core lowering.
    --
    -- It carries no obligation: the solver reads it and unifies nothing, so
    -- adding one cannot change what typechecks. That is deliberate — a
    -- constraint that recorded by allocating a variable at the current rank
    -- could change what generalization sees, and this pass has to be
    -- observationally invisible to inference (`docs/m1a-node-types.md`).
    CNode Can.NodeId Type
  | CAnd [Constraint]
  | CLet
      { _rigidVars :: [Variable],
        _flexVars :: [Variable],
        _header :: Map.Map Name.Name (A.Located Type),
        _headerCon :: Constraint,
        _bodyCon :: Constraint
      }

exists :: [Variable] -> Constraint -> Constraint
exists flexVars constraint =
  CLet [] flexVars Map.empty constraint CTrue

-- TYPE PRIMITIVES

type Variable =
  UF.Point Descriptor

data FlatType
  = App1 ModuleName.Canonical Name.Name [Variable]
  | Fun1 Variable Variable
  | EmptyRecord1
  | Record1 (Map.Map Name.Name Variable) Variable

data Type
  = PlaceHolder Name.Name
  | AliasN ModuleName.Canonical Name.Name [(Name.Name, Type)] Type
  | VarN Variable
  | AppN ModuleName.Canonical Name.Name [Type]
  | FunN Type Type
  | EmptyRecordN
  | RecordN (Map.Map Name.Name Type) Type

-- DESCRIPTORS

data Descriptor = Descriptor
  { _content :: Content,
    _rank :: Int,
    _mark :: Mark,
    _copy :: Maybe Variable
  }

data Content
  = FlexVar (Maybe Name.Name)
  | FlexSuper Class.Classes (Maybe Name.Name)
  | RigidVar Name.Name
  | RigidSuper Class.Classes Name.Name
  | Structure FlatType
  | Alias ModuleName.Canonical Name.Name [(Name.Name, Variable)] Variable
  | Error

makeDescriptor :: Content -> Descriptor
makeDescriptor content =
  Descriptor content noRank noMark Nothing

-- RANKS

noRank :: Int
noRank =
  0

outermostRank :: Int
outermostRank =
  1

-- MARKS

newtype Mark = Mark Word32
  deriving (Eq, Ord)

noMark :: Mark
noMark =
  Mark 2

occursMark :: Mark
occursMark =
  Mark 1

getVarNamesMark :: Mark
getVarNamesMark =
  Mark 0

nextMark :: Mark -> Mark
nextMark (Mark mark) =
  Mark (mark + 1)

-- FUNCTION TYPES

infixr 9 ==>

(==>) :: Type -> Type -> Type
(==>) =
  FunN

-- PRIMITIVE TYPES

int :: Type
int = AppN ModuleName.basics "Int" []

float :: Type
float = AppN ModuleName.basics "Float" []

char :: Type
char = AppN ModuleName.char "Char" []

string :: Type
string = AppN ModuleName.string "String" []

bool :: Type
bool = AppN ModuleName.basics "Bool" []

never :: Type
never = AppN ModuleName.basics "Never" []

-- MAKE FLEX VARIABLES

mkFlexVar :: IO Variable
mkFlexVar =
  UF.fresh flexVarDescriptor

flexVarDescriptor :: Descriptor
flexVarDescriptor =
  makeDescriptor unnamedFlexVar

unnamedFlexVar :: Content
unnamedFlexVar =
  FlexVar Nothing

-- MAKE FLEX NUMBERS

mkFlexNumber :: IO Variable
mkFlexNumber =
  UF.fresh flexNumberDescriptor

flexNumberDescriptor :: Descriptor
flexNumberDescriptor =
  makeDescriptor (unnamedFlexSuper (Class.singleton Class.Num))

unnamedFlexSuper :: Class.Classes -> Content
unnamedFlexSuper classes =
  FlexSuper classes Nothing

-- | The unifier's reading of a written context: the closed classes in it
-- (D135).
--
-- `Nothing` when there are none, which is a `FlexVar`/`RigidVar` rather than a
-- constrained one. An /open/ class in the list is not lost — it is
-- `Type.Resolve`'s, and this is the seam where D130's two mechanisms divide.
-- It lives here rather than in "Type.Class" only so that that module stays a
-- leaf `AST.Canonical` can import.
classesOf :: [Can.Class] -> Maybe Class.Classes
classesOf classes =
  Class.fromList [c | Can.Class home name <- classes, Just c <- [Class.fromDeclared home name]]

-- | A class the unifier knows, as the constraint an annotation writes.
toCanClass :: Class.Class -> Can.Class
toCanClass c =
  let (home, name) = Class.toDeclared c
   in Can.Class home name

-- MAKE NAMED VARIABLES

-- | A type variable an annotation binds, under the constraints it was written
-- with.
--
-- __The constraint list is the input, not the name__ (D135). Until verb 7 these
-- read `Class.fromName`, so `number` was a constrained variable and `a` was
-- not; a variable's name means nothing now and what makes it constrained is the
-- context beside the type. Only the closed classes reach here — an open one is
-- `Type.Resolve`'s and leaves the variable flexible, which is exactly D130.
nameToFlex :: Name.Name -> [Can.Class] -> IO Variable
nameToFlex name constraints =
  UF.fresh $
    makeDescriptor $
      maybe FlexVar FlexSuper (classesOf constraints) (Just name)

nameToRigid :: Name.Name -> [Can.Class] -> IO Variable
nameToRigid name constraints =
  UF.fresh $
    makeDescriptor $
      maybe RigidVar RigidSuper (classesOf constraints) name

-- TO TYPE ANNOTATION

toAnnotation :: Variable -> IO Can.Annotation
toAnnotation variable =
  do
    userNames <- getVarNames variable Map.empty
    (tipe, NameState freeVars _ _ _ constrained) <-
      State.runStateT (variableToCanType variable) (makeNameState userNames)
    -- A constrained variable comes back constrained (D135). `Basics` declares
    -- the closed classes now, so `Class.toDeclared` has a real name to point a
    -- `Can.Class` at, and an annotation the solver produced says what the
    -- solver knew — which is what closes §G21.3's unenforced promise for them:
    -- an importer's `srcTypeToVariable` reads the constraint back and the
    -- unifier demands it again.
    --
    -- An /open/ class is not here and cannot be: the solver never saw one.
    -- `Compile.withContexts` puts a written context back for that reason, and
    -- the two are consistent because a written closed constraint arrives here
    -- as a `FlexSuper`/`RigidSuper` and leaves as itself.
    let contextOf name =
          maybe [] (map toCanClass . Class.toList) (Map.lookup name constrained)
    return $ Can.Forall (Map.mapWithKey (\name _ -> contextOf name) freeVars) tipe

-- | Zonk a whole map of recorded node types at once, and say what each
-- variable in them is constrained by.
--
-- One shared 'NameState', not one per entry: 'variableToCanType' writes the
-- name it picks back into the variable, so a variable shared between two nodes
-- already comes out with the same name — but two *different* variables zonked
-- against two fresh name states would both be handed "a". Core needs a
-- lambda's binder type and its body's occurrence of it to agree, so the naming
-- has to be module-wide.
--
-- The classes come out with the types because this is the only walk that sees
-- every variable in the module — an annotation's walk sees one definition's —
-- and `classes.md` §0's rule has to be answerable for any of them once an
-- /open/ constraint can put a variable in front of it (§G33.2).
toNodeTypes :: Mark -> Map.Map Can.NodeId Type -> IO (Map.Map Can.NodeId Can.Type, Map.Map Name.Name Class.Classes)
toNodeTypes visited types =
  do
    userNames <- foldrM (collectTypeVarNames visited) Map.empty (Map.elems types)
    (canTypes, NameState _ _ _ _ constrained) <-
      State.runStateT (traverse typeToCanType types) (makeNameState userNames)
    return (canTypes, constrained)

collectTypeVarNames :: Mark -> Type -> Map.Map Name.Name Variable -> IO (Map.Map Name.Name Variable)
collectTypeVarNames visited tipe taken =
  let recurse = collectTypeVarNames visited
   in case tipe of
        PlaceHolder _ -> return taken
        VarN var -> keepVarNames visited var taken
        AliasN _ _ args real ->
          recurse real =<< foldrM recurse taken (map snd args)
        AppN _ _ args -> foldrM recurse taken args
        FunN a b -> recurse b =<< recurse a taken
        EmptyRecordN -> return taken
        RecordN fields ext ->
          recurse ext =<< foldrM recurse taken (Map.elems fields)

-- | Convert a constraint-level 'Type' without going through
-- 'Type.Solve.typeToVariable'.
--
-- The round trip through a 'Variable' would allocate into a rank's pool, and
-- 'CNode' exists on the promise that recording a type cannot perturb
-- inference. Walking the structure directly keeps that promise: the only
-- variables touched are the ones the type already refers to.
typeToCanType :: Type -> StateT NameState IO Can.Type
typeToCanType tipe =
  case tipe of
    PlaceHolder name ->
      return (Can.TVar name)
    VarN var ->
      variableToCanType var
    AliasN home name args real ->
      Can.TAlias home name
        <$> traverse (traverse typeToCanType) args
        <*> (Can.Filled <$> typeToCanType real)
    AppN home name args ->
      Can.TType home name <$> traverse typeToCanType args
    FunN a b ->
      Can.TLambda <$> typeToCanType a <*> typeToCanType b
    EmptyRecordN ->
      return (Can.TRecord Map.empty Nothing)
    RecordN fields ext ->
      do
        canFields <- traverse (fmap (Can.FieldType 0) . typeToCanType) fields
        canExt <- Type.iteratedDealias <$> typeToCanType ext
        return $
          case canExt of
            Can.TRecord subFields subExt ->
              Can.TRecord (Map.union subFields canFields) subExt
            Can.TVar name ->
              Can.TRecord canFields (Just name)
            _ ->
              error "Used toNodeTypes on a record type that is not well-formed"

variableToCanType :: Variable -> StateT NameState IO Can.Type
variableToCanType variable =
  do
    (Descriptor content _ _ _) <- liftIO $ UF.get variable
    case content of
      Structure term ->
        termToCanType term
      FlexVar maybeName ->
        case maybeName of
          Just name ->
            return (Can.TVar name)
          Nothing ->
            do
              name <- getFreshVarName
              liftIO $ UF.modify variable (\desc -> desc {_content = FlexVar (Just name)})
              return (Can.TVar name)
      FlexSuper super maybeName ->
        case maybeName of
          Just name ->
            do
              noteClasses name super
              return (Can.TVar name)
          Nothing ->
            do
              name <- getFreshSuperName super
              liftIO $ UF.modify variable (\desc -> desc {_content = FlexSuper super (Just name)})
              noteClasses name super
              return (Can.TVar name)
      RigidVar name ->
        return (Can.TVar name)
      RigidSuper super name ->
        do
          noteClasses name super
          return (Can.TVar name)
      Alias home name args realVariable ->
        do
          canArgs <- traverse (traverse variableToCanType) args
          canType <- variableToCanType realVariable
          return (Can.TAlias home name canArgs (Can.Filled canType))
      Error ->
        error "cannot handle Error types in variableToCanType"

termToCanType :: FlatType -> StateT NameState IO Can.Type
termToCanType term =
  case term of
    App1 home name args ->
      Can.TType home name <$> traverse variableToCanType args
    Fun1 a b ->
      Can.TLambda
        <$> variableToCanType a
        <*> variableToCanType b
    EmptyRecord1 ->
      return $ Can.TRecord Map.empty Nothing
    Record1 fields extension ->
      do
        canFields <- traverse fieldToCanType fields
        canExt <- Type.iteratedDealias <$> variableToCanType extension
        return $
          case canExt of
            Can.TRecord subFields subExt ->
              Can.TRecord (Map.union subFields canFields) subExt
            Can.TVar name ->
              Can.TRecord canFields (Just name)
            _ ->
              error "Used toAnnotation on a type that is not well-formed"

fieldToCanType :: Variable -> StateT NameState IO Can.FieldType
fieldToCanType variable =
  do
    tipe <- variableToCanType variable
    return (Can.FieldType 0 tipe)

-- TO ERROR TYPE

toErrorType :: Variable -> IO ET.Type
toErrorType variable =
  do
    userNames <- getVarNames variable Map.empty
    State.evalStateT (variableToErrorType variable) (makeNameState userNames)

-- | The two sides of a mismatch, named against __one__ state.
--
-- Same reason 'toNodeTypes' shares one: a name this invents for a variable
-- nobody named has to avoid every name in the message, and two independent
-- states each avoid only their own half. The result is a report that says
-- "this is a `number`, but I need a `number`" — which is what
-- `corpus/reject/method-at-a-numeric-variable` produced the day `number`
-- stopped being reserved and became a name a program may bind
-- (`docs/m1b-classes.md` §G32).
--
-- Reachable before D135 too, with an ordinary @a@ on one side and an invented
-- @a@ on the other. What changed is how easy it is to reach.
toErrorTypePair :: Variable -> Variable -> IO (ET.Type, ET.Type)
toErrorTypePair v1 v2 =
  do
    userNames <- getVarNames v2 =<< getVarNames v1 Map.empty
    State.evalStateT
      ((,) <$> variableToErrorType v1 <*> variableToErrorType v2)
      (makeNameState userNames)

variableToErrorType :: Variable -> StateT NameState IO ET.Type
variableToErrorType variable =
  do
    descriptor <- liftIO $ UF.get variable
    let mark = _mark descriptor
    if mark == occursMark
      then return ET.Infinite
      else do
        liftIO $ UF.modify variable (\desc -> desc {_mark = occursMark})
        errType <- contentToErrorType variable (_content descriptor)
        liftIO $ UF.modify variable (\desc -> desc {_mark = mark})
        return errType

contentToErrorType :: Variable -> Content -> StateT NameState IO ET.Type
contentToErrorType variable content =
  case content of
    Structure term ->
      termToErrorType term
    FlexVar maybeName ->
      case maybeName of
        Just name ->
          return (ET.FlexVar name)
        Nothing ->
          do
            name <- getFreshVarName
            liftIO $ UF.modify variable (\desc -> desc {_content = FlexVar (Just name)})
            return (ET.FlexVar name)
    FlexSuper super maybeName ->
      case maybeName of
        Just name ->
          return (ET.FlexSuper (classesToSuper super) name)
        Nothing ->
          do
            name <- getFreshSuperName super
            liftIO $ UF.modify variable (\desc -> desc {_content = FlexSuper super (Just name)})
            return (ET.FlexSuper (classesToSuper super) name)
    RigidVar name ->
      return (ET.RigidVar name)
    RigidSuper super name ->
      return (ET.RigidSuper (classesToSuper super) name)
    Alias home name args realVariable ->
      do
        errArgs <- traverse (traverse variableToErrorType) args
        errType <- variableToErrorType realVariable
        return (ET.Alias home name errArgs errType)
    Error ->
      return ET.Error

-- | The error layer keeps a vocabulary of its own, and this is the seam that
-- lets it.
--
-- It was the four magic names once — `number`, `comparable`, `appendable`,
-- `compappend` — and what kept it after D135 is that `ET.Super` is a
-- *classification*, not a spelling: `Reporting.Error.Type` keys its hints on
-- it ("only Int and Float work as numbers") and would key them on the class if
-- it could see one. Rendering a constraint in an error type is D12's
-- (`docs/m1b-classes.md` §G32.6).
--
-- The reduction in `Class.union` is what makes this total in practice: the
-- only sets that reach here are the ones the old enum could hold.
classesToSuper :: Class.Classes -> ET.Super
classesToSuper classes =
  case Class.toList classes of
    [Class.Appendable] -> ET.Appendable
    _ -> ET.Number

termToErrorType :: FlatType -> StateT NameState IO ET.Type
termToErrorType term =
  case term of
    App1 home name args ->
      ET.Type home name <$> traverse variableToErrorType args
    Fun1 a b ->
      do
        arg <- variableToErrorType a
        result <- variableToErrorType b
        return $
          case result of
            ET.Lambda arg1 arg2 others ->
              ET.Lambda arg arg1 (arg2 : others)
            _ ->
              ET.Lambda arg result []
    EmptyRecord1 ->
      return $ ET.Record Map.empty ET.Closed
    Record1 fields extension ->
      do
        errFields <- traverse variableToErrorType fields
        errExt <- ET.iteratedDealias <$> variableToErrorType extension
        return $
          case errExt of
            ET.Record subFields subExt ->
              ET.Record (Map.union subFields errFields) subExt
            ET.FlexVar ext ->
              ET.Record errFields (ET.FlexOpen ext)
            ET.RigidVar ext ->
              ET.Record errFields (ET.RigidOpen ext)
            _ ->
              error "Used toErrorType on a type that is not well-formed"

-- MANAGE FRESH VARIABLE NAMES

data NameState = NameState
  { _taken :: Map.Map Name.Name (),
    _normals :: Int,
    _numbers :: Int,
    _appendables :: Int,
    -- | The classes each variable the walk met is constrained by (D135).
    --
    -- Collected on the way through rather than read back off the type, because
    -- by the time there is a `Can.Type` the variable is a bare `Can.TVar` and
    -- the constraint is gone. `Can.FreeVars` wants exactly this map.
    _constrained :: Map.Map Name.Name Class.Classes
  }

makeNameState :: Map.Map Name.Name Variable -> NameState
makeNameState taken =
  NameState (Map.map (const ()) taken) 0 0 0 Map.empty

noteClasses :: (Monad m) => Name.Name -> Class.Classes -> StateT NameState m ()
noteClasses name classes =
  State.modify $ \state ->
    state {_constrained = Map.insertWith Class.union name classes (_constrained state)}

-- FRESH VAR NAMES

getFreshVarName :: (Monad m) => StateT NameState m Name.Name
getFreshVarName =
  do
    index <- State.gets _normals
    taken <- State.gets _taken
    let (name, newIndex, newTaken) = getFreshVarNameHelp index taken
    State.modify $ \state -> state {_taken = newTaken, _normals = newIndex}
    return name

getFreshVarNameHelp :: Int -> Map.Map Name.Name () -> (Name.Name, Int, Map.Map Name.Name ())
getFreshVarNameHelp index taken =
  let name =
        Name.fromTypeVariableScheme index
   in if Map.member name taken
        then getFreshVarNameHelp (index + 1) taken
        else (name, index + 1, Map.insert name () taken)

-- FRESH SUPER NAMES

-- | The name an /unnamed/ constrained variable is shown under.
--
-- It is invented, not read: a literal's type is a variable nobody named, and
-- `number` is the friendliest thing to call it. That it is now a name a program
-- may also bind is exactly why 'toErrorTypePair' exists — two independent name
-- states could hand the same one to two different variables in one message
-- (`docs/m1b-classes.md` §G32.6).
getFreshSuperName :: (Monad m) => Class.Classes -> StateT NameState m Name.Name
getFreshSuperName classes =
  case Class.toList classes of
    [Class.Appendable] ->
      getFreshSuper "appendable" _appendables (\index state -> state {_appendables = index})
    _ ->
      getFreshSuper "number" _numbers (\index state -> state {_numbers = index})

getFreshSuper :: (Monad m) => Name.Name -> (NameState -> Int) -> (Int -> NameState -> NameState) -> StateT NameState m Name.Name
getFreshSuper prefix getter setter =
  do
    index <- State.gets getter
    taken <- State.gets _taken
    let (name, newIndex, newTaken) = getFreshSuperHelp prefix index taken
    State.modify (\state -> setter newIndex state {_taken = newTaken})
    return name

getFreshSuperHelp :: Name.Name -> Int -> Map.Map Name.Name () -> (Name.Name, Int, Map.Map Name.Name ())
getFreshSuperHelp prefix index taken =
  let name =
        Name.fromTypeVariable prefix index
   in if Map.member name taken
        then getFreshSuperHelp prefix (index + 1) taken
        else (name, index + 1, Map.insert name () taken)

-- GET ALL VARIABLE NAMES

getVarNames :: Variable -> Map.Map Name.Name Variable -> IO (Map.Map Name.Name Variable)
getVarNames =
  varNames getVarNamesMark (addName 0)

-- | The same, without renaming a duplicate — see 'keepName'.
keepVarNames :: Mark -> Variable -> Map.Map Name.Name Variable -> IO (Map.Map Name.Name Variable)
keepVarNames visited =
  varNames visited keepName

-- | Register a name that is already taken by a different variable.
--
-- 'addName' renames: two distinct rigid variables both called @a@ come out as
-- @a@ and @a1@, which is what a message showing one type at a time needs, and
-- what an annotation needs so that its own variables are distinct.
--
-- __Node types are not one type at a time.__ They are every node in the module
-- at once (`docs/m1a-node-types.md`), and two definitions each writing @a@ in
-- their own signature is ordinary rather than a clash: a rigid variable is
-- scoped to the definition whose annotation names it, and no node type mentions
-- two of them. Renaming there makes a body's type disagree with the signature
-- the body is checked against — which is invisible while nothing reads the two
-- together, and is exactly what a witness parameter is looked up by (§G26).
keepName :: Name.Name -> Variable -> (Name.Name -> Content) -> Map.Map Name.Name Variable -> IO (Map.Map Name.Name Variable)
keepName givenName var _ takenNames =
  return (Map.insertWith (\_ old -> old) givenName var takenNames)

type Register =
  Name.Name -> Variable -> (Name.Name -> Content) -> Map.Map Name.Name Variable -> IO (Map.Map Name.Name Variable)

-- | Every name already spoken for in what this walk can reach.
--
-- __The mark is a parameter because it says what "already visited" means.__
-- 'getVarNamesMark' is a constant, so a variable one walk has visited is
-- invisible to every later one — which is right for 'toAnnotation', where each
-- definition is asked about its own type once, and __wrong for
-- 'toNodeTypes'__, which runs after all of them and would collect almost
-- nothing. What it collects is the set a fresh name has to avoid, so collecting
-- nothing means inventing a name another variable in the module already has
-- (§G33.3).
varNames :: Mark -> Register -> Variable -> Map.Map Name.Name Variable -> IO (Map.Map Name.Name Variable)
varNames visited register var takenNames =
  do
    (Descriptor content rank mark copy) <- UF.get var
    if mark == visited
      then return takenNames
      else do
        UF.set var (Descriptor content rank visited copy)
        let recurse = varNames visited register
        case content of
          Error ->
            return takenNames
          FlexVar maybeName ->
            case maybeName of
              Nothing ->
                return takenNames
              Just name ->
                register name var (FlexVar . Just) takenNames
          FlexSuper super maybeName ->
            case maybeName of
              Nothing ->
                return takenNames
              Just name ->
                register name var (FlexSuper super . Just) takenNames
          RigidVar name ->
            register name var RigidVar takenNames
          RigidSuper super name ->
            register name var (RigidSuper super) takenNames
          Alias _ _ args _ ->
            foldrM recurse takenNames (map snd args)
          Structure flatType ->
            case flatType of
              App1 _ _ args ->
                foldrM recurse takenNames args
              Fun1 arg body ->
                recurse arg =<< recurse body takenNames
              EmptyRecord1 ->
                return takenNames
              Record1 fields extension ->
                recurse extension
                  =<< foldrM recurse takenNames (Map.elems fields)

-- REGISTER NAME / RENAME DUPLICATES

addName :: Int -> Name.Name -> Variable -> (Name.Name -> Content) -> Map.Map Name.Name Variable -> IO (Map.Map Name.Name Variable)
addName index givenName var makeContent takenNames =
  let indexedName =
        Name.fromTypeVariable givenName index
   in case Map.lookup indexedName takenNames of
        Nothing ->
          do
            if indexedName == givenName
              then return ()
              else UF.modify var $ \(Descriptor _ rank mark copy) ->
                Descriptor (makeContent indexedName) rank mark copy
            return $ Map.insert indexedName var takenNames
        Just otherVar ->
          do
            same <- UF.equivalent var otherVar
            if same
              then return takenNames
              else addName (index + 1) givenName var makeContent takenNames
