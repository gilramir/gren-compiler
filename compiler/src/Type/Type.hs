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
    nameToRigid,
    toAnnotation,
    toNodeTypes,
    toErrorType,
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

-- MAKE NAMED VARIABLES

nameToFlex :: Name.Name -> IO Variable
nameToFlex name =
  UF.fresh $
    makeDescriptor $
      maybe FlexVar FlexSuper (Class.fromName name) (Just name)

nameToRigid :: Name.Name -> IO Variable
nameToRigid name =
  UF.fresh $
    makeDescriptor $
      maybe RigidVar RigidSuper (Class.fromName name) name

-- TO TYPE ANNOTATION

toAnnotation :: Variable -> IO Can.Annotation
toAnnotation variable =
  do
    userNames <- getVarNames variable Map.empty
    (tipe, NameState freeVars _ _ _ _ _) <-
      State.runStateT (variableToCanType variable) (makeNameState userNames)
    return $ Can.Forall freeVars tipe

-- | Zonk a whole map of recorded node types at once.
--
-- One shared 'NameState', not one per entry: 'variableToCanType' writes the
-- name it picks back into the variable, so a variable shared between two nodes
-- already comes out with the same name — but two *different* variables zonked
-- against two fresh name states would both be handed "a". Core needs a
-- lambda's binder type and its body's occurrence of it to agree, so the naming
-- has to be module-wide.
toNodeTypes :: Map.Map Can.NodeId Type -> IO (Map.Map Can.NodeId Can.Type)
toNodeTypes types =
  do
    userNames <- foldrM collectTypeVarNames Map.empty (Map.elems types)
    State.evalStateT (traverse typeToCanType types) (makeNameState userNames)

collectTypeVarNames :: Type -> Map.Map Name.Name Variable -> IO (Map.Map Name.Name Variable)
collectTypeVarNames tipe taken =
  case tipe of
    PlaceHolder _ -> return taken
    VarN var -> getVarNames var taken
    AliasN _ _ args real ->
      collectTypeVarNames real =<< foldrM collectTypeVarNames taken (map snd args)
    AppN _ _ args -> foldrM collectTypeVarNames taken args
    FunN a b -> collectTypeVarNames b =<< collectTypeVarNames a taken
    EmptyRecordN -> return taken
    RecordN fields ext ->
      collectTypeVarNames ext =<< foldrM collectTypeVarNames taken (Map.elems fields)

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
            return (Can.TVar name)
          Nothing ->
            do
              name <- getFreshSuperName super
              liftIO $ UF.modify variable (\desc -> desc {_content = FlexSuper super (Just name)})
              return (Can.TVar name)
      RigidVar name ->
        return (Can.TVar name)
      RigidSuper _ name ->
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

-- | The error layer keeps its own four-constructor vocabulary, and this is the
-- seam that lets it: `number`, `comparable`, `appendable` and `compappend` are
-- what a Gren programmer has written and what every error message says, so
-- they go on meaning that until D13 and the `core` rewrite change what a
-- programmer writes. `Reporting/Error/Type.hs` is untouched by verb 2 for
-- exactly this reason.
--
-- The reduction in `Class.union` is what makes this total in practice: the
-- only sets that reach here are the four the old enum could hold.
classesToSuper :: Class.Classes -> ET.Super
classesToSuper classes =
  case Class.toList classes of
    [Class.Num] -> ET.Number
    [Class.Ord] -> ET.Comparable
    [Class.Appendable] -> ET.Appendable
    [Class.Ord, Class.Appendable] -> ET.CompAppend
    _ -> ET.Comparable

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
    _comparables :: Int,
    _appendables :: Int,
    _compAppends :: Int
  }

makeNameState :: Map.Map Name.Name Variable -> NameState
makeNameState taken =
  NameState (Map.map (const ()) taken) 0 0 0 0 0

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

-- | The name a constrained variable is shown under, which is the name the
-- author would have written for it. Same seam as `classesToSuper`, and it goes
-- the same way when `core` stops writing `number`.
getFreshSuperName :: (Monad m) => Class.Classes -> StateT NameState m Name.Name
getFreshSuperName classes =
  case Class.toList classes of
    [Class.Num] ->
      getFreshSuper "number" _numbers (\index state -> state {_numbers = index})
    [Class.Appendable] ->
      getFreshSuper "appendable" _appendables (\index state -> state {_appendables = index})
    [Class.Ord, Class.Appendable] ->
      getFreshSuper "compappend" _compAppends (\index state -> state {_compAppends = index})
    _ ->
      getFreshSuper "comparable" _comparables (\index state -> state {_comparables = index})

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
getVarNames var takenNames =
  do
    (Descriptor content rank mark copy) <- UF.get var
    if mark == getVarNamesMark
      then return takenNames
      else do
        UF.set var (Descriptor content rank getVarNamesMark copy)
        case content of
          Error ->
            return takenNames
          FlexVar maybeName ->
            case maybeName of
              Nothing ->
                return takenNames
              Just name ->
                addName 0 name var (FlexVar . Just) takenNames
          FlexSuper super maybeName ->
            case maybeName of
              Nothing ->
                return takenNames
              Just name ->
                addName 0 name var (FlexSuper super . Just) takenNames
          RigidVar name ->
            addName 0 name var RigidVar takenNames
          RigidSuper super name ->
            addName 0 name var (RigidSuper super) takenNames
          Alias _ _ args _ ->
            foldrM getVarNames takenNames (map snd args)
          Structure flatType ->
            case flatType of
              App1 _ _ args ->
                foldrM getVarNames takenNames args
              Fun1 arg body ->
                getVarNames arg =<< getVarNames body takenNames
              EmptyRecord1 ->
                return takenNames
              Record1 fields extension ->
                getVarNames extension
                  =<< foldrM getVarNames takenNames (Map.elems fields)

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
