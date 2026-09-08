module Gren.Interface
  ( Interface (..),
    Union (..),
    Alias (..),
    Binop (..),
    Class (..),
    fromModule,
    toPublicUnion,
    toPublicAlias,
    toPublicClass,
    classDecl,
    DependencyInterface (..),
    public,
    private,
    privatize,
    extractUnion,
    extractAlias,
  )
where

import AST.Canonical qualified as Can
import AST.Utils.Binop qualified as Binop
import Control.Monad (liftM, liftM3, liftM4)
import Data.Binary
import Data.Map.Merge.Strict qualified as Map
import Data.Map.Strict ((!))
import Data.Map.Strict qualified as Map
import Data.Name qualified as Name
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Reporting.Annotation qualified as A

-- INTERFACE

data Interface = Interface
  { _home :: Pkg.Name,
    _values :: Map.Map Name.Name Can.Annotation,
    _unions :: Map.Map Name.Name Union,
    _aliases :: Map.Map Name.Name Alias,
    _binops :: Map.Map Name.Name Binop,
    -- | The classes this module declares (`docs/m1b-classes.md` §G20).
    --
    -- A fifth map rather than entries in '_values', because a class has a name
    -- and is exported like a type, and its methods travel with it (D121). It
    -- is D114's field's opposite number: an __instance__ has no name and is
    -- global, so it can never live in a map keyed by name and cut down by an
    -- export list, and conflating the two would export instances by accident.
    _classes :: Map.Map Name.Name Class,
    -- | The instances this module makes visible: its own and its imports'
    -- (D114, D122, §G22.3).
    --
    -- The one field 'restrict' does not touch, because there is no such thing
    -- as a private instance or an imported one — an instance holds for every
    -- module that transitively depends on the one declaring it. Publishing the
    -- __closure__ rather than the module's own is what makes that transitive
    -- reach an ordinary union over direct imports, so nothing in the build
    -- graph has to know that instances exist.
    _instances :: Map.Map Can.InstanceKey Can.InstanceHead
  }
  deriving (Eq, Show)

data Union
  = OpenUnion Can.Union
  | ClosedUnion Can.Union
  | PrivateUnion Can.Union
  deriving (Eq, Show)

data Alias
  = PublicAlias Can.Alias
  | PrivateAlias Can.Alias
  deriving (Eq, Show)

-- | A private class is kept for the same reason a private alias is: an exposed
-- value's annotation may be constrained by a class the module does not expose,
-- and reading that annotation means resolving the name.
data Class
  = PublicClass Can.ClassDecl
  | PrivateClass Can.ClassDecl
  deriving (Eq, Show)

data Binop = Binop
  { _op_name :: Name.Name,
    _op_annotation :: Can.Annotation,
    _op_associativity :: Binop.Associativity,
    _op_precedence :: Binop.Precedence
  }
  deriving (Eq, Show)

-- FROM MODULE

fromModule :: Pkg.Name -> Map.Map ModuleName.Raw Interface -> Can.Module -> Map.Map Name.Name Can.Annotation -> Interface
fromModule home imports (Can.Module _ exports _ _ unions aliases classes instances binops _) annotations =
  Interface
    { _home = home,
      _values = restrict exports annotations,
      _unions = restrictUnions exports unions,
      _aliases = restrictAliases exports aliases,
      _binops = restrict exports (Map.map (toOp annotations) binops),
      _classes = restrictClasses exports classes,
      _instances =
        Map.union
          (Map.map Can._in_head instances)
          (Map.unions (map _instances (Map.elems imports)))
    }

restrict :: Can.Exports -> Map.Map Name.Name a -> Map.Map Name.Name a
restrict exports dict =
  case exports of
    Can.ExportEverything _ ->
      dict
    Can.Export explicitExports ->
      Map.intersection dict explicitExports

toOp :: Map.Map Name.Name Can.Annotation -> Can.Binop -> Binop
toOp types (Can.Binop_ associativity precedence name) =
  Binop name (types ! name) associativity precedence

restrictUnions :: Can.Exports -> Map.Map Name.Name Can.Union -> Map.Map Name.Name Union
restrictUnions exports unions =
  case exports of
    Can.ExportEverything _ ->
      Map.map OpenUnion unions
    Can.Export explicitExports ->
      Map.merge onLeft onRight onBoth explicitExports unions
      where
        onLeft = Map.dropMissing
        onRight = Map.mapMissing (\_ union -> PrivateUnion union)
        onBoth = Map.zipWithMatched $ \_ (A.At _ export) union ->
          case export of
            Can.ExportUnionOpen -> OpenUnion union
            Can.ExportUnionClosed -> ClosedUnion union
            _ -> error "impossible exports discovered in restrictUnions"

restrictAliases :: Can.Exports -> Map.Map Name.Name Can.Alias -> Map.Map Name.Name Alias
restrictAliases exports aliases =
  case exports of
    Can.ExportEverything _ ->
      Map.map PublicAlias aliases
    Can.Export explicitExports ->
      Map.merge onLeft onRight onBoth explicitExports aliases
      where
        onLeft = Map.dropMissing
        onRight = Map.mapMissing (\_ a -> PrivateAlias a)
        onBoth = Map.zipWithMatched (\_ _ a -> PublicAlias a)

restrictClasses :: Can.Exports -> Map.Map Name.Name Can.ClassDecl -> Map.Map Name.Name Class
restrictClasses exports classes =
  case exports of
    Can.ExportEverything _ ->
      Map.map PublicClass classes
    Can.Export explicitExports ->
      Map.merge onLeft onRight onBoth explicitExports classes
      where
        onLeft = Map.dropMissing
        onRight = Map.mapMissing (\_ c -> PrivateClass c)
        onBoth = Map.zipWithMatched (\_ _ c -> PublicClass c)

-- TO PUBLIC

toPublicUnion :: Union -> Maybe Can.Union
toPublicUnion iUnion =
  case iUnion of
    OpenUnion union -> Just union
    ClosedUnion (Can.Union vars _ _ opts) -> Just (Can.Union vars [] 0 opts)
    PrivateUnion _ -> Nothing

toPublicAlias :: Alias -> Maybe Can.Alias
toPublicAlias iAlias =
  case iAlias of
    PublicAlias alias -> Just alias
    PrivateAlias _ -> Nothing

toPublicClass :: Class -> Maybe Can.ClassDecl
toPublicClass iClass =
  case iClass of
    PublicClass decl -> Just decl
    PrivateClass _ -> Nothing

-- | The declaration, whether or not the module exposes it.
--
-- Exposure decides whether the class can be /named/; a witness for a
-- constraint is built out of what the class declares either way (§G26).
classDecl :: Class -> Can.ClassDecl
classDecl iClass =
  case iClass of
    PublicClass decl -> decl
    PrivateClass decl -> decl

-- DEPENDENCY INTERFACE

data DependencyInterface
  = Public Interface
  | Private
      Pkg.Name
      (Map.Map Name.Name Can.Union)
      (Map.Map Name.Name Can.Alias)

public :: Interface -> DependencyInterface
public =
  Public

private :: Interface -> DependencyInterface
private (Interface pkg _ unions aliases _ _ _) =
  Private pkg (Map.map extractUnion unions) (Map.map extractAlias aliases)

extractUnion :: Union -> Can.Union
extractUnion iUnion =
  case iUnion of
    OpenUnion union -> union
    ClosedUnion union -> union
    PrivateUnion union -> union

extractAlias :: Alias -> Can.Alias
extractAlias iAlias =
  case iAlias of
    PublicAlias alias -> alias
    PrivateAlias alias -> alias

privatize :: DependencyInterface -> DependencyInterface
privatize di =
  case di of
    Public i -> private i
    Private _ _ _ -> di

-- BINARY

instance Binary Interface where
  get = Interface <$> get <*> get <*> get <*> get <*> get <*> get <*> get
  put (Interface a b c d e f g) = put a >> put b >> put c >> put d >> put e >> put f >> put g

instance Binary Union where
  put union =
    case union of
      OpenUnion u -> putWord8 0 >> put u
      ClosedUnion u -> putWord8 1 >> put u
      PrivateUnion u -> putWord8 2 >> put u

  get =
    do
      n <- getWord8
      case n of
        0 -> liftM OpenUnion get
        1 -> liftM ClosedUnion get
        2 -> liftM PrivateUnion get
        _ -> fail "binary encoding of Union was corrupted"

instance Binary Alias where
  put union =
    case union of
      PublicAlias a -> putWord8 0 >> put a
      PrivateAlias a -> putWord8 1 >> put a

  get =
    do
      n <- getWord8
      case n of
        0 -> liftM PublicAlias get
        1 -> liftM PrivateAlias get
        _ -> fail "binary encoding of Alias was corrupted"

instance Binary Class where
  put c =
    case c of
      PublicClass a -> putWord8 0 >> put a
      PrivateClass a -> putWord8 1 >> put a

  get =
    do
      n <- getWord8
      case n of
        0 -> liftM PublicClass get
        1 -> liftM PrivateClass get
        _ -> fail "binary encoding of Class was corrupted"

instance Binary Binop where
  get =
    liftM4 Binop get get get get

  put (Binop a b c d) =
    put a >> put b >> put c >> put d

instance Binary DependencyInterface where
  put union =
    case union of
      Public a -> putWord8 0 >> put a
      Private a b c -> putWord8 1 >> put a >> put b >> put c

  get =
    do
      n <- getWord8
      case n of
        0 -> liftM Public get
        1 -> liftM3 Private get get get
        _ -> fail "binary encoding of DependencyInterface was corrupted"
