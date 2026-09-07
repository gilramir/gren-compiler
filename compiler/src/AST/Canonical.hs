{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module AST.Canonical
  ( Expr (..),
    Expr_ (..),
    NodeId (..),
    unnumbered,
    at,
    exprId,
    exprRegion,
    exprValue,
    CaseBranch (..),
    FieldUpdate (..),
    CtorOpts (..),
    -- definitions
    Def (..),
    Decls (..),
    -- patterns
    Pattern,
    Pattern_ (..),
    PatternRecordField,
    PatternRecordField_ (..),
    PatternCtorArg (..),
    -- types
    Annotation (..),
    FreeVars,
    Class (..),
    Type (..),
    AliasType (..),
    FieldType (..),
    fieldsToList,
    -- modules
    Module (..),
    Alias (..),
    Binop (..),
    ClassDecl (..),
    Instance (..),
    InstanceHead (..),
    InstanceKey (..),
    instanceKey,
    instanceType,
    Union (..),
    Ctor (..),
    Exports (..),
    Export (..),
    Effects (..),
    Port (..),
    Manager (..),
  )
where

{- Creating a canonical AST means finding the home module for all variables.
So if you have L.map, you need to figure out that it is from the core/core
package in the List module.

In later phases (e.g. type inference, exhaustiveness checking, optimization)
you need to look up additional info from these modules. What is the type?
What are the alternative type constructors? These lookups can be quite costly,
especially in type inference. To reduce costs the canonicalization phase
caches info needed in later phases. This means we no longer build large
dictionaries of metadata with O(log(n)) lookups in those phases. Instead
there is an O(1) read of an existing field! I have tried to mark all
cached data with comments like:

-- CACHE for exhaustiveness
-- CACHE for inference

So it is clear why the data is kept around.
-}

import AST.Source qualified as Src
import AST.Utils.Binop qualified as Binop
import Control.Monad (liftM, liftM2, liftM3, liftM4, replicateM)
import Data.Binary
import Data.Index qualified as Index
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Name (Name)
import Gren.Float qualified as EF
import Gren.ModuleName qualified as ModuleName
import Gren.String qualified as ES
import Reporting.Annotation qualified as A

-- EXPRESSIONS

-- | A node's identity, distinct from its region.
--
-- A region cannot serve as one: `detectCycles` in `Canonicalize.Expression`
-- gives every nested `Let` of a `let` block the same `letRegion`, and `Parens`
-- hands the outer region to the inner expression. Both are correct for
-- reporting and useless for identity.
--
-- Types are recorded per node during solving and joined back on afterwards
-- (`docs/m1a-node-types.md`), which is what Core needs and what nothing before
-- Core did.
newtype NodeId = NodeId Int
  deriving (Eq, Ord, Show)

-- | What canonicalization builds every node with. `Canonicalize.NodeId.number`
-- replaces them all in one fixed traversal, so numbering is deterministic by
-- construction rather than by discipline (C6).
unnumbered :: NodeId
unnumbered = NodeId 0

data Expr = Expr !NodeId !A.Region Expr_
  deriving (Show)

-- | Build an unnumbered node. The counterpart of `A.At`, which `Expr` no
-- longer is.
at :: A.Region -> Expr_ -> Expr
at = Expr unnumbered

exprId :: Expr -> NodeId
exprId (Expr nid _ _) = nid

exprRegion :: Expr -> A.Region
exprRegion (Expr _ region _) = region

exprValue :: Expr -> Expr_
exprValue (Expr _ _ value) = value

-- CACHE Annotations for type inference
data Expr_
  = VarLocal Name
  | VarTopLevel ModuleName.Canonical Name
  | VarKernel Name Name
  | VarForeign ModuleName.Canonical Name Annotation
  | VarCtor CtorOpts ModuleName.Canonical Name Index.ZeroBased Annotation
  | VarDebug ModuleName.Canonical Name Annotation
  | VarOperator Name ModuleName.Canonical Name Annotation -- CACHE real name for optimization
  | Chr ES.String
  | Str ES.String
  | Int Int
  | Float EF.Float
  | Array [Expr]
  | Negate Expr
  | Binop Name ModuleName.Canonical Name Annotation Expr Expr -- CACHE real name for optimization
  | Lambda [Pattern] Expr
  | Call Expr [Expr]
  | If [(Expr, Expr)] Expr
  | Let Def Expr
  | LetRec [Def] Expr
  | LetDestruct Pattern Expr Expr
  | Case Expr [CaseBranch]
  | Accessor Name
  | Access Expr (A.Located Name)
  | Update Expr (Map.Map (A.Located Name) FieldUpdate)
  | Record (Map.Map (A.Located Name) Expr)
  deriving (Show)

data CaseBranch
  = CaseBranch Pattern Expr
  deriving (Show)

data FieldUpdate
  = FieldUpdate A.Region Expr
  deriving (Show)

-- DEFS

-- | The 'NodeId' on 'Def' is the *un*typed definition's type
-- (`docs/m1a-node-types.md` §N9): its argument patterns bind names that Core
-- needs types for, and a pattern's type is derivable top-down from the type of
-- the thing it destructures — except here, where there is no signature and
-- nothing recorded the function type the solver built. 'TypedDef' needs no id
-- because it already caches a 'Type' per argument.
data Def
  = Def NodeId (A.Located Name) [Pattern] Expr
  | TypedDef (A.Located Name) FreeVars [(Pattern, Type)] Expr Type
  deriving (Show)

-- DECLARATIONS

data Decls
  = Declare Def Decls
  | DeclareRec Def [Def] Decls
  | SaveTheEnvironment
  deriving (Show)

-- PATTERNS

type Pattern =
  A.Located Pattern_

data Pattern_
  = PAnything
  | PVar Name
  | PRecord [PatternRecordField]
  | PAlias Pattern Name
  | PArray [Pattern]
  | PBool Union Bool
  | PChr ES.String
  | PStr ES.String
  | PInt Int
  | PCtor
      { _p_home :: ModuleName.Canonical,
        _p_type :: Name,
        _p_union :: Union,
        _p_name :: Name,
        _p_index :: Index.ZeroBased,
        _p_args :: [PatternCtorArg]
      }
  deriving (Show)

type PatternRecordField = A.Located PatternRecordField_

data PatternRecordField_ = PRFieldPattern Name Pattern
  deriving (Show)

-- CACHE _p_home, _p_type, and _p_vars for type inference
-- CACHE _p_index to replace _p_name in PROD code gen
-- CACHE _p_opts to allocate less in PROD code gen
-- CACHE _p_alts and _p_numAlts for exhaustiveness checker

data PatternCtorArg = PatternCtorArg
  { _index :: Index.ZeroBased, -- CACHE for destructors/errors
    _type :: Type, -- CACHE for type inference
    _arg :: Pattern
  }
  deriving (Show)

-- TYPES

data Annotation = Forall FreeVars Type
  deriving (Eq, Show)

-- | The variables an annotation binds, and what each is constrained by.
--
-- The payload is where a constraint lives (D111): `Eq a =>` says something
-- about the binder `a`, not about any type written to its right, so it
-- qualifies the annotation rather than appearing inside `Type`. `[]` is an
-- unconstrained variable, which is every variable until a class declaration
-- gives one something to point at.
type FreeVars = Map.Map Name [Class]

-- | A class named in a constraint, resolved to the module that declares it.
data Class = Class ModuleName.Canonical Name
  deriving (Eq, Ord, Show)

data Type
  = TLambda Type Type
  | TVar Name
  | TType ModuleName.Canonical Name [Type]
  | TRecord (Map.Map Name FieldType) (Maybe Name)
  | TAlias ModuleName.Canonical Name [(Name, Type)] AliasType
  deriving (Eq, Show)

data AliasType
  = Holey Type
  | Filled Type
  deriving (Eq, Show)

data FieldType = FieldType {-# UNPACK #-} !Word16 Type
  deriving (Eq, Show)

-- NOTE: The Word16 marks the source order, but it may not be available
-- for every canonical type. For example, if the canonical type is inferred
-- the orders will all be zeros.
--
fieldsToList :: Map.Map Name FieldType -> [(Name, Type)]
fieldsToList fields =
  let getIndex (_, FieldType index _) =
        index
      dropIndex (name, FieldType _ tipe) =
        (name, tipe)
   in map dropIndex (List.sortOn getIndex (Map.toList fields))

-- MODULES

data Module = Module
  { _name :: ModuleName.Canonical,
    _exports :: Exports,
    _docs :: Src.Docs,
    _decls :: Decls,
    _unions :: Map.Map Name Union,
    _aliases :: Map.Map Name Alias,
    -- | The classes this module declares (`docs/m1b-classes.md` §G20). Not in
    -- '_decls', because a method is not a top-level binding and nothing may
    -- ever ask one for a body (§G19.2).
    _classes :: Map.Map Name ClassDecl,
    -- | The instances this module declares (`docs/m1b-classes.md` §G22).
    --
    -- Keyed rather than listed, because 'InstanceKey' is what makes two
    -- instances the same instance and a map is the check: a second
    -- @instance Eq Path@ has nowhere to go. The module's __own__ instances
    -- only; what a module makes /visible/ is its imports' closure and lives in
    -- 'Gren.Interface', which is where the closure can be assembled (D122).
    _instances :: Map.Map InstanceKey Instance,
    _binops :: Map.Map Name Binop,
    _effects :: Effects
  }
  deriving (Show)

data Alias = Alias [Name] Type
  deriving (Eq, Show)

-- | @class Eq a where eq : a -> a -> Bool@, canonicalized.
--
-- The methods are a 'Map.Map' rather than a list because two of them may not
-- share a name and because ascending order is the one Core wants: C2 asks for
-- an order that two frontends agree on without having to agree on a traversal,
-- and alphabetical is the same answer record fields get.
--
-- Each method's 'Annotation' is its __published signature__, not the type
-- written in the class body: the class parameter carries a constraint naming
-- the class being declared, which is §G19.1's reason a class declaration needs
-- no environment to canonicalize.
data ClassDecl = ClassDecl
  { _cl_param :: Name,
    _cl_methods :: Map.Map Name Annotation
  }
  deriving (Eq, Show)

-- | What two instances have to differ in, and all resolution ever looks up.
--
-- The class and the head's __type constructor__. D11 keeps a class
-- single-parameter, and §G22.1 keeps an instance head a constructor applied to
-- arguments, so this pair identifies an instance exactly — which is what makes
-- resolution a lookup rather than a search over a list, and makes overlap
-- something a 'Map.Map' rejects rather than something a pass has to hunt for.
data InstanceKey = InstanceKey !Class !ModuleName.Canonical !Name
  deriving (Eq, Ord, Show)

-- | @instance Eq a => Eq (Array a)@ without its bodies, which is everything a
-- dependent module needs (D114): an instance is chosen by its head and
-- discharged through its context, and nothing outside the declaring module
-- ever reads a method's definition.
--
-- The head is stored split — a type constructor and its arguments — rather
-- than as a 'Type'. §G22.1's rule is that an instance head /is/ a constructor
-- applied to arguments, and storing it that way is the difference between a
-- rule checked once and remembered and a rule the representation cannot
-- express a violation of. 'instanceKey' is total because of it.
data InstanceHead = InstanceHead
  { -- | The module that declares it, so a witness can be named.
    _ih_home :: ModuleName.Canonical,
    _ih_class :: Class,
    -- | The head's type constructor: @Array@ of @Eq (Array a)@.
    _ih_con :: ModuleName.Canonical,
    _ih_conName :: Name,
    -- | Its arguments: @[a]@ of @Eq (Array a)@.
    _ih_args :: [Type],
    -- | @Eq a =>@, resolved onto the variables the head binds, exactly as an
    -- annotation's context is resolved onto the ones its type binds.
    _ih_context :: FreeVars
  }
  deriving (Eq, Show)

-- | An instance declaration: its head and the methods under it.
--
-- Each method is a 'TypedDef' whose annotation is the class's published
-- signature with the class parameter replaced by the head, so an instance body
-- is checked by exactly the machinery a top-level annotated definition is
-- checked by. They are not in '_decls': a method is not a top-level binding
-- (§G19.2), and two instances of the same class define the same method name.
data Instance = Instance
  { _in_head :: InstanceHead,
    _in_methods :: Map.Map Name Def
  }
  deriving (Show)

instanceKey :: InstanceHead -> InstanceKey
instanceKey (InstanceHead _ cls home name _ _) =
  InstanceKey cls home name

-- | The type the instance is for: @Array a@ of @Eq (Array a)@.
instanceType :: InstanceHead -> Type
instanceType (InstanceHead _ _ home name args _) =
  TType home name args

data Binop = Binop_ Binop.Associativity Binop.Precedence Name
  deriving (Eq, Show)

data Union = Union
  { _u_vars :: [Name],
    _u_alts :: [Ctor],
    _u_numAlts :: Int, -- CACHE numAlts for exhaustiveness checking
    _u_opts :: CtorOpts -- CACHE which optimizations are available
  }
  deriving (Eq, Show)

data CtorOpts
  = Normal
  | Enum
  | Unbox
  deriving (Eq, Ord, Show)

data Ctor = Ctor Name Index.ZeroBased Int [Type] -- CACHE length args
  deriving (Eq, Show)

-- EXPORTS

data Exports
  = ExportEverything A.Region
  | Export (Map.Map Name (A.Located Export))
  deriving (Show)

data Export
  = ExportValue
  | ExportBinop
  | ExportAlias
  | ExportClass
  | ExportUnionOpen
  | ExportUnionClosed
  | ExportPort
  deriving (Show)

-- EFFECTS

data Effects
  = NoEffects
  | Ports (Map.Map Name Port)
  | Manager A.Region A.Region A.Region Manager
  deriving (Show)

data Port
  = Incoming {_freeVars :: FreeVars, _payload :: Type, _func :: Type}
  | Outgoing {_freeVars :: FreeVars, _payload :: Type, _func :: Type}
  | Task {_freeVars :: FreeVars, _input :: Maybe Type, _payload :: Type, _func :: Type}
  deriving (Show)

data Manager
  = Cmd Name
  | Sub Name
  | Fx Name Name
  deriving (Show)

-- BINARY

instance Binary Alias where
  get = liftM2 Alias get get
  put (Alias a b) = put a >> put b

instance Binary ClassDecl where
  get = liftM2 ClassDecl get get
  put (ClassDecl a b) = put a >> put b

instance Binary InstanceKey where
  get = liftM3 InstanceKey get get get
  put (InstanceKey a b c) = put a >> put b >> put c

instance Binary InstanceHead where
  get = InstanceHead <$> get <*> get <*> get <*> get <*> get <*> get
  put (InstanceHead a b c d e f) = put a >> put b >> put c >> put d >> put e >> put f

instance Binary Union where
  put (Union a b c d) = put a >> put b >> put c >> put d
  get = liftM4 Union get get get get

instance Binary Ctor where
  get = liftM4 Ctor get get get get
  put (Ctor a b c d) = put a >> put b >> put c >> put d

instance Binary CtorOpts where
  put opts =
    case opts of
      Normal -> putWord8 0
      Enum -> putWord8 1
      Unbox -> putWord8 2

  get =
    do
      n <- getWord8
      case n of
        0 -> return Normal
        1 -> return Enum
        2 -> return Unbox
        _ -> fail "binary encoding of CtorOpts was corrupted"

instance Binary Annotation where
  get = liftM2 Forall get get
  put (Forall a b) = put a >> put b

instance Binary Class where
  get = liftM2 Class get get
  put (Class a b) = put a >> put b

instance Binary Type where
  put tipe =
    case tipe of
      TLambda a b -> putWord8 0 >> put a >> put b
      TVar a -> putWord8 1 >> put a
      TRecord a b -> putWord8 2 >> put a >> put b
      TAlias a b c d -> putWord8 3 >> put a >> put b >> put c >> put d
      TType home name ts ->
        let potentialWord = length ts + 5
         in if potentialWord <= fromIntegral (maxBound :: Word8)
              then do
                putWord8 (fromIntegral potentialWord)
                put home
                put name
                mapM_ put ts
              else putWord8 4 >> put home >> put name >> put ts

  get =
    do
      word <- getWord8
      case word of
        0 -> liftM2 TLambda get get
        1 -> liftM TVar get
        2 -> liftM2 TRecord get get
        3 -> liftM4 TAlias get get get get
        4 -> liftM3 TType get get get
        n -> liftM3 TType get get (replicateM (fromIntegral (n - 5)) get)

instance Binary AliasType where
  put aliasType =
    case aliasType of
      Holey tipe -> putWord8 0 >> put tipe
      Filled tipe -> putWord8 1 >> put tipe

  get =
    do
      n <- getWord8
      case n of
        0 -> liftM Holey get
        1 -> liftM Filled get
        _ -> fail "binary encoding of AliasType was corrupted"

instance Binary FieldType where
  get = liftM2 FieldType get get
  put (FieldType a b) = put a >> put b
