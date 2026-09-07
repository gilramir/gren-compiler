{-# LANGUAGE EmptyDataDecls #-}
{-# OPTIONS_GHC -Wall #-}

module AST.Source
  ( Comment,
    Comment_ (..),
    GREN_COMMENT,
    Expr,
    Expr_ (..),
    VarType (..),
    ArrayEntry,
    BinopsSegment,
    IfBranch,
    CaseBranch,
    RecordField,
    Def (..),
    Pattern,
    Pattern_ (..),
    RecordFieldPattern,
    RecordFieldPattern_ (..),
    PArrayEntry,
    Type,
    Type_ (..),
    TRecordField,
    Annotation (..),
    Context (..),
    ContextEntry,
    Constraint,
    Constraint_ (..),
    SourceOrder,
    Module (..),
    getName,
    getImportName,
    Import (..),
    Value (..),
    Class (..),
    ClassMethod,
    Instance (..),
    InstanceMethod,
    Union (..),
    UnionVariant,
    Alias (..),
    Infix (..),
    Port (..),
    Effects (..),
    Manager (..),
    Docs (..),
    DocComment (..),
    Exposing (..),
    Exposed (..),
    Privacy (..),
  )
where

import AST.SourceComments (Comment, Comment_, GREN_COMMENT)
import AST.SourceComments qualified as SC
import AST.Utils.Binop qualified as Binop
import Data.List.NonEmpty (NonEmpty)
import Data.Name (Name)
import Data.Name qualified as Name
import Gren.Float qualified as EF
import Gren.Int qualified as GI
import Gren.String qualified as ES
import Parse.Primitives qualified as P
import Reporting.Annotation qualified as A

-- EXPRESSIONS

type Expr = A.Located Expr_

data Expr_
  = Chr ES.String
  | Str ES.String ES.StringFormat
  | Int Int GI.IntFormat
  | Float EF.Float
  | Var VarType Name
  | VarQual VarType Name Name
  | Array [ArrayEntry]
  | Op Name
  | Negate Expr
  | Binops [BinopsSegment] Expr
  | Lambda [([Comment], Pattern)] Expr SC.LambdaComments
  | Call Expr [([Comment], Expr)]
  | If [IfBranch] Expr SC.IfComments
  | Let [([Comment], A.Located Def)] Expr SC.LetComments
  | Case Expr [CaseBranch] SC.CaseComments
  | Accessor Name
  | Access Expr (A.Located Name)
  | Update Expr [RecordField] SC.UpdateComments
  | Record [RecordField]
  | Parens [Comment] Expr [Comment]
  deriving (Show)

data VarType = LowVar | CapVar
  deriving (Show)

type ArrayEntry =
  (Expr, SC.ArrayEntryComments)

type BinopsSegment =
  (Expr, A.Located Name, SC.BinopsSegmentComments)

type IfBranch =
  (Expr, Expr, SC.IfBranchComments)

type CaseBranch =
  (Pattern, Expr, SC.CaseBranchComments)

type RecordField =
  (A.Located Name, Expr, SC.RecordFieldComments)

-- DEFINITIONS

data Def
  = Define (A.Located Name) [([Comment], Pattern)] Expr (Maybe Annotation) SC.ValueComments
  | Destruct Pattern Expr SC.ValueComments
  deriving (Show)

-- PATTERN

type Pattern = A.Located Pattern_

data Pattern_
  = PAnything Name
  | PVar Name
  | PRecord [RecordFieldPattern]
  | PAlias Pattern (A.Located Name)
  | PCtor A.Region Name [([Comment], Pattern)]
  | PCtorQual A.Region Name Name [([Comment], Pattern)]
  | PArray [PArrayEntry]
  | PChr ES.String
  | PStr ES.String
  | PInt Int GI.IntFormat
  deriving (Show)

type RecordFieldPattern = A.Located RecordFieldPattern_

data RecordFieldPattern_ = RFPattern (A.Located Name) Pattern
  deriving (Show)

type PArrayEntry = (Pattern, SC.PArrayEntryComments)

-- TYPE

type Type =
  A.Located Type_

data Type_
  = TLambda Type Type SC.TLambdaComments
  | TVar Name
  | TType A.Region Name [([Comment], Type)]
  | TTypeQual A.Region Name Name [([Comment], Type)]
  | TRecord [TRecordField] (Maybe (A.Located Name, SC.UpdateComments))
  | TParens Type SC.TParensComments
  deriving (Show)

type TRecordField = (A.Located Name, Type, SC.RecordFieldComments)

-- ANNOTATION

-- | A type, optionally qualified by a constraint context.
--
-- The context lives here rather than inside `Type_` because a constraint is
-- not a type — it qualifies one (D111). `Eq a =>` says something about the
-- binder `a`, and there is no position in the language where a constraint
-- could stand as a type: `Array (Eq a => a)` is not a thing to be written, and
-- a constructor inside `Type_` would make it parse.
data Annotation = Annotation (Maybe Context) Type SC.ValueTypeComments
  deriving (Show)

-- | The @(Eq a, Ord b) =>@ in front of an annotation.
--
-- There is no empty context — @() =>@ does not parse — so a `Context` always
-- holds at least one entry and `Nothing` is the only way to say "unqualified".
data Context = Context [ContextEntry] SC.ContextComments
  deriving (Show)

type ContextEntry = (Constraint, SC.ConstraintComments)

type Constraint = A.Located Constraint_

-- | A class applied to a bound type variable, and only to a variable: `Eq a`
-- is a context and `Eq (Array a)` is an instance head. Keeping the argument a
-- variable is what lets D111 key the constraint list off `FreeVars`.
data Constraint_
  = Constraint A.Region Name (A.Located Name)
  | ConstraintQual A.Region Name Name (A.Located Name)
  deriving (Show)

-- MODULE

type SourceOrder = Int

data Module = Module
  { _name :: Maybe (A.Located Name),
    _exports :: A.Located Exposing,
    _docs :: Docs,
    _imports :: [([Comment], Import)],
    _values :: [(SourceOrder, A.Located Value)],
    _classes :: [(SourceOrder, A.Located Class)],
    _instances :: [(SourceOrder, A.Located Instance)],
    _unions :: [(SourceOrder, A.Located Union)],
    _aliases :: [(SourceOrder, A.Located Alias)],
    _binops :: ([Comment], [A.Located Infix]),
    _topLevelComments :: [(SourceOrder, NonEmpty Comment)],
    _headerComments :: SC.HeaderComments,
    _effects :: Effects
  }
  deriving (Show)

getName :: Module -> Name
getName (Module maybeName _ _ _ _ _ _ _ _ _ _ _ _) =
  case maybeName of
    Just (A.At _ name) ->
      name
    Nothing ->
      Name._Main

getImportName :: Import -> Name
getImportName (Import (A.At _ name) _ _ _ _) =
  name

data Import = Import
  { _import :: A.Located Name,
    _alias :: Maybe (Name, SC.ImportAliasComments),
    _exposing :: Exposing,
    _exposingComments :: Maybe SC.ImportExposingComments,
    _importComments :: SC.ImportComments
  }
  deriving (Show)

data Value = Value (A.Located Name) [([Comment], Pattern)] Expr (Maybe Annotation) SC.ValueComments
  deriving (Show)

-- | @class Eq a where@ and the annotations under it.
--
-- Methods are annotations and nothing else: a default implementation would be
-- a decision `classes.md` has not taken, and there is no shape here to put one
-- in by accident. There is no superclass context either — §1.3 has none among
-- the open classes, and the closed ones need no entailment because their
-- membership is a table.
data Class = Class (A.Located Name) (A.Located Name) [ClassMethod] SC.ClassComments
  deriving (Show)

type ClassMethod =
  ([Comment], A.Located Name, Annotation)

-- | @instance Eq a => Eq (Array a) where@ and the definitions under it.
--
-- The head is kept as the `Type` it was written as, rather than split into a
-- class and an argument here. `Eq (Array a)` is a type expression and parses
-- as one; whether its head names a class is a question for the environment
-- that knows what a class is, and there is no answer the parser could give
-- that the resolver would not have to give again.
--
-- Methods take no annotation of their own: the class already gave each one a
-- type, and a second one would be a place for them to disagree.
data Instance = Instance (Maybe Context) Type [InstanceMethod] SC.InstanceComments
  deriving (Show)

type InstanceMethod =
  ([Comment], A.Located Value)

-- | A custom type, and the classes `@derive` says it derives.
--
-- The derived set is empty for a transparent type and stays empty: §2.1 says a
-- transparent type derives structurally by being transparent, and §8.1 makes
-- `@derive` on one a redundancy error rather than a no-op. So a non-empty list
-- here means someone wrote the attribute, which is the only thing the parser
-- can know — whether the type is abstract is an export question.
data Union = Union (A.Located Name) [([Comment], A.Located Name)] [UnionVariant] [A.Located Name] SC.UnionComments
  deriving (Show)

type UnionVariant =
  ([Comment], A.Located Name, [([Comment], Type)], [Comment])

data Alias = Alias (A.Located Name) [A.Located Name] Type
  deriving (Show)

data Infix = Infix Name Binop.Associativity Binop.Precedence Name
  deriving (Show)

data Port = Port (A.Located Name) Type
  deriving (Show)

data Effects
  = NoEffects
  | Ports [(SourceOrder, Port)] SC.PortsComments
  | Manager A.Region Manager SC.ManagerComments
  deriving (Show)

data Manager
  = Cmd (A.Located Name) SC.CmdComments
  | Sub (A.Located Name) SC.SubComments
  | Fx (A.Located Name) (A.Located Name) SC.FxComments
  deriving (Show)

data Docs
  = NoDocs A.Region
  | YesDocs DocComment [(Name, DocComment)]
  deriving (Show)

newtype DocComment
  = DocComment P.Snippet
  deriving (Show)

-- EXPOSING

data Exposing
  = Open
  | Explicit [Exposed]
  deriving (Show)

data Exposed
  = Lower (A.Located Name)
  | Upper (A.Located Name) Privacy
  | Operator A.Region Name
  deriving (Show)

data Privacy
  = Public A.Region
  | Private
  deriving (Show)
