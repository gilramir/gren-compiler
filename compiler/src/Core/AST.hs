{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wall #-}

-- | The Core IR: the compiler's waist.
--
-- @docs/core.md@ §C2 is the specification and this module is meant to be read
-- beside it. Core is a typed, explicit-datatype IR lowered from 'AST.Canonical'
-- plus the solved type annotations — GHC Core / OCaml Lambda shaped, not STG
-- shaped. Every binder and every node carries a type and a source span, and
-- datatype declarations and patterns are preserved.
--
-- @
-- source ─▶ parse ─▶ canonicalize ─▶ typecheck ─▶ CORE ─▶ passes ─▶ CORE' ─▶ backends
--                                                  ▲                   ▲
--                                     golden test compares this    backends read this
-- @
--
-- Three properties this module exists to hold, each of which a backend depends
-- on:
--
--   * __Arity is explicit__ (C3). Lambdas and applications are n-ary, because
--     every backend has fixed-arity functions. Partial application is an
--     'ELam' in Core rather than something a backend has to infer.
--   * __Patterns are preserved__ (C4). Decision trees are an optional
--     Core→Core pass whose output is still Core, so the BEAM backend — which
--     has real multi-clause dispatch — can skip it and lose nothing.
--   * __Type and witness abstraction are separate nodes__ (C2). Specialization
--     erases exactly 'ETyLam', 'ETyApp', 'EWitLam' and 'EWitApp' and nothing
--     else, so "has this module been specialized?" is a syntactic question.
module Core.AST
  ( -- * Modules
    Module (..),
    DataDecl (..),
    Alias (..),
    Signature (..),
    Named (..),
    Step (..),
    Ctor (..),
    Transparency (..),
    ClassDecl (..),
    Openness (..),
    InstanceDecl (..),
    Origin (..),
    Extern (..),
    ExternImpl (..),
    ExternLanguage (..),
    Main (..),

    -- * Names
    QualName (..),
    Field,
    Text,

    -- * Types
    Type (TVar, TCon, TFun, TRecord, TForall),
    typeId,
    typeHeight,
    typeIsClosed,
    Constraint (..),

    -- * Expressions
    Expr (..),
    Expr_ (..),
    Binder (..),
    Bind (..),
    Alt (..),
    Pattern (..),
    Literal (..),
    CrashKind (..),

    -- * Spans
    Span (..),
    FileId (..),
    FileTable,

    -- * Helpers
    typeOf,
    spanOf,
    isSpecialized,
  )
where

import Core.Prim (PrimOp)
import Data.IORef (IORef, atomicModifyIORef', newIORef)
import Data.Int (Int32, Int64)
import Data.Map qualified as Map
import Data.Name (Name)
import Data.Utf8 qualified as Utf8
import Data.Word (Word32, Word64)
import Gren.ModuleName qualified as ModuleName
import System.IO.Unsafe (unsafePerformIO)

-- NAMES

-- | A name that has a home. Core has no unqualified globals: 'EVar' is always
-- a local binder and 'EGlobal' always carries the module it came from.
data QualName = QualName
  { _qnHome :: !ModuleName.Canonical,
    _qnName :: !Name
  }
  deriving (Eq, Ord, Show)

-- | A record field name. Fields are stored __alphabetically__ everywhere they
-- appear — in 'TRecord', 'ERecord', 'EUpdate' and 'PRecord' — which is what
-- makes structural record types compare canonically, and what @classes.md@
-- §2.2's derived 'Ord' agrees with.
type Field = Name

-- | Text: the characters themselves, UTF-8 encoded.
--
-- Deliberately __not__ 'Gren.String', which is not text. That type holds
-- JavaScript string-literal /source/ — escapes left as the backslash-u
-- sequences they were written as, because the JS backend pastes them straight
-- into its output — so @\"A\"@ and @\"\\u{41}\"@ are two different values
-- standing for one string. C10's byte-identical Core cannot rest on a
-- representation where that is true, and neither can a second frontend, which
-- would have no reason to invent the same escaping.
--
-- "Core.Lower.Literal" is the decoder. The phantom type is the point of
-- declaring this at all: it makes putting the undecoded form here a type
-- error rather than a thing to remember.
data CORE_TEXT

type Text = Utf8.Utf8 CORE_TEXT

-- SPANS

-- | An index into a module's 'FileTable'.
--
-- A span names a file rather than assuming the enclosing module's, because a
-- Core→Core pass may inline an expression across a module boundary and the
-- span has to survive it. In the wire format this is a varint (C5).
newtype FileId = FileId Int
  deriving (Eq, Ord, Show)

-- | The interned table a module's spans index into.
--
-- C2 writes this as @FileId -> FilePath@, and it is a module name instead. A
-- path is where a machine happened to keep the source — absolute on one
-- machine, package-relative on another, different again from a tarball — and
-- C10's gate is that two frontends produce byte-identical Core, which a path
-- cannot survive. A canonical module name is stable, identifies the source
-- exactly as precisely, and resolving one to a path for an error message is
-- the build system's job. See "Core.Lower.Module".
type FileTable = Map.Map FileId ModuleName.Canonical

-- | Where a node came from. C5: __every__ node carries one, not only the ones
-- that can fail, because spans feed error messages, D12's constraint
-- provenance, @Debug.todo@, D19's stack-exhaustion report and future debug
-- info. Three varints per node is the whole cost.
data Span = Span
  { _spanFile :: !FileId,
    _spanStartRow :: !Word32,
    _spanStartCol :: !Word32,
    _spanEndRow :: !Word32,
    _spanEndCol :: !Word32
  }
  deriving (Eq, Ord, Show)

-- TYPES

-- | A Core type, __interned__ (geng-lang @m3-sweep.md@ §SW44, D743): every
-- type is built through one process-wide table, so two equal types are one
-- value with one '_typeId', and building one costs its arity, not its size.
-- Before, every node carried a copy of its own, and a type of size /s/ at /n/
-- nodes cost /n·s/ wherever it was built, compared or written.
--
-- It is matched and built through the five pattern synonyms below exactly as
-- the five constructors it used to have, so no reader changes.
--
-- __An id decides equality and nothing else.__ Modules are built on several
-- threads, so the order types are first met, and with it every id, differs
-- from run to run. '==' is the ids'; 'compare' is the derived order the
-- constructors had, the same in every run, short-cut where two subtrees'
-- ids agree. Nothing iterated into output may be keyed on an id.
data Type = Type
  { _typeId :: !Int,
    _typeHeight :: !Int,
    _typeClosed :: !Bool,
    _typeNode :: !TypeNode
  }

-- | One level of a 'Type'. The constructors are in the order 'Type''s were,
-- which is what keeps the derived 'Ord' the one Core has always had.
data TypeNode
  = TVar_ !Name
  | TCon_ !QualName ![Type]
  | TFun_ ![Type] !Type
  | TRecord_ ![(Field, Type)] !(Maybe Name)
  | TForall_ ![Name] ![Constraint] !Type
  deriving (Eq, Ord)

{-# COMPLETE TVar, TCon, TFun, TRecord, TForall #-}

pattern TVar :: Name -> Type
pattern TVar name <- (_typeNode -> TVar_ name)
  where
    TVar name = intern (TVar_ name)

-- | @Int@, @Array a@, @Dict k v@, @MyType a b@
pattern TCon :: QualName -> [Type] -> Type
pattern TCon name args <- (_typeNode -> TCon_ name args)
  where
    TCon name args = intern (TCon_ name args)

-- | n-ary, per C3: the argument list is the function's real arity, not a
-- chain of one-argument arrows to be recovered by analysis.
pattern TFun :: [Type] -> Type -> Type
pattern TFun args result <- (_typeNode -> TFun_ args result)
  where
    TFun args result = intern (TFun_ args result)

-- | Closed (@Nothing@) or open with a row variable (@Just r@):
-- @{ x : Int }@ is @TRecord [("x", Int)] Nothing@ and @{ r | x : Int }@ is
-- @TRecord [("x", Int)] (Just "r")@. Fields alphabetical.
pattern TRecord :: [(Field, Type)] -> Maybe Name -> Type
pattern TRecord fields row <- (_typeNode -> TRecord_ fields row)
  where
    TRecord fields row = intern (TRecord_ fields row)

-- | Quantification and its constraints, together. D11 keeps constraints
-- single-parameter, which is what keeps resolution decidable.
pattern TForall :: [Name] -> [Constraint] -> Type -> Type
pattern TForall vars constraints body <- (_typeNode -> TForall_ vars constraints body)
  where
    TForall vars constraints body = intern (TForall_ vars constraints body)

-- | The type's number in this run's table. Equal types have equal ids; the
-- number itself means nothing from one run to the next.
typeId :: Type -> Int
typeId = _typeId

-- | One more than the tallest type inside it; a 'TVar' is 1. A constraint's
-- type is inside its 'TForall'.
typeHeight :: Type -> Int
typeHeight = _typeHeight

-- | Whether no type variable appears in it, bound or free: a substitution
-- leaves it as it is.
typeIsClosed :: Type -> Bool
typeIsClosed = _typeClosed

instance Eq Type where
  a == b = _typeId a == _typeId b

instance Ord Type where
  compare a b
    | _typeId a == _typeId b = EQ
    | otherwise = compare (_typeNode a) (_typeNode b)

-- | What the derived instance wrote.
instance Show Type where
  showsPrec d t =
    case _typeNode t of
      TVar_ name -> con "TVar" [showsPrec 11 name]
      TCon_ name args -> con "TCon" [showsPrec 11 name, showsPrec 11 args]
      TFun_ args result -> con "TFun" [showsPrec 11 args, showsPrec 11 result]
      TRecord_ fields row -> con "TRecord" [showsPrec 11 fields, showsPrec 11 row]
      TForall_ vars constraints body -> con "TForall" [showsPrec 11 vars, showsPrec 11 constraints, showsPrec 11 body]
    where
      con name fields =
        showParen (d > 10) (foldl (\acc f -> acc . showChar ' ' . f) (showString name) fields)

-- | A node with its children as their ids: what the table is keyed on, so a
-- look-up compares integers and names, never a whole type.
--
-- The ids come first in each, so most look-ups are settled on integers before
-- a name, a package and a module, is compared. Its order reaches nothing.
data Key
  = KVar !Name
  | KCon ![Int] !QualName
  | KFun ![Int] !Int
  | KRecord ![Int] ![Field] !(Maybe Name)
  | KForall !Int ![Int] ![Name] ![QualName]
  deriving (Eq, Ord)

-- | Every type this process has built (D744). Never emptied: a build's
-- distinct types are the types its modules write, the size of their wire
-- tables. A 'Map.Map' on the 'Key', not a hash table (D745), which would be a
-- new dependency for a log factor.
typeTable :: IORef (Map.Map Key Type)
typeTable = unsafePerformIO (newIORef Map.empty)
{-# NOINLINE typeTable #-}

-- | The one value for this node. Pure to its callers: the same node always
-- answers an equal type, whichever thread asks and whenever.
--
-- The key, and with it every child, is forced before the table is touched.
-- 'atomicModifyIORef'' leaves a thunk in the reference while it evaluates the
-- function, and a child built lazily would intern itself against that thunk,
-- which is the parent's own update: @<<loop>>@.
intern :: TypeNode -> Type
intern node =
  forceKey key `seq`
    height `seq`
      unsafePerformIO $
        atomicModifyIORef' typeTable $ \table ->
          case Map.lookup key table of
            Just t -> (table, t)
            Nothing ->
              let !t = Type (Map.size table + 1) height closed node
               in (Map.insert key t table, t)
  where
    key =
      case node of
        TVar_ name -> KVar name
        TCon_ name args -> KCon (map _typeId args) name
        TFun_ args result -> KFun (map _typeId args) (_typeId result)
        TRecord_ fields row -> KRecord (map (_typeId . snd) fields) (map fst fields) row
        TForall_ vars constraints body -> KForall (_typeId body) [_typeId t | CClass _ t <- constraints] vars [c | CClass c _ <- constraints]
    height =
      1 + case node of
        TVar_ _ -> 0
        TCon_ _ args -> tallest args
        TFun_ args result -> tallest (result : args)
        TRecord_ fields _ -> tallest (map snd fields)
        TForall_ _ constraints body -> tallest (body : [t | CClass _ t <- constraints])
    tallest = foldr (max . _typeHeight) 0
    closed =
      case node of
        TVar_ _ -> False
        TCon_ _ args -> all _typeClosed args
        TFun_ args result -> all _typeClosed (result : args)
        TRecord_ fields row -> null row && all (_typeClosed . snd) fields
        TForall_ _ _ _ -> False
{-# NOINLINE intern #-}

forceKey :: Key -> ()
forceKey key =
  case key of
    KVar _ -> ()
    KCon ids _ -> forceAll ids
    KFun ids result -> forceAll ids `seq` result `seq` ()
    KRecord ids _ _ -> forceAll ids
    KForall body ids _ _ -> body `seq` forceAll ids
  where
    forceAll = foldr seq ()

-- | Single-parameter only (D11).
data Constraint = CClass !QualName !Type
  deriving (Eq, Ord, Show)

-- DECLARATIONS

-- | A datatype declaration, preserved into Core because backends need layout
-- and because the class set is a published, semver-relevant property
-- (@classes.md@ §2.4).
data DataDecl = DataDecl
  { _dataName :: !QualName,
    _dataParams :: ![Name],
    _dataTransparency :: !Transparency,
    _dataCtors :: ![Ctor],
    -- | The published class set.
    _dataClasses :: ![QualName],
    -- | Whether the type is declared @\@affine@ (geng-lang @m4-own.md@ D921):
    -- a value of it is used at most once. The ownership checker reads it,
    -- and "Core.Pass.FloatIn", which moves nothing that names one (D976).
    _dataAffine :: !Bool
  }
  deriving (Eq, Show)

data Ctor = Ctor
  { _ctorName :: !QualName,
    _ctorTag :: !Int,
    _ctorFields :: ![Type]
  }
  deriving (Eq, Show)

-- | @classes.md@ §2.5. An abstract type derives nothing implicitly.
data Transparency
  = Transparent
  | Abstract
  deriving (Eq, Show)

data ClassDecl = ClassDecl
  { _classNameC :: !QualName,
    _classParam :: !Name,
    _classOpenness :: !Openness,
    _classMethods :: ![(Name, Type)]
  }
  deriving (Eq, Show)

-- | @Eq@, @Ord@ and @Inspect@ are 'Open'; @Num@, @Integral@, @Fractional@ and
-- @Bits@ are 'Closed', and their membership is a table lookup with no solver
-- cost and no superclass entailment (@classes.md@ §1.2).
data Openness
  = Open
  | Closed
  deriving (Eq, Show)

data InstanceDecl = InstanceDecl
  { _instClass :: !QualName,
    _instHead :: !Type,
    _instOrigin :: !Origin,
    _instMethods :: ![(Name, Expr)]
  }
  deriving (Eq, Show)

data Origin
  = Derived
  | Written
  deriving (Eq, Show)

-- | One compiled module's Core.
data Module = Module
  { _moduleName :: !ModuleName.Canonical,
    -- | The interned table this module's spans index into (C5).
    _moduleFiles :: !FileTable,
    _moduleData :: ![DataDecl],
    _moduleClasses :: ![ClassDecl],
    _moduleInstances :: ![InstanceDecl],
    -- | Top-level bindings, in a deterministic order (C6). Mutual recursion
    -- among them is expressed by the group being a single 'ELetRec'-shaped
    -- unit; see '_moduleDefsRec'.
    _moduleDefs :: ![Bind],
    -- | The names of top-level bindings that are part of a recursive group,
    -- so a backend that needs to emit them together can.
    _moduleDefsRec :: ![[QualName]],
    _moduleExports :: ![QualName],
    -- | What this module's @main@ is, if it declares one (C19).
    _moduleMain :: !(Maybe Main),
    -- | The @\@extern@ declarations this module makes, sorted by name (C6,
    -- D196). An extern is referred to by an 'EGlobal' like any top-level name,
    -- and it is here rather than among '_moduleDefs' because what it is bound
    -- to is the host's. One with a Geng body (D222) also has that body among
    -- '_moduleDefs', under the same name, and the backend keeps one of the two.
    _moduleExterns :: ![Extern],
    -- | The bindings @core@ wrote @\@inline@ on (D545, geng-lang
    -- @m3-bytes-access.md@ §BA13), sorted by name: "Core.Pass.Inline" opens
    -- them, and the copies "Core.Pass.Specialize" and "Core.Pass.Mono" make
    -- of them, whatever their size.
    _moduleInline :: ![QualName],
    -- | The type aliases this module declares whose body is a closed record,
    -- sorted by name (geng-lang @m3-embed.md@ D630). Every type in Core has
    -- its aliases expanded; these are kept only so that a native library's
    -- header can name a record that crosses into C by the name its author
    -- gave it. No pass reads them.
    _moduleAliases :: ![Alias],
    -- | Every signature in the module that names an argument or its result,
    -- top-level and @let@ alike, sorted by where its definition's binder
    -- starts (geng-lang @m4-refine.md@ §RF18, D824): what the refinement
    -- checker reads. No pass reads them, and a backend drops them with the
    -- module, which is the erasure D797 asks for.
    _moduleSignatures :: ![Signature],
    -- | The binder of every definition in the module written with a type
    -- signature, top-level and @let@ alike, exactly as its 'Bind' has it,
    -- sorted by where it starts (geng-lang @m4-own.md@ D920, §OW28): the
    -- ownership checker holds such a definition's affine parameters to the
    -- signature's @moved@ marks, and infers the rest. No pass reads them.
    _moduleTyped :: ![Binder]
  }
  deriving (Eq, Show)

-- | A type alias whose body is a closed record: @type alias Point = { x :
-- Int, y : Float }@, its body lowered as every Core type is.
data Alias = Alias
  { _aliasName :: !QualName,
    _aliasParams :: ![Name],
    _aliasType :: !Type
  }
  deriving (Eq, Show)

-- | A definition's named arguments and result (D814), by the definition's
-- binder exactly as its 'Bind' has it, which no other definition in the module
-- shares: a binder's span is where its name is written.
data Signature = Signature
  { _sigBinder :: !Binder,
    _sigNamed :: ![Named]
  }
  deriving (Eq, Show)

-- | One named argument or result, in the order they are written.
--
-- The binder is the name, the type it names with the name taken off, and the
-- name's span. The predicate is a 'Bool' expression whose 'EVar's are the
-- names of this signature or, in a @let@, of a signature around it (D823),
-- lowered as a body's expression is; the source is the predicate as written
-- (D812), empty when there is no predicate. A moved name is an argument whose
-- value the function takes (geng-lang @m4-own.md@ D920); it may have no
-- predicate, and nothing but the ownership checker reads it.
data Named = Named
  { _namedPath :: ![Step],
    _namedBinder :: !Binder,
    _namedPredicate :: !(Maybe Expr),
    _namedSource :: !Text,
    _namedMoved :: !Bool
  }
  deriving (Eq, Show)

-- | Where in a signature's type a name is: @[StepArg 1]@ is the second
-- argument, @[StepResult]@ the last arrow's target, @[StepArg 1, StepArg 0]@
-- the first argument of a callback that is the second argument.
data Step
  = StepArg !Int
  | StepResult
  deriving (Eq, Ord, Show)

-- | An @\@extern@ declaration (@ffi.md@ F1, @m1b-extern.md@ §H12, D196).
--
-- The binder is the name every reference uses and the declared type, which is
-- the extern's contract. The implementations are one per language, sorted by
-- language, and each has the names D77's table gives its language: a module
-- and a function for 'ExternJs' and 'ExternErlang', a symbol for 'ExternC'.
-- '_externPure' is @\@externPure@, which S2 publishes a count of.
data Extern = Extern
  { _externBinder :: !Binder,
    _externImpls :: ![ExternImpl],
    _externPure :: !Bool,
    -- | Whether the declaration has a Geng body (D222, @m1b-json.md@ §O17).
    -- When it does, the body is the module binding of the same name, which a
    -- backend with no implementation in its language compiles; when it does
    -- not, no binding has the name.
    _externHasBody :: !Bool
  }
  deriving (Eq, Show)

data ExternImpl = ExternImpl
  { _implLanguage :: !ExternLanguage,
    _implNames :: ![Text]
  }
  deriving (Eq, Show)

-- | D77's extern languages, in wire-code order.
data ExternLanguage
  = ExternJs
  | ExternErlang
  | ExternC
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | A module's entry point, as a declaration (C19, D85).
--
-- @main@ is an ordinary binding and stays one; what is /not/ a value is the
-- thing a runtime does with it, which depends on the binding's __type__ and not
-- on its body, so the choice is recorded here, beside the binding.
--
-- There is one kind left. D72 makes a @main@ a @Task Never {}@ on every
-- executing runtime, and @main : String@, @main : Html msg@ and
-- @Program flags model msg@ left with @Platform@ (@m1b-source.md@ §SO19, D273).
-- The type stays a type rather than becoming a flag, because the schema's
-- enum is where a later kind would go. The frontend has already rejected every
-- other shape by the time this is built (@Reporting.Error.Main@).
data Main
  = -- | @main : Task Never {}@ (D72, @m1b-source.md@ §SO12). The program ends
    -- when the task completes, and the task is all there is.
    MainTask
  deriving (Eq, Show)

-- EXPRESSIONS

-- | Every node carries its type and its span (C2).
data Expr = Expr
  { _exprValue :: !Expr_,
    _exprType :: !Type,
    _exprSpan :: !Span
  }
  deriving (Eq, Show)

data Expr_
  = -- | A local binder.
    EVar !Name
  | -- | Top-level or imported.
    EGlobal !QualName
  | ELit !Literal
  | -- | n-ary (C3).
    ELam ![Binder] !Expr
  | -- | n-ary (C3). A known function of arity /n/ applied to /n/ arguments is
    -- one 'EApp' and compiles to a direct @f\/N@ call; a partial application is
    -- an 'ELam' closing over the supplied arguments, so it is visible in Core
    -- rather than inferred by a backend.
    EApp !Expr ![Expr]
  | ELet ![Bind] !Expr
  | ELetRec ![Bind] !Expr
  | -- | Patterns are preserved (C4). The fallback is the incomplete-match
    -- crash, present only where the frontend could not prove exhaustiveness of
    -- a literal or array pattern set.
    ECase !Expr ![Alt] !(Maybe Expr)
  | -- | Saturated; the 'Int' is the constructor tag.
    ECtor !QualName !Int ![Expr]
  | -- | Fields alphabetical.
    ERecord ![(Field, Expr)]
  | EUpdate !Expr ![(Field, Expr)]
  | EAccess !Expr !Field
  | -- | An array literal. Primitive because array literals are surface syntax
    -- (C7).
    EArray ![Expr]
  | -- | Saturated. The set is enumerated in "Core.Prim" (C13).
    EPrim !PrimOp ![Expr]
  | -- | Join points (C15): a body that is reached from more than one place, and
    -- the jump to it. A decision tree is the producer — "Core.Pass.Case" — and a
    -- self tail call is the other one, "Core.Pass.TailCall".
    --
    -- Each 'Bind' binds one join. A join with parameters holds an 'ELam' and is
    -- entered by an 'EJump' carrying that many arguments; a join with none holds
    -- its body directly and is entered by @EJump j []@. Either way the binder's
    -- type is the type of what 'EJump' evaluates to.
    --
    -- __The rule that makes it a join point rather than a function__: an
    -- 'EJump' appears only in __tail position__ within the body of the 'EJoin'
    -- that binds it, and names a join in scope. A join is therefore not a
    -- value — it cannot be passed, returned or captured — which is what lets
    -- every backend compile it to a jump: a labelled block and a @break@ on JS,
    -- a local tail call on the BEAM, a @goto@ in C.
    EJoin ![Bind] !Expr
  | -- | Enter a join. Tail position only; see 'EJoin'.
    EJump !Name ![Expr]
  | -- | Type abstraction.    ⎫
    ETyLam ![Name] !Expr
  | -- | Type application.    ⎬ erased by specialization (R1)
    ETyApp !Expr ![Type]
  | -- | Witness abstraction. ⎪
    EWitLam ![Binder] !Expr
  | -- | Witness application. ⎭
    EWitApp !Expr ![Expr]
  | ECrash !CrashKind
  deriving (Eq, Show)

data Binder = Binder
  { _binderName :: !Name,
    _binderType :: !Type,
    _binderSpan :: !Span
  }
  deriving (Eq, Show)

data Bind = Bind
  { _bindBinder :: !Binder,
    _bindValue :: !Expr
  }
  deriving (Eq, Show)

data Alt = Alt
  { _altPattern :: !Pattern,
    _altBody :: !Expr
  }
  deriving (Eq, Show)

data Pattern
  = PVar !Binder
  | PWild
  | PLit !Literal
  | PCtor !QualName !Int ![Pattern]
  | PRecord ![(Field, Pattern)]
  | -- | The optional 'Binder' is the tail: @[ a, b, ..rest ]@.
    PArray ![Pattern] !(Maybe Binder)
  | PAs !Binder !Pattern
  deriving (Eq, Show)

-- | A scalar constant, at the width its type gives it.
--
-- There used to be an 'LIntLegacy' beside these carrying an unbounded
-- @Integer@, because M1a's gate was that the existing JS suite passed and a
-- pre-D2 @Int@ was a JavaScript double exact to 2^53 — so real programs held
-- literals past 'Int32' and they could not be an 'LInt' without changing the
-- program. It was a separate constructor rather than a widened 'LInt64' so
-- that deleting it would be a visible event with a compiler error at every
-- site, which is what D2's flag day wanted and what it got
-- (@docs\/m1b-int.md@ §I20).
data Literal
  = LInt !Int32
  | LInt64 !Int64
  | LUInt32 !Word32
  | LUInt64 !Word64
  | LFloat !Double
  | LFloat32 !Float
  | -- | A codepoint (C8). @Char@ is a Unicode scalar value, @Int32@-sized, on
    -- every backend — surrogates are not valid @Char@ values.
    LChar !Int32
  | -- | UTF-8 in the wire format.
    LString !Text
  deriving (Eq, Ord, Show)

-- | Why a program stops.
--
-- @Todo@ is @Debug.todo@: where it was written, as the text the lowering renders
-- (@TODO in module `Main` on line 19@, stock's words), and the message it was
-- handed, which is an expression because it need not be a literal (D335,
-- @m1a-lowering.md@ §L4). The message is the one child a crash has, and it runs
-- before the program stops.
data CrashKind
  = Todo !Text !Expr
  | IncompleteMatch
  | StackExhausted
  | Unreachable
  deriving (Eq, Show)

-- HELPERS

typeOf :: Expr -> Type
typeOf = _exprType

spanOf :: Expr -> Span
spanOf = _exprSpan

-- | Whether an expression is free of the four nodes specialization erases.
--
-- After specialization a well-formed Core module contains no 'ETyLam',
-- 'ETyApp', 'EWitLam' or 'EWitApp', so this is the check a backend can make
-- before assuming monomorphic code — and it is a syntactic check precisely
-- because C2 kept those four as their own nodes.
isSpecialized :: Expr -> Bool
isSpecialized (Expr e _ _) =
  case e of
    ETyLam _ _ -> False
    ETyApp _ _ -> False
    EWitLam _ _ -> False
    EWitApp _ _ -> False
    EVar _ -> True
    EGlobal _ -> True
    ELit _ -> True
    ECrash (Todo _ message) -> isSpecialized message
    ECrash _ -> True
    ELam _ body -> isSpecialized body
    EApp fn args -> all isSpecialized (fn : args)
    ELet binds body -> all (isSpecialized . _bindValue) binds && isSpecialized body
    ELetRec binds body -> all (isSpecialized . _bindValue) binds && isSpecialized body
    EJoin binds body -> all (isSpecialized . _bindValue) binds && isSpecialized body
    EJump _ args -> all isSpecialized args
    ECase scrut alts fallback ->
      isSpecialized scrut
        && all (isSpecialized . _altBody) alts
        && all isSpecialized fallback
    ECtor _ _ args -> all isSpecialized args
    ERecord fields -> all (isSpecialized . snd) fields
    EUpdate base fields -> isSpecialized base && all (isSpecialized . snd) fields
    EAccess base _ -> isSpecialized base
    EArray elems -> all isSpecialized elems
    EPrim _ args -> all isSpecialized args
