{-# LANGUAGE OverloadedStrings #-}
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
    Type (..),
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
import Data.Int (Int32, Int64)
import Data.Map qualified as Map
import Data.Name (Name)
import Data.Utf8 qualified as Utf8
import Data.Word (Word32, Word64)
import Gren.ModuleName qualified as ModuleName

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

data Type
  = TVar !Name
  | -- | @Int@, @Array a@, @Dict k v@, @MyType a b@
    TCon !QualName ![Type]
  | -- | n-ary, per C3: the argument list is the function's real arity, not a
    -- chain of one-argument arrows to be recovered by analysis.
    TFun ![Type] !Type
  | -- | Closed (@Nothing@) or open with a row variable (@Just r@):
    -- @{ x : Int }@ is @TRecord [("x", Int)] Nothing@ and @{ r | x : Int }@ is
    -- @TRecord [("x", Int)] (Just "r")@. Fields alphabetical.
    TRecord ![(Field, Type)] !(Maybe Name)
  | -- | Quantification and its constraints, together. D11 keeps constraints
    -- single-parameter, which is what keeps resolution decidable.
    TForall ![Name] ![Constraint] !Type
  deriving (Eq, Ord, Show)

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
    _dataClasses :: ![QualName]
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
    _moduleExterns :: ![Extern]
  }
  deriving (Eq, Show)

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
