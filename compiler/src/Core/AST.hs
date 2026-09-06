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
    Manager (..),
    ManagerKind (..),
    Port (..),
    PortFlow (..),
    Converter (..),

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
    -- | The @effect module@ manager this module declares, if it declares one.
    _moduleManager :: !(Maybe Manager),
    -- | The @port@s this module declares, by name (C18).
    _modulePorts :: ![Port]
  }
  deriving (Eq, Show)

-- | What an @effect module@ declares, as a declaration rather than as an
-- expression (C17).
--
-- Registering a manager is a load-time effect on a runtime's own dictionary,
-- and the record it registers has that runtime's field names. Neither is a
-- value any Gren expression computes, so neither is written as one here: Core
-- names the five functions and the kind, and each backend assembles what its
-- runtime wants from them. The JS backend already has @_Platform_createManager@
-- and uses it.
--
-- @portable-core.md@ P3 deletes the whole construct at M1b, and this with it.
data Manager = Manager
  { _managerKind :: !ManagerKind,
    -- | The bindings a program enters the manager through: @command@,
    -- @subscription@, or both. These are ordinary bindings in '_moduleDefs' —
    -- @Platform.leaf "<module>"@ — and reaching one of them is what makes the
    -- manager live, exactly as the @Opt.Link@ to @$fx$@ does in the old
    -- pipeline.
    _managerEntries :: ![QualName],
    _managerInit :: !QualName,
    _managerOnEffects :: !QualName,
    _managerOnSelfMsg :: !QualName,
    -- | Present for 'ManagerCmd' and 'ManagerFx'.
    _managerCmdMap :: !(Maybe QualName),
    -- | Present for 'ManagerSub' and 'ManagerFx'.
    _managerSubMap :: !(Maybe QualName)
  }
  deriving (Eq, Show)

data ManagerKind
  = ManagerCmd
  | ManagerSub
  | ManagerFx
  deriving (Eq, Show)

-- | A @port@, as a declaration rather than as an expression (C18, D84).
--
-- A port /defines a name/ — unlike a manager, a program refers to it, so
-- ordinary reachability keeps it alive and no extra rule is needed. What it
-- does not define is a value any Gren expression computes: the runtime's port
-- constructor takes the wire name, the converter and the flags in its own
-- calling convention, and hands back the @Cmd@, @Sub@ or @Task@ the binding
-- stands for. So Core names the pieces and each backend assembles the call its
-- runtime wants, exactly as it does for a 'Manager'.
--
-- The pieces that /are/ ordinary Core are the converters, and they are the
-- whole of what @Optimize.Port@ generates: a JSON encoder or decoder built
-- from the payload type out of @Json.Encode@, @Json.Decode@ and @Maybe@.
--
-- @portable-core.md@ P3 rebuilds the port mechanism on @ffi.md@ F4 at M1b and
-- deletes this with it.
data Port = Port
  { -- | The binding a program refers to. Its name is also the wire name the
    -- runtime registers the port under; they are the same name in the source
    -- and there is no second one to carry.
    _portBinder :: !Binder,
    _portFlow :: !PortFlow
  }
  deriving (Eq, Show)

-- | Which way a payload crosses, and what converts it.
data PortFlow
  = -- | @port foo : Payload -> Cmd msg@. The converter encodes.
    PortOut !Converter
  | -- | @port foo : (Payload -> msg) -> Sub msg@. The converter decodes.
    PortIn !Converter
  | -- | @port foo : Input -> Task x Payload@, or @port foo : Task x Payload@
    -- with no input at all. The 'Maybe' is that distinction, and it is the one
    -- place a runtime's own spelling of "absent" would otherwise have had to
    -- be written into Core — the JS runtime's is a @null@ in the argument
    -- position, which is not a Gren value and not something Core can say.
    PortTask !(Maybe Converter) !Converter
  deriving (Eq, Show)

-- | How one payload crosses the boundary.
data Converter = Converter
  { -- | The payload is @Bytes@, and the runtime moves it whole rather than
    -- through JSON.
    _convBytes :: !Bool,
    -- | The encoder — @payload -> Json.Encode.Value@ — or the decoder —
    -- @Json.Decode.Decoder payload@ — as ordinary Core.
    --
    -- @Basics.identity@ when '_convBytes', which is what "no conversion" is
    -- as an expression, and not dead weight: a @Bytes@ /outgoing/ port really
    -- does apply it before taking the payload's buffer.
    _convCode :: !Expr
  }
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
  | -- | __Transitional; removed at M1b.__
    --
    -- D2 makes @Int@ 32-bit, but that lands at M1b and M1a's gate is that the
    -- existing JS test suite passes with the JS backend reading Core. Until
    -- then @Int@ is a JS double, exact to 2^53, and real programs hold literals
    -- past 'Int32' — every millisecond timestamp since 1970, for one. Those
    -- cannot be an 'LInt' without changing the program.
    --
    -- So the pre-D2 @Int@ gets its own constructor rather than being quietly
    -- widened into one of the specified ones. Deleting it is then a visible
    -- event with a compiler error at every site, which is what M1b wants; a
    -- widened 'LInt64' would have compiled silently and left D2 half-applied.
    LIntLegacy !Integer
  deriving (Eq, Ord, Show)

data CrashKind
  = Todo !Text
  | IncompleteMatch
  | StackExhausted
  | Unreachable
  deriving (Eq, Ord, Show)

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
