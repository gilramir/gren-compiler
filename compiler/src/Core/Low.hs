{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | @Low@: the stage between Core and C, and the Core → C spike's actual
-- deliverable (@docs/m1a-c-spike.md@ §X6).
--
-- D4 says the C backend is __two__ stages, @Core → Low → printer@, and
-- @DESIGN.md@ §4.3a attaches a condition to it: "it is only cheap if the C
-- backend is built as /two/ stages… If those decisions instead get made inside
-- the C emitter, 'add LLVM later' becomes 'write a second native backend'." A
-- spike is exactly where that condition is most likely to be quietly dropped,
-- so it is the structure here rather than advice.
--
-- __Everything representational is decided in this module.__ Closure
-- conversion, the calling convention, the layout of every record and every
-- datatype, and every allocation site. "Generate.LowC" is a printer: it is
-- handed 'Rep' and 'TypeId' and never sees a 'Core.Type'. That is the cheap
-- test of the split (§X6) and 'lower' holds it by construction — no 'Core.Type'
-- appears anywhere in this module's exports.
--
-- __The other output is the finding.__ §X9 makes the spike's criterion a
-- written list — everything @Low@ had to compute that Core does not carry — and
-- the honest way to produce that list is mechanically, as this module goes. So
-- 'lower' returns 'Note's alongside the program and each one is classified
-- 'Derived', 'Assumed' or 'Absent'. A list written by hand afterwards is a list
-- of what the author remembered.
module Core.Low
  ( -- * The program
    Program (..),
    Fun (..),
    Group (..),
    Expr (..),
    Lit (..),

    -- * Representation — what the printer is allowed to know
    Rep (..),
    TypeId (..),
    RecordLayout (..),
    DataLayout (..),
    CtorLayout (..),

    -- * The finding (§X9)
    Note (..),
    Source (..),

    -- * Lowering
    lower,
    renderNotes,
  )
where

import Control.Monad.State.Strict (State, gets, modify', runState)
import Core.AST qualified as Core
import Core.Program (Linked (..), Missing (..), MissingKind (..))
import Core.Program qualified as Program
import Data.ByteString.Builder qualified as B
import Data.Char qualified as Char
import Data.List qualified as List
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Utf8 qualified as Utf8
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg

-- REPRESENTATION

-- | An index into one of the program's layout tables.
--
-- The printer turns this into a C struct name and nothing else. It is an
-- integer rather than a 'Core.QualName' because a record type has no name —
-- Gren records are structural, so two modules' @{ x : Int }@ are one layout —
-- and giving datatypes the same currency keeps the printer's job uniform.
newtype TypeId = TypeId Int
  deriving (Eq, Ord, Show)

-- | What a value /is/, at the C level. R2 and R2.1 are the specification.
--
-- This is the entire vocabulary "Generate.LowC" has. Note what is not here:
-- there is no @RAny@, no boxed universal, no tag bit. R2 says native has "no
-- uniform boxed representation; monomorphization is mandatory", so a 'Rep' is
-- always exact, and §X4's monomorphic-programs-only limit is what makes that
-- reachable at M1a.
data Rep
  = -- | @int32_t@ (R2.1, D2).
    RInt
  | -- | @double@ (R2.1).
    RFloat
  | -- | @int32_t@ holding a Unicode scalar value (R2.1, C8).
    RChar
  | -- | @geng_string *@ — the C kernel's, not @core@'s (§X10: not @core@ on C).
    RString
  | -- | The empty record. One value, so it needs no storage at all.
    RUnit
  | -- | A datatype whose every constructor is nullary, which is therefore an
    -- @int32_t@ tag and __not a pointer__. @Bool@ is the one that matters:
    -- without this, every @if@ in the spike allocates.
    REnum !TypeId
  | -- | A datatype with at least one constructor carrying a field: a pointer to
    -- @{ tag; payload }@.
    RData !TypeId
  | -- | A record: a pointer to a struct whose fields are in alphabetical order
    -- (R2).
    RRecord !TypeId
  | -- | @geng_closure *@ — a code pointer and its captured environment.
    RClosure
  deriving (Eq, Ord, Show)

-- | A record's layout: its fields, alphabetical, with each field's 'Rep'.
--
-- Alphabetical is R2's word and it is also Core's — 'Core.AST.Field' says
-- fields are stored alphabetically in @TRecord@, @ERecord@ and @PRecord@
-- alike — so the order is /derived/ and not chosen here. That is a 'Derived'
-- note and one of the clearest cases of Core carrying enough.
data RecordLayout = RecordLayout
  { _rlId :: !TypeId,
    _rlFields :: ![(Name, Rep)]
  }
  deriving (Show)

-- | A datatype's layout.
data DataLayout = DataLayout
  { _dlId :: !TypeId,
    _dlName :: !String,
    _dlCtors :: ![CtorLayout],
    -- | Every constructor nullary, so the whole type is its tag ('REnum').
    _dlEnum :: !Bool
  }
  deriving (Show)

data CtorLayout = CtorLayout
  { _clTag :: !Int,
    _clName :: !String,
    _clFields :: ![Rep]
  }
  deriving (Show)

-- THE FINDING

-- | One thing @Low@ needed in order to emit C. §X9.
data Note = Note
  { -- | What was needed.
    _noteWhat :: !String,
    _noteSource :: !Source
  }
  deriving (Eq, Ord, Show)

-- | Where @Low@ got it, which is the whole classification §X9 asks for.
data Source
  = -- | Read off Core. Core working: this is what an IR waist is for. The
    -- 'String' names the construct it came from.
    Derived !String
  | -- | Core is silent and @Low@ chose. Safe here, but a native-side obligation
    -- that has to be written down rather than rediscovered.
    Assumed !String
  | -- | Core cannot express it and @Low@ had to get it from outside. This is
    -- the serious result — a Core change to make at M1b.
    Absent !String
  deriving (Eq, Ord, Show)

-- THE PROGRAM

-- | A whole C-able program: layouts, functions, and the root to print.
data Program = Program
  { _lowRecords :: ![RecordLayout],
    _lowDatas :: ![DataLayout],
    -- | Top-level functions and CAFs, in link order. A CAF is a 'Fun' with no
    -- parameters; §X8's bump allocator never frees, so a CAF is computed once
    -- into a static slot and the printer emits the guard.
    _lowFuns :: ![Fun],
    -- | The binding the program exists to compute (§X3), and its 'Rep' — which
    -- is how @main()@ knows what to print.
    _lowRoot :: !(String, Rep),
    -- | Kernel functions the C runtime must supply, deduplicated. §X5 bounds
    -- this by the linker's own @missing@ list.
    _lowKernel :: ![String],
    -- | The mutually-recursive groups that need a trampoline (D14).
    _lowGroups :: ![Group],
    -- | @Basics.True@'s tag and @Basics.False@'s, in that order.
    --
    -- __The hand-written C kernel cannot be written without this.__ A
    -- comparison returns a @Bool@, the generated code @switch@es on Core's own
    -- constructor tags, and those tags are not C's @0@ and @1@: @core@ declares
    -- @True@ first, so __@True@ is 0 and @False@ is 1__ and a kernel function
    -- that returns @a <= b@ returns @False@ for every true comparison. Measured
    -- 2026-09-06 by reading the emitted Core, not by debugging the C.
    --
    -- So "Generate.LowC" emits these as @#define@s and @geng_kernel.c@ is
    -- compiled against them. It is a good result rather than an awkward one:
    -- the layout is Core's, it is derivable, and the alternative — a convention
    -- agreed by hand in two files — is exactly the kind of thing that is
    -- silently wrong.
    _lowBoolTags :: !(Maybe (Int, Int)),
    _lowNotes :: ![Note]
  }

-- | A top-level function after closure conversion.
--
-- __The calling convention__, decided here and nowhere else: a top-level
-- function of arity /n/ is a C function of /n/ arguments taking its captured
-- environment, if it has one, as a leading @geng_env *@. Nothing is curried;
-- Core is already n-ary (C3), so arity is read off 'Core.AST.ELam' rather than
-- recovered.
data Fun = Fun
  { _funName :: !String,
    -- | Non-empty when this function was a lambda that captured something. A
    -- top-level binding captures nothing.
    _funCaptures :: ![(Name, Rep)],
    _funParams :: ![(Name, Rep)],
    _funResult :: !Rep,
    _funBody :: !Expr,
    -- | True for a nullary top-level binding: computed once, memoised in a
    -- static slot.
    _funIsCaf :: !Bool,
    -- | The trampoline group this function belongs to, and its index in it.
    -- 'Nothing' for the ordinary case, which is nearly every function.
    _funGroup :: !(Maybe (String, Int))
  }

-- | A mutually-recursive group, and the trampoline's layout.
--
-- The bounce has to carry the arguments of whichever member is entered next,
-- and R2 gives native no uniform boxed representation to carry them in — so
-- the payload is a union over the members' parameter lists, computed here.
-- That is a layout decision of exactly the kind the spike exists to test, and
-- Core supplies what it needs: 'Core.Program._progRecursive' says which
-- bindings are in the group, and every binder carries its type.
--
-- All members share '_grResult': a tail call's result /is/ its caller's, so
-- every member of a tail-calling chain returns the same type. A group where
-- that is not true is not trampolined and is noted instead.
data Group = Group
  { _grName :: !String,
    _grResult :: !Rep,
    -- | Each member's C name and parameters, in the order the bounce's tag
    -- numbers them.
    _grMembers :: ![(String, [(Name, Rep)])]
  }

data Lit
  = LInt !Integer
  | LFloat !Double
  | LChar !Int
  | LString !String
  deriving (Show)

-- | @Low@'s expressions. Every one of these has a direct C spelling and none of
-- them needs a type to print.
data Expr
  = -- | A scalar constant, __with the representation it is used at__.
    --
    -- The 'Rep' is not derivable from the 'Lit'. At M1a Core spells every
    -- integer literal 'Core.AST.LIntLegacy', so the @2@ in @x / 2@ where @x@ is
    -- a @Float@ is an integer literal at @double@ -- and a printer that read the
    -- constructor would emit @INT32_C(2)@ and call the wrong kernel function.
    -- The representation comes from the node's Core type.
    XLit !Lit !Rep
  | XVar !Name !Rep
  | -- | Read a captured variable out of the environment.
    XCapture !Name !Rep
  | XLet !Name !Rep !Expr !Expr
  | -- | @Bool@ is an 'REnum', so this is a C @if@ and allocates nothing.
    XIf !Expr !Expr !Expr !Rep
  | -- | Switch on a datatype tag. The scrutinee is already the tag.
    XSwitch !Expr ![(Int, Expr)] !(Maybe Expr) !Rep
  | -- | A saturated call to a known top-level function: a direct @f(...)@.
    XCallTop !String ![Expr] !Rep
  | -- | A call into the hand-written C kernel (§X5).
    XCallKernel !String ![Expr] !Rep
  | -- | A call through a closure: the indirect case, and the only one that
    -- costs a pointer hop.
    XCallClosure !Expr ![Expr] !Rep
  | -- | Read a top-level nullary binding, through its memoising accessor.
    XCaf !String !Rep
  | -- | Allocate a closure: a code pointer and the captured values. An
    -- allocation site, so it goes through @geng_alloc()@ (§X8).
    XMakeClosure !String ![Expr]
  | XMakeRecord !TypeId ![Expr]
  | XField !Expr !Name !Rep
  | -- | Allocate a constructor. Nullary constructors of an 'REnum' type do not
    -- reach here; they are 'XLit'-like tags via 'XTagOf'.
    XMakeData !TypeId !Int ![Expr]
  | -- | The tag of a value, as an @int32_t@.
    XTagOf !Expr !TypeId
  | -- | A nullary constructor of an enum datatype: just its tag.
    XEnumTag !TypeId !Int
  | -- | Field /i/ of the payload of constructor /tag/.
    XPayload !Expr !TypeId !Int !Int !Rep
  | -- | A join point (C15): a label, and the expression that may jump to it.
    -- D80 wrote this with C exactly in mind — "a labelled block and a @break@ on
    -- JS, a local tail call on the BEAM, __a @goto@ in C__".
    XJoin !Name ![(Name, Rep)] !Expr !Expr
  | -- | Enter a join. Tail position only, which Core already guarantees.
    XJump !Name ![Expr]
  | -- | A tail call to another member of this function's recursive group:
    -- D14's trampoline, and the one place the spike does not simply call.
    --
    -- "Core.Pass.TailCall" turns a /self/ tail call into a join point, which is
    -- a @goto@ — but it cannot do that across two functions, and a mutual tail
    -- call is an ordinary call that grows the C stack. So a member of a
    -- multi-member recursive group does not call its sibling: it records which
    -- sibling and with what arguments, and returns to the loop that entered it.
    --
    -- Measured: without this, @mutual-recursion@ at ten million dies with
    -- SIGSEGV. With it, it runs in constant stack.
    XBounce !String ![Expr]
  | XCrash !String !Rep
  deriving (Show)

-- LOWERING

-- | What the walk carries.
data Env = Env
  { -- | Record layouts, interned by their alphabetical field/'Rep' list.
    _envRecords :: !(Map [(Name, Rep)] TypeId),
    _envRecordList :: ![RecordLayout],
    -- | Datatype layouts, by name.
    _envDatas :: !(Map Core.QualName DataLayout),
    _envDataList :: ![DataLayout],
    -- | The next 'TypeId'.
    _envNext :: !Int,
    -- | Lambdas lifted out, in the order they were found.
    _envLifted :: ![Fun],
    -- | A counter for generated names.
    _envFresh :: !Int,
    -- | Notes, newest first; deduplicated at the end.
    _envNotes :: !(Set Note),
    -- | Kernel names reached.
    _envKernel :: !(Set String),
    -- | Which top-level names are functions of known arity, so a saturated
    -- 'Core.AST.EApp' can become a direct call.
    _envArity :: !(Map Core.QualName Int),
    -- | Constructor tags and their owning datatype.
    _envCtors :: !(Map Core.QualName (Core.QualName, Int)),
    -- | @core@ bindings that are nothing but a kernel reference, mapped to the
    -- kernel name they stand for. See 'kernelAliases'.
    _envAlias :: !(Map Core.QualName Core.QualName),
    -- | Join parameters renamed away from the names they shadow. See
    -- 'lowerJoin'.
    _envRename :: !(Map Name Name),
    -- | The trampoline groups, once 'trampolines' has computed them.
    _envGroups :: ![Group],
    -- | Locals in scope, and whether each is a parameter or a capture.
    _envLocals :: !(Map Name Rep),
    _envCaptured :: !(Set Name)
  }

type L a = State Env a

note :: String -> Source -> L ()
note what src =
  modify' (\e -> e {_envNotes = Set.insert (Note what src) (_envNotes e)})

fresh :: String -> L Name
fresh prefix =
  do
    n <- gets _envFresh
    modify' (\e -> e {_envFresh = n + 1})
    return (Name.fromChars (prefix ++ show n))

-- | The whole spike: a linked Core program in, a C-able program and the finding
-- out.
--
-- The root is the binding §X3 put at the head of the link, and its 'Rep' is
-- what @main()@ prints.
lower :: Program.Program -> Core.QualName -> Either String Program
lower prog root =
  let datas = Program._progData prog
      ctors =
        Map.fromList
          [ (Core._ctorName c, (Core._dataName d, Core._ctorTag c))
          | d <- datas,
            c <- Core._dataCtors d
          ]
      arity =
        Map.fromList
          [ (q, length bs)
          | (q, Core.Bind _ (Core.Expr (Core.ELam bs _) _ _)) <- topLams (Program._progBindings prog)
          ]
      env0 =
        Env
          { _envRecords = Map.empty,
            _envRecordList = [],
            _envDatas = Map.empty,
            _envDataList = [],
            _envNext = 0,
            _envLifted = [],
            _envFresh = 0,
            _envNotes = Set.empty,
            _envKernel = Set.empty,
            _envArity = arity,
            _envCtors = ctors,
            _envAlias = kernelAliases (Program._progBindings prog),
            _envRename = Map.empty,
            _envGroups = [],
            _envLocals = Map.empty,
            _envCaptured = Set.empty
          }
      (result, env) = runState (lowerProgram prog root) env0
   in case result of
        Left err -> Left err
        Right (funs, rootRep) ->
          Right
            Program
              { _lowRecords = reverse (_envRecordList env),
                _lowDatas = reverse (_envDataList env),
                _lowFuns = funs ++ reverse (_envLifted env),
                _lowRoot = (cName root, rootRep),
                _lowGroups = _envGroups env,
                _lowKernel = Set.toAscList (_envKernel env),
                _lowBoolTags = boolTags (Program._progData prog),
                _lowNotes = Set.toAscList (_envNotes env)
              }

-- | The recursive groups that need a trampoline, and their layout. D14.
--
-- A group qualifies when it has more than one member, every member is a
-- function this program emits, and all of them return the same 'Rep'. The last
-- condition is not a restriction in practice — a tail call\'s result /is/ its
-- caller\'s result, so a chain of mutual tail calls returns one type — but it
-- is checked rather than assumed, and a group that fails it is noted and left
-- to call normally.
--
-- Single-member groups are not here. A self-recursive function\'s tail call is
-- already a join point by the time @Low@ sees it ("Core.Pass.TailCall", D82),
-- and D80 makes that a @goto@. D14\'s "self tail calls are already loops" is
-- therefore literally true and the trampoline is for the rest.
trampolines :: Program.Program -> [Fun] -> L [Group]
trampolines prog funs =
  fmap Maybe.catMaybes (mapM group (zip [(0 :: Int) ..] (Program._progRecursive prog)))
  where
    byName = Map.fromList [(_funName f, f) | f <- funs]
    group (i, members)
      | length members < 2 = return Nothing
      | otherwise =
          case traverse (\q -> Map.lookup (cName q) byName) members of
            Nothing -> return Nothing
            Just fs
              | any _funIsCaf fs -> return Nothing
              | otherwise ->
                  case List.nub (map _funResult fs) of
                    [result] ->
                      do
                        note
                          "a mutually-recursive group needed a trampoline"
                          ( Derived
                              "Core.Program._progRecursive names the group and every \
                              \binder carries its type, so the bounce's argument union \
                              \is computed rather than guessed. D14 decided the \
                              \trampoline; Core said who is in it"
                          )
                        return
                          ( Just
                              Group
                                { _grName = "geng_group" ++ show i,
                                  _grResult = result,
                                  _grMembers = [(_funName f, _funParams f) | f <- fs]
                                }
                          )
                    _ ->
                      do
                        note
                          "a mutually-recursive group whose members return different types"
                          ( Assumed
                              "Low does not trampoline it, so it calls normally and \
                              \grows the stack. No spike program reaches this"
                          )
                        return Nothing

-- | Rewrite each group member\'s tail calls to its siblings into 'XBounce', and
-- record which group and index each member is.
--
-- Done as a pass over the lowered body rather than during lowering, because
-- tail position is exactly the shape of "Generate.LowC"\'s @Dest@ and is
-- clearer here than a flag threaded through every case.
bounce :: [Group] -> [Fun] -> [Fun]
bounce groups funs =
  map one funs
  where
    index =
      Map.fromList
        [ (name, (_grName g, i))
        | g <- groups,
          (i, (name, _)) <- zip [0 ..] (_grMembers g)
        ]
    siblings =
      Map.fromList
        [ (name, Set.fromList (map fst (_grMembers g)))
        | g <- groups,
          (name, _) <- _grMembers g
        ]
    one fun =
      case Map.lookup (_funName fun) index of
        Nothing -> fun
        Just here ->
          fun
            { _funGroup = Just here,
              _funBody =
                markBounces
                  (Map.findWithDefault Set.empty (_funName fun) siblings)
                  (_funBody fun)
            }

-- | Turn tail calls to @members@ into 'XBounce', in tail position only.
--
-- Tail position is where the value becomes the function\'s result: the body of
-- a @let@, both arms of an @if@, every arm of a @switch@, and both halves of a
-- join. A call anywhere else has to return a value to the expression around it
-- and cannot be a bounce.
markBounces :: Set String -> Expr -> Expr
markBounces members expr =
  case expr of
    XCallTop name args _
      | Set.member name members -> XBounce name args
    XLet n r v body -> XLet n r v (markBounces members body)
    XIf c y n r -> XIf c (markBounces members y) (markBounces members n) r
    XSwitch sc arms fb r ->
      XSwitch
        sc
        [(t, markBounces members a) | (t, a) <- arms]
        (fmap (markBounces members) fb)
        r
    XJoin n ps b rest ->
      XJoin n ps (markBounces members b) (markBounces members rest)
    _ -> expr

-- | @core@ bindings that are nothing but a reference to a kernel function.
--
-- Measured on the first spike run, and it is the difference between a spike and
-- a @core@ port. @core@\'s @Basics.gren@ says
--
-- > add : number -> number -> number
-- > add = Gren.Kernel.Basics.add
--
-- so in Core @Basics.add@ is a binding whose whole body is
-- @EGlobal gren-lang/kernel:Basics.add@. Without this, @1 + 1@ compiles to a
-- closure allocated for @Basics.add@, a memoising accessor around it and an
-- indirect call through its code pointer — for an integer addition.
--
-- With it, the binding is not emitted at all and the call site names the C
-- kernel function directly. That is what makes §X5\'s six-function budget the
-- real number rather than an aspiration.
--
-- Note what this does /not/ do: it does not inline anything, and it does not
-- look through a binding that computes. The body has to be exactly a kernel
-- global, which is a syntactic test on Core.
kernelAliases :: [(Core.QualName, Core.Bind)] -> Map Core.QualName Core.QualName
kernelAliases binds =
  Map.fromList
    [ (q, k)
    | (q, Core.Bind _ (Core.Expr (Core.EGlobal k) _ _)) <- binds,
      isKernel k
    ]

-- | @True@'s tag and @False@'s, read off @core@'s own declaration.
boolTags :: [Core.DataDecl] -> Maybe (Int, Int)
boolTags datas =
  case [d | d <- datas, Core._dataName d == basics "Bool"] of
    (d : _) ->
      let tagOf n =
            Maybe.listToMaybe
              [ Core._ctorTag c
              | c <- Core._dataCtors d,
                Core._qnName (Core._ctorName c) == Name.fromChars n
              ]
       in (,) <$> tagOf "True" <*> tagOf "False"
    [] -> Nothing

-- | The bindings whose value is a lambda, so their arity is known statically.
topLams :: [(Core.QualName, Core.Bind)] -> [(Core.QualName, Core.Bind)]
topLams = filter (isLam . snd)
  where
    isLam (Core.Bind _ (Core.Expr (Core.ELam _ _) _ _)) = True
    isLam _ = False

lowerProgram :: Program.Program -> Core.QualName -> L (Either String ([Fun], Rep))
lowerProgram prog root =
  do
    mapM_ recordMissing (Program._progMissing prog)
    mapM_ layoutData (Program._progData prog)
    aliases <- gets _envAlias
    funs <-
      mapM
        lowerTop
        [(q, b) | LBind q b <- Program._progLinked prog, not (Map.member q aliases)]
    rootRep <- repOfBinding prog root
    case sequence funs of
      Left err -> return (Left err)
      Right fs ->
        do
          groups <- trampolines prog fs
          modify' (\e -> e {_envGroups = groups})
          return (Right (bounce groups fs, rootRep))

-- | §X5's budget, mechanically: the C kernel may implement only names the
-- linker already reports as @missing@, so the list is the linker's rather than
-- a matter of taste.
recordMissing :: Missing -> L ()
recordMissing (Missing q kind _) =
  case kind of
    MissingKernel -> return ()
    MissingDebug ->
      note
        ("Debug." ++ Name.toChars (Core._qnName q) ++ " has no Core")
        (Absent "the frontend routes Debug through its own module")
    MissingValue ->
      note
        (Program.qualToChars q ++ " is referred to and not defined")
        (Absent "a lowering bug, per Core.Program.MissingValue")

repOfBinding :: Program.Program -> Core.QualName -> L Rep
repOfBinding prog root =
  case [b | (q, b) <- Program._progBindings prog, q == root] of
    (Core.Bind (Core.Binder _ ty _) _ : _) -> repOf ty
    [] -> return RInt

-- LAYOUT

-- | A datatype's layout, and the one decision in it that matters.
--
-- __All-nullary datatypes are their tag.__ @Bool@ is the case that pays for
-- itself immediately: without it every @if@ in every spike program allocates a
-- two-word object to hold no fields. Core carries what this needs — 'Ctor'
-- lists its field types, so "every constructor is nullary" is a fold — so this
-- is 'Derived'.
layoutData :: Core.DataDecl -> L ()
layoutData d =
  do
    tid <- nextId
    ctors <-
      mapM
        ( \c ->
            do
              fs <- mapM repOf (Core._ctorFields c)
              return (CtorLayout (Core._ctorTag c) (cName (Core._ctorName c)) fs)
        )
        (Core._dataCtors d)
    let isEnum = all (null . _clFields) ctors
    let layout = DataLayout tid (cName (Core._dataName d)) ctors isEnum
    note
      ("layout of " ++ Program.qualToChars (Core._dataName d))
      (Derived "Core.AST.DataDecl: constructor tags and field types")
    if isEnum
      then
        note
          "a datatype whose constructors are all nullary is its tag, unboxed"
          (Derived "Core.AST.Ctor._ctorFields being empty for every constructor")
      else
        note
          "a datatype with a field is a pointer to { tag; payload }"
          (Derived "Core.AST.Ctor._ctorFields")
    modify'
      ( \e ->
          e
            { _envDatas = Map.insert (Core._dataName d) layout (_envDatas e),
              _envDataList = layout : _envDataList e
            }
      )

nextId :: L TypeId
nextId =
  do
    n <- gets _envNext
    modify' (\e -> e {_envNext = n + 1})
    return (TypeId n)

-- | Intern a record layout by its field list.
--
-- Gren records are structural: the layout /is/ the alphabetical field list, so
-- two modules that both write @{ x : Int, y : Int }@ get one struct. This is
-- where R2's "monomorphized struct, fields alphabetical" is actually performed.
recordId :: [(Name, Rep)] -> L TypeId
recordId fields =
  do
    seen <- gets _envRecords
    case Map.lookup fields seen of
      Just tid -> return tid
      Nothing ->
        do
          tid <- nextId
          let layout = RecordLayout tid fields
          modify'
            ( \e ->
                e
                  { _envRecords = Map.insert fields tid (_envRecords e),
                    _envRecordList = layout : _envRecordList e
                  }
            )
          return tid

-- | A Core type's representation. __This is the only place a 'Core.Type' is
-- read__, which is what makes §X6's test — the printer never sees one — hold by
-- construction rather than by discipline.
repOf :: Core.Type -> L Rep
repOf ty =
  case ty of
    Core.TCon q _
      | q == basics "Int" -> return RInt
      | q == basics "Float" -> return RFloat
      | q == basics "Bool" -> enumRep q
      | q == charMod "Char" -> return RChar
      | q == stringMod "String" -> return RString
      | otherwise ->
          do
            known <- gets _envDatas
            case Map.lookup q known of
              Just layout ->
                do
                  return (if _dlEnum layout then RData (_dlId layout) `seq` REnum (_dlId layout) else RData (_dlId layout))
              Nothing ->
                do
                  note
                    ("the representation of " ++ Program.qualToChars q)
                    ( Absent
                        "no reachable constructor, so Core.Program._progData omits the declaration"
                    )
                  return RClosure
    Core.TRecord fields Nothing ->
      do
        reps <- mapM (repOf . snd) fields
        tid <- recordId (zip (map fst fields) reps)
        note
          "a record's struct layout"
          (Derived "Core.AST.TRecord, whose fields are already alphabetical")
        return (RRecord tid)
    Core.TRecord fields (Just row) ->
      do
        note
          ("an open record { " ++ Name.toChars row ++ " | … } reached the native backend")
          ( Absent
              "R3 makes this a native-only compile error under monomorphization; \
              \the spike is monomorphic (X4) so it should not arise"
          )
        reps <- mapM (repOf . snd) fields
        tid <- recordId (zip (map fst fields) reps)
        return (RRecord tid)
    Core.TFun _ _ -> return RClosure
    Core.TVar v ->
      do
        note
          ("a bare type variable " ++ Name.toChars v ++ " needed a representation")
          ( Absent
              "specialization is M1b's (R1); X4 makes the spike's programs \
              \monomorphic so a TVar here means one is not"
          )
        return RClosure
    Core.TForall _ _ inner ->
      do
        note
          "a quantified type needed a representation"
          (Absent "R1's specialization would have erased it; it is M1b's")
        repOf inner

enumRep :: Core.QualName -> L Rep
enumRep q =
  do
    known <- gets _envDatas
    case Map.lookup q known of
      Just layout -> return (if _dlEnum layout then REnum (_dlId layout) else RData (_dlId layout))
      Nothing ->
        do
          note
            "Bool's layout was needed before its declaration was reachable"
            (Absent "Core.Program._progData omits a datatype with no reachable constructor")
          return RInt

basics :: String -> Core.QualName
basics = coreName "Basics"

charMod :: String -> Core.QualName
charMod = coreName "Char"

stringMod :: String -> Core.QualName
stringMod = coreName "String"

coreName :: String -> String -> Core.QualName
coreName modul n =
  Core.QualName
    (ModuleName.Canonical Pkg.core (Name.fromChars modul))
    (Name.fromChars n)

-- TOP LEVEL

-- | One top-level binding.
--
-- A lambda becomes a C function of its arity; anything else becomes a CAF —
-- computed once into a static slot, which is sound precisely because §X8's
-- allocator never frees and a spike program computes one value and exits.
lowerTop :: (Core.QualName, Core.Bind) -> L (Either String Fun)
lowerTop (q, Core.Bind (Core.Binder _ ty _) value) =
  case value of
    Core.Expr (Core.ELam binders body) _ _ ->
      do
        params <- mapM binderRep binders
        result <- resultRep ty (length binders)
        modify' (\e -> e {_envLocals = Map.fromList params, _envCaptured = Set.empty})
        body' <- lowerExpr body
        note
          "a function's arity"
          (Derived "Core.AST.ELam being n-ary (C3), so arity is read and not recovered")
        return
          ( Right
              Fun
                { _funName = cName q,
                  _funCaptures = [],
                  _funParams = params,
                  _funResult = result,
                  _funBody = body',
                  _funIsCaf = False,
                  _funGroup = Nothing
                }
          )
    _ ->
      do
        rep <- repOf ty
        modify' (\e -> e {_envLocals = Map.empty, _envCaptured = Set.empty})
        body' <- lowerExpr value
        return
          ( Right
              Fun
                { _funName = cName q,
                  _funCaptures = [],
                  _funParams = [],
                  _funResult = rep,
                  _funBody = body',
                  _funIsCaf = True,
                  _funGroup = Nothing
                }
          )

binderRep :: Core.Binder -> L (Name, Rep)
binderRep (Core.Binder n ty _) =
  do
    rep <- repOf ty
    return (n, rep)

-- | The result type of a function of the given arity.
--
-- Core's 'Core.AST.TFun' is n-ary too, so this is a lookup rather than a walk
-- down a chain of arrows — which is C3 paying for itself.
resultRep :: Core.Type -> Int -> L Rep
resultRep ty n =
  case ty of
    Core.TForall _ _ inner -> resultRep inner n
    Core.TFun args res
      | length args == n -> repOf res
      | length args > n -> repOf (Core.TFun (drop n args) res)
      | otherwise ->
          do
            note
              "a function's result type, where the lambda binds more than the arrow"
              ( Absent
                  "the annotation's arity and the ELam's disagree; Core has both \
                  \and does not say which is the calling convention"
              )
            repOf res
    _ -> repOf ty

-- EXPRESSIONS

lowerExpr :: Core.Expr -> L Expr
lowerExpr (Core.Expr e ty _) = lowerExpr_ ty e

lowerExpr_ :: Core.Type -> Core.Expr_ -> L Expr
lowerExpr_ ty expr =
  case expr of
    Core.ELit lit -> XLit <$> lowerLit lit <*> repOfLiteral ty lit
    Core.EVar n ->
      do
        locals <- gets _envLocals
        captured <- gets _envCaptured
        renames <- gets _envRename
        let n' = Maybe.fromMaybe n (Map.lookup n renames)
        let rep = Maybe.fromMaybe RClosure (Map.lookup n' locals)
        return (if Set.member n' captured then XCapture n' rep else XVar n' rep)
    Core.EGlobal q ->
      do
        arities <- gets _envArity
        ctors <- gets _envCtors
        aliases <- gets _envAlias
        case Map.lookup q ctors of
          Just (owner, tag) -> nullaryCtor owner tag
          Nothing
            | Map.member q aliases || isKernel q ->
                do
                  note
                    ("kernel " ++ Program.qualToChars q ++ " used as a value, not called")
                    ( Absent
                        "a C function is not a closure; giving one a closure \
                        \wrapper means emitting a shim per kernel arity, which \
                        \the spike's programs do not need and X10 keeps out"
                    )
                  return (XCrash "a kernel function used as a value" RClosure)
          Nothing ->
            case Map.lookup q arities of
              -- A known function used as a value: it has to become a closure,
              -- because C function pointers and closures are not the same
              -- thing and the call sites cannot tell them apart.
              Just _ ->
                do
                  note
                    "a top-level function used as a value rather than called"
                    (Derived "Core.AST.EGlobal in a non-head position")
                  return (XMakeClosure (cName q) [])
              Nothing -> return (XCaf (cName q) RClosure)
    Core.ELam binders body -> lowerLambda binders body
    Core.EApp f args -> lowerApp f args
    Core.ELet binds body -> lowerLet binds body
    Core.ELetRec binds body ->
      do
        note
          "a recursive local group"
          ( Assumed
              "Low lifts each member to a top level and ties the knot through \
              \the closure's environment; Core says the group is recursive and \
              \not how to allocate it"
          )
        lowerLet binds body
    Core.ECase scrut alts fallback -> lowerCase scrut alts fallback
    Core.ECtor q tag args -> lowerCtor q tag args
    -- The layout comes from __this node's own type__, not from the field
    -- expressions' types. It has to: an unannotated @{ x = 1, y = 2 }@ has
    -- field expressions whose Core type is still `number`, and laying the
    -- struct out from those would intern a second layout with the wrong
    -- representations while the annotated `{ x : Int, y : Int }` interned the
    -- right one. Measured: `records` emitted `geng_r0` with two `int32_t` and
    -- `geng_r1` with two `geng_closure *`, for one Gren record type.
    Core.ERecord fields ->
      do
        rep <- repOf ty
        vals <- mapM (lowerExpr . snd) fields
        case rep of
          RRecord tid -> return (XMakeRecord tid vals)
          _ ->
            do
              note
                "a record literal whose own Core type is not a TRecord"
                (Absent "the node's type did not resolve to a record")
              return (XCrash "a record with no layout" rep)
    Core.EAccess record field ->
      do
        rep <- repOfExpr record
        record' <- lowerExpr record
        case rep of
          RRecord tid ->
            do
              fieldRep <- fieldRepOf tid field
              return (XField record' field fieldRep)
          _ ->
            do
              note
                ("field ." ++ Name.toChars field ++ " read from a non-record representation")
                (Absent "the scrutinee's Core type did not resolve to a TRecord")
              return (XField record' field RClosure)
    Core.EUpdate _ _ ->
      do
        note
          "record update"
          ( Assumed
              "Low copies the struct and overwrites the named fields, which is \
              \an allocation Core does not name; EUpdate says which fields change"
          )
        return (XCrash "record update is not in the spike" RClosure)
    Core.EArray _ ->
      do
        note
          "an array literal"
          (Absent "Array is core's and X10 keeps core off C; the spike has no Array")
        return (XCrash "arrays are not in the spike" RClosure)
    Core.EPrim _ _ ->
      do
        note
          "an EPrim node"
          (Absent "C13's @prim table is M1b's (D81); at M1a Core emits none")
        return (XCrash "EPrim is not in the spike" RClosure)
    Core.EJoin binds body -> lowerJoin binds body
    Core.EJump n args -> XJump n <$> mapM lowerExpr args
    Core.ETyLam _ body ->
      do
        note "a type abstraction" (Absent "R1's specialization is M1b's")
        lowerExpr body
    Core.ETyApp body _ ->
      do
        note "a type application" (Absent "R1's specialization is M1b's")
        lowerExpr body
    Core.EWitLam _ body ->
      do
        note "a witness abstraction" (Absent "R1's specialization is M1b's")
        lowerExpr body
    Core.EWitApp body _ ->
      do
        note "a witness application" (Absent "R1's specialization is M1b's")
        lowerExpr body
    Core.ECrash kind -> return (XCrash (crashText kind) RClosure)

crashText :: Core.CrashKind -> String
crashText kind =
  case kind of
    Core.Todo t -> Utf8.toChars t
    Core.IncompleteMatch -> "incomplete match"
    Core.StackExhausted -> "stack exhausted"
    Core.Unreachable -> "unreachable"

-- | Core's @Int@ literal is 'Core.AST.LIntLegacy' at M1a and carries no width.
--
-- This is a real finding and it is worth stating precisely. D2 makes @Int@
-- 32-bit; 'Core.AST.LIntLegacy' holds an unbounded 'Integer' because M1a's gate
-- is that the existing JS suite passes, and a JS @Int@ is a double exact to
-- 2^53. So the literal itself does not say what C type it has: @Low@ takes the
-- width from the binder's type, which is @Basics.Int@, and the literal would
-- not have said. When D2 lands and 'Core.AST.LInt' replaces it, this note goes
-- away — which is exactly the sort of thing the list is for.
lowerLit :: Core.Literal -> L Lit
lowerLit lit =
  case lit of
    Core.LIntLegacy n ->
      do
        note
          "the width of an integer literal"
          ( Absent
              "Core.AST.LIntLegacy carries an unbounded Integer, so the literal \
              \does not say it is 32 bits; Low takes the width from the type. \
              \D2's LInt at M1b removes this"
          )
        return (LInt n)
    Core.LInt n -> return (LInt (fromIntegral n))
    Core.LInt64 n -> return (LInt (fromIntegral n))
    Core.LUInt32 n -> return (LInt (fromIntegral n))
    Core.LUInt64 n -> return (LInt (fromIntegral n))
    Core.LFloat d -> return (LFloat d)
    Core.LFloat32 f -> return (LFloat (realToFrac f))
    Core.LChar c -> return (LChar (fromIntegral c))
    Core.LString t -> return (LString (Utf8.toChars t))

-- | A literal's representation, which is a harder question than it looks.
--
-- Two facts about M1a Core meet here.
--
-- __An integer literal does not say its own width.__ 'Core.AST.LIntLegacy'
-- holds an unbounded 'Integer' because M1a\'s gate is that the existing JS
-- suite passes and a JS @Int@ is a double exact to 2^53. D2\'s @LInt@ at M1b
-- replaces it.
--
-- __An integer literal does not even say it is an integer.__ @core@ declares
-- @(\/) : Float -> Float -> Float@, so in @x \/ 2@ the @2@ is a @Float@ — and
-- Core spells it 'Core.AST.LIntLegacy' all the same, because that is what was
-- written. Reading the constructor gives @int32_t@ and calls
-- @geng_kernel_Basics_fdiv_d_i@, which does not exist. Measured on the
-- @float-arith@ program before this was here.
--
-- So the type wins where the type is concrete. Where it is a bare @number@ —
-- an unannotated literal the solver left polymorphic — there is nothing to
-- read, and @Low@ falls back to the literal\'s own shape and says so. That
-- fallback is a real gap and not a convenience: it is R1\'s specialization
-- doing the job at M1b.
repOfLiteral :: Core.Type -> Core.Literal -> L Rep
repOfLiteral ty lit =
  case ty of
    Core.TVar _ ->
      do
        note
          "a numeric literal whose Core type is still a type variable"
          ( Absent
              "an unannotated literal keeps Gren's `number`, so Core does not \
              \say whether it is an int32_t or a double; Low falls back to the \
              \literal's own shape. R1's specialization is what answers this"
          )
        return (shapeOf lit)
    Core.TForall _ _ inner -> repOfLiteral inner lit
    _ ->
      do
        rep <- repOf ty
        case rep of
          RClosure -> return (shapeOf lit)
          _ -> return rep

-- | What a literal looks like, when its type will not say.
shapeOf :: Core.Literal -> Rep
shapeOf lit =
  case lit of
    Core.LFloat _ -> RFloat
    Core.LFloat32 _ -> RFloat
    Core.LChar _ -> RChar
    Core.LString _ -> RString
    _ -> RInt

-- | The representation of what an expression evaluates to.
--
-- Every Core node carries its type ('Core.AST.typeOf'), which is the single
-- property this whole module leans on hardest: without it, @Low@ would be
-- re-inferring types to lay out values, and D4's split would not be affordable.
repOfExpr :: Core.Expr -> L Rep
repOfExpr e = repOf (Core.typeOf e)

fieldRepOf :: TypeId -> Name -> L Rep
fieldRepOf tid field =
  do
    records <- gets _envRecordList
    case [r | l <- records, _rlId l == tid, (f, r) <- _rlFields l, f == field] of
      (r : _) -> return r
      [] -> return RClosure

-- | A lambda that is not a top-level binding: lift it, and capture what it
-- refers to from outside.
--
-- __Closure conversion happens here and only here__, which is §X6's point.
-- Core does not say what a lambda captures — it says what is in scope and what
-- the body mentions, and the difference is a free-variable calculation @Low@
-- performs. That is an 'Assumed' entry and one of the clearest answers to "does
-- Core carry enough": it carries enough to /compute/ it, but it does not carry
-- it.
lowerLambda :: [Core.Binder] -> Core.Expr -> L Expr
lowerLambda binders body =
  do
    name <- fresh "geng_lam_"
    params <- mapM binderRep binders
    outer <- gets _envLocals
    let bound = Set.fromList (map fst params)
    let free = Set.toAscList (Set.difference (freeVars body) bound)
    let captures = [(n, r) | n <- free, Just r <- [Map.lookup n outer]]
    note
      "what a lambda captures"
      ( Assumed
          "Core gives scope and the body, not the capture set; Low computes the \
          \free variables. This is closure conversion and it is the spike's \
          \main representational decision"
      )
    saveLocals <- gets _envLocals
    saveCaptured <- gets _envCaptured
    modify'
      ( \e ->
          e
            { _envLocals = Map.union (Map.fromList params) (Map.fromList captures),
              _envCaptured = Set.fromList (map fst captures)
            }
      )
    body' <- lowerExpr body
    result <- repOfExpr body
    modify'
      ( \e ->
          e
            { _envLocals = saveLocals,
              _envCaptured = saveCaptured,
              _envLifted =
                Fun
                  { _funName = Name.toChars name,
                    _funCaptures = captures,
                    _funParams = params,
                    _funResult = result,
                    _funBody = body',
                    _funIsCaf = False,
                    _funGroup = Nothing
                  }
                  : _envLifted e
            }
      )
    captureVals <-
      mapM
        ( \(n, r) ->
            do
              wasCaptured <- gets (Set.member n . _envCaptured)
              return (if wasCaptured then XCapture n r else XVar n r)
        )
        captures
    return (XMakeClosure (Name.toChars name) captureVals)

-- | Application. The three cases are the calling convention.
lowerApp :: Core.Expr -> [Core.Expr] -> L Expr
lowerApp f args =
  do
    args' <- mapM lowerExpr args
    rep <- repOf . resultOf (length args) . Core.typeOf $ f
    case f of
      Core.Expr (Core.EGlobal q) _ _ ->
        do
          ctors <- gets _envCtors
          arities <- gets _envArity
          aliases <- gets _envAlias
          let target = Maybe.fromMaybe q (Map.lookup q aliases)
          case Map.lookup q ctors of
            Just (owner, tag) -> saturatedCtor owner tag args'
            Nothing
              | isKernel target ->
                  do
                    let n = kernelCName target ++ concatMap (repTag . repOfLow) args'
                    modify' (\e -> e {_envKernel = Set.insert n (_envKernel e)})
                    note
                      ("the C kernel must supply " ++ Program.qualToChars target)
                      ( Derived
                          "Core.Program's missing list, which X5 makes the budget"
                      )
                    note
                      "a kernel name had to be monomorphized by representation"
                      ( Derived
                          "core's Basics.add is `number -> number -> number` and \
                          \Utils.le is `comparable`, so one Core name is several C \
                          \functions. The call site's Core types are solved, so Low \
                          \computes which -- but Core names one function and C needs \
                          \one per Rep"
                      )
                    return (XCallKernel n args' rep)
              | otherwise ->
                  case Map.lookup q arities of
                    Just n
                      | n == length args' -> return (XCallTop (cName q) args' rep)
                      | otherwise ->
                          do
                            note
                              "an application that is not saturated"
                              ( Derived
                                  "C3 says a partial application is an ELam in Core, \
                                  \so a bare EApp of the wrong arity should not occur"
                              )
                            return (XCallClosure (XCaf (cName q) RClosure) args' rep)
                    Nothing -> return (XCallClosure (XCaf (cName q) RClosure) args' rep)
      _ ->
        do
          f' <- lowerExpr f
          return (XCallClosure f' args' rep)

-- | The result of applying a function type to /n/ arguments.
resultOf :: Int -> Core.Type -> Core.Type
resultOf n ty =
  case ty of
    Core.TForall _ _ inner -> resultOf n inner
    Core.TFun args res
      | length args == n -> res
      | length args > n -> Core.TFun (drop n args) res
      | otherwise -> res
    _ -> ty

-- | A representation's one-letter tag, for a monomorphized kernel name.
--
-- @Basics.add@ on two @Int@s is @geng_kernel_Basics_add_i_i@ and on two
-- @Float@s is @geng_kernel_Basics_add_d_d@. One Core name, several C
-- functions, and the suffix is what says which -- computed from the call
-- site's solved types, which is the whole reason Core is typed.
repTag :: Rep -> String
repTag rep =
  case rep of
    RInt -> "_i"
    RFloat -> "_d"
    RChar -> "_c"
    RString -> "_s"
    RUnit -> "_u"
    REnum _ -> "_e"
    RData _ -> "_p"
    RRecord _ -> "_r"
    RClosure -> "_f"

-- | A lowered expression's representation.
repOfLow :: Expr -> Rep
repOfLow expr =
  case expr of
    XLit _ r -> r
    XVar _ r -> r
    XCapture _ r -> r
    XCaf _ r -> r
    XLet _ _ _ rest -> repOfLow rest
    XIf _ _ _ r -> r
    XSwitch _ _ _ r -> r
    XCallTop _ _ r -> r
    XCallKernel _ _ r -> r
    XCallClosure _ _ r -> r
    XMakeClosure _ _ -> RClosure
    XMakeRecord tid _ -> RRecord tid
    XField _ _ r -> r
    XMakeData tid _ _ -> RData tid
    XTagOf _ _ -> RInt
    XEnumTag tid _ -> REnum tid
    XPayload _ _ _ _ r -> r
    XJoin _ _ _ rest -> repOfLow rest
    XJump _ _ -> RInt
    XBounce _ _ -> RInt
    XCrash _ r -> r

-- | Is this a @gren\/kernel@ name? Those are what §X5's C kernel implements.
isKernel :: Core.QualName -> Bool
isKernel (Core.QualName (ModuleName.Canonical pkg _) _) = pkg == Pkg.kernel

-- | @gren-lang\/kernel:Basics.add@ becomes @geng_kernel_Basics_add@.
kernelCName :: Core.QualName -> String
kernelCName (Core.QualName (ModuleName.Canonical _ raw) n) =
  "geng_kernel_" ++ mangle (ModuleName.toChars raw) ++ "_" ++ mangle (Name.toChars n)

-- | Core reaches a kernel name through the @core@ binding that wraps it, so a
-- call to @Basics.add@ is an 'Core.AST.EApp' of a @gren-lang\/core@ global whose
-- body is the kernel reference. The spike shortcuts that one hop: a @core@
-- binding whose whole body is a kernel global is the kernel function.
--
-- This is why the six-function budget is reachable at all. Without it every
-- arithmetic operator drags in @core@'s wrapper, its @Basics@ imports, and the
-- transitive closure §X2 measured.
lowerCtor :: Core.QualName -> Int -> [Core.Expr] -> L Expr
lowerCtor q tag args =
  do
    args' <- mapM lowerExpr args
    ctors <- gets _envCtors
    case Map.lookup q ctors of
      Just (owner, _) -> saturatedCtor owner tag args'
      Nothing ->
        do
          note
            ("constructor " ++ Program.qualToChars q ++ " has no datatype")
            (Absent "Core.Program._progData did not carry the declaration")
          return (XCrash "unknown constructor" RClosure)

saturatedCtor :: Core.QualName -> Int -> [Expr] -> L Expr
saturatedCtor owner tag args =
  do
    datas <- gets _envDatas
    case Map.lookup owner datas of
      Just layout
        | _dlEnum layout -> return (XEnumTag (_dlId layout) tag)
        | otherwise -> return (XMakeData (_dlId layout) tag args)
      Nothing -> return (XCrash "unknown datatype" RClosure)

nullaryCtor :: Core.QualName -> Int -> L Expr
nullaryCtor owner tag = saturatedCtor owner tag []

lowerLet :: [Core.Bind] -> Core.Expr -> L Expr
lowerLet binds body =
  do
    entries <-
      mapM
        ( \(Core.Bind b@(Core.Binder n _ _) value) ->
            do
              (_, rep) <- binderRep b
              value' <- lowerExpr value
              modify' (\e -> e {_envLocals = Map.insert n rep (_envLocals e)})
              return (n, rep, value')
        )
        binds
    body' <- lowerExpr body
    return (List.foldr (\(n, rep, v) acc -> XLet n rep v acc) body' entries)

-- | A join point is a label and a @goto@ (D80, §X7).
--
-- __The parameters are renamed, and the reason is C rather than Core.__
-- "Core.Pass.TailCall" turns @sumTo n acc = … sumTo (n - 1) (acc + n)@ into a
-- join whose parameters are also called @n@ and @acc@ — which is right, they
-- are the same loop variables — but the join body is emitted inline in the same
-- C function as the enclosing @sumTo@, so declaring them again is a
-- redeclaration in one scope and does not compile. Core has no scope problem;
-- C does, because a @goto@ target cannot be inside a block the jump comes from.
--
-- So the parameters get fresh names and references inside the body follow. This
-- is an 'Assumed' entry: Core said everything needed and @Low@ still had to do
-- something Core did not ask for, which is what the classification is for.
lowerJoin :: [Core.Bind] -> Core.Expr -> L Expr
lowerJoin binds body =
  do
    note
      "a join point"
      ( Derived
          "Core.AST.EJoin/EJump, which D80 wrote as a goto in C; Low does not \
          \have to discover that a block is joinable"
      )
    entries <-
      mapM
        ( \(Core.Bind (Core.Binder n _ _) value) ->
            case value of
              Core.Expr (Core.ELam bs inner) _ _ ->
                do
                  params <- mapM binderRep bs
                  renamed <-
                    mapM (\(pn, r) -> (\fresh_ -> (pn, fresh_, r)) <$> fresh "geng_p") params
                  note
                    "a join point's parameters had to be renamed"
                    ( Assumed
                        "the join binds the same names as the enclosing function \
                        \and both land in one C scope; Core has no such \
                        \constraint, so nothing in Core says to do it"
                    )
                  saveRename <- gets _envRename
                  modify'
                    ( \e ->
                        e
                          { _envLocals =
                              Map.union (Map.fromList [(f, r) | (_, f, r) <- renamed]) (_envLocals e),
                            _envRename =
                              Map.union (Map.fromList [(pn, f) | (pn, f, _) <- renamed]) (_envRename e)
                          }
                    )
                  inner' <- lowerExpr inner
                  modify' (\e -> e {_envRename = saveRename})
                  return (n, [(f, r) | (_, f, r) <- renamed], inner')
              _ ->
                do
                  value' <- lowerExpr value
                  return (n, [], value')
        )
        binds
    body' <- lowerExpr body
    return (List.foldr (\(n, ps, v) acc -> XJoin n ps v acc) body' entries)

-- | A @case@ becomes a C @switch@ on a tag, or an @if@ when the type is
-- @Bool@.
--
-- The patterns Core preserves (C4) are what makes this readable: @Low@ switches
-- on 'Core.AST.PCtor's tag, which Core supplies, rather than reconstructing a
-- discriminant. Nested patterns are not handled — the case pass (C4) flattens
-- them and §X7 runs the spike with it on.
lowerCase :: Core.Expr -> [Core.Alt] -> Maybe Core.Expr -> L Expr
lowerCase scrut alts fallback =
  do
    scrutRep <- repOfExpr scrut
    scrut' <- lowerExpr scrut
    rep <- case alts of
      (Core.Alt _ body : _) -> repOfExpr body
      [] -> return RClosure
    fallback' <- traverse lowerExpr fallback
    case scrutRep of
      REnum tid -> enumCase scrut' tid alts fallback' rep
      RData tid ->
        do
          arms <- mapM (dataArm scrut' tid) alts
          return (XSwitch (XTagOf scrut' tid) (Maybe.catMaybes arms) fallback' rep)
      _ ->
        do
          binds <- mapM (bindArm scrut') alts
          case Maybe.catMaybes binds of
            (b : _) -> return b
            [] -> return (Maybe.fromMaybe (XCrash "incomplete match" rep) fallback')

-- | @Bool@ and any other all-nullary datatype: switch on the value itself.
enumCase :: Expr -> TypeId -> [Core.Alt] -> Maybe Expr -> Rep -> L Expr
enumCase scrut tid alts fallback rep =
  do
    arms <-
      mapM
        ( \(Core.Alt pat body) ->
            case pat of
              Core.PCtor _ tag _ ->
                do
                  body' <- lowerExpr body
                  return (Just (tag, body'))
              Core.PVar (Core.Binder n _ _) ->
                do
                  modify' (\e -> e {_envLocals = Map.insert n (REnum tid) (_envLocals e)})
                  body' <- lowerExpr body
                  return (Just (-1, XLet n (REnum tid) scrut body'))
              Core.PWild -> (\b -> Just (-1, b)) <$> lowerExpr body
              _ -> return Nothing
        )
        alts
    let real = [(t, b) | Just (t, b) <- arms, t >= 0]
    let dflt = Maybe.listToMaybe [b | Just (t, b) <- arms, t < 0]
    return (XSwitch scrut real (maybe fallback Just dflt) rep)

-- | One arm over a boxed datatype: bind the constructor's fields out of the
-- payload, then the body.
dataArm :: Expr -> TypeId -> Core.Alt -> L (Maybe (Int, Expr))
dataArm scrut tid (Core.Alt pat body) =
  case pat of
    Core.PCtor _ tag subs ->
      do
        datas <- gets _envDataList
        let fieldReps =
              concat
                [ _clFields c
                | l <- datas,
                  _dlId l == tid,
                  c <- _dlCtors l,
                  _clTag c == tag
                ]
        binders <-
          mapM
            ( \(i, sub, r) ->
                case sub of
                  Core.PVar (Core.Binder n _ _) ->
                    do
                      modify' (\e -> e {_envLocals = Map.insert n r (_envLocals e)})
                      return (Just (n, r, i))
                  _ ->
                    do
                      note
                        "a nested pattern inside a constructor"
                        ( Derived
                            "C4's decision-tree pass flattens these; X7 runs the \
                            \spike with GENG_CORE_PASSES=case"
                        )
                      return Nothing
            )
            (zip3 [0 ..] subs (fieldReps ++ repeat RClosure))
        body' <- lowerExpr body
        let wrapped =
              List.foldr
                (\(n, r, i) acc -> XLet n r (XPayload scrut tid tag i r) acc)
                body'
                (Maybe.catMaybes binders)
        return (Just (tag, wrapped))
    _ -> return Nothing

-- | A @case@ over something that is not a datatype at all: a single irrefutable
-- binding, which is what a record destructuring lowers to.
bindArm :: Expr -> Core.Alt -> L (Maybe Expr)
bindArm scrut (Core.Alt pat body) =
  case pat of
    Core.PVar (Core.Binder n ty _) ->
      do
        rep <- repOf ty
        modify' (\e -> e {_envLocals = Map.insert n rep (_envLocals e)})
        body' <- lowerExpr body
        return (Just (XLet n rep scrut body'))
    Core.PWild -> Just <$> lowerExpr body
    Core.PRecord fields ->
      do
        binders <-
          mapM
            ( \(f, sub) ->
                case sub of
                  Core.PVar (Core.Binder n ty _) ->
                    do
                      r <- repOf ty
                      modify' (\e -> e {_envLocals = Map.insert n r (_envLocals e)})
                      return (Just (n, r, f))
                  _ -> return Nothing
            )
            fields
        body' <- lowerExpr body
        return
          ( Just
              ( List.foldr
                  (\(n, r, f) acc -> XLet n r (XField scrut f r) acc)
                  body'
                  (Maybe.catMaybes binders)
              )
          )
    _ -> return Nothing

-- FREE VARIABLES

-- | What a Core expression refers to and does not bind.
--
-- Closure conversion's input. Core does not carry this — it carries scope and
-- the body, and the difference is this fold.
freeVars :: Core.Expr -> Set Name
freeVars (Core.Expr e _ _) = freeVars_ e

freeVars_ :: Core.Expr_ -> Set Name
freeVars_ expr =
  case expr of
    Core.EVar n -> Set.singleton n
    Core.EGlobal _ -> Set.empty
    Core.ELit _ -> Set.empty
    Core.ELam bs body -> Set.difference (freeVars body) (binderNames bs)
    Core.EApp f args -> Set.unions (freeVars f : map freeVars args)
    Core.ELet binds body -> letFree binds body
    Core.ELetRec binds body ->
      Set.difference
        (Set.unions (freeVars body : map (freeVars . Core._bindValue) binds))
        (binderNames (map Core._bindBinder binds))
    Core.ECase scrut alts fallback ->
      Set.unions
        ( freeVars scrut
            : maybe Set.empty freeVars fallback
            : map altFree alts
        )
    Core.ECtor _ _ args -> Set.unions (map freeVars args)
    Core.ERecord fields -> Set.unions (map (freeVars . snd) fields)
    Core.EUpdate r fields -> Set.unions (freeVars r : map (freeVars . snd) fields)
    Core.EAccess r _ -> freeVars r
    Core.EArray xs -> Set.unions (map freeVars xs)
    Core.EPrim _ args -> Set.unions (map freeVars args)
    Core.EJoin binds body -> letFree binds body
    Core.EJump _ args -> Set.unions (map freeVars args)
    Core.ETyLam _ body -> freeVars body
    Core.ETyApp body _ -> freeVars body
    Core.EWitLam bs body -> Set.difference (freeVars body) (binderNames bs)
    Core.EWitApp body args -> Set.unions (freeVars body : map freeVars args)
    Core.ECrash _ -> Set.empty

letFree :: [Core.Bind] -> Core.Expr -> Set Name
letFree binds body =
  List.foldr
    ( \(Core.Bind (Core.Binder n _ _) value) acc ->
        Set.union (freeVars value) (Set.delete n acc)
    )
    (freeVars body)
    binds

altFree :: Core.Alt -> Set Name
altFree (Core.Alt pat body) = Set.difference (freeVars body) (patternNames pat)

binderNames :: [Core.Binder] -> Set Name
binderNames = Set.fromList . map Core._binderName

patternNames :: Core.Pattern -> Set Name
patternNames pat =
  case pat of
    Core.PVar (Core.Binder n _ _) -> Set.singleton n
    Core.PWild -> Set.empty
    Core.PLit _ -> Set.empty
    Core.PCtor _ _ subs -> Set.unions (map patternNames subs)
    Core.PRecord fields -> Set.unions (map (patternNames . snd) fields)
    Core.PArray subs tail_ ->
      Set.union
        (Set.unions (map patternNames subs))
        (maybe Set.empty (Set.singleton . Core._binderName) tail_)
    Core.PAs (Core.Binder n _ _) sub -> Set.insert n (patternNames sub)

-- NAMES

-- | A Core name as a C identifier.
--
-- @gren-lang\/core:Basics.add@ becomes @geng_gren_lang_core__Basics_add@. The
-- package is in it because two packages may hold the same module name, which
-- is the same reason 'Core.Dump.fileName' puts it in a file name.
cName :: Core.QualName -> String
cName (Core.QualName (ModuleName.Canonical pkg raw) n) =
  "geng_"
    ++ mangle (Pkg.toChars pkg)
    ++ "__"
    ++ mangle (ModuleName.toChars raw)
    ++ "_"
    ++ mangle (Name.toChars n)

-- | Anything C will not take in an identifier becomes an underscore.
mangle :: String -> String
mangle = concatMap one
  where
    one c
      | Char.isAlphaNum c = [c]
      | c == '_' = "_"
      | otherwise = "_"

-- RENDERING THE FINDING

-- | §X9's list, as a file.
--
-- Grouped by classification, because the classification is the reading: what
-- Core /derives/ is Core working, what @Low@ /assumed/ is a native-side
-- obligation, and what is /absent/ is a Core change to make at M1b.
renderNotes :: [Note] -> B.Builder
renderNotes notes =
  mconcat
    [ section
        "derived"
        "Core carried it. This is what an IR waist is for."
        [(w, why) | Note w (Derived why) <- notes],
      section
        "assumed"
        "Core is silent and Low chose. A native-side obligation, not a Core gap."
        [(w, why) | Note w (Assumed why) <- notes],
      section
        "absent"
        "Core could not say it. Each of these is a Core change to weigh at M1b."
        [(w, why) | Note w (Absent why) <- notes]
    ]
  where
    section title blurb entries =
      B.stringUtf8 title
        <> " "
        <> B.stringUtf8 (show (length entries))
        <> "\n  "
        <> B.stringUtf8 blurb
        <> "\n"
        <> mconcat
          [ "  - " <> B.stringUtf8 what <> "\n      " <> B.stringUtf8 why <> "\n"
          | (what, why) <- entries
          ]
        <> "\n"
