{-# LANGUAGE OverloadedStrings #-}

-- | The Core wire format (@docs/core.md@ C10, @docs/m1a-wire.md@).
--
-- @harness/wire.py@ is the gate and it does the heavy work — every module of
-- every corpus case decoded by a second codec built from the schema, and
-- re-encoded byte for byte. What it cannot do is exercise a node the corpus
-- never builds, and its own coverage report says which those are: @EPrim@,
-- because D81 keeps @\@prim@ out of M1a; the four specialization nodes, because
-- R1 is M1b's; @EJoin@ and @EJump@, because C11 dumps __pre-pass__ Core and
-- C15's join points have no producer before the decision-tree pass runs;
-- @ECrash@'s other three kinds, which nothing produces (D335 made @Debug.todo@
-- one, and @accept/debug-todo@ builds it); and five of the nine
-- literals, because D2's sized integers and @Float32@ arrive at M1b.
--
-- So this file builds them by hand. Every constructor of 'Expr_', 'Pattern',
-- 'Literal' and 'CrashKind', plus 'Main', which C19 added after C10 was written,
-- in one module that is encoded, decoded and compared. C17's 'Manager' and C18's
-- 'Port' were here too until they left with @Platform@ (@m1b-source.md@ §SO19).
--
-- The comparison is structural equality, which the round-trip needs and the
-- byte comparison in the harness covers from the other side: a field written at
-- the wrong position round-trips through 'Eq' perfectly, and a field dropped
-- entirely does not.
module Core.WireSpec where

import Core.AST
import Core.Prim qualified as Prim
import Core.Target qualified as Target
import Core.Whole qualified as Whole
import Core.Wire qualified as Wire
import Data.ByteString qualified as BS
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Name qualified as Name
import Data.Utf8 qualified as Utf8
import Data.Word (Word32)
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Test.Hspec

spec :: Spec
spec = do
  describe "the file" $ do
    it "starts with the magic, the schema version and the kind" $
      -- The literals 7 and 0 are deliberate (D336, D379). A version bump is meant
      -- to be a visible event, and this failing is what one looks like; the kind
      -- says the file holds a module.
      case Wire.encode (moduleWith []) of
        Left problems -> expectationFailure (unwords problems)
        Right bytes -> BS.take 10 bytes `shouldBe` Wire.magic <> BS.pack [7, 0]

    it "says a program file holds a program" $
      case Wire.encodeProgram someProgram of
        Left problems -> expectationFailure (unwords problems)
        Right bytes -> BS.take 10 bytes `shouldBe` Wire.magic <> BS.pack [7, 1]

    it "round-trips a program (D378)" $
      case Wire.encodeProgram someProgram of
        Left problems -> expectationFailure (unwords problems)
        Right bytes -> Wire.decodeProgram bytes `shouldBe` Right someProgram

    it "refuses a module file to a reader that wants a program" $
      case Wire.encode (moduleWith []) of
        Left problems -> expectationFailure (unwords problems)
        Right bytes -> isLeft (Wire.decodeProgram bytes) `shouldBe` True

    it "refuses a program file to a reader that wants a module" $
      case Wire.encodeProgram someProgram of
        Left problems -> expectationFailure (unwords problems)
        Right bytes -> isLeft (Wire.decode bytes) `shouldBe` True

    it "refuses a file that is not Core" $
      isLeft (Wire.decode "not core at all, not even close") `shouldBe` True

    it "refuses an empty file" $
      isLeft (Wire.decode "") `shouldBe` True

  describe "round-tripping" $ do
    it "carries a module with every expression node" $
      roundTrip (moduleWith (map bindOf everyNode))

    it "carries a module with every pattern form" $
      roundTrip (moduleWith [bindOf (caseOverEveryPattern)])

    it "carries a module with every literal" $
      roundTrip (moduleWith (map (bindOf . lit) everyLiteral))

    it "carries a module with every crash kind" $
      roundTrip (moduleWith (map (bindOf . crash) everyCrash))

    it "carries externs in every language, pure and not (D196)" $
      roundTrip ((moduleWith []) {_moduleExterns = externs})

    it "refuses an extern whose languages are out of order, or whose names do not fit its language" $
      do
        refused ((moduleWith []) {_moduleExterns = [Extern (binder "e") [ExternImpl ExternC [utf8 "geng_e"], ExternImpl ExternJs [utf8 "m", utf8 "e"]] False False]})
        refused ((moduleWith []) {_moduleExterns = [Extern (binder "e") [ExternImpl ExternC [utf8 "m", utf8 "e"]] False False]})
        refused ((moduleWith []) {_moduleExterns = [Extern (binder "e") [] False False]})

    it "carries an extern with a Geng body beside its binding (D222)" $
      roundTrip ((moduleWith [bindOf (lit (LInt 1))]) {_moduleExterns = [Extern (binder "b") [ExternImpl ExternJs [utf8 "m", utf8 "b"]] True True]})

    it "refuses an extern with a body and no binding, or a binding and no body" $
      do
        refused ((moduleWith []) {_moduleExterns = [Extern (binder "b") [ExternImpl ExternJs [utf8 "m", utf8 "b"]] True True]})
        refused ((moduleWith [bindOf (lit (LInt 1))]) {_moduleExterns = [Extern (binder "b") [ExternImpl ExternJs [utf8 "m", utf8 "b"]] True False]})

    it "carries each kind of main" $
      mapM_ (\m -> roundTrip ((moduleWith []) {_moduleMain = Just m})) everyMain

    it "carries the file table" $
      roundTrip
        ( (moduleWith [])
            { _moduleFiles =
                Map.fromList [(FileId 0, home), (FileId 1, otherHome), (FileId 7, home)]
            }
        )

    it "carries declarations" $
      roundTrip
        ( (moduleWith [])
            { _moduleData = [dataDecl],
              _moduleClasses = [classDecl],
              _moduleInstances = [instanceDecl]
            }
        )

  describe "the string table (D92)" $ do
    it "sorts by content and not by the order the strings were met" $
      -- The property the whole scheme rests on: two frontends that walked a
      -- module in different orders must still produce the same table, so the
      -- order has to be a property of the set and not of the traversal. Here
      -- the names are met as z, a, m and must be written as a, m, z.
      case Wire.encode (moduleWith (map (bindOf . expr . EVar) ["zzz", "aaa", "mmm"])) of
        Left problems -> expectationFailure (unwords problems)
        Right bytes ->
          let at needle = fst (BS.breakSubstring needle bytes)
           in map BS.length [at "aaa", at "mmm", at "zzz"]
                `shouldSatisfy` \ns -> ns == List.sort ns

    it "writes a repeated string once" $
      -- Ten uses of a forty-character name against ten uses of a one-character
      -- name. Interned, the difference is the one table entry — about forty
      -- bytes. Written inline it would be ten of them, about four hundred.
      case (tenUsesOf "x", tenUsesOf "aVeryLongIdentifierIndeedYesQuiteLong") of
        (Right short, Right long) ->
          (BS.length long - BS.length short) `shouldSatisfy` (< 100)
        _ -> expectationFailure "did not encode"

    it "carries an empty string, which is index zero and not a table entry" $
      roundTrip (moduleWith [bindOf (lit (LString (utf8 "")))])

  describe "spans (D95)" $ do
    it "carries a tree whose every span differs from the one enclosing it" $
      -- Every other test in this file gives each node the same 'span_', so
      -- every delta it writes is zero and a broken reconstruction would round-
      -- trip anyway. This one moves in both directions: `g` is far below its
      -- enclosing span and `x` is above and to the left of it, which is the
      -- sign the corpus never exercises -- 0 of its 15,732 rows go backwards,
      -- and 58 of its columns do.
      roundTrip nestedSpans

    it "carries the span that writes no bytes at all, and it is not its parent" $
      -- Every delta is zero, so rule 5 omits all five fields — which under D95's
      -- three bases means "starts where the enclosing span starts, one row long,
      -- ending in the column the enclosing span ends in". It must come back as
      -- itself and not as the span enclosing it.
      --
      -- __This is what B22's candidate C would have cost.__ C proposed that an
      -- absent span mean "the same as the enclosing one". Inlined into 'Expr',
      -- absence already means the span below, 1,327 of the corpus's 17,793 spans
      -- are it and write nothing, and 5 of those are not their enclosing span.
      -- The rule would not have been a reinterpretation of rule 5 so much as
      -- five values the format could no longer write down.
      roundTrip (moduleWith [Bind (binder "f") (accessAt (at 3 7 9 20) (at 3 7 3 20))])

    it "pays for the distance between a span and the one enclosing it" $
      -- Both modules are the same shape and both are written at row 5000, so
      -- every absolute row in either is a two-byte varint and an encoding that
      -- wrote them out would make the two files the same size. Under D95 the
      -- one whose spans agree with their enclosing span writes nothing at all
      -- for four of the five fields.
      case (encodeOf (chain 0), encodeOf (chain 1000)) of
        (Right together, Right apart) ->
          BS.length together `shouldSatisfy` (< BS.length apart)
        _ -> expectationFailure "did not encode"

  -- D91 used to live here: the transitional `LIntLegacy` carried an unbounded
  -- `Integer` and the wire format carries a `sint64`, so the encoder had a
  -- refusal for a literal that did not fit. D2's flag day deleted the
  -- constructor (`docs/m1b-int.md` §I20) and every integer literal now has a
  -- width its constructor names, so the edge cases are ordinary round trips.
  describe "integer literals at their edges" $ do
    it "carries an Int64 at the edge of the range" $ do
      roundTrip (moduleWith [bindOf (lit (LInt64 9223372036854775807))])
      roundTrip (moduleWith [bindOf (lit (LInt64 (-9223372036854775808)))])

    it "carries an Int at the edge of the range" $ do
      roundTrip (moduleWith [bindOf (lit (LInt 2147483647))])
      roundTrip (moduleWith [bindOf (lit (LInt (-2147483648)))])

    it "carries a UInt64 with every bit set" $
      roundTrip (moduleWith [bindOf (lit (LUInt64 18446744073709551615))])

  describe "floats" $ do
    it "distinguishes negative zero from zero" $ do
      roundTrip (moduleWith [bindOf (lit (LFloat (-0.0)))])
      roundTrip (moduleWith [bindOf (lit (LFloat 0.0))])
      encodeOf (lit (LFloat (-0.0))) `shouldNotBe` encodeOf (lit (LFloat 0.0))

    it "carries infinities" $ do
      roundTrip (moduleWith [bindOf (lit (LFloat (1 / 0)))])
      roundTrip (moduleWith [bindOf (lit (LFloat32 (-1 / 0)))])

-- THE ROUND TRIP

roundTrip :: Module -> Expectation
roundTrip m =
  case Wire.encode m of
    Left problems -> expectationFailure ("did not encode: " ++ unwords problems)
    Right bytes ->
      case Wire.decode bytes of
        Left err -> expectationFailure ("did not decode: " ++ Wire.renderError err)
        Right back -> back `shouldBe` m

-- | The bytes, for the questions structural equality cannot answer.
--
-- @-0.0 == 0.0@ is 'True' for 'Double' and therefore for 'Core.AST.Literal', so
-- a round-trip that dropped the sign bit would pass. The bytes are the only
-- place the difference is visible, which is the same reason C10 compares bytes.
encodeOf :: Expr -> Either [String] BS.ByteString
encodeOf e = Wire.encode (moduleWith [bindOf e])

-- | A module holding ten bindings whose bodies all name one variable.
tenUsesOf :: Name.Name -> Either [String] BS.ByteString
tenUsesOf n = Wire.encode (moduleWith (replicate 10 (bindOf (expr (EVar n)))))

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False

-- THE PIECES

home :: ModuleName.Canonical
home = ModuleName.Canonical Pkg.core "Basics"

otherHome :: ModuleName.Canonical
otherHome = ModuleName.Canonical Pkg.application "Some.Module"

qual :: Name.Name -> QualName
qual = QualName home

-- | 'Core.AST.Text' has no 'IsString' instance, and
-- 'Core.AST.Text' deliberately does not: its whole purpose is that putting
-- undecoded JavaScript string-literal source there is a type error rather than
-- a thing to remember.
utf8 :: String -> Utf8.Utf8 t
utf8 = Utf8.fromChars

span_ :: Span
span_ = Span (FileId 0) 1 2 3 4

-- | A span in the module's one file.
at :: Word32 -> Word32 -> Word32 -> Word32 -> Span
at = Span (FileId 0)

-- | An 'EAccess' at @outer@ whose base is an 'EVar' at @inner@ — the shallowest
-- way to put one span inside another.
accessAt :: Span -> Span -> Expr
accessAt outer inner =
  Expr (EAccess (Expr (EVar "x") intType inner) "field") intType outer

-- | Four spans, none of them the same, and two of them moving backwards.
nestedSpans :: Module
nestedSpans =
  moduleWith
    [ Bind
        (Binder "f" intType (at 12 5 12 9))
        ( Expr
            ( ELam
                [Binder "x" intType (at 12 7 12 8)]
                ( Expr
                    ( EApp
                        (Expr (EVar "g") intType (at 40 3 41 80))
                        [Expr (EVar "x") intType (at 12 1 12 2)]
                    )
                    intType
                    (at 13 9 15 4)
                )
            )
            intType
            (at 12 5 20 1)
        )
    ]

-- | Ten nested accesses at row 5000, each @gap@ rows below the one enclosing it.
chain :: Word32 -> Expr
chain gap =
  List.foldl'
    (\inner i -> Expr (EAccess inner "field") intType (at (5000 + i * gap) 1 (5000 + i * gap) 9))
    (Expr (EVar "x") intType (at (5000 + 10 * gap) 1 (5000 + 10 * gap) 9))
    [9, 8 .. 0]

intType :: Type
intType = TCon (qual "Int") []

binder :: Name.Name -> Binder
binder n = Binder n intType span_

expr :: Expr_ -> Expr
expr node = Expr node intType span_

lit :: Literal -> Expr
lit = expr . ELit

crash :: CrashKind -> Expr
crash = expr . ECrash

var :: Expr
var = expr (EVar "x")

bindOf :: Expr -> Bind
bindOf e = Bind (binder "b") e

-- | A program for the file tests: two roots, so their order is visible, and a
-- target, mode and runtime that are not the enums' zero codes, so the fields
-- are actually on the wire.
someProgram :: Whole.Program
someProgram =
  Whole.Program
    [ Whole.Root (ModuleName.Canonical Pkg.application (Name.fromChars "Main")) (Name.fromChars "main"),
      Whole.Root (ModuleName.Canonical Pkg.core (Name.fromChars "Basics")) (Name.fromChars "add")
    ]
    Target.Js
    Whole.Prod
    Whole.Node

moduleWith :: [Bind] -> Module
moduleWith defs =
  Module
    { _moduleName = home,
      _moduleFiles = Map.fromList [(FileId 0, home)],
      _moduleData = [],
      _moduleClasses = [],
      _moduleInstances = [],
      _moduleDefs = defs,
      _moduleDefsRec = [[qual "a", qual "b"]],
      _moduleExports = [qual "b"],
      _moduleMain = Nothing,
      _moduleExterns = []
    }

-- | All 21 of them (C2). The list is the point: adding a node to 'Expr_' and
-- not to the wire format is a compile error here, because the @case@ below is
-- exhaustive over the constructors it names.
everyNode :: [Expr]
everyNode =
  [ var,
    expr (EGlobal (qual "add")),
    lit (LString (utf8 "hello")),
    expr (ELam [binder "p", binder "q"] var),
    expr (EApp var [var, var]),
    expr (ELet [bindOf var] var),
    expr (ELetRec [bindOf var, bindOf var] var),
    expr (ECase var [Alt PWild var] (Just var)),
    expr (ECase var [Alt PWild var] Nothing),
    expr (ECtor (qual "Just") 1 [var]),
    expr (ERecord [("x", var), ("y", var)]),
    expr (EUpdate var [("x", var)]),
    expr (EAccess var "x"),
    expr (EArray [var, var]),
    expr (EPrim somePrim [var, var]),
    expr (EJoin [bindOf (expr (ELam [binder "j"] var))] (expr (EJump "b" [var]))),
    expr (EJump "b" []),
    expr (ETyLam ["a", "b"] var),
    expr (ETyApp var [intType, TVar "a"]),
    expr (EWitLam [binder "w"] var),
    expr (EWitApp var [var]),
    crash Unreachable
  ]

caseOverEveryPattern :: Expr
caseOverEveryPattern =
  expr
    ( ECase
        var
        [ Alt (PVar (binder "v")) var,
          Alt PWild var,
          Alt (PLit (LChar 0x1F600)) var,
          Alt (PCtor (qual "Just") 1 [PWild]) var,
          Alt (PRecord [("x", PWild), ("y", PVar (binder "y"))]) var,
          Alt (PArray [PWild] (Just (binder "rest"))) var,
          Alt (PArray [] Nothing) var,
          Alt (PAs (binder "whole") PWild) var
        ]
        Nothing
    )

-- | All eight (C8, D2). Nine until D2's flag day deleted the transitional
-- @LIntLegacy@ (`docs/m1b-int.md` §I20); this list is written by hand because
-- the corpus reaches a constructor only when something produces it, and the
-- point of the round trip is that the codec does not depend on that.
everyLiteral :: [Literal]
everyLiteral =
  [ LInt 0,
    LInt (-2147483648),
    LInt64 9007199254740993,
    LUInt32 4294967295,
    LUInt64 18446744073709551615,
    LFloat 3.141592653589793,
    LFloat32 1.5,
    LChar 0x10FFFF,
    LString (utf8 "")
  ]

-- | 'Core.Prim.primCode' 0. Named rather than taken with @head@, because an
-- empty 'Core.Prim.allPrims' should fail here loudly rather than partially.
somePrim :: Prim.PrimOp
somePrim =
  case Prim.primFromCode 0 of
    Just op -> op
    Nothing -> error "Core.Prim.allPrims is empty"

everyCrash :: [CrashKind]

-- | A @Todo@ carries an expression since D335: a literal message, and one
-- computed from a variable, which is what made the message a child.
everyCrash = [Todo (utf8 "not done") (lit (LString (utf8 "why"))), Todo (utf8 "") var, IncompleteMatch, StackExhausted, Unreachable]

-- | One extern in each of D77's languages and one pure one, with names that
-- need the string table.
externs :: [Extern]
externs =
  [ Extern (binder "now") [ExternImpl ExternJs [utf8 "geng_time", utf8 "now"], ExternImpl ExternErlang [utf8 "geng_time", utf8 "now"], ExternImpl ExternC [utf8 "geng_time_now"]] False False,
    Extern (binder "sha256") [ExternImpl ExternJs [utf8 "geng_hash", utf8 "sha256"]] True False
  ]

-- | A module the encoder writes and the reader must refuse: the rules the
-- schema cannot state are the reader's to enforce (D196).
refused :: Module -> Expectation
refused m =
  case Wire.encode m of
    Left problems -> expectationFailure (unwords problems)
    Right bytes ->
      case Wire.decode bytes of
        Left _ -> return ()
        Right _ -> expectationFailure "the reader accepted an extern it should refuse"

everyMain :: [Main]
everyMain = [MainTask]

dataDecl :: DataDecl
dataDecl =
  DataDecl
    { _dataName = qual "Maybe",
      _dataParams = ["a"],
      _dataTransparency = Abstract,
      _dataCtors =
        [ Ctor (qual "Nothing") 0 [],
          Ctor (qual "Just") 1 [TVar "a"]
        ],
      _dataClasses = [qual "Eq", qual "Ord"]
    }

classDecl :: ClassDecl
classDecl =
  ClassDecl
    { _classNameC = qual "Num",
      _classParam = "a",
      _classOpenness = Closed,
      _classMethods = [("add", TFun [TVar "a", TVar "a"] (TVar "a"))]
    }

instanceDecl :: InstanceDecl
instanceDecl =
  InstanceDecl
    { _instClass = qual "Num",
      _instHead = intType,
      _instOrigin = Written,
      _instMethods = [("add", var)]
    }
