{-# LANGUAGE OverloadedStrings #-}

-- | Lowering canonical expressions and patterns to Core (@docs/core.md@ §C2).
--
-- The cases here are the places where Canonical and Core do not line up, since
-- the ones where they do are a rename. Node types are supplied by hand, keyed
-- by explicit node ids, which is what the solver hands the lowering in a real
-- compile (@docs/m1a-node-types.md@).
module Core.LowerExpressionSpec where

import AST.Canonical qualified as Can
import Core.AST qualified as Core
import Core.Lower.Expression qualified as Lower
import Core.Lower.Literal qualified as Literal
import Core.Lower.Type (lowerType)
import Data.Index qualified as Index
import Data.Map qualified as Map
import Data.Name qualified as Name
import Data.Utf8 qualified as Utf8
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Gren.String qualified as ES
import Reporting.Annotation qualified as A
import Test.Hspec

spec :: Spec
spec = do
  describe "literals" $ do
    it "resolves the escapes a string literal is stored with" $
      -- `Gren.String` holds JavaScript literal source, not text: the parser
      -- leaves `\n` as a backslash and an `n`, and turns `\u{...}` into a
      -- four-hex-digit `\uXXXX`. Core's `LString` is the string itself.
      Literal.str (escaped "a\\nb\\u0041") `shouldBe` Core.LString (text "a\nbA")

    it "puts a surrogate pair back together" $
      -- An astral code point is stored as the pair a UTF-16 literal needs.
      -- Core is not UTF-16.
      Literal.str (escaped "\\uD83D\\uDE00") `shouldBe` Core.LString (text "\128512")

    it "passes an unpaired surrogate through" $
      -- C8 says a surrogate is not a `Char`, but the parser accepts one today
      -- and rejecting it is a language decision, not the lowering's.
      Literal.decode (escaped "\\uD800") `shouldBe` "\55296"

    it "makes a character a code point" $
      -- C8. In Canonical a `Char` is a one- or two-unit string.
      Literal.chr (escaped "\\uD83D\\uDE00") `shouldBe` Core.LChar 128512

    it "reads a float literal, which Canonical stores as its digits" $ do
      Literal.float (Utf8.fromChars "1.5") `shouldBe` Core.LFloat 1.5
      Literal.float (Utf8.fromChars "1e3") `shouldBe` Core.LFloat 1000.0
      Literal.float (Utf8.fromChars "2.2250738585072014e-308")
        `shouldBe` Core.LFloat 2.2250738585072014e-308

    it "keeps an integer in the transitional constructor" $
      -- LIntLegacy, not LInt: `Int` is a JS double until D2 lands at M1b, and
      -- real programs hold literals past Int32.
      Literal.int 1735689600000 `shouldBe` Core.LIntLegacy 1735689600000

  describe "constructors" $ do
    it "makes a saturated application one ECtor" $
      -- C2 has no unsaturated ECtor, and recognizing the saturated call here
      -- is what keeps the node describing the program rather than the AST.
      value
        [(1, Can.TType home "Maybe" [intT]), (2, Can.TLambda intT (Can.TType home "Maybe" [intT])), (3, intT)]
        (at 1 (Can.Call (at 2 just) [at 3 (Can.Int 5)]))
        `shouldBe` Core.ECtor (qual "Just") 1 [expr (core intT) (Core.ELit (Core.LIntLegacy 5))]

    it "eta-expands a constructor used as a value" $
      value
        [(1, Can.TLambda intT (Can.TType home "Maybe" [intT]))]
        (at 1 just)
        `shouldBe` Core.ELam
          [Core.Binder "$0" (core intT) here]
          (expr (core (Can.TType home "Maybe" [intT])) (Core.ECtor (qual "Just") 1 [expr (core intT) (Core.EVar "$0")]))

    it "leaves a nullary constructor alone" $
      value [(1, Can.TType home "Maybe" [intT])] (at 1 nothing)
        `shouldBe` Core.ECtor (qual "Nothing") 0 []

  describe "conditionals" $ do
    it "becomes a when on Bool" $
      value
        [(1, intT), (2, boolT), (3, intT), (4, intT)]
        (at 1 (Can.If [(at 2 true, at 3 (Can.Int 1))] (at 4 (Can.Int 2))))
        `shouldBe` Core.ECase
          (expr (core boolT) (Core.ECtor (qual' ModuleName.basics "True") 0 []))
          [ Core.Alt (Core.PCtor (qual' ModuleName.basics "True") 0 []) (expr (core intT) (Core.ELit (Core.LIntLegacy 1))),
            Core.Alt (Core.PCtor (qual' ModuleName.basics "False") 1 []) (expr (core intT) (Core.ELit (Core.LIntLegacy 2)))
          ]
          Nothing

    it "nests an else-if chain, which Canonical keeps flat" $
      let lowered =
            value
              [(1, intT), (2, boolT), (3, intT), (4, boolT), (5, intT), (6, intT)]
              ( at 1 $
                  Can.If
                    [(at 2 true, at 3 (Can.Int 1)), (at 4 true, at 5 (Can.Int 2))]
                    (at 6 (Can.Int 3))
              )
       in case lowered of
            Core.ECase _ [_, Core.Alt _ (Core.Expr (Core.ECase _ inner _) _ _)] _ ->
              length inner `shouldBe` 2
            other ->
              expectationFailure ("expected a nested when, got " ++ show other)

  describe "accessors" $
    it "makes .field the function it stands for" $
      let recordT = Can.TRecord (Map.fromList [("x", Can.FieldType 0 intT)]) Nothing
       in value [(1, Can.TLambda recordT intT)] (at 1 (Can.Accessor "x"))
            `shouldBe` Core.ELam
              [Core.Binder "$r" (core recordT) here]
              (expr (core intT) (Core.EAccess (expr (core recordT) (Core.EVar "$r")) "x"))

  describe "records" $ do
    it "orders the fields of a literal alphabetically" $
      fieldNames
        ( value
            [(1, Can.TRecord (Map.fromList [("b", Can.FieldType 0 intT), ("a", Can.FieldType 1 intT)]) Nothing), (2, intT), (3, intT)]
            (at 1 (Can.Record (Map.fromList [(located "b", at 2 (Can.Int 1)), (located "a", at 3 (Can.Int 2))])))
        )
        `shouldBe` ["a", "b"]

    it "orders the fields of a pattern alphabetically" $
      -- Canonical keeps a record pattern in source order; Core does not.
      case Lower.pattern (env []) (core recordAB) (A.At here' (Can.PRecord [recordField "b" (Can.PVar "y"), recordField "a" (Can.PVar "x")])) of
        Core.PRecord fields ->
          map fst fields `shouldBe` ["a", "b"]
        other ->
          expectationFailure ("expected a record pattern, got " ++ show other)

  describe "patterns" $ do
    it "gives a record pattern's binder the field's type" $
      case Lower.pattern (env []) (core recordAB) (A.At here' (Can.PRecord [recordField "a" (Can.PVar "x")])) of
        Core.PRecord [("a", Core.PVar (Core.Binder name tipe _))] -> do
          name `shouldBe` "x"
          tipe `shouldBe` core intT
        other ->
          expectationFailure ("unexpected shape: " ++ show other)

    it "gives a constructor pattern's binder the argument's cached type" $
      let p =
            Can.PCtor home "Maybe" maybeUnion "Just" Index.second [Can.PatternCtorArg Index.first intT (A.At here' (Can.PVar "n"))]
       in case Lower.pattern (env []) (core (Can.TType home "Maybe" [intT])) (A.At here' p) of
            Core.PCtor name 1 [Core.PVar (Core.Binder "n" tipe _)] -> do
              name `shouldBe` qual "Just"
              tipe `shouldBe` core intT
            other ->
              expectationFailure ("unexpected shape: " ++ show other)

    it "gives an array pattern's binders the element type" $
      case Lower.pattern (env []) (core (Can.TType home "Array" [intT])) (A.At here' (Can.PArray [A.At here' (Can.PVar "a")])) of
        Core.PArray [Core.PVar (Core.Binder "a" tipe _)] Nothing ->
          tipe `shouldBe` core intT
        other ->
          expectationFailure ("unexpected shape: " ++ show other)

    it "checks a Bool pattern's tag against the union it came from" $
      Lower.pattern (env []) (core boolT) (A.At here' (Can.PBool boolUnion True))
        `shouldBe` Core.PCtor (qual' ModuleName.basics "True") 0 []

  describe "lambdas" $ do
    it "takes only as many argument types as it has arguments" $
      -- Core function types are collapsed maximally (C3), so `\x -> \y -> ...`
      -- has a two-argument type on a one-argument lambda.
      case value
        [(1, Can.TLambda intT (Can.TLambda intT intT)), (2, Can.TLambda intT intT), (3, intT)]
        (at 1 (Can.Lambda [A.At here' (Can.PVar "x")] (at 2 (Can.Lambda [A.At here' (Can.PVar "y")] (at 3 (Can.VarLocal "y")))))) of
        Core.ELam binders _ ->
          map Core._binderName binders `shouldBe` ["x"]
        other ->
          expectationFailure ("unexpected shape: " ++ show other)

    it "destructures a pattern argument through a generated binder" $
      case value
        [(1, Can.TLambda recordAB intT), (2, intT)]
        (at 1 (Can.Lambda [A.At here' (Can.PRecord [recordField "a" (Can.PVar "x")])] (at 2 (Can.VarLocal "x")))) of
        Core.ELam [Core.Binder "$0" tipe _] (Core.Expr (Core.ECase scrutinee [Core.Alt (Core.PRecord _) _] Nothing) _ _) -> do
          tipe `shouldBe` core recordAB
          Core._exprValue scrutinee `shouldBe` Core.EVar "$0"
        other ->
          expectationFailure ("unexpected shape: " ++ show other)

  describe "definitions" $ do
    it "makes an argument list a lambda" $
      case Lower.def
        (env [(1, Can.TLambda intT intT), (2, intT)])
        (Can.Def (Can.NodeId 1) (located "f") [A.At here' (Can.PVar "x")] (at 2 (Can.VarLocal "x"))) of
        Core.Bind (Core.Binder "f" tipe _) (Core.Expr (Core.ELam [Core.Binder "x" _ _] _) _ _) ->
          tipe `shouldBe` Core.TFun [core intT] (core intT)
        other ->
          expectationFailure ("unexpected shape: " ++ show other)

    it "builds a typed definition's type from its annotation" $
      case Lower.def
        (env [(2, intT)])
        (Can.TypedDef (located "f") Map.empty [(A.At here' (Can.PVar "x"), intT)] (at 2 (Can.VarLocal "x")) intT) of
        Core.Bind (Core.Binder "f" tipe _) _ ->
          tipe `shouldBe` Core.TFun [core intT] (core intT)
        other ->
          expectationFailure ("unexpected shape: " ++ show other)

    it "makes a destructuring let a one-alternative when" $
      case value
        [(1, intT), (2, recordAB), (3, intT)]
        (at 1 (Can.LetDestruct (A.At here' (Can.PRecord [recordField "a" (Can.PVar "x")])) (at 2 (Can.VarLocal "r")) (at 3 (Can.VarLocal "x")))) of
        Core.ECase _ [Core.Alt (Core.PRecord _) _] Nothing ->
          pure ()
        other ->
          expectationFailure ("unexpected shape: " ++ show other)

  describe "operators and kernel references" $ do
    it "makes a binop a call of the function it names" $
      case value
        [(1, intT), (2, intT), (3, intT)]
        (at 1 (Can.Binop "+" ModuleName.basics "add" plusAnnotation (at 2 (Can.Int 1)) (at 3 (Can.Int 2)))) of
        Core.EApp (Core.Expr (Core.EGlobal name) tipe _) [_, _] -> do
          name `shouldBe` qual' ModuleName.basics "add"
          tipe `shouldBe` Core.TFun [core intT, core intT] (core intT)
        other ->
          expectationFailure ("unexpected shape: " ++ show other)

    it "makes negate a call of Basics.negate" $
      case value [(1, intT), (2, intT)] (at 1 (Can.Negate (at 2 (Can.Int 1)))) of
        Core.EApp (Core.Expr (Core.EGlobal name) _ _) [_] ->
          name `shouldBe` qual' ModuleName.basics "negate"
        other ->
          expectationFailure ("unexpected shape: " ++ show other)

    it "gives a kernel reference the module the optimizer already gives it" $
      value [(1, intT)] (at 1 (Can.VarKernel "Array" "length"))
        `shouldBe` Core.EGlobal (Core.QualName (ModuleName.Canonical Pkg.kernel "Array") "length")

    it "points a Debug reference at Debug, not at the module using it" $
      value [(1, intT)] (at 1 (Can.VarDebug home "log" plusAnnotation))
        `shouldBe` Core.EGlobal (Core.QualName ModuleName.debug "log")

-- FIXTURES

home :: ModuleName.Canonical
home = ModuleName.Canonical Pkg.core "Maybe"

qual :: Name.Name -> Core.QualName
qual = Core.QualName home

qual' :: ModuleName.Canonical -> Name.Name -> Core.QualName
qual' = Core.QualName

intT :: Can.Type
intT = Can.TType home "Int" []

boolT :: Can.Type
boolT = Can.TType ModuleName.basics "Bool" []

recordAB :: Can.Type
recordAB =
  Can.TRecord (Map.fromList [("a", Can.FieldType 0 intT), ("b", Can.FieldType 1 intT)]) Nothing

core :: Can.Type -> Core.Type
core = lowerType

maybeUnion :: Can.Union
maybeUnion =
  Can.Union
    ["a"]
    [Can.Ctor "Nothing" Index.first 0 [], Can.Ctor "Just" Index.second 1 [Can.TVar "a"]]
    2
    Can.Normal

boolUnion :: Can.Union
boolUnion =
  Can.Union
    []
    [Can.Ctor "True" Index.first 0 [], Can.Ctor "False" Index.second 0 []]
    2
    Can.Enum

just :: Can.Expr_
just = Can.VarCtor Can.Normal home "Just" Index.second (Can.Forall Map.empty intT)

nothing :: Can.Expr_
nothing = Can.VarCtor Can.Normal home "Nothing" Index.first (Can.Forall Map.empty intT)

true :: Can.Expr_
true = Can.VarCtor Can.Enum ModuleName.basics "True" Index.first (Can.Forall Map.empty boolT)

plusAnnotation :: Can.Annotation
plusAnnotation = Can.Forall Map.empty (Can.TLambda intT (Can.TLambda intT intT))

-- BUILDING

here' :: A.Region
here' = A.Region (A.Position 1 1) (A.Position 1 2)

here :: Core.Span
here = Core.Span (Core.FileId 0) 1 1 1 2

at :: Int -> Can.Expr_ -> Can.Expr
at i = Can.Expr (Can.NodeId i) here'

located :: Name.Name -> A.Located Name.Name
located = A.At here'

recordField :: Name.Name -> Can.Pattern_ -> Can.PatternRecordField
recordField name p = A.At here' (Can.PRFieldPattern name (A.At here' p))

env :: [(Int, Can.Type)] -> Lower.Env
env types =
  Lower.Env (Core.FileId 0) (Map.fromList [(Can.NodeId i, t) | (i, t) <- types])

value :: [(Int, Can.Type)] -> Can.Expr -> Core.Expr_
value types = Core._exprValue . Lower.expr (env types)

expr :: Core.Type -> Core.Expr_ -> Core.Expr
expr tipe v = Core.Expr v tipe here

fieldNames :: Core.Expr_ -> [Name.Name]
fieldNames v =
  case v of
    Core.ERecord fields -> map fst fields
    _ -> []

-- | A string as `Gren.String` stores one: escapes unresolved.
escaped :: String -> ES.String
escaped = ES.fromChars

text :: String -> Core.Text
text = Utf8.fromChars
