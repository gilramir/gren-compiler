{-# LANGUAGE OverloadedStrings #-}

-- | A local group whose calls to one another are all tail calls becomes one
-- function (D479, geng-lang @docs/pre-m3-tail.md@ §MT4).
module Core.PassMutualSpec where

import Core.AST qualified as Core
import Core.Pass.Mutual qualified as Mutual
import Data.Map qualified as Map
import Data.Name (Name)
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Test.Hspec

spec :: Spec
spec = do
  describe "what it rewrites" $ do
    it "makes a pair of one signature one function over a member index" $
      let (out, made) = pass (letRec [isEven, isOdd] (call (var "isEven") [one]))
       in do
            shapeOf out `shouldBe` Rec ["$g0"] (Let ["isEven"] Other)
            paramsOf "$g0" out `shouldBe` ["$g0$i", "$g0$0"]
            made `shouldBe` []

    it "calls the function in place of each member" $
      let (out, _) = pass (letRec [isEven, isOdd] (call (var "isEven") [one]))
       in callsTo "$g0" out `shouldBe` 3

    it "declares a data type when the members' parameters differ" $
      let first = bind "first" (lam ["k"] (call (var "second") [var "k", one]))
          second = bind "second" (lam ["k", "v"] (call (var "first") [var "k"]))
          (out, made) = pass (letRec [first, second] (call (var "first") [one]))
       in do
            map Core._dataName made `shouldBe` [Core.QualName home "$G0"]
            map (map Core._ctorName . Core._dataCtors) made
              `shouldBe` [[Core.QualName home "$G0$first", Core.QualName home "$G0$second"]]
            paramsOf "$g0" out `shouldBe` ["$g0$c"]

    it "binds a helper the group uses outside the group" $
      let helper = bind "step" (lam ["k"] (var "k"))
          ping = bind "ping" (lam ["k"] (call (var "pong") [call (var "step") [var "k"]]))
          pong = bind "pong" (lam ["k"] (call (var "ping") [call (var "step") [var "k"]]))
          (out, _) = pass (letRec [ping, pong, helper] (call (var "ping") [one]))
       in shapeOf out `shouldBe` Let ["step"] (Rec ["$g0"] (Let ["ping"] Other))

  describe "what it leaves alone" $ do
    it "leaves a group with a call that is not in tail position" $
      let first = bind "first" (lam ["k"] (call (globalE "other") [call (var "second") [var "k"]]))
          second = bind "second" (lam ["k"] (call (var "first") [var "k"]))
          expr = letRec [first, second] (call (var "first") [one])
       in fst (pass expr) `shouldBe` expr

    it "leaves a group with a member named as a value" $
      let first = bind "first" (lam ["k"] (call (globalE "apply") [var "second", var "k"]))
          second = bind "second" (lam ["k"] (call (var "first") [var "k"]))
          expr = letRec [first, second] (call (var "first") [one])
       in fst (pass expr) `shouldBe` expr

    it "leaves a partial application of a member" $
      let first = bind "first" (lam ["k"] (call (var "second") [var "k"]))
          second = bind "second" (lam ["k", "j"] (call (var "first") [var "k"]))
          expr = letRec [first, second] (call (var "first") [one])
       in fst (pass expr) `shouldBe` expr

    it "leaves a function that calls only itself" $
      let go = bind "go" (lam ["k"] (call (var "go") [var "k"]))
          expr = letRec [go] (call (var "go") [one])
       in fst (pass expr) `shouldBe` expr

-- RUNNING THE PASS

pass :: Core.Expr -> (Core.Expr, [Core.DataDecl])
pass value =
  let out = Mutual.run (modul [Core.Bind (Core.Binder "f" intT span0) (lam ["n"] value)])
   in case Core._moduleDefs out of
        [Core.Bind _ (Core.Expr (Core.ELam _ body) _ _)] -> (body, Core._moduleData out)
        _ -> error "the pass lost the definition"

-- SHAPES

data Shape
  = Rec [Name] Shape
  | Let [Name] Shape
  | Other
  deriving (Eq, Show)

shapeOf :: Core.Expr -> Shape
shapeOf e =
  case Core._exprValue e of
    Core.ELetRec binds body -> Rec (map (Core._binderName . Core._bindBinder) binds) (shapeOf body)
    Core.ELet binds body -> Let (map (Core._binderName . Core._bindBinder) binds) (shapeOf body)
    _ -> Other

paramsOf :: Name -> Core.Expr -> [Name]
paramsOf name e =
  case Core._exprValue e of
    Core.ELetRec binds body ->
      case [ps | Core.Bind b (Core.Expr (Core.ELam ps _) _ _) <- binds, Core._binderName b == name] of
        ps : _ -> map Core._binderName ps
        [] -> paramsOf name body
    Core.ELet _ body -> paramsOf name body
    _ -> []

callsTo :: Name -> Core.Expr -> Int
callsTo name e =
  let here = case Core._exprValue e of
        Core.EApp (Core.Expr (Core.EVar n) _ _) _ | n == name -> 1
        _ -> 0
   in here + sum (map (callsTo name) (children e))

children :: Core.Expr -> [Core.Expr]
children e =
  case Core._exprValue e of
    Core.ELam _ body -> [body]
    Core.EApp fn args -> fn : args
    Core.ELet binds body -> body : map Core._bindValue binds
    Core.ELetRec binds body -> body : map Core._bindValue binds
    Core.ECase scrutinee alts fallback -> scrutinee : map Core._altBody alts ++ maybe [] pure fallback
    Core.ECtor _ _ args -> args
    _ -> []

-- BUILDING CORE

home :: ModuleName.Canonical
home = ModuleName.Canonical Pkg.application "Main"

span0 :: Core.Span
span0 = Core.Span (Core.FileId 0) 1 1 1 1

intT :: Core.Type
intT = Core.TCon (Core.QualName (ModuleName.Canonical Pkg.core "Basics") "Int") []

node :: Core.Expr_ -> Core.Expr
node v = Core.Expr v intT span0

var :: Name -> Core.Expr
var n = node (Core.EVar n)

globalE :: Name -> Core.Expr
globalE n = node (Core.EGlobal (Core.QualName home n))

one :: Core.Expr
one = node (Core.ELit (Core.LInt 1))

lam :: [Name] -> Core.Expr -> Core.Expr
lam names body = node (Core.ELam [Core.Binder n intT span0 | n <- names] body)

call :: Core.Expr -> [Core.Expr] -> Core.Expr
call fn args = node (Core.EApp fn args)

bind :: Name -> Core.Expr -> Core.Bind
bind n value = Core.Bind (Core.Binder n intT span0) value

letRec :: [Core.Bind] -> Core.Expr -> Core.Expr
letRec binds body = node (Core.ELetRec binds body)

-- | @isEven k = case k of 0 -> 1; _ -> isOdd k@, and the other way round.
isEven :: Core.Bind
isEven = bind "isEven" (lam ["k"] (node (Core.ECase (var "k") [Core.Alt (Core.PLit (Core.LInt 0)) one, Core.Alt Core.PWild (call (var "isOdd") [var "k"])] Nothing)))

isOdd :: Core.Bind
isOdd = bind "isOdd" (lam ["k"] (node (Core.ECase (var "k") [Core.Alt (Core.PLit (Core.LInt 0)) one, Core.Alt Core.PWild (call (var "isEven") [var "k"])] Nothing)))

modul :: [Core.Bind] -> Core.Module
modul defs =
  Core.Module
    { Core._moduleName = home,
      Core._moduleFiles = Map.singleton (Core.FileId 0) home,
      Core._moduleData = [],
      Core._moduleClasses = [],
      Core._moduleInstances = [],
      Core._moduleDefs = defs,
      Core._moduleDefsRec = [],
      Core._moduleMain = Nothing,
      Core._moduleExports = [],
      Core._moduleExterns = [],
      Core._moduleInline = [],
      Core._moduleAliases = []
    }
