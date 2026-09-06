{-# LANGUAGE OverloadedStrings #-}

-- | Self tail calls become a join entered with the function's own parameters
-- (@docs/core.md@ C9, C15).
module Core.PassTailCallSpec where

import Core.AST qualified as Core
import Core.Pass.TailCall qualified as TailCall
import Data.Map qualified as Map
import Data.Name (Name)
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Test.Hspec

spec :: Spec
spec = do
  describe "what it rewrites" $ do
    it "turns a self call in tail position into a jump, and the body into a join" $
      let out = pass (lam ["n"] (call selfE [var "n"]))
       in shapeOf out `shouldBe` Lam ["n"] (Join "$t0" (Lam ["n"] (Jump "$t0" 1)) (Jump "$t0" 1))

    it "finds a tail call inside a case alternative" $
      let out = pass (lam ["n"] (caseOf (var "n") [one, call selfE [var "n"]]))
       in jumps out `shouldBe` 2

    it "finds a tail call inside a let body" $
      let out = pass (lam ["n"] (letIn "x" one (call selfE [var "x"])))
       in jumps out `shouldBe` 2

    it "rewrites a let-bound function against its own name" $
      let out = pass (lam ["n"] (letIn "go" (lam ["m"] (call (var "go") [var "m"])) one))
       in jumps out `shouldBe` 2

  describe "what it leaves alone" $ do
    it "leaves a function with no self call untouched" $
      let body = lam ["n"] (var "n")
       in pass body `shouldBe` body

    it "leaves a self call that is not in tail position" $
      -- The call is an argument, so its result is used: it needs a frame, and
      -- the definition it calls is still there to be called.
      let body = lam ["n"] (call (globalE "other") [call selfE [var "n"]])
       in pass body `shouldBe` body

    it "leaves a partial application of itself" $
      let body = lam ["n", "m"] (call selfE [var "n"])
       in pass body `shouldBe` body

    it "leaves a value that is not a function" $
      pass one `shouldBe` one

-- RUNNING THE PASS

pass :: Core.Expr -> Core.Expr
pass value =
  case Core._moduleDefs (TailCall.run (modul [Core.Bind (Core.Binder "f" intT span0) value])) of
    [Core.Bind _ out] -> out
    _ -> error "the pass lost the definition"

-- SHAPES

data Shape
  = Lam [Name] Shape
  | Join Name Shape Shape
  | Jump Name Int
  | Other
  deriving (Eq, Show)

shapeOf :: Core.Expr -> Shape
shapeOf e =
  case Core._exprValue e of
    Core.ELam binders body -> Lam (map Core._binderName binders) (shapeOf body)
    Core.EJoin [Core.Bind b v] body -> Join (Core._binderName b) (shapeOf v) (shapeOf body)
    Core.EJump j args -> Jump j (length args)
    _ -> Other

jumps :: Core.Expr -> Int
jumps e =
  case Core._exprValue e of
    Core.EJump _ args -> 1 + sum (map jumps args)
    Core.ELam _ body -> jumps body
    Core.EApp fn args -> jumps fn + sum (map jumps args)
    Core.ELet binds body -> sum (map (jumps . Core._bindValue) binds) + jumps body
    Core.ELetRec binds body -> sum (map (jumps . Core._bindValue) binds) + jumps body
    Core.EJoin binds body -> sum (map (jumps . Core._bindValue) binds) + jumps body
    Core.ECase scrutinee alts fallback ->
      jumps scrutinee + sum (map (jumps . Core._altBody) alts) + maybe 0 jumps fallback
    _ -> 0

-- BUILDING CORE

home :: ModuleName.Canonical
home = ModuleName.Canonical Pkg.dummyName "Main"

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

selfE :: Core.Expr
selfE = globalE "f"

one :: Core.Expr
one = node (Core.ELit (Core.LIntLegacy 1))

lam :: [Name] -> Core.Expr -> Core.Expr
lam names body = node (Core.ELam [Core.Binder n intT span0 | n <- names] body)

call :: Core.Expr -> [Core.Expr] -> Core.Expr
call fn args = node (Core.EApp fn args)

letIn :: Name -> Core.Expr -> Core.Expr -> Core.Expr
letIn n value body = node (Core.ELet [Core.Bind (Core.Binder n intT span0) value] body)

caseOf :: Core.Expr -> [Core.Expr] -> Core.Expr
caseOf scrutinee bodies =
  node (Core.ECase scrutinee [Core.Alt Core.PWild b | b <- bodies] Nothing)

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
      Core._moduleManager = Nothing,
      Core._moduleExports = []
    }
