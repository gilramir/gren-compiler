{-# LANGUAGE OverloadedStrings #-}

-- | The decision-tree pass (@docs/core.md@ C4, C15).
--
-- Four properties, one per thing the pass promises: its output is Core, the
-- tests it emits are one level deep, a body reached twice becomes a join
-- point rather than two copies, and a branch's own variables still reach its
-- body.
module Core.PassCaseSpec where

import Core.AST qualified as Core
import Core.Pass.Case qualified as Case
import Data.Map qualified as Map
import Data.Name (Name)
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Test.Hspec

spec :: Spec
spec = do
  describe "shape" $ do
    it "tests a two-constructor type with one case, one alternative per constructor" $
      let out = pass [alt (pctor "J" 1 [Core.PWild]) one, alt (pctor "N" 0 []) one]
       in shapeOf out `shouldBe` Case_ [Ctor_ "J" 1, Ctor_ "N" 0]

    it "keeps a single-constructor type as one alternative, which is a destructuring" $
      -- The node is not collapsed away, unlike @Optimize.DecisionTree@'s: it is
      -- what binds the value inside, and a backend emits no test for the only
      -- alternative of a case.
      let out = pass [alt (pctor "Box" 0 [pvar "n"]) (var "n")]
       in shapeOf out `shouldBe` Case_ [Ctor_ "Box" 1]

    it "compiles a nested pattern into nested cases, each one level deep" $
      let out =
            pass
              [ alt (pctor "J" 1 [pctor "J" 1 [Core.PWild]]) one,
                alt (pctor "J" 1 [pctor "N" 0 []]) one,
                alt (pctor "N" 0 []) one
              ]
       in case out of
            Core.Expr (Core.ECase _ (Core.Alt (Core.PCtor _ _ [Core.PVar _]) inner : _) _) _ _ ->
              shapeOf inner `shouldBe` Case_ [Ctor_ "J" 1, Ctor_ "N" 0]
            _ -> expectationFailure ("not a case over a binder: " ++ show (shapeOf out))

  describe "join points" $ do
    it "binds a body reached twice once, and jumps to it" $
      -- The first test covers the type, so the wildcard branch is reached from
      -- inside both of its edges rather than through one shared default: two
      -- leaves, one body. C15's node is what keeps it one body.
      let out =
            pass
              [ alt (precord [("l", pctor "J" 1 [Core.PWild]), ("r", pctor "J" 1 [Core.PWild])]) one,
                alt (precord [("l", pctor "N" 0 []), ("r", pctor "N" 0 [])]) one,
                alt Core.PWild one
              ]
       in (joinCount out, jumpCount out) `shouldBe` (1, 2)

    it "inlines a body reached once, and leaves no join at all" $
      let out = pass [alt (pctor "J" 1 [Core.PWild]) one, alt (pctor "N" 0 []) one]
       in (joinCount out, jumpCount out) `shouldBe` (0, 0)

  describe "bindings" $ do
    it "rebinds a branch's variables from the scrutinee, with the tests gone" $
      -- The leaf destructures `J n` again, and the pattern it does it with has
      -- no test left in it — `bindingsOnly` is where the literal goes.
      let out = pass [alt (pctor "J" 1 [pvar "n"]) (var "n"), alt (pctor "N" 0 []) one]
       in leafPatterns out `shouldBe` [Core.PCtor (q "J") 1 [Core.PVar (binder "n")]]

    it "gives a branch that binds nothing no wrapper" $
      let out = pass [alt (pctor "J" 1 [Core.PWild]) one, alt (pctor "N" 0 []) one]
       in leafPatterns out `shouldBe` []

-- RUNNING THE PASS

-- | Compile one @when@ over the two-constructor type `M` and the
-- one-constructor type `Box`, and hand back the definition's new body.
pass :: [Core.Alt] -> Core.Expr
pass alts =
  let m = modul [Core.Bind (binder "f") (Core.Expr (Core.ECase (var "scrutinee") alts Nothing) intT span0)]
   in case Core._moduleDefs (Case.run table m) of
        [Core.Bind _ value] -> value
        _ -> error "the pass lost the definition"

table :: Map.Map Core.QualName Case.Ctors
table = Case.table [modul []]

-- SHAPES

data Shape
  = Case_ [Shape]
  | Ctor_ Name Int
  | Other
  deriving (Eq, Show)

shapeOf :: Core.Expr -> Shape
shapeOf e =
  case Core._exprValue e of
    Core.ECase _ alts _ -> Case_ (map (patternShape . Core._altPattern) alts)
    _ -> Other

patternShape :: Core.Pattern -> Shape
patternShape p =
  case p of
    Core.PCtor (Core.QualName _ n) _ args -> Ctor_ n (length args)
    _ -> Other

joinCount :: Core.Expr -> Int
joinCount e =
  case Core._exprValue e of
    Core.EJoin binds body -> length binds + joinCount body
    Core.ELet _ body -> joinCount body
    _ -> 0

jumpCount :: Core.Expr -> Int
jumpCount e =
  case Core._exprValue e of
    Core.EJump _ _ -> 1
    Core.ECase scrutinee alts fallback ->
      sum (map (jumpCount . Core._altBody) alts) + maybe 0 jumpCount fallback + jumpCount scrutinee
    Core.EJoin binds body -> sum (map (jumpCount . Core._bindValue) binds) + jumpCount body
    Core.ELet binds body -> sum (map (jumpCount . Core._bindValue) binds) + jumpCount body
    _ -> 0

-- | The patterns of every one-alternative case, which is what a leaf's
-- rebinding looks like.
leafPatterns :: Core.Expr -> [Core.Pattern]
leafPatterns e =
  case Core._exprValue e of
    Core.ECase _ [Core.Alt p body] Nothing -> p : leafPatterns body
    Core.ECase _ alts fallback ->
      concatMap (leafPatterns . Core._altBody) alts ++ maybe [] leafPatterns fallback
    Core.EJoin binds body -> concatMap (leafPatterns . Core._bindValue) binds ++ leafPatterns body
    Core.ELet binds body -> concatMap (leafPatterns . Core._bindValue) binds ++ leafPatterns body
    _ -> []

-- BUILDING CORE

home :: ModuleName.Canonical
home = ModuleName.Canonical Pkg.dummyName "Main"

q :: Name -> Core.QualName
q = Core.QualName home

span0 :: Core.Span
span0 = Core.Span (Core.FileId 0) 1 1 1 1

intT :: Core.Type
intT = Core.TCon (Core.QualName (ModuleName.Canonical Pkg.core "Basics") "Int") []

mT :: Core.Type
mT = Core.TCon (q "M") []

binder :: Name -> Core.Binder
binder n = Core.Binder n intT span0

var :: Name -> Core.Expr
var n = Core.Expr (Core.EVar n) mT span0

one :: Core.Expr
one = Core.Expr (Core.ELit (Core.LIntLegacy 1)) intT span0

alt :: Core.Pattern -> Core.Expr -> Core.Alt
alt = Core.Alt

pvar :: Name -> Core.Pattern
pvar n = Core.PVar (binder n)

pctor :: Name -> Int -> [Core.Pattern] -> Core.Pattern
pctor n tag = Core.PCtor (q n) tag

precord :: [(Name, Core.Pattern)] -> Core.Pattern
precord = Core.PRecord

-- | Two datatypes: `M`, with two constructors, and `Box`, with one.
modul :: [Core.Bind] -> Core.Module
modul defs =
  Core.Module
    { Core._moduleName = home,
      Core._moduleFiles = Map.singleton (Core.FileId 0) home,
      Core._moduleData =
        [ Core.DataDecl (q "M") [] Core.Transparent [ctorDecl "N" 0 [], ctorDecl "J" 1 [intT]] [],
          Core.DataDecl (q "Box") [] Core.Transparent [ctorDecl "Box" 0 [intT]] []
        ],
      Core._moduleClasses = [],
      Core._moduleInstances = [],
      Core._moduleDefs = defs,
      Core._moduleDefsRec = [],
      Core._moduleExports = []
    }

ctorDecl :: Name -> Int -> [Core.Type] -> Core.Ctor
ctorDecl n tag fields = Core.Ctor (q n) tag fields
