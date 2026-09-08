{-# LANGUAGE OverloadedStrings #-}

-- | A constrained definition becomes one copy per witness it is handed, and the
-- projection out of the witness becomes the method itself (@docs/core.md@ C2,
-- @docs/m1b-classes.md@ §G27).
module Core.PassSpecializeSpec where

import Core.AST qualified as Core
import Core.Pass.Specialize qualified as Specialize
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Name (Name)
import Data.Name qualified as Name
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Test.Hspec

spec :: Spec
spec = do
  describe "one copy per instantiation" $ do
    it "makes a copy for each distinct witness a generic is applied to" $
      let out = pass [same, use "callInt" (witnessOf "eqInt"), use "callStr" (witnessOf "eqStr")]
       in defNames out `shouldBe` ["callInt", "callStr", "eqInt", "eqStr", "same", "same$s0", "same$s1"]

    it "makes one copy when two sites ask for the same witness" $
      let out = pass [same, use "one" (witnessOf "eqInt"), use "two" (witnessOf "eqInt")]
       in List.filter (isCopy "same") (defNames out) `shouldBe` ["same$s0"]

    it "leaves the generic binding alone, for the linker to drop" $
      let out = pass [same, use "callInt" (witnessOf "eqInt")]
       in valueOf out "same" `shouldSatisfy` isWitLam

    it "rewrites the call site to name the copy" $
      let out = pass [same, use "callInt" (witnessOf "eqInt")]
       in globalsOf (valueOf out "callInt") `shouldBe` ["same$s0"]

  describe "erasing the witness" $ do
    it "substitutes the witness parameter away" $
      let out = pass [same, use "callInt" (witnessOf "eqInt")]
       in valueOf out "same$s0" `shouldSatisfy` not . isWitLam

    it "folds the projection out of a known table into the method itself" $
      -- The half that pays: dropping the parameter alone would leave the copy
      -- reading a field out of a record whose identity it now knows, which was
      -- the cost the pass exists to remove (§G27.2).
      let out = pass [same, use "callInt" (witnessOf "eqInt")]
       in globalsOf (valueOf out "same$s0") `shouldBe` ["intEq"]

    it "leaves a projection off a record whose fields are not names" $
      -- The fold's condition is that the field is a name, so that replacing the
      -- projection duplicates no work. A computed field is not one.
      let table = def "computed" (record [("eq", call (globalE "mk") [])])
          out = pass [same, table, use "callInt" (globalE "computed")]
       in globalsOf (valueOf out "same$s0") `shouldBe` ["computed"]

  describe "an instance with a context" $ do
    it "specializes the table binding too, so a nested witness is a name" $
      -- `Eq a => Eq (Array a)` is an `EWitLam` over a table, which is a generic
      -- binding like any other — D125 doing its job.
      let out = pass [same, arrayEq, use "callArr" (witApp (globalE "eqArray") [witnessOf "eqInt"])]
       in List.filter (isCopy "eqArray") (defNames out) `shouldBe` ["eqArray$s0"]

    it "reaches the witness the nested one is built from" $
      let out = pass [same, arrayEq, use "callArr" (witApp (globalE "eqArray") [witnessOf "eqInt"])]
       in globalsOf (valueOf out "same$s0") `shouldBe` ["eqArray$s0"]

  describe "what it leaves alone" $ do
    it "leaves a witness application whose argument is a parameter" $
      -- The site waits for its own caller. It is not an error and the program
      -- still runs, which is why the pass is allowed to give up (§G27.3).
      let onward =
            Core.Bind
              (Core.Binder "twice" witFunT span0)
              (witLam ["$w0"] (witApp (globalE "same") [var "$w0"]))
          out = pass [same, onward]
       in valueOf out "twice" `shouldSatisfy` hasWitApp

    it "does nothing at all to a program with no witnesses" $
      let defs = [def "plain" (call (globalE "f") [one])]
       in Core._moduleDefs (only (Specialize.run (one_ (modul defs)))) `shouldBe` defs

  describe "the copy's types" $ do
    it "substitutes the variable its key fixed into the copy's own type" $
      -- §G26.1's open item, closed at §G29.7. The witness the key names is an
      -- instance table whose binding carries the concrete type, so matching it
      -- against the generic witness parameter says what `a` was.
      let out = pass [generic, useOf "generic" "callInt" (witnessOf "eqInt")]
       in typeOf out "generic$s0" `shouldBe` Core.TFun [intT] intT

    it "substitutes it into the binders inside the body too" $
      -- What a JS backend never reads and the Core -> C spike does: a copy with
      -- a boxed parameter where the call site passes an int32_t.
      let out = pass [generic, useOf "generic" "callInt" (witnessOf "eqInt")]
       in lamBinderTypes (valueOf out "generic$s0") `shouldBe` [intT]

    it "keeps quantifying whatever the instantiation did not fix" $
      let out = pass [generic2, useOf "generic2" "callInt" (witnessOf "eqInt")]
       in typeOf out "generic2$s0" `shouldBe` Core.TForall ["b"] [] (Core.TFun [intT] (Core.TVar "b"))

  describe "the names" $
    it "numbers a generic's copies over the sorted key set, not the traversal" $
      -- Same two instantiations, opposite discovery order, same two names on the
      -- same two witnesses (C6).
      let forward = pass [same, use "a" (witnessOf "eqInt"), use "b" (witnessOf "eqStr")]
          backward = pass [same, use "b" (witnessOf "eqStr"), use "a" (witnessOf "eqInt")]
       in globalsOf (valueOf forward "a") `shouldBe` globalsOf (valueOf backward "a")

-- RUNNING THE PASS

pass :: [Core.Bind] -> Core.Module
pass defs = only (Specialize.run (one_ (modul (defs ++ tables))))

one_ :: Core.Module -> Map.Map ModuleName.Canonical Core.Module
one_ m = Map.singleton home m

only :: Map.Map ModuleName.Canonical Core.Module -> Core.Module
only cores =
  case Map.elems cores of
    [m] -> m
    _ -> error "the pass lost the module"

-- READING THE RESULT

defNames :: Core.Module -> [Name]
defNames = List.sort . map (Core._binderName . Core._bindBinder) . Core._moduleDefs

typeOf :: Core.Module -> Name -> Core.Type
typeOf m wanted =
  case [Core._binderType b | Core.Bind b _ <- Core._moduleDefs m, Core._binderName b == wanted] of
    t : _ -> t
    [] -> error ("no definition named " ++ show wanted)

-- | The types an expression's outermost ordinary lambda binds.
lamBinderTypes :: Core.Expr -> [Core.Type]
lamBinderTypes e =
  case Core._exprValue e of
    Core.ELam binders _ -> map Core._binderType binders
    Core.EWitLam _ body -> lamBinderTypes body
    _ -> []

valueOf :: Core.Module -> Name -> Core.Expr
valueOf m wanted =
  case [v | Core.Bind b v <- Core._moduleDefs m, Core._binderName b == wanted] of
    v : _ -> v
    [] -> error ("no definition named " ++ show wanted)

-- | Whether a name is one of @base@'s copies.
isCopy :: Name -> Name -> Bool
isCopy base name = (Name.toChars base ++ "$s") `List.isPrefixOf` Name.toChars name

isWitLam :: Core.Expr -> Bool
isWitLam e = case Core._exprValue e of
  Core.EWitLam _ _ -> True
  _ -> False

hasWitApp :: Core.Expr -> Bool
hasWitApp e = case Core._exprValue e of
  Core.EWitApp _ _ -> True
  Core.EWitLam _ body -> hasWitApp body
  Core.ELam _ body -> hasWitApp body
  Core.EApp fn args -> any hasWitApp (fn : args)
  _ -> False

-- | Every global a body names, sorted, so a test can say what a copy calls.
globalsOf :: Core.Expr -> [Name]
globalsOf = List.sort . go
  where
    go e = case Core._exprValue e of
      Core.EGlobal (Core.QualName _ n) -> [n]
      Core.ELam _ body -> go body
      Core.EWitLam _ body -> go body
      Core.EApp fn args -> concatMap go (fn : args)
      Core.EWitApp fn args -> concatMap go (fn : args)
      Core.EAccess base _ -> go base
      Core.ERecord fields -> concatMap (go . snd) fields
      Core.ELet binds body -> concatMap (go . Core._bindValue) binds ++ go body
      _ -> []

-- BUILDING CORE

home :: ModuleName.Canonical
home = ModuleName.Canonical Pkg.dummyName "Main"

span0 :: Core.Span
span0 = Core.Span (Core.FileId 0) 1 1 1 1

intT :: Core.Type
intT = Core.TCon (Core.QualName (ModuleName.Canonical Pkg.core "Basics") "Int") []

-- | The witness record type: one field per method of the class.
witT :: Core.Type
witT = Core.TRecord [("eq", intT)] Nothing

-- | A constrained definition's type, with the constraint the copy discharges.
witFunT :: Core.Type
witFunT = Core.TForall ["a"] [Core.CClass (Core.QualName home "Eq") (Core.TVar "a")] intT

node :: Core.Expr_ -> Core.Expr
node v = Core.Expr v intT span0

var :: Name -> Core.Expr
var n = node (Core.EVar n)

globalE :: Name -> Core.Expr
globalE n = node (Core.EGlobal (Core.QualName home n))

one :: Core.Expr
one = node (Core.ELit (Core.LIntLegacy 1))

call :: Core.Expr -> [Core.Expr] -> Core.Expr
call fn args = node (Core.EApp fn args)

record :: [(Name, Core.Expr)] -> Core.Expr
record fields = Core.Expr (Core.ERecord fields) witT span0

access :: Core.Expr -> Name -> Core.Expr
access base field = node (Core.EAccess base field)

witLam :: [Name] -> Core.Expr -> Core.Expr
witLam names body = node (Core.EWitLam [Core.Binder n witT span0 | n <- names] body)

witApp :: Core.Expr -> [Core.Expr] -> Core.Expr
witApp fn args = node (Core.EWitApp fn args)

def :: Name -> Core.Expr -> Core.Bind
def n = Core.Bind (Core.Binder n intT span0)

-- | @same : Eq a => …@, whose body reads its method out of the witness it was
-- handed — the shape @Core.Lower.Expression@ builds for a call at a variable.
same :: Core.Bind
same =
  Core.Bind
    (Core.Binder "same" witFunT span0)
    (witLam ["$w0"] (access (var "$w0") "eq"))

-- | @instance Eq a => Eq (Array a)@: a table built from a table (D125).
arrayEq :: Core.Bind
arrayEq =
  Core.Bind
    (Core.Binder "eqArray" witFunT span0)
    (witLam ["$w0"] (record [("eq", witApp (globalE "arrayEqMethod") [var "$w0"])]))

-- | The witness parameter's type as the lowering really writes it: a record of
-- the class's methods /at the class parameter/, which is what makes the copy's
-- substitution derivable.
genericWitT :: Core.Type
genericWitT = Core.TRecord [("eq", Core.TVar "a")] Nothing

-- | @generic : Eq a => a -> a@, with the variable everywhere it belongs.
generic :: Core.Bind
generic =
  Core.Bind
    (Core.Binder "generic" (Core.TForall ["a"] [Core.CClass (Core.QualName home "Eq") (Core.TVar "a")] (Core.TFun [Core.TVar "a"] (Core.TVar "a"))) span0)
    ( Core.Expr
        (Core.EWitLam
           [Core.Binder "$w0" genericWitT span0]
           (Core.Expr (Core.ELam [Core.Binder "x" (Core.TVar "a") span0] (var "x")) (Core.TFun [Core.TVar "a"] (Core.TVar "a")) span0))
        (Core.TFun [Core.TVar "a"] (Core.TVar "a"))
        span0
    )

-- | @generic2 : Eq a => a -> b@: one variable the witness fixes and one it does
-- not.
generic2 :: Core.Bind
generic2 =
  Core.Bind
    (Core.Binder "generic2" (Core.TForall ["a", "b"] [Core.CClass (Core.QualName home "Eq") (Core.TVar "a")] (Core.TFun [Core.TVar "a"] (Core.TVar "b"))) span0)
    ( Core.Expr
        (Core.EWitLam
           [Core.Binder "$w0" genericWitT span0]
           (Core.Expr (Core.ELam [Core.Binder "x" (Core.TVar "a") span0] (var "x")) (Core.TFun [Core.TVar "a"] (Core.TVar "b")) span0))
        (Core.TFun [Core.TVar "a"] (Core.TVar "b"))
        span0
    )

-- | A use of a named generic at one witness.
useOf :: Name -> Name -> Core.Expr -> Core.Bind
useOf callee name witness = def name (witApp (globalE callee) [witness])

-- | A use of the generic at one witness.
use :: Name -> Core.Expr -> Core.Bind
use name witness = def name (witApp (globalE "same") [witness])

witnessOf :: Name -> Core.Expr
witnessOf = globalE

-- | The instance tables the witnesses name: a record whose fields are names, so
-- the fold applies.
tables :: [Core.Bind]
tables =
  [ Core.Bind (Core.Binder "eqInt" witT span0) (record [("eq", globalE "intEq")]),
    Core.Bind (Core.Binder "eqStr" witT span0) (record [("eq", globalE "strEq")])
  ]

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
      Core._modulePorts = [],
      Core._moduleMain = Nothing,
      Core._moduleExports = []
    }
