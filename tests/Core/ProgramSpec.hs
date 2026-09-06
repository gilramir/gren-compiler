{-# LANGUAGE OverloadedStrings #-}

-- | Linking Core into a reachable program (@docs/m1a-js-on-core.md@ §J3 item 1).
--
-- Four properties, each of which the JS backend will depend on: only what the
-- roots reach is kept, the order is a specified one rather than a library's,
-- mutual recursion stays grouped, and a name Core cannot supply is reported
-- rather than dropped.
module Core.ProgramSpec where

import Core.AST qualified as Core
import Core.Program (Missing (..), MissingKind (..), Program (..))
import Core.Program qualified as Program
import Data.List (elemIndex)
import Data.Map qualified as Map
import Data.Name (Name)
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Test.Hspec

spec :: Spec
spec = do
  describe "reachability" $ do
    it "keeps what a root reaches and drops what it does not" $
      let p =
            link
              [modul home [bind "main" (globalE (q "used")), bind "used" one, bind "unused" one]]
              [q "main"]
       in names p `shouldBe` [q "used", q "main"]

    it "follows a chain of references" $
      let p =
            link
              [ modul
                  home
                  [ bind "main" (globalE (q "a")),
                    bind "a" (globalE (q "b")),
                    bind "b" one,
                    bind "elsewhere" (globalE (q "b"))
                  ]
              ]
              [q "main"]
       in names p `shouldBe` [q "b", q "a", q "main"]

    it "crosses a module boundary" $
      let p =
            link
              [ modul home [bind "main" (globalE (qIn other "helper"))],
                modul other [bind "helper" one, bind "unused" one]
              ]
              [q "main"]
       in names p `shouldBe` [qIn other "helper", q "main"]

  describe "order" $ do
    it "puts a definition after everything it uses" $
      -- The property a backend needs. Written in the opposite order on purpose.
      let p =
            link
              [modul home [bind "c" (globalE (q "b")), bind "b" (globalE (q "a")), bind "a" one]]
              [q "c"]
       in names p `shouldBe` [q "a", q "b", q "c"]

    it "breaks ties by the least name, not by source order" $
      -- `zed` and `abc` are independent, so nothing but the rule decides which
      -- comes first. Source order says `zed`; the rule says `abc`.
      let p =
            link
              [ modul
                  home
                  [ bind "main" (appE (globalE (q "zed")) [globalE (q "abc")]),
                    bind "zed" one,
                    bind "abc" one
                  ]
              ]
              [q "main"]
       in names p `shouldBe` [q "abc", q "zed", q "main"]

  describe "recursive groups" $ do
    it "keeps a mutually recursive pair together, ordered within the group" $
      let p =
            link
              [ modul
                  home
                  [ bind "main" (globalE (q "isEven")),
                    bind "isEven" (globalE (q "isOdd")),
                    bind "isOdd" (globalE (q "isEven"))
                  ]
              ]
              [q "main"]
       in do
            _progRecursive p `shouldBe` [[q "isEven", q "isOdd"]]
            names p `shouldBe` [q "isEven", q "isOdd", q "main"]

    it "reports no group for a self-recursive binding" $
      -- One name is not a group: a backend that emits a group together has
      -- nothing extra to do for a function that calls itself.
      let p = link [modul home [bind "loop" (globalE (q "loop"))]] [q "loop"]
       in _progRecursive p `shouldBe` []

  describe "missing names" $ do
    it "classifies a kernel reference" $
      let kernelName = Core.QualName (ModuleName.Canonical Pkg.kernel "Utils") "compare"
          p = link [modul home [bind "main" (globalE kernelName)]] [q "main"]
       in map (\m -> (_missingKind m, _missingName m, _missingUsedBy m)) (_progMissing p)
            `shouldBe` [(MissingKernel, kernelName, q "main")]

    it "classifies anything else as a value" $
      -- An effect manager or a port today (§L8), and a lowering bug if neither.
      let p = link [modul home [bind "main" (globalE (qIn other "manager"))]] [q "main"]
       in map _missingKind (_progMissing p) `shouldBe` [MissingValue]

    it "reports a root that has no binding" $
      -- Otherwise the program quietly has no entry point.
      let p = link [modul home [bind "other" one]] [q "main"]
       in map (\m -> (_missingKind m, _missingName m)) (_progMissing p)
            `shouldBe` [(MissingValue, q "main")]

    it "says nothing about a name only unreachable code refers to" $
      let kernelName = Core.QualName (ModuleName.Canonical Pkg.kernel "Utils") "compare"
          p = link [modul home [bind "main" one, bind "dead" (globalE kernelName)]] [q "main"]
       in _progMissing p `shouldBe` []

  describe "fields" $ do
    it "collects field names from reachable code only" $
      let p =
            link
              [ modul
                  home
                  [ bind "main" (Core.Expr (Core.EAccess one "reached") intT span0),
                    bind "dead" (Core.Expr (Core.ERecord [("skipped", one)]) intT span0)
                  ]
              ]
              [q "main"]
       in Set.toAscList (_progFields p) `shouldBe` ["reached"]

  describe "datatypes" $ do
    it "keeps a datatype whose constructor is reachable, and no others" $
      let used = dataDecl "Used" "Yes"
          unused = dataDecl "Unused" "No"
          ctorE = Core.Expr (Core.ECtor (q "Yes") 0 []) intT span0
          m =
            (modul home [bind "main" ctorE])
              { Core._moduleData = [used, unused]
              }
          p = link [m] [q "main"]
       in map Core._dataName (_progData p) `shouldBe` [q "Used"]

  describe "effect managers" $ do
    it "roots a manager's functions when an entry binding is reached" $
      -- The rule the old pipeline gets from its `Opt.Link` to `$fx$`: using
      -- `command` is what makes the manager live, and the manager is what needs
      -- `init`, `onEffects`, `onSelfMsg` and `cmdMap`. None of them is
      -- mentioned by any expression here.
      let p = link (managerModules cmdManager) [qIn other "main"]
       in map snd (map splitQ (names p))
            `shouldBe` ["cmdMap", "init", "onEffects", "onSelfMsg", "command", "main"]

    it "emits a manager's functions before the entry that reaches them" $
      -- A runtime registers a manager at load time, reading those names, so
      -- they have to be defined by then.
      let p = link (managerModules cmdManager) [qIn other "main"]
          order = map snd (map splitQ (names p))
       in (elemIndex "init" order < elemIndex "command" order) `shouldBe` True

    it "reports a manager the program reaches" $
      let p = link (managerModules cmdManager) [qIn other "main"]
       in map (fmap Core._managerKind) (_progManagers p)
            `shouldBe` [(home, Core.ManagerCmd)]

    it "reports no manager when no entry is reached" $
      let p = link (managerModules cmdManager) [qIn other "unrelated"]
       in _progManagers p `shouldBe` []

    it "takes both entries of an `Fx` manager, and its two maps" $
      -- No package in existence declares one — all eleven `effect module`s in
      -- `core` and `node` are `command` or `subscription`, never both — so this
      -- is the only thing that exercises the shape.
      let p = link (managerModules fxManager) [qIn other "both"]
          reached = map snd (map splitQ (names p))
       in (all (`elem` reached) ["cmdMap", "subMap", "command", "subscription"], map (fmap Core._managerKind) (_progManagers p))
            `shouldBe` (True, [(home, Core.ManagerFx)])

    it "does not root the other entry's map when only one entry is reached" $
      -- `command` and `subscription` are separate bindings, so reaching one
      -- roots the manager and not the other way in.
      let p = link (managerModules fxManager) [qIn other "main"]
       in ("subscription" `elem` map snd (map splitQ (names p))) `shouldBe` False

  describe "ports" $ do
    it "keeps a port the program reaches, and drops one it does not" $
      let p = link (portModules [outPort "used", outPort "unused"]) [qIn other "main"]
       in map (fmap portName) (_progPorts p) `shouldBe` [(home, "used")]

    it "follows a port to its converter" $
      -- The converter is not a binding, so nothing else names it: an edge from
      -- the port to what its converter refers to is the only thing keeping the
      -- encoder alive.
      let p = link (portModules [outPort "used"]) [qIn other "main"]
       in (q "encode" `elem` names p) `shouldBe` True

    it "puts a port after the converter's dependencies" $
      -- The converter has to be defined by the time the port's definition runs,
      -- which is why ports are ordered with the bindings rather than after them.
      let p = link (portModules [outPort "used"]) [qIn other "main"]
          order = map (snd . splitQ) (map fst (_progBindings p) ++ [portQ pt | (_, pt) <- _progPorts p])
       in (elemIndex "encode" order < elemIndex "used" order) `shouldBe` True

    it "does not report a port as a missing value" $
      -- A port defines its name. Before C18 it did not, and every port in a
      -- program was a `MissingValue` line in this summary.
      let p = link (portModules [outPort "used"]) [qIn other "main"]
       in _progMissing p `shouldBe` []

    it "takes both converters of a task port with an input" $
      let p = link (portModules [taskPort "used" True]) [qIn other "main"]
       in (all (`elem` map (snd . splitQ) (names p)) ["encode", "decode"]) `shouldBe` True

    it "takes only the decoder of a task port with no input" $
      -- The shape whose runtime call Core cannot write as an expression. What
      -- the linker sees of it is one converter instead of two.
      let p = link (portModules [taskPort "used" False]) [qIn other "main"]
          reached = map (snd . splitQ) (names p)
       in ("decode" `elem` reached, "encode" `elem` reached) `shouldBe` (True, False)

-- HELPERS

-- | A module declaring ports, and a second module that names one of them.
--
-- Two modules for the same reason 'managerModules' uses two: a root inside the
-- port's own module could reach everything by naming it directly, and what is
-- being tested is that naming the /port/ is enough.
portModules :: [Core.Port] -> [Core.Module]
portModules ports =
  [ (modul home [bind "encode" one, bind "decode" one]) {Core._modulePorts = ports},
    modul other [bind "main" (globalE (q "used"))]
  ]

-- | An outgoing port whose encoder names @Main.encode@ and nothing else.
outPort :: Name -> Core.Port
outPort name =
  Core.Port (Core.Binder name intT span0) (Core.PortOut (converter "encode"))

-- | A task port, with an input converter or without one.
taskPort :: Name -> Bool -> Core.Port
taskPort name hasInput =
  Core.Port (Core.Binder name intT span0) $
    Core.PortTask
      (if hasInput then Just (converter "encode") else Nothing)
      (converter "decode")

converter :: Name -> Core.Converter
converter name = Core.Converter False (globalE (q name))

portName :: Core.Port -> Name
portName = Core._binderName . Core._portBinder

portQ :: Core.Port -> Core.QualName
portQ = q . portName

-- | A module with a manager, and a second module that enters it.
--
-- Two modules rather than one because the entries are what the rule is about:
-- a root inside the manager's own module would be free to reach everything by
-- naming it. The entry bindings are @one@ here rather than
-- @Platform.leaf "Main"@ — what matters to the linker is that they are ordinary
-- bindings that name none of the five functions.
managerModules :: Core.Manager -> [Core.Module]
managerModules m =
  [ (modul home defs) {Core._moduleManager = Just m},
    modul
      other
      [ bind "main" (globalE (q "command")),
        bind "both" (appE (globalE (q "command")) [globalE (q "subscription")]),
        bind "unrelated" one
      ]
  ]
  where
    defs =
      [ bind "command" one,
        bind "subscription" one,
        bind "init" one,
        bind "onEffects" one,
        bind "onSelfMsg" one,
        bind "cmdMap" one,
        bind "subMap" one
      ]

cmdManager :: Core.Manager
cmdManager =
  Core.Manager
    { Core._managerKind = Core.ManagerCmd,
      Core._managerEntries = [q "command"],
      Core._managerInit = q "init",
      Core._managerOnEffects = q "onEffects",
      Core._managerOnSelfMsg = q "onSelfMsg",
      Core._managerCmdMap = Just (q "cmdMap"),
      Core._managerSubMap = Nothing
    }

fxManager :: Core.Manager
fxManager =
  cmdManager
    { Core._managerKind = Core.ManagerFx,
      Core._managerEntries = [q "command", q "subscription"],
      Core._managerSubMap = Just (q "subMap")
    }

splitQ :: Core.QualName -> (ModuleName.Canonical, Name)
splitQ (Core.QualName h n) = (h, n)

link :: [Core.Module] -> [Core.QualName] -> Program
link modules roots =
  Program.link (Map.fromList [(Core._moduleName m, m) | m <- modules]) roots

names :: Program -> [Core.QualName]
names = map fst . _progBindings

home :: ModuleName.Canonical
home = ModuleName.Canonical Pkg.dummyName "Main"

other :: ModuleName.Canonical
other = ModuleName.Canonical Pkg.dummyName "Other"

q :: Name -> Core.QualName
q = Core.QualName home

qIn :: ModuleName.Canonical -> Name -> Core.QualName
qIn = Core.QualName

span0 :: Core.Span
span0 = Core.Span (Core.FileId 0) 1 1 1 1

intT :: Core.Type
intT = Core.TCon (Core.QualName (ModuleName.Canonical Pkg.core "Basics") "Int") []

one :: Core.Expr
one = Core.Expr (Core.ELit (Core.LIntLegacy 1)) intT span0

globalE :: Core.QualName -> Core.Expr
globalE name = Core.Expr (Core.EGlobal name) intT span0

appE :: Core.Expr -> [Core.Expr] -> Core.Expr
appE fn args = Core.Expr (Core.EApp fn args) intT span0

bind :: Name -> Core.Expr -> Core.Bind
bind name value = Core.Bind (Core.Binder name intT span0) value

dataDecl :: Name -> Name -> Core.DataDecl
dataDecl name ctorName =
  Core.DataDecl
    { Core._dataName = q name,
      Core._dataParams = [],
      Core._dataTransparency = Core.Transparent,
      Core._dataCtors = [Core.Ctor {Core._ctorName = q ctorName, Core._ctorTag = 0, Core._ctorFields = []}],
      Core._dataClasses = []
    }

modul :: ModuleName.Canonical -> [Core.Bind] -> Core.Module
modul name defs =
  Core.Module
    { Core._moduleName = name,
      Core._moduleFiles = Map.singleton (Core.FileId 0) name,
      Core._moduleData = [],
      Core._moduleClasses = [],
      Core._moduleInstances = [],
      Core._moduleDefs = defs,
      Core._moduleDefsRec = [],
      Core._moduleManager = Nothing,
      Core._modulePorts = [],
      Core._moduleExports = []
    }
