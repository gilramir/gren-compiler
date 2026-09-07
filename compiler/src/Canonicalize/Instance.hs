{-# OPTIONS_GHC -Wall #-}

-- | Canonicalize a module's @instance@ declarations (@docs/m1b-classes.md@
-- §G22).
--
-- __An instance head is an annotation.__ `Eq a => Eq (Array a)` parses as one
-- (§G16) and is split here, into the class it names and the one type it is
-- for; what is left — a context and a type — is exactly what
-- "Canonicalize.Type".'Canonicalize.Type.toAnnotation' takes, and it resolves
-- the context onto the head's variables for the same reason it resolves an
-- annotation's onto the type's. So @Eq a =>@ on an instance and @Eq a =>@ on a
-- signature are one piece of code and cannot drift apart.
--
-- __An instance method is a definition with an annotation it did not write.__
-- The class published one; specializing it at the head is a substitution, and
-- from there the method is canonicalized by the same path a top-level
-- annotated definition takes, down to 'Expr.gatherTypedArgs' reporting an
-- argument the type has no room for. Nothing about an instance body is a new
-- kind of thing.
--
-- __What the head's shape buys is termination.__ D11 asks for a Paterson-style
-- check, and there is nothing left for one to reject: a constraint's argument
-- is a variable by grammar (§G16), a context variable must be one the head
-- binds, and the head is a constructor applied to arguments. Every context
-- constraint is therefore strictly smaller than the head it belongs to, which
-- is the Paterson condition itself. §G22.2.
module Canonicalize.Instance
  ( canonicalize,
  )
where

import AST.Canonical qualified as Can
import AST.Source qualified as Src
import AST.Utils.Type qualified as Type
import Canonicalize.Environment qualified as Env
import Canonicalize.Environment.Dups qualified as Dups
import Canonicalize.Expression qualified as Expr
import Canonicalize.Pattern qualified as Pattern
import Canonicalize.Type qualified as Type
import Control.Monad (foldM)
import Data.Index qualified as Index
import Data.Map.Strict qualified as Map
import Data.Name qualified as Name
import Data.Set qualified as Set
import Gren.Package qualified as Pkg
import Reporting.Annotation qualified as A
import Reporting.Error.Canonicalize qualified as Error
import Reporting.Result qualified as Result
import Reporting.Warning qualified as W

-- RESULT

type Result i w a =
  Result.Result i w Error.Error a

type Instances =
  Map.Map Can.InstanceKey Can.Instance

-- CANONICALIZE

-- | The module's instances, checked against the instances already visible.
--
-- The environment it is checked against is the __closure__ of what this
-- module's imports publish (D114, D122), not the direct imports' own
-- declarations: an instance holds for every module that transitively depends
-- on the one declaring it, so the question "is there already one of these" has
-- to be asked of everything, and 'Gren.Interface' is where the closure is
-- assembled.
canonicalize ::
  Pkg.Name ->
  Map.Map Can.InstanceKey Can.InstanceHead ->
  Env.Env ->
  [A.Located Src.Instance] ->
  Result i [W.Warning] Instances
canonicalize pkg imported env instances =
  foldM (addInstance pkg imported env) Map.empty instances

addInstance ::
  Pkg.Name ->
  Map.Map Can.InstanceKey Can.InstanceHead ->
  Env.Env ->
  Instances ->
  A.Located Src.Instance ->
  Result i [W.Warning] Instances
addInstance pkg imported env sofar (A.At region (Src.Instance maybeContext srcHead methods _)) =
  do
    (classRegion, srcClassName, srcArg) <- splitHead srcHead

    -- Before the class name is resolved, because at M1b no package ships a
    -- class: a third-party `instance Eq Int` would otherwise report that there
    -- is no `Eq`, which is true and is not what is wrong with it.
    checkFirstParty pkg region srcClassName

    (cls@(Can.Class _ className), decl) <-
      case srcClassName of
        Unqualified name -> Env.findClassDecl classRegion env name
        Qualified home name -> Env.findClassDeclQual classRegion env home name

    (Can.Forall context canArgType) <- Type.toAnnotation env maybeContext srcArg

    head_ <-
      case canArgType of
        Can.TType home name args ->
          Result.ok $
            Can.InstanceHead
              { Can._ih_home = Env._home env,
                Can._ih_class = cls,
                Can._ih_con = home,
                Can._ih_conName = name,
                Can._ih_args = args,
                Can._ih_context = context
              }
        Can.TAlias _ name _ _ ->
          Result.throw (Error.InstanceHeadIsAlias (A.toRegion srcArg) className name)
        _ ->
          Result.throw (Error.InstanceHeadNotType (A.toRegion srcArg) className)

    let key = Can.instanceKey head_
    if Map.member key sofar || Map.member key imported
      then Result.throw (Error.InstanceDuplicate region className (Can._ih_conName head_))
      else do
        canMethods <- canonicalizeMethods env region className decl head_ methods
        Result.ok (Map.insert key (Can.Instance head_ canMethods) sofar)

-- | `classes.md` §8.3's gate, which classes and instances share.
--
-- The class name is the one the author wrote rather than one that resolved,
-- for the reason at the call site: nothing declares a class a third-party
-- module could name, so resolving first would report the missing class every
-- time and never the restriction.
checkFirstParty :: Pkg.Name -> A.Region -> ClassName -> Result i w ()
checkFirstParty pkg region srcClassName
  | Pkg.isFirstParty pkg = Result.ok ()
  | otherwise =
      Result.throw $
        Error.InstanceDeclThirdParty region $
          case srcClassName of
            Unqualified name -> name
            Qualified _ name -> name

-- THE HEAD

-- | A class name as the head wrote it, before anything resolves it.
data ClassName
  = Unqualified Name.Name
  | Qualified Name.Name Name.Name

-- | The head, split into the class it names and the one type it is for.
--
-- Split rather than canonicalized whole, because `Eq (Array a)` is a type
-- expression to the parser and only the environment knows that `Eq` is not a
-- type (§G16). A class takes one argument (D11), so a head of any other shape
-- is not one.
splitHead :: Src.Type -> Result i w (A.Region, ClassName, Src.Type)
splitHead (A.At headRegion head_) =
  case head_ of
    Src.TType region name [(_, arg)] ->
      Result.ok (region, Unqualified name, arg)
    Src.TTypeQual region home name [(_, arg)] ->
      Result.ok (region, Qualified home name, arg)
    Src.TParens inner _ ->
      splitHead inner
    _ ->
      Result.throw (Error.InstanceHeadNotApplied headRegion)

-- THE METHODS

-- | The definitions under the head, each against the signature its class
-- published.
--
-- Three things are checked and all three are about the class rather than about
-- the body: a name the class does not declare has nothing to be, a name
-- written twice has two answers, and a name left out is one a call cannot use
-- — a class has no default implementations (§G15), so there is nothing to fall
-- back to.
canonicalizeMethods ::
  Env.Env ->
  A.Region ->
  Name.Name ->
  Can.ClassDecl ->
  Can.InstanceHead ->
  [Src.InstanceMethod] ->
  Result i [W.Warning] (Map.Map Name.Name Can.Def)
canonicalizeMethods env region className (Can.ClassDecl param published) head_ methods =
  do
    let dups =
          foldr
            (\(_, A.At r (Src.Value (A.At nameRegion name) _ _ _ _)) d -> Dups.insert name nameRegion r d)
            Dups.none
            methods
    _ <- Dups.detect Error.DuplicateDecl dups

    canMethods <- traverse (canonicalizeMethod env className published head_ param) methods

    case Map.keys (Map.difference published (Map.fromList canMethods)) of
      [] ->
        Result.ok (Map.fromList canMethods)
      missing ->
        Result.throw (Error.InstanceMethodMissing region className (Can._ih_conName head_) missing)

canonicalizeMethod ::
  Env.Env ->
  Name.Name ->
  Map.Map Name.Name Can.Annotation ->
  Can.InstanceHead ->
  Name.Name ->
  Src.InstanceMethod ->
  Result i [W.Warning] (Name.Name, Can.Def)
canonicalizeMethod env className published head_ param (_, A.At _ (Src.Value aname@(A.At nameRegion name) srcArgs body _ _)) =
  case Map.lookup name published of
    Nothing ->
      Result.throw (Error.InstanceMethodUnknown nameRegion className name (Map.keys published))
    Just annotation ->
      do
        let (Can.Forall freeVars tipe) = specialize head_ param annotation

        ((args, resultType), argBindings) <-
          Pattern.verify (Error.DPFuncArgs name) $
            Expr.gatherTypedArgs env name (fmap snd srcArgs) tipe Index.first []

        newEnv <- Env.addLocals argBindings env

        (cbody, _) <-
          Expr.verifyBindings W.Pattern argBindings (Expr.canonicalize newEnv body)

        Result.ok (name, Can.TypedDef aname freeVars args cbody resultType)

-- SPECIALIZE

-- | A class method's published signature, at this instance's head.
--
-- @eq : Eq a => a -> a -> Bool@ at @instance Eq b => Eq (Array b)@ is
-- @eq : Eq b => Array b -> Array b -> Bool@: substitute the class parameter,
-- and the constraint that named the class being declared goes with it — it is
-- discharged by the instance existing, which is what an instance /is/.
--
-- The remaining variables are read back off the substituted type rather than
-- carried over by deleting the parameter, so that the constraint list and the
-- type cannot disagree about which variables there are. Each keeps whatever it
-- was constrained by: the head's variables from the instance's context, the
-- method's own from the class's declaration.
specialize :: Can.InstanceHead -> Name.Name -> Can.Annotation -> Can.Annotation
specialize head_ param (Can.Forall methodVars methodType) =
  let context = Can._ih_context head_
      (renamedVars, renamedType) = avoidCapture (Map.keysSet context) param methodVars methodType
      tipe = Type.substitute (Map.singleton param (Can.instanceType head_)) renamedType
      constraintsOf var _ =
        case Map.lookup var context of
          Just classes -> classes
          Nothing -> Map.findWithDefault [] var renamedVars
   in Can.Forall (Map.mapWithKey constraintsOf (Type.addFreeVars Map.empty tipe)) tipe

-- | Rename the method's own variables out of the way of the head's.
--
-- @class Sortable a where sortBy : Ord b => (a -> b) -> a -> a@ at
-- @instance Sortable (Array b)@ has two different variables both called @b@,
-- and the substitution would make them one. The class's are the ones renamed,
-- because the author of the instance wrote the head and did not write the
-- class body — a message about a collision would be about a name they cannot
-- see.
avoidCapture ::
  Set.Set Name.Name ->
  Name.Name ->
  Can.FreeVars ->
  Can.Type ->
  (Can.FreeVars, Can.Type)
avoidCapture headVars param methodVars methodType =
  let taken = Set.union headVars (Map.keysSet methodVars)
      colliding = [v | v <- Map.keys methodVars, v /= param, Set.member v headVars]
      pick used v =
        case [candidate | n <- [(1 :: Int) ..], let candidate = freshen v n, not (Set.member candidate used)] of
          candidate : _ -> candidate
          [] -> v
      step (used, renaming) v =
        let v' = pick used v
         in (Set.insert v' used, Map.insert v v' renaming)
      (_, names) = foldl step (taken, Map.empty) colliding
      rename vars =
        Map.fromList [(Map.findWithDefault v v names, cs) | (v, cs) <- Map.toList vars]
   in ( rename methodVars,
        Type.substitute (Map.map Can.TVar names) methodType
      )

freshen :: Name.Name -> Int -> Name.Name
freshen name n =
  Name.fromChars (Name.toChars name ++ show n)
