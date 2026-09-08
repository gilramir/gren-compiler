{-# OPTIONS_GHC -Wall #-}

-- | Elaborate every use of a constrained name (@docs/m1b-classes.md@ §G23,
-- §G26).
--
-- Three things happen here and they are one question asked three ways: which
-- instance does this call use?
--
--   * @eq 1 2@ — the class parameter is a type, so an instance is looked up and
--     the call becomes a reference to that instance's binding (§G23).
--   * @eq x y@ inside @f : Eq a => a -> Bool@ — the class parameter is a
--     variable the definition is /constrained on/, so the instance is whatever
--     the caller passed and the call takes the method out of it (§G26).
--   * @f 1 2@ where @f : Eq a => …@ — the callee needs an instance, so the call
--     site builds one and passes it.
--
-- __It runs after the solve, because the type at the call is the input.__ The
-- canonicalizer does not know it; the solver records one per expression node
-- (@docs/m1a-node-types.md@), and matching a name's /declared/ type against the
-- type its use site came out as is the substitution the constraints ride on.
-- That is one rule for all four ways a name can be used — local, top-level,
-- imported, operator — where the solver has a different constraint form for
-- each and one of them, 'Type.Solve.CLocal', copies a generalized variable
-- without ever naming its parts.
--
-- __It runs before the lowering, because a bad program is a program.__
-- @Core.Lower@ is total and reports nothing; "there is no instance for this"
-- is an error a person reads, so it has to be produced by a phase that can
-- produce one. The lowering then reads the answers and is total, exactly as it
-- is with node types.
--
-- __What it produces is names.__ D123: an instance method is a Core binding
-- with a compiler-made name, and D125 makes the instance's method table one
-- too. So a resolved call is an ordinary reference to an ordinary definition,
-- and every pass, DCE and backend already knows what to do with it.
module Type.Resolve
  ( Env (..),
    Elaboration (..),
    Uses,
    Params,
    Use (..),
    localNames,
    Witness (..),
    Bound,
    run,
    witnessFor,
    witnessRecord,
    witnessType,
    witnessParams,
  )
where

import AST.Canonical qualified as Can
import AST.Utils.Type qualified as Type
import Control.Monad.Trans.State.Strict (State, get, modify', put, runState)
import Data.Map.Strict qualified as Map
import Data.Name (Name)
import Data.Name qualified as Name
import Data.NonEmptyList qualified as NE
import Gren.ModuleName qualified as ModuleName
import Reporting.Annotation qualified as A
import Reporting.Error.Instance qualified as E

-- WHAT COMES OUT

-- | Everything the lowering needs to turn constraints into code.
data Elaboration = Elaboration
  { -- | One entry per use of a constrained name, keyed by the node it is.
    _uses :: Uses,
    -- | The witness parameters each definition binds, keyed by the node id of
    -- the definition's __body__.
    --
    -- Keyed by the body rather than by the definition, because a
    -- 'AST.Canonical.TypedDef' has no id of its own and its body always does.
    -- Published rather than recomputed in the lowering: the names have to be
    -- distinct all the way down a nesting chain, so they come from one counter
    -- in one traversal instead of two traversals agreeing about depth.
    _params :: Params,
    -- | The witness parameters each of the module's own instances binds, for
    -- the method table D125 gives it. Its body names only globals and these,
    -- so they start at @$w0@ again rather than sharing the counter.
    _instanceParams :: Map.Map Can.InstanceKey [(Name, Can.Type)]
  }

type Uses =
  Map.Map Can.NodeId Use

type Params =
  Map.Map Can.NodeId [(Name, Can.Type)]

-- | What one use of a constrained name elaborates to.
data Use
  = -- | A class-method call whose class parameter is a type: the module the
    -- instance is declared in, the name of that instance's binding for this
    -- method, and witnesses for the instance's own context.
    Instantiated ModuleName.Canonical Name [Witness]
  | -- | A class-method call at a variable the definition is constrained on:
    -- the witness it was passed, and the method to take out of it.
    Projected Witness Name
  | -- | Any other use of a name whose annotation is constrained: the witnesses
    -- to apply it to. Never empty.
    Applied [Witness]

-- | An instance, as a value a call site can hand over.
data Witness
  = -- | The enclosing definition's witness parameter, and its type.
    FromParam Name Can.Type
  | -- | An instance's method table — the binding D125 gives every instance —
    -- applied to witnesses for the instance's own context, and its type.
    FromInstance ModuleName.Canonical Name [Witness] Can.Type

-- WHAT GOES IN

data Env = Env
  { -- | Every instance this module can see: its own and its imports' closure.
    _envInstances :: Map.Map Can.InstanceKey Can.InstanceHead,
    -- | Every class this module can name, for the record a witness for a
    -- constrained /variable/ has. An instance's witness needs no entry here:
    -- 'Can._ih_methods' carries what it holds, because an instance is global
    -- and may mention a class this module cannot name.
    _envClasses :: Map.Map Can.Class Can.ClassDecl,
    -- | One type per expression node, from the solver.
    _envTypes :: Map.Map Can.NodeId Can.Type
  }

-- THE WITNESS RECORD

-- | The record a witness for @C t@ is: one field per method of @C@, at @t@.
--
-- A witness is a record and not a nominal thing, so the lowering needs no new
-- Core type and a backend needs no new node — 'Core.AST.EWitLam' and
-- 'Core.AST.EWitApp' are marked so that specialization knows which to erase
-- (R1), and are otherwise a lambda and a call.
witnessRecord :: Map.Map Name Can.Type -> Can.Type
witnessRecord methods =
  Can.TRecord
    (Map.fromList [(m, Can.FieldType (fromIntegral i) t) | (i, (m, t)) <- zip [0 :: Int ..] (Map.toAscList methods)])
    Nothing

-- | The witness type for @C t@, read off the class's published signatures.
witnessType :: Env -> Can.Class -> Can.Type -> Can.Type
witnessType env cls tipe =
  case Map.lookup cls (_envClasses env) of
    Nothing ->
      -- A constraint that resolved has a class, and a class this module wrote
      -- a constraint against is one it can name. An empty record is the
      -- harmless answer if that is ever wrong.
      witnessRecord Map.empty
    Just (Can.ClassDecl param methods) ->
      witnessRecord $
        Map.map
          (\(Can.Forall _ methodType) -> Type.substitute (Map.singleton param tipe) methodType)
          methods

-- | The witness parameters a context binds, in 'Can.witnessOrder'.
--
-- The names are the caller's, because they have to be distinct down a whole
-- nesting chain; the types are computed here.
--
-- 'Can.witnessOrder' and not 'Can.contextOrder': a closed class binds nothing
-- (D130, D135). `Num a =>` is enforced by unification, has no instances and no
-- methods, so there is no witness to pass and a definition constrained only by
-- closed classes takes exactly the arguments it is written with.
witnessParams :: Env -> [Name] -> Can.FreeVars -> [(Name, Can.Type)]
witnessParams env names context =
  [ (name, witnessType env cls (Can.TVar var))
  | (name, (var, cls)) <- zip names (Can.witnessOrder context)
  ]

-- MATCHING

-- | The substitution that turns a declared type into the type at a use site.
--
-- First-order and total: a bound variable of the declared type occurs in it
-- (§G21 checks that when the constraint is resolved), so every constrained
-- variable gets an answer, and anything that does not line up is left out
-- rather than reported — the solver has already decided the program typechecks
-- and this is reading its answer, not checking it.
match :: Can.Type -> Can.Type -> Map.Map Name Can.Type -> Map.Map Name Can.Type
match declared actual acc =
  case (declared, actual) of
    (Can.TAlias _ _ args aliased, _) ->
      match (Type.dealias args aliased) actual acc
    (_, Can.TAlias _ _ args aliased) ->
      match declared (Type.dealias args aliased) acc
    (Can.TVar name, _) ->
      Map.insertWith (\_ old -> old) name actual acc
    (Can.TLambda a b, Can.TLambda c d) ->
      match b d (match a c acc)
    (Can.TType _ _ as, Can.TType _ _ bs) ->
      foldl (\seen (a, b) -> match a b seen) acc (zip as bs)
    (Can.TRecord as _, Can.TRecord bs _) ->
      foldl
        (\seen (Can.FieldType _ a, Can.FieldType _ b) -> match a b seen)
        acc
        (Map.elems (Map.intersectionWith (,) as bs))
    _ ->
      acc

-- | Apply a substitution, leaving a variable it says nothing about alone.
under :: Map.Map Name Can.Type -> Name -> Can.Type
under sub var =
  Map.findWithDefault (Can.TVar var) var sub

-- BUILDING A WITNESS

-- | Where the witness for one constraint comes from.
--
-- @Eq Int@ is an instance. @Eq (Array Int)@ is an instance applied to the
-- witness its own context asks for, which is the recursive case §G23.6 left
-- open — and which is also what discharges a context, so
-- @instance Sizey a => Sizey (Array a)@ no longer answers for
-- @Array (Int -> Int)@. @Eq a@ is the parameter the enclosing definition was
-- given.
witnessFor ::
  Env ->
  Bound ->
  A.Region ->
  E.Wanted ->
  [(Can.Class, Can.Type)] ->
  Can.Class ->
  Can.Type ->
  Either E.Error Witness
witnessFor env bound region wanted because cls tipe =
  case Type.iteratedDealias tipe of
    Can.TVar var ->
      case Map.lookup (cls, var) bound of
        Just name ->
          Right (FromParam name (witnessType env cls (Can.TVar var)))
        Nothing ->
          Left (E.NotConstrained region wanted cls var because)
    actual@(Can.TType home name args) ->
      case Map.lookup (Can.InstanceKey cls home name) (_envInstances env) of
        Nothing ->
          Left (E.NoInstance region wanted cls actual because)
        Just head_ ->
          do
            let sub = foldl (\seen (a, b) -> match a b seen) Map.empty (zip (Can._ih_args head_) args)
            let deeper = because ++ [(cls, actual)]
            args' <-
              traverse
                (\(var, ctxCls) -> witnessFor env bound region wanted deeper ctxCls (under sub var))
                (Can.witnessOrder (Can._ih_context head_))
            Right $
              FromInstance
                (Can._ih_home head_)
                (Can._ih_witness head_)
                args'
                (witnessRecord (Map.map (Type.substitute sub) (Can._ih_methods head_)))
    actual ->
      -- A function or a record. An instance head is a type constructor applied
      -- to arguments (§G22.1), so neither can ever have one.
      Left (E.NoInstance region wanted cls actual because)

-- THE WALK

-- | What is in scope at a node: the witness parameters the enclosing
-- definitions bind, and the annotations of the constrained names they define.
-- | The constrained variables in scope, and the witness parameter each was
-- given.
type Bound =
  Map.Map (Can.Class, Name) Name

data Scope = Scope
  { _scopeParams :: Bound,
    -- | @let@-bound definitions with a written annotation, so that a use of one
    -- knows what it needs. A name bound by a pattern removes its entry, because
    -- it is then a different name.
    _scopeLocals :: Map.Map Name Can.Annotation
  }

type Walk a =
  State (Uses, Params, [E.Error], Int) a

emit :: Can.NodeId -> Either E.Error Use -> Walk ()
emit nid answer =
  modify' $ \(uses, params, errs, n) ->
    case answer of
      Right use -> (Map.insert nid use uses, params, errs, n)
      Left err -> (uses, params, errs ++ [err], n)

failure :: E.Error -> Walk ()
failure err =
  modify' $ \(uses, params, errs, n) -> (uses, params, errs ++ [err], n)

-- | Distinct names for a definition's witness parameters.
--
-- One counter for the module, advanced in the traversal order below, because
-- an inner definition's parameters are in scope beside an outer definition's
-- and two of them called @$w0@ would make the inner one shadow a witness the
-- body still needs. A @$@ cannot appear in a Gren name, so nothing written can
-- collide with one either.
freshNames :: Int -> Walk [Name]
freshNames count =
  do
    (uses, params, errs, n) <- get
    put (uses, params, errs, n + count)
    return [Name.fromChars ("$w" ++ show i) | i <- [n .. n + count - 1]]

-- | Elaborate a module, or report every use that cannot be.
--
-- Every one of them, rather than the first: they are independent questions
-- about independent call sites, and a person fixing one wants to see the rest.
run :: Env -> Can.Module -> Either (NE.List E.Error) Elaboration
run env modul =
  let scope = Scope Map.empty Map.empty
      walk =
        do
          let tops = topLevel (Can._decls modul)
          decls env tops scope (Can._decls modul)
          mapM_ (instanceMethods env tops scope) (Map.elems (Can._instances modul))
      (_, (uses, params, errs, _)) = runState walk (Map.empty, Map.empty, [], 0)
      ofInstance i =
        let context = Can._ih_context (Can._in_head i)
         in witnessParams env (localNames (length (Can.witnessOrder context))) context
   in case errs of
        [] -> Right (Elaboration uses params (Map.map ofInstance (Can._instances modul)))
        err : rest -> Left (NE.List err rest)

-- | Witness parameter names for a binding whose body names nothing else local.
localNames :: Int -> [Name]
localNames count =
  [Name.fromChars ("$w" ++ show i) | i <- [0 .. count - 1]]

-- | The module's own annotated top-level definitions, which is what a
-- 'Can.VarTopLevel' names and does not carry.
topLevel :: Can.Decls -> Map.Map Name Can.Annotation
topLevel ds =
  case ds of
    Can.Declare d rest -> Map.union (annotationOf d) (topLevel rest)
    Can.DeclareRec d others rest ->
      Map.unions (map annotationOf (d : others) ++ [topLevel rest])
    Can.SaveTheEnvironment -> Map.empty

annotationOf :: Can.Def -> Map.Map Name Can.Annotation
annotationOf d =
  case d of
    Can.Def {} -> Map.empty
    Can.TypedDef (A.At _ name) freeVars args _ result ->
      Map.singleton name (Can.Forall freeVars (foldr (Can.TLambda . snd) result args))

decls :: Env -> Map.Map Name Can.Annotation -> Scope -> Can.Decls -> Walk ()
decls env tops scope ds =
  case ds of
    Can.Declare d rest ->
      def env tops scope d >> decls env tops scope rest
    Can.DeclareRec d others rest ->
      mapM_ (def env tops scope) (d : others) >> decls env tops scope rest
    Can.SaveTheEnvironment ->
      return ()

-- | An instance's methods, under the module's own top-level annotations.
--
-- Those annotations are not optional here and it took a corpus case to say so
-- (`docs/m1b-classes.md` §G29.7). An instance method is an ordinary definition
-- (§G22.4) and its body may call an ordinary constrained one — `instance Ord a
-- => Ord (Array a)` calls `Array.compareFrom`, which is `Ord a =>` — and a use
-- of a name this map does not hold is a use the elaborator has no annotation
-- for, so it passes no witness and the call is left with its arguments shifted
-- by one. It compiles and it is wrong at runtime.
instanceMethods :: Env -> Map.Map Name Can.Annotation -> Scope -> Can.Instance -> Walk ()
instanceMethods env tops scope i =
  mapM_ (def env tops scope) (Map.elems (Can._in_methods i))

-- | A definition: bind its witness parameters, then walk its body under them.
def :: Env -> Map.Map Name Can.Annotation -> Scope -> Can.Def -> Walk ()
def env tops scope d =
  case d of
    Can.Def _ _ args body ->
      expr env tops (bindPatterns args scope) body
    Can.TypedDef _ freeVars args body _ ->
      do
        let context = Can.witnessOrder freeVars
        names <- freshNames (length context)
        let bound = witnessParams env names freeVars
        let scope' =
              scope
                { _scopeParams =
                    Map.union
                      (Map.fromList [((cls, var), name) | ((var, cls), name) <- zip context names])
                      (_scopeParams scope)
                }
        modify' $ \(uses, params, errs, n) ->
          (uses, Map.insert (nodeIdOf body) bound params, errs, n)
        expr env tops (bindPatterns (map fst args) scope') body

nodeIdOf :: Can.Expr -> Can.NodeId
nodeIdOf (Can.Expr nid _ _) = nid

typeOf :: Env -> Can.NodeId -> Can.Type
typeOf env nid =
  Map.findWithDefault (Can.TVar (Name.fromChars "?")) nid (_envTypes env)

-- | Names a pattern binds stop naming whatever they named outside it.
bindPatterns :: [Can.Pattern] -> Scope -> Scope
bindPatterns patterns scope =
  scope {_scopeLocals = foldr (Map.delete) (_scopeLocals scope) (concatMap patternNames patterns)}

patternNames :: Can.Pattern -> [Name]
patternNames (A.At _ p) =
  case p of
    Can.PVar name -> [name]
    Can.PAlias inner name -> name : patternNames inner
    Can.PRecord fields -> concatMap (\(A.At _ (Can.PRFieldPattern _ inner)) -> patternNames inner) fields
    Can.PArray items -> concatMap patternNames items
    Can.PCtor _ _ _ _ _ args -> concatMap (\(Can.PatternCtorArg _ _ inner) -> patternNames inner) args
    _ -> []

-- | One expression node, then its children.
expr :: Env -> Map.Map Name Can.Annotation -> Scope -> Can.Expr -> Walk ()
expr env tops scope (Can.Expr nid region value) =
  let go = expr env tops scope
      used name = Map.lookup name (_scopeLocals scope)
   in case value of
        Can.VarLocal name ->
          constrainedUse env scope nid region (E.ForValue name) (used name)
        Can.VarTopLevel _ name ->
          constrainedUse env scope nid region (E.ForValue name) (Map.lookup name tops)
        Can.VarForeign _ name annotation ->
          constrainedUse env scope nid region (E.ForValue name) (Just annotation)
        Can.VarOperator op _ _ annotation ->
          constrainedUse env scope nid region (E.ForValue op) (Just annotation)
        Can.VarCtor _ _ _ _ _ ->
          return ()
        Can.VarDebug _ _ _ ->
          return ()
        Can.VarKernel _ _ ->
          return ()
        Can.VarMethod cls param name annotation ->
          methodUse env scope nid region cls param name annotation (typeOf env nid)
        Can.Binop op home name annotation left right ->
          do
            -- A binop node's own type is the result, so the operator's type at
            -- this use is rebuilt from the operands' — which is what
            -- @Core.Lower.Expression@ does with it too.
            let actual =
                  Can.TLambda
                    (typeOf env (nodeIdOf left))
                    (Can.TLambda (typeOf env (nodeIdOf right)) (typeOf env nid))
            constrainedAt env scope nid region (E.ForValue op) annotation actual
            _ <- pure (home, name)
            go left
            go right
        Can.Array items -> mapM_ go items
        Can.Negate inner -> go inner
        Can.Lambda args body -> expr env tops (bindPatterns args scope) body
        Can.Call func args -> mapM_ go (func : args)
        Can.If branches final ->
          mapM_ (\(c, b) -> go c >> go b) branches >> go final
        Can.Let d body ->
          do
            def env tops scope d
            expr env tops (letScope d scope) body
        Can.LetRec ds body ->
          do
            let scope' = foldr letScope scope ds
            mapM_ (def env tops scope') ds
            expr env tops scope' body
        Can.LetDestruct pat scrutinized body ->
          do
            go scrutinized
            expr env tops (bindPatterns [pat] scope) body
        Can.Case scrutinee branches ->
          do
            go scrutinee
            mapM_ (\(Can.CaseBranch pat body) -> expr env tops (bindPatterns [pat] scope) body) branches
        Can.Access record _ -> go record
        Can.Update record fields ->
          go record >> mapM_ (\(Can.FieldUpdate _ v) -> go v) (Map.elems fields)
        Can.Record fields -> mapM_ go (Map.elems fields)
        _ -> return ()

-- | What a @let@ definition adds to the names a use can be constrained by.
letScope :: Can.Def -> Scope -> Scope
letScope d scope =
  case annotationOf d of
    added | Map.null added -> scope
    added -> scope {_scopeLocals = Map.union added (_scopeLocals scope)}

-- | A use of a name that may or may not have a constrained annotation.
constrainedUse ::
  Env ->
  Scope ->
  Can.NodeId ->
  A.Region ->
  E.Wanted ->
  Maybe Can.Annotation ->
  Walk ()
constrainedUse env scope nid region wanted maybeAnnotation =
  case maybeAnnotation of
    Nothing -> return ()
    Just annotation -> constrainedAt env scope nid region wanted annotation (typeOf env nid)

constrainedAt ::
  Env ->
  Scope ->
  Can.NodeId ->
  A.Region ->
  E.Wanted ->
  Can.Annotation ->
  Can.Type ->
  Walk ()
constrainedAt env scope nid region wanted (Can.Forall freeVars declared) actual =
  case Can.witnessOrder freeVars of
    [] ->
      return ()
    context ->
      let sub = match declared actual Map.empty
       in emit nid $
            Applied
              <$> traverse
                (\(var, cls) -> witnessFor env (_scopeParams scope) region wanted [] cls (under sub var))
                context

-- | A use of a class method.
--
-- The class's own constraint on the class parameter is what picks the
-- instance; the method's remaining context, which §G21.1 allows, has no
-- witness path yet and is refused rather than silently dropped.
methodUse ::
  Env ->
  Scope ->
  Can.NodeId ->
  A.Region ->
  Can.Class ->
  Name ->
  Name ->
  Can.Annotation ->
  Can.Type ->
  Walk ()
methodUse env scope nid region cls param name (Can.Forall freeVars declared) actual =
  let sub = match declared actual Map.empty
      others = [c | (v, c) <- Can.witnessOrder freeVars, (v, c) /= (param, cls)]
      wanted = E.ForMethod name
   in case others of
        extra : _ ->
          failure (E.MethodContext region name cls extra)
        [] ->
          emit nid $
            do
              witness <- witnessFor env (_scopeParams scope) region wanted [] cls (under sub param)
              case witness of
                FromParam _ _ ->
                  Right (Projected witness name)
                FromInstance home instanceName args _ ->
                  Right (Instantiated home (Name.sepBy 0x24 instanceName name) args)
