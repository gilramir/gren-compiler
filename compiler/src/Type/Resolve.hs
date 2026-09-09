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
    Answer (..),
    Substitution (..),
    Elaboration (..),
    Uses,
    Params,
    Inferred,
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
import Canonicalize.NodeId qualified as NodeId
import Control.Monad (foldM)
import Control.Monad.Trans.State.Strict (State, execState, get, gets, modify', put)
import Data.Map.Strict qualified as Map
import Data.Maybe (listToMaybe)
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
    _instanceParams :: Map.Map Can.InstanceKey [(Name, Can.Type)],
    -- | The context inferred for each unannotated definition that turned out
    -- to have one.
    _inferred :: Inferred
  }

type Uses =
  Map.Map Can.NodeId Use

type Params =
  Map.Map Can.NodeId [(Name, Can.Type)]

-- | The context an unannotated definition carries that nobody wrote
-- (@docs/m1b-classes.md@ §G33), keyed by the node id of the definition itself.
--
-- @countDown n = if n <= 0 then [] else Array.pushLast n (countDown (n - 1))@
-- is @(Num a, Ord a) => a -> Array a@, and no line of it says so. The closed
-- half of that context is the solver's, which knows @Num@; the open half is
-- this, because @Ord@ left the unifier with D130 and an open constraint is
-- discharged here or nowhere.
--
-- Keyed by the definition and not by its body, unlike '_params': an
-- 'AST.Canonical.Def' has a node id of its own, and it is the one the solver
-- recorded the definition's type at.
--
-- Each entry names every variable of that type, the unconstrained ones
-- included, because it is the 'AST.Canonical.FreeVars' the lowering quantifies
-- the definition over and @Compile.withContexts@ publishes.
type Inferred =
  Map.Map Can.NodeId Can.FreeVars

-- | What one run of the elaborator answers.
data Answer
  = -- | Every use elaborated.
    Answered Elaboration
  | -- | A definition that takes no arguments needs a witness, and a value may
    -- not quietly become a function (§G33.2). The variables named here take
    -- `classes.md` §0's default instead, and the elaborator is asked again
    -- against the types that substitution produces.
    Defaulted [Substitution]
  | -- | Uses that cannot be elaborated at all.
    Refused (NE.List E.Error)

-- | §0's rule applied to one definition's variables.
--
-- __Scoped to the definition, because a type variable's name is not a
-- module-wide identity.__ Each top-level annotation is zonked against a name
-- state of its own, and a signature's variables are named by the author, so two
-- unrelated definitions in one module can both have a variable called @number@
-- or @a@ — and substituting by name across the module would close a variable
-- that has nothing to do with this one. The variable a definition quantifies
-- occurs in that definition's own nodes and nowhere else (every use elsewhere
-- is a copy), so those nodes are the whole of where the substitution belongs.
data Substitution = Substitution
  { -- | The published annotation to close as well, when the definition is a
    -- top-level one and therefore has one.
    _sTopLevel :: Maybe Name,
    -- | The nodes whose recorded types the substitution applies to.
    _sNodes :: [Can.NodeId],
    _sTypes :: Map.Map Name Can.Type
  }

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
    _envTypes :: Map.Map Can.NodeId Can.Type,
    -- | What `classes.md` §0 makes of each constrained type variable, from the
    -- solver. A variable no candidate admits has no entry.
    _envDefaults :: Map.Map Name Can.Type
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
    -- | @let@-bound definitions with an annotation, written or inferred, so
    -- that a use of one knows what it needs. A name bound by a pattern removes
    -- its entry, because it is then a different name.
    _scopeLocals :: Map.Map Name Can.Annotation,
    -- | The unannotated definitions this node is inside, __outermost first__.
    -- This is what a constraint with nowhere to go is attributed to; see
    -- 'refuse'.
    _scopeInferable :: [Quantifier]
  }

-- | An unannotated definition a constraint at a type variable can belong to.
data Quantifier = Quantifier
  { _qDef :: Can.NodeId,
    -- | Whether it takes arguments. One that does not is a __value__, and a
    -- value may not grow a witness parameter (§G33.2).
    _qFunction :: Bool,
    -- | The type variables its type mentions.
    _qVars :: [Name],
    -- | The definition itself, for the nodes a 'Substitution' is scoped to.
    _qSource :: Can.Def,
    -- | Its name, when it is a top-level declaration.
    _qTopLevel :: Maybe Name
  }

-- | What one pass over the module produced.
data Progress = Progress
  { _pUses :: Uses,
    _pParams :: Params,
    _pErrors :: [E.Error],
    -- | The witness-parameter counter; see 'freshNames'.
    _pFresh :: !Int,
    _pInferred :: Inferred,
    -- | Whether this pass attributed a constraint no earlier pass had.
    _pLearned :: !Bool,
    -- | The variables §0's rule has to close before this module can be
    -- elaborated at all, one entry per definition. Not an error and not
    -- something a pass can act on: the types have to change, which is
    -- 'Compile''s to do.
    _pDefaults :: Map.Map Can.NodeId Substitution
  }

type Walk a =
  State Progress a

emit :: Env -> Scope -> Can.NodeId -> Either E.Error Use -> Walk ()
emit env scope nid answer =
  case answer of
    Right use -> modify' $ \p -> p {_pUses = Map.insert nid use (_pUses p)}
    Left err -> refuse env scope err

failure :: E.Error -> Walk ()
failure err =
  modify' $ \p -> p {_pErrors = _pErrors p ++ [err]}

-- | An error, or a constraint that was nobody's until now.
--
-- 'Reporting.Error.Instance.NotConstrained' says a constraint sits at a type
-- variable the definition does not say has an instance. When the definition is
-- /unannotated/ that is not a fact about the program: the variable's
-- quantifier is an enclosing definition that wrote no signature, and the
-- constraint is that definition's inferred context. Attributing it rather than
-- reporting it is what 'run' iterates on.
--
-- __Outermost, not innermost.__ A variable that is in an inner definition's
-- type and in an outer one's is the /outer/ one's — the inner is monomorphic
-- in it — so attributing it there gives the inner definition no witness
-- parameter it does not need, and the inner body finds the outer's parameter
-- in scope already.
refuse :: Env -> Scope -> E.Error -> Walk ()
refuse env scope err =
  case err of
    E.NotConstrained _ _ cls var _
      | Just q <- quantifier scope var ->
          if _qFunction q
            then attribute (_qDef q) (_qVars q) var cls
            else case Map.lookup var (_envDefaults env) of
              Just tipe -> close q var tipe
              -- §0's ambiguity error, which nothing produces yet: the variable
              -- is constrained by an open class alone, so there is no candidate
              -- to pick. What is said instead is true and the fix it names
              -- works — write the context down.
              Nothing -> failure err
    _ ->
      failure err

-- | Record that one of a definition's variables takes §0's default.
close :: Quantifier -> Name -> Can.Type -> Walk ()
close q var tipe =
  modify' $ \p ->
    let one =
          Substitution
            (_qTopLevel q)
            (map NodeId.nodeId (NodeId.defNodes (_qSource q)))
            (Map.singleton var tipe)
        merge new old = old {_sTypes = Map.union (_sTypes new) (_sTypes old)}
     in p {_pDefaults = Map.insertWith merge (_qDef q) one (_pDefaults p)}

-- | Which enclosing definition, if any, quantifies a type variable.
--
-- __A name and not an identity, and that is as good as this gets.__ Two
-- variables in one module can share a name — a use of @abs : (Num a, Ord a) =>
-- a -> a@ makes a flexible variable called @a@, and any signature may call one
-- of its own variables @a@ too ('Type.Type.keepName' says why nothing renames
-- them). So this asks the question the rest of the elaborator asks: within the
-- definitions this node is nested in, which one's type mentions the name? An
-- enclosing /signature/ is deliberately not consulted. It would be the better
-- answer when the names really are the same variable, and it is the wrong
-- answer far more often, because @a@ is the commonest variable name there is.
-- The cost of not consulting it is where the error is reported, not whether:
-- a constraint attributed to an inner definition still has to be discharged by
-- whatever calls it, and nothing outside can.
quantifier :: Scope -> Name -> Maybe Quantifier
quantifier scope var =
  listToMaybe [q | q <- _scopeInferable scope, var `elem` _qVars q]

-- | Add one class to a definition's inferred context.
--
-- Idempotent, and 'run' terminates because of it: a context only ever gains a
-- class it did not have, and a definition's type has finitely many variables.
attribute :: Can.NodeId -> [Name] -> Name -> Can.Class -> Walk ()
attribute nid vars var cls =
  modify' $ \p ->
    let context = Map.findWithDefault (Map.fromList [(v, []) | v <- vars]) nid (_pInferred p)
        already = Map.findWithDefault [] var context
     in if cls `elem` already
          then p
          else
            p
              { _pInferred = Map.insert nid (Map.insert var (cls : already) context) (_pInferred p),
                _pLearned = True
              }

-- | Every type variable a type mentions.
typeVars :: Can.Type -> [Name]
typeVars tipe =
  case tipe of
    Can.TVar name -> [name]
    Can.TLambda arg result -> typeVars arg ++ typeVars result
    Can.TType _ _ args -> concatMap typeVars args
    Can.TRecord fields ext ->
      maybe [] (: []) ext ++ concatMap (\(Can.FieldType _ t) -> typeVars t) (Map.elems fields)
    Can.TAlias _ _ args aliased -> typeVars (Type.dealias args aliased)

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
    p <- get
    let n = _pFresh p
    put p {_pFresh = n + count}
    return [Name.fromChars ("$w" ++ show i) | i <- [n .. n + count - 1]]

-- | Elaborate a module, or report every use that cannot be.
--
-- Every one of them, rather than the first: they are independent questions
-- about independent call sites, and a person fixing one wants to see the rest.
--
-- __It is a fixpoint, because a context can be inferred__ (§G33). Each pass
-- answers every use against the contexts the pass before it knew, and
-- attributes what it cannot answer ('refuse') instead of reporting it.
-- Contexts only grow and there are finitely many of them, so this terminates;
-- and __a pass that learned nothing is a pass whose errors are real__, which
-- is why reporting is not a separate mode. A caller sees a definition's
-- inferred context one pass after the definition does, so recursion and mutual
-- recursion need no special case: they are the passes it takes.
run :: Env -> Can.Module -> Answer
run env modul =
  let final = converge env modul Map.empty
      ofInstance i =
        let context = Can._ih_context (Can._in_head i)
         in witnessParams env (localNames (length (Can.witnessOrder context))) context
   in if not (Map.null (_pDefaults final))
        then -- Before the errors, and they are ignored: an error at a variable
        -- that is about to become @Int@ is an error about a type the module
        -- does not have yet.
          Defaulted (Map.elems (_pDefaults final))
        else case _pErrors final of
          [] ->
            Answered $
              Elaboration
                (_pUses final)
                (_pParams final)
                (Map.map ofInstance (Can._instances modul))
                (_pInferred final)
          err : rest -> Refused (NE.List err rest)

converge :: Env -> Can.Module -> Inferred -> Progress
converge env modul inferred =
  let pass = onePass env modul inferred
   in if _pLearned pass
        then converge env modul (_pInferred pass)
        else pass

onePass :: Env -> Can.Module -> Inferred -> Progress
onePass env modul inferred =
  let scope = Scope Map.empty Map.empty []
      tops = topLevel env inferred (Can._decls modul)
      walk =
        do
          decls env tops scope (Can._decls modul)
          mapM_ (instanceMethods env tops scope) (Map.elems (Can._instances modul))
   in execState walk (Progress Map.empty Map.empty [] 0 inferred False Map.empty)

-- | Witness parameter names for a binding whose body names nothing else local.
localNames :: Int -> [Name]
localNames count =
  [Name.fromChars ("$w" ++ show i) | i <- [0 .. count - 1]]

-- | The module's own top-level definitions that carry a context, which is what
-- a 'Can.VarTopLevel' names and does not carry.
topLevel :: Env -> Inferred -> Can.Decls -> Map.Map Name Can.Annotation
topLevel env inferred ds =
  case ds of
    Can.Declare d rest -> Map.union (annotationOf env inferred d) (topLevel env inferred rest)
    Can.DeclareRec d others rest ->
      Map.unions (map (annotationOf env inferred) (d : others) ++ [topLevel env inferred rest])
    Can.SaveTheEnvironment -> Map.empty

-- | What a use of a definition's name has to know: its type, and the context
-- it carries.
--
-- An unannotated definition has one from the pass this map is built for, and
-- its type is the one the solver recorded at the definition's own node — the
-- same type a 'Can.TypedDef' rebuilds from its arguments and its result, seen
-- from the other side.
annotationOf :: Env -> Inferred -> Can.Def -> Map.Map Name Can.Annotation
annotationOf env inferred d =
  case d of
    Can.Def nid (A.At _ name) _ _ ->
      case Map.lookup nid inferred of
        Nothing -> Map.empty
        Just context -> Map.singleton name (Can.Forall context (typeOf env nid))
    Can.TypedDef (A.At _ name) freeVars args _ result ->
      Map.singleton name (Can.Forall freeVars (foldr (Can.TLambda . snd) result args))

decls :: Env -> Map.Map Name Can.Annotation -> Scope -> Can.Decls -> Walk ()
decls env tops scope ds =
  case ds of
    Can.Declare d rest ->
      topDef env tops scope d >> decls env tops scope rest
    Can.DeclareRec d others rest ->
      mapM_ (topDef env tops scope) (d : others) >> decls env tops scope rest
    Can.SaveTheEnvironment ->
      return ()

-- | A top-level definition, which is one whose annotation is published.
topDef :: Env -> Map.Map Name Can.Annotation -> Scope -> Can.Def -> Walk ()
topDef env tops scope d =
  case d of
    Can.Def _ (A.At _ name) _ _ -> defWith (Just name) env tops scope d
    Can.TypedDef {} -> def env tops scope d

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
--
-- An unannotated one binds the parameters of the context inferred for it so
-- far, and adds itself to the definitions a constraint with nowhere else to go
-- can be attributed to. An annotated one binds what it wrote and adds nothing:
-- a signature says what a definition's callers supply, so a constraint at one
-- of its own variables that it does not name is the error it has always been.
def :: Env -> Map.Map Name Can.Annotation -> Scope -> Can.Def -> Walk ()
def = defWith Nothing

defWith :: Maybe Name -> Env -> Map.Map Name Can.Annotation -> Scope -> Can.Def -> Walk ()
defWith published env tops scope d =
  case d of
    Can.Def nid _ args body ->
      do
        context <- gets (Map.findWithDefault Map.empty nid . _pInferred)
        scope' <- bindWitnesses env context (nodeIdOf body) scope
        let quantifies = Quantifier nid (not (null args)) (typeVars (typeOf env nid)) d published
        let inferable = _scopeInferable scope ++ [quantifies]
        expr env tops (bindPatterns args scope' {_scopeInferable = inferable}) body
    Can.TypedDef _ freeVars args body _ ->
      do
        scope' <- bindWitnesses env freeVars (nodeIdOf body) scope
        expr env tops (bindPatterns (map fst args) scope') body

-- | Give a definition's context fresh witness parameters, record them for the
-- lowering, and put them in scope for the body.
bindWitnesses :: Env -> Can.FreeVars -> Can.NodeId -> Scope -> Walk Scope
bindWitnesses env context bodyNid scope =
  do
    let order = Can.witnessOrder context
    names <- freshNames (length order)
    modify' $ \p ->
      p {_pParams = Map.insert bodyNid (witnessParams env names context) (_pParams p)}
    return $
      scope
        { _scopeParams =
            Map.union
              (Map.fromList [((cls, var), name) | ((var, cls), name) <- zip order names])
              (_scopeParams scope)
        }

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
        Can.Binop op target annotation left right ->
          do
            -- A binop node's own type is the result, so the operator's type at
            -- this use is rebuilt from the operands' — which is what
            -- @Core.Lower.Expression@ does with it too.
            let actual =
                  Can.TLambda
                    (typeOf env (nodeIdOf left))
                    (Can.TLambda (typeOf env (nodeIdOf right)) (typeOf env nid))
            case target of
              Can.OpValue _ _ ->
                constrainedAt env scope nid region (E.ForValue op) annotation actual
              Can.OpMethod cls param name ->
                -- The same question a written method name asks, asked of the
                -- operator's type rather than of the node's (D138, §G35).
                methodUse env scope nid region cls param name annotation actual
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
            scope' <- letScope env d scope
            expr env tops scope' body
        Can.LetRec ds body ->
          do
            scope' <- foldM (flip (letScope env)) scope ds
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
--
-- Read out of the walk's own state rather than out of the pass's, so that an
-- unannotated definition and the body that follows it agree within one pass
-- about what was just inferred for it.
letScope :: Env -> Can.Def -> Scope -> Walk Scope
letScope env d scope =
  do
    inferred <- gets _pInferred
    return $ case annotationOf env inferred d of
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
       in emit env scope nid $
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
          emit env scope nid $
            do
              witness <- witnessFor env (_scopeParams scope) region wanted [] cls (under sub param)
              case witness of
                FromParam _ _ ->
                  Right (Projected witness name)
                FromInstance home instanceName args _ ->
                  Right (Instantiated home (Name.sepBy 0x24 instanceName name) args)
