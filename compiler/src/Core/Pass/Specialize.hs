{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | Specialization: a constrained definition becomes one copy per witness it is
-- ever handed (@docs/core.md@ C2, @docs/m1b-classes.md@ §G27, R1).
--
-- §G26 made a witness a value: a record of a class's methods, built by the
-- binding D125 gives every instance, passed to a definition through
-- 'Core.AST.EWitLam' and 'Core.AST.EWitApp'. That is a correct program and a
-- slow one — every constrained call goes through a record projection. This pass
-- is the other half of verb 6, and it is the ordinary dictionary specialization
-- every such compiler ends up with:
--
-- > same : Eq a => a -> a -> Bool          same$s0 = \x y -> (…Basics.Eq$Int…)
-- > same = \$w0 x y -> …$w0.eq…      ⟹     same$s1 = \x y -> (…String.Eq$String…)
-- > same $wEqInt 1 2                       same$s0 1 2
--
-- __What it erases is witnesses, not types__ (D126). C2 marks four nodes for
-- this pass and only two of them have a producer: "Core.Lower.Expression" says
-- in its header that it emits no 'Core.AST.ETyLam' or 'Core.AST.ETyApp', and
-- nothing else does either — outside @tests\/Core\/WireSpec.hs@ the two nodes do
-- not occur. Monomorphizing every polymorphic definition, which is what R1
-- describes, would mean /first building/ type abstraction at every generalized
-- definition and type application at every use site in order to erase it again
-- in the same pass. R1 calls the extent a code-size knob rather than a semantic
-- choice, so the knob is set where there is something to turn: the definitions a
-- witness rides on. Type-level monomorphization stays available and its
-- precondition is a producer for those two nodes.
--
-- __The pass is allowed to give up__ (§G27.3). A site it does not specialize
-- keeps its 'Core.AST.EWitApp' and runs, because the witness path is a correct
-- one and not a fallback invented here — which is the whole reason §G26 built
-- witnesses first. So the depth cap below is a budget rather than a
-- correctness condition, and a shape this pass does not recognize costs speed
-- and not meaning.
--
-- __Where the copies live__: in the module that defines the generic binding, not
-- at the use site, so one instantiation is one binding however many modules ask
-- for it. The generic binding itself is left alone; nothing refers to it once
-- its uses are rewritten, and 'Core.Program.link' drops what nothing reaches.
module Core.Pass.Specialize
  ( run,
  )
where

import Core.AST qualified as Core
import Core.Order qualified as Order
import Core.Refs qualified as Refs
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set (Set)
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName

-- WHAT A WITNESS IS, TO THIS PASS

-- | A witness that names its instances all the way down.
--
-- A witness expression is built by @Core.Lower.Expression.witness@ out of
-- exactly two shapes: an 'Core.AST.EGlobal' naming an instance's table, and an
-- 'Core.AST.EWitApp' of one to witnesses for that instance's own context. The
-- third shape it can have is an 'Core.AST.EVar' — the enclosing definition's
-- witness parameter — and that is precisely the case this pass cannot resolve
-- yet, because the parameter has no value until the enclosing definition is
-- itself specialized.
--
-- So reading an expression into this type /is/ the test for "closed", and
-- failing to read one is not an error: it is a site that waits for its caller.
data Wit = Wit !Core.QualName ![Wit]
  deriving (Eq, Ord, Show)

-- | A generic binding applied to a full row of witnesses. This is what gets a
-- copy, and it is the copy's name.
type Key = (Core.QualName, [Wit])

-- | How deep a witness tree may be before the pass leaves the site alone.
--
-- A witness for @Eq (Array (Array Int))@ is three deep, so real programs are
-- nowhere near this. What the cap is for is polymorphic recursion — a
-- constrained definition that calls itself at a /larger/ witness — where the
-- demand set is infinite and no whole-program pass can enumerate it. Giving up
-- there leaves a working program, per the header.
depthCap :: Int
depthCap = 16

depth :: Wit -> Int
depth (Wit _ args) = 1 + maximum (0 : map depth args)

-- THE PASS

run :: Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
run cores =
  let gens = generics cores
   in if Map.null gens
        then cores
        else
          let keys = demand gens cores
              names = assign keys
              tys = bindingTypes cores
              added =
                Map.fromListWith
                  (++)
                  [ (Core._qnHome name, [copy gens tys names key])
                  | key@(name, _) <- Set.toAscList keys
                  ]
              collapsed = Map.mapWithKey (module_ gens names added) cores
              tbl = tables collapsed
           in if Map.null tbl
                then collapsed
                else Map.map (onExprs (project tbl)) collapsed

-- | Every top-level binding that takes witnesses, by name.
--
-- Both producers of 'Core.AST.EWitLam' land here: a constrained definition
-- (@Core.Lower.Expression.witnessLam@) and an instance whose head has a context
-- (@Core.Lower.Module.witnessBind@ — the @Eq a => Eq (Array a)@ case). They are
-- the same thing to this pass, which is D125 doing its job: an instance's table
-- is an ordinary binding, so specializing it needs no second rule.
generics :: Map ModuleName.Canonical Core.Module -> Map Core.QualName ([Core.Binder], Core.Expr, Core.Type)
generics cores =
  Map.fromList
    [ (Core.QualName home (Core._binderName binder), (binders, body, Core._binderType binder))
    | (home, modul) <- Map.toAscList cores,
      Core.Bind binder value <- Core._moduleDefs modul,
      Core.EWitLam binders body <- [Core._exprValue value]
    ]

-- | Every top-level binding's declared type, by name.
--
-- What it is for: a witness is an instance's table, and that table's binding
-- carries the /concrete/ type of the instance — @{ compare : Int -> Int -> Order }@
-- for @Ord Int@. Matching it against the generic witness parameter's type is
-- how a copy learns what its key fixed, which is the substitution 'copy' needs
-- and the only place the answer is written down.
bindingTypes :: Map ModuleName.Canonical Core.Module -> Map Core.QualName Core.Type
bindingTypes cores =
  Map.fromList
    [ (Core.QualName home (Core._binderName binder), Core._binderType binder)
    | (home, modul) <- Map.toAscList cores,
      Core.Bind binder _ <- Core._moduleDefs modul
    ]

-- | Every instantiation the program asks for, to a fixed point.
--
-- The seed is what the modules say; each key's own body is then substituted and
-- read for the keys /it/ asks for, which is how @Eq (Array Int)@ reaches
-- @Eq Int@ and how a recursive constrained definition reaches itself. A key
-- already in the set is not expanded twice, so a self-recursive definition
-- terminates on the first repeat and only 'depthCap' stands between the pass
-- and polymorphic recursion.
demand :: Map Core.QualName ([Core.Binder], Core.Expr, Core.Type) -> Map ModuleName.Canonical Core.Module -> Set Key
demand gens cores =
  go Set.empty (concatMap (sites gens) (concatMap exprsOf (Map.elems cores)))
  where
    go seen [] = seen
    go seen (key : rest)
      | key `Set.member` seen = go seen rest
      | otherwise =
          let seen' = Set.insert key seen
           in go seen' (sites gens (substituted gens key) ++ rest)

-- | The keys one expression asks for, including the ones nested inside a
-- witness: a witness for @Eq (Array Int)@ is the @Eq (Array a)@ table applied to
-- one for @Eq Int@, and that application is an instantiation like any other.
sites :: Map Core.QualName ([Core.Binder], Core.Expr, Core.Type) -> Core.Expr -> [Key]
sites gens = collect
  where
    collect e =
      case Core._exprValue e of
        Core.EWitApp fn args
          | Just (name, wits) <- keyOf gens fn args -> (name, wits) : concatMap fromWit wits
        _ -> children_ collect e

    fromWit (Wit name args)
      | null args = []
      | otherwise = (name, args) : concatMap fromWit args

-- | The key an application makes, when it makes one.
keyOf :: Map Core.QualName a -> Core.Expr -> [Core.Expr] -> Maybe Key
keyOf gens fn args =
  case Core._exprValue fn of
    Core.EGlobal name
      | Map.member name gens ->
          do
            wits <- traverse witOf args
            if any ((> depthCap) . depth) wits then Nothing else Just (name, wits)
    _ -> Nothing

-- | Read a witness expression, or fail because it is a parameter.
witOf :: Core.Expr -> Maybe Wit
witOf e =
  case Core._exprValue e of
    Core.EGlobal name -> Just (Wit name [])
    Core.EWitApp fn args ->
      case Core._exprValue fn of
        Core.EGlobal name -> Wit name <$> traverse witOf args
        _ -> Nothing
    _ -> Nothing

-- NAMES

-- | One name per instantiation, assigned from the sorted key set.
--
-- The suffix is positional over @Set.toAscList@ rather than a counter over the
-- traversal, so the name a copy gets depends on /which/ instantiations a program
-- needs and not on the order they were found in — the same discipline C6 asks of
-- every other generated name, and one less thing for a second frontend to
-- reproduce. @$@ cannot appear in a Gren name, so no copy can collide with
-- something written.
assign :: Set Key -> Map Key Name
assign keys =
  Map.fromList
    [ (key, suffixed (Core._qnName name) i)
    | (name, group) <- Map.toAscList grouped,
      (i, key) <- zip [0 :: Int ..] group
    ]
  where
    grouped =
      Map.map List.sort (Map.fromListWith (++) [(name, [key]) | key@(name, _) <- Set.toList keys])
    suffixed base i = Name.fromChars (Name.toChars base ++ "$s" ++ show i)

nameOf :: Map Key Name -> Key -> Core.QualName
nameOf names key@(Core.QualName home _, _) =
  case Map.lookup key names of
    Just name -> Core.QualName home name
    Nothing -> fst key

-- BUILDING A COPY

-- | A generic binding's body with its witness parameters replaced by the
-- witnesses this key names — still in terms of the /generic/ instance tables,
-- because 'rewrite' is what collapses those and it runs once, over this body
-- and the modules alike.
substituted :: Map Core.QualName ([Core.Binder], Core.Expr, Core.Type) -> Key -> Core.Expr
substituted gens (name, wits) =
  -- Total: 'keyOf' only builds a key for a name it found in @gens@.
  let (binders, body, _) = gens Map.! name
   in subst (Map.fromList (zip (map Core._binderName binders) (zipWith canonical binders wits))) body

-- | A witness, written back as the expression it was read from. The type and
-- span are the parameter's, so a copy is a function of its key alone.
canonical :: Core.Binder -> Wit -> Core.Expr
canonical binder = expand
  where
    tipe = Core._binderType binder
    sp = Core._binderSpan binder
    expand (Wit name args) =
      let global = Core.Expr (Core.EGlobal name) tipe sp
       in case args of
            [] -> global
            _ -> Core.Expr (Core.EWitApp global (map expand args)) tipe sp

copy :: Map Core.QualName ([Core.Binder], Core.Expr, Core.Type) -> Map Core.QualName Core.Type -> Map Key Name -> Key -> Core.Bind
copy gens tys names key@(name, _) =
  let sub = fixed gens tys key
      body = retype (substituteT sub) (rewrite gens names (substituted gens key))
      (binders, _, declared) = gens Map.! name
      sp = maybe (Core.spanOf body) Core._binderSpan (Maybe.listToMaybe binders)
   in Core.Bind (Core.Binder (Core._qnName (nameOf names key)) (discharged sub declared) sp) body

-- | What a key fixed: one type per variable its witnesses are about.
--
-- Read off the witnesses rather than off the constraint list, because a witness
-- names an instance and an instance's table binding carries the concrete type.
-- A witness that is itself an application — @Ord (Array Int)@ is the
-- @Ord (Array a)@ table applied to @Ord Int@ — is resolved the same way,
-- recursively.
fixed :: Map Core.QualName ([Core.Binder], Core.Expr, Core.Type) -> Map Core.QualName Core.Type -> Key -> Map Name Core.Type
fixed gens tys (name, wits) =
  let (binders, _, _) = gens Map.! name
   in Map.unions
        [ matchT (Core._binderType binder) actual
        | (binder, wit) <- zip binders wits,
          Just actual <- [witType gens tys wit]
        ]

-- | The type of a witness expression: the instance table's own type, with the
-- context it was applied to substituted in.
witType :: Map Core.QualName ([Core.Binder], Core.Expr, Core.Type) -> Map Core.QualName Core.Type -> Wit -> Maybe Core.Type
witType gens tys (Wit name args) =
  case args of
    [] ->
      Map.lookup name tys
    _ ->
      do
        (binders, _, _) <- Map.lookup name gens
        declared <- Map.lookup name tys
        let sub =
              Map.unions
                [ matchT (Core._binderType binder) actual
                | (binder, arg) <- zip binders args,
                  Just actual <- [witType gens tys arg]
                ]
        return (substituteT sub declared)

-- | The substitution that turns one type into another, where it can.
--
-- First-order and total, exactly as @Type.Resolve.match@ is and for the same
-- reason: this is reading an answer the solver already gave, not checking one.
matchT :: Core.Type -> Core.Type -> Map Name Core.Type
matchT declared actual =
  case (declared, actual) of
    (Core.TVar v, _) -> Map.singleton v actual
    (Core.TCon _ as, Core.TCon _ bs) -> Map.unions (zipWith matchT as bs)
    (Core.TFun as a, Core.TFun bs b) -> Map.unions (matchT a b : zipWith matchT as bs)
    (Core.TRecord as _, Core.TRecord bs _) ->
      Map.unions [matchT a b | (f, a) <- as, Just b <- [lookup f bs]]
    (Core.TForall _ _ a, Core.TForall _ _ b) -> matchT a b
    _ -> Map.empty

substituteT :: Map Name Core.Type -> Core.Type -> Core.Type
substituteT sub tipe =
  case tipe of
    Core.TVar n -> Map.findWithDefault tipe n sub
    Core.TCon q args -> Core.TCon q (map (substituteT sub) args)
    Core.TFun args result -> Core.TFun (map (substituteT sub) args) (substituteT sub result)
    Core.TRecord fields row -> Core.TRecord [(f, substituteT sub t) | (f, t) <- fields] row
    Core.TForall vars constraints body ->
      let inner = foldr Map.delete sub vars
       in Core.TForall
            vars
            [Core.CClass c (substituteT inner t) | Core.CClass c t <- constraints]
            (substituteT inner body)

-- | A copy's type is the generic one with its constraints discharged and the
-- variables they were about replaced by what the key fixed.
--
-- The quantifier has to be taken off first: 'substituteT' respects binding, and
-- the variables being substituted are the ones this @forall@ binds. What is
-- left quantified is whatever the instantiation did not fix, which is an
-- ordinary polymorphic argument and stays polymorphic.
--
-- §G26.1's open item was that this said only @discharged@ and left the variable
-- quantified: a JS backend does not read a binder's type, and the Core -> C
-- spike does — it gave a specialized copy a boxed parameter where the call site
-- passed an @int32_t@ (§G29.8).
discharged :: Map Name Core.Type -> Core.Type -> Core.Type
discharged sub tipe =
  case tipe of
    Core.TForall vars _ body ->
      let body' = substituteT sub body
          left = [v | v <- vars, not (Map.member v sub)]
       in if null left then body' else Core.TForall left [] body'
    _ -> substituteT sub tipe

-- | Apply a type function to every type an expression carries: its own, and
-- every binder inside it.
--
-- 'childrenA' rebuilds the children; the case below is only the constructors
-- that bind a name, which is where a type lives that is not some node's own.
retype :: (Core.Type -> Core.Type) -> Core.Expr -> Core.Expr
retype f = go
  where
    go e =
      let rebuilt = runIdentity (childrenA (Identity . go) e)
       in Core.Expr (value (Core._exprValue rebuilt)) (f (Core.typeOf e)) (Core.spanOf e)

    value v =
      case v of
        Core.ELam bs body -> Core.ELam (map binder bs) body
        Core.ELet bs body -> Core.ELet (map bind bs) body
        Core.ELetRec bs body -> Core.ELetRec (map bind bs) body
        Core.EJoin bs body -> Core.EJoin (map bind bs) body
        Core.EWitLam bs body -> Core.EWitLam (map binder bs) body
        Core.ECase scrut alts fallback -> Core.ECase scrut (map alt alts) fallback
        other -> other

    binder b = b {Core._binderType = f (Core._binderType b)}
    bind (Core.Bind b v) = Core.Bind (binder b) v
    alt (Core.Alt p b) = Core.Alt (pattern_ p) b
    pattern_ p =
      case p of
        Core.PVar b -> Core.PVar (binder b)
        Core.PCtor q t ps -> Core.PCtor q t (map pattern_ ps)
        Core.PRecord fs -> Core.PRecord [(field, pattern_ q) | (field, q) <- fs]
        Core.PArray ps tl -> Core.PArray (map pattern_ ps) (fmap binder tl)
        Core.PAs b q -> Core.PAs (binder b) (pattern_ q)
        other -> other

-- REWRITING

-- | Replace every application of a generic binding to a closed witness row with
-- the copy's name.
--
-- The arguments are not walked: a witness row is described entirely by the key,
-- and the copies its own nesting needs were registered by 'sites'. Everything
-- else recurses.
rewrite :: Map Core.QualName ([Core.Binder], Core.Expr, Core.Type) -> Map Key Name -> Core.Expr -> Core.Expr
rewrite gens names = go
  where
    go e =
      case Core._exprValue e of
        Core.EWitApp fn args
          | Just key <- keyOf gens fn args,
            Map.member key names ->
              Core.Expr (Core.EGlobal (nameOf names key)) (Core.typeOf e) (Core.spanOf e)
        _ -> runIdentity (childrenA (Identity . go) e)

module_ ::
  Map Core.QualName ([Core.Binder], Core.Expr, Core.Type) ->
  Map Key Name ->
  Map ModuleName.Canonical [Core.Bind] ->
  ModuleName.Canonical ->
  Core.Module ->
  Core.Module
module_ gens names added home modul =
  let touched = onExprs (rewrite gens names) modul
      new = Map.findWithDefault [] home added
   in if null new
        then touched
        else
          let ordered = reorder home (Core._moduleDefs touched ++ new)
           in touched
                { Core._moduleDefs = concat ordered,
                  Core._moduleDefsRec =
                    [ map (Core.QualName home . Core._binderName . Core._bindBinder) g
                    | g <- ordered,
                      length g > 1
                    ]
                }

-- FOLDING THE PROJECTION AWAY

-- | The constant records a projection can be read off, by name.
--
-- Every instance's method table is one — D125 makes it a record whose fields are
-- 'Core.AST.EGlobal's naming the instance's method bindings — and after the
-- collapse above a specialized table is one too. The condition is stated
-- structurally rather than by asking which bindings are instance tables: a field
-- that is a /name/ can replace the projection that reads it without duplicating
-- any work, and that is the whole of what makes the rewrite safe.
tables :: Map ModuleName.Canonical Core.Module -> Map Core.QualName [(Core.Field, Core.Expr)]
tables cores =
  Map.fromList
    [ (Core.QualName home (Core._binderName binder), fields)
    | (home, modul) <- Map.toAscList cores,
      Core.Bind binder value <- Core._moduleDefs modul,
      Core.ERecord fields <- [Core._exprValue value],
      all (isName . snd) fields
    ]
  where
    isName e = case Core._exprValue e of
      Core.EGlobal _ -> True
      _ -> False

-- | @table.method@ becomes @method@.
--
-- This is the second half of erasing a witness and the half that pays. Dropping
-- the parameter alone leaves every call reading a field out of a record it now
-- knows the identity of — which was the cost the pass exists to remove — so a
-- specialization that stopped at the parameter would have made a copy per
-- instance and bought nothing.
project :: Map Core.QualName [(Core.Field, Core.Expr)] -> Core.Expr -> Core.Expr
project tbl = go
  where
    go e =
      case Core._exprValue e of
        Core.EAccess base field
          | Core.EGlobal name <- Core._exprValue base,
            Just fields <- Map.lookup name tbl,
            Just found <- List.lookup field fields ->
              Core.Expr (Core._exprValue found) (Core.typeOf e) (Core.spanOf e)
        _ -> runIdentity (childrenA (Identity . go) e)

-- | One rule for "every expression a module holds", so 'demand', the collapse
-- and the fold cannot disagree about the set. 'exprsOf' is its read-only twin.
onExprs :: (Core.Expr -> Core.Expr) -> Core.Module -> Core.Module
onExprs f modul =
  modul
    { Core._moduleDefs = [Core.Bind b (f v) | Core.Bind b v <- Core._moduleDefs modul],
      Core._modulePorts = map (port f) (Core._modulePorts modul),
      Core._moduleMain = fmap (main_ f) (Core._moduleMain modul)
    }

-- | C14's order, recomputed, because the module gained bindings.
--
-- "Core.Order" is the only implementation of that sentence and this is a third
-- caller of it rather than a second rule. Only a module that gained a copy is
-- reordered; one that did not is already in the order it was lowered in.
reorder :: ModuleName.Canonical -> [Core.Bind] -> [[Core.Bind]]
reorder home defs =
  let byName = Map.fromList [(Core._binderName (Core._bindBinder b), b) | b <- defs]
      deps =
        Map.fromList
          [ ( Core._binderName (Core._bindBinder b),
              Set.fromList
                [ n
                | Core.QualName h n <- Set.toList (Refs._refGlobals (Refs.refsIn (Core._bindValue b))),
                  h == home
                ]
            )
          | b <- defs
          ]
   in [ [byName Map.! n | n <- group]
      | group <- Order.groups (Map.keys byName) deps
      ]

port :: (Core.Expr -> Core.Expr) -> Core.Port -> Core.Port
port f p = p {Core._portFlow = flow (Core._portFlow p)}
  where
    flow fl =
      case fl of
        Core.PortOut c -> Core.PortOut (conv c)
        Core.PortIn c -> Core.PortIn (conv c)
        Core.PortTask i o -> Core.PortTask (fmap conv i) (conv o)
    conv c = c {Core._convCode = f (Core._convCode c)}

main_ :: (Core.Expr -> Core.Expr) -> Core.Main -> Core.Main
main_ f m =
  case m of
    Core.MainProgram c -> Core.MainProgram (c {Core._convCode = f (Core._convCode c)})
    _ -> m

-- | Every expression a module holds, for the two walks that have to agree about
-- the set: 'demand' reads it and 'module_' rewrites it.
--
-- An instance declaration's methods are not here. D123 makes each of them an
-- 'Core.AST.EGlobal' naming a binding in @_moduleDefs@, so the binding is walked
-- and the reference has nothing in it to rewrite.
exprsOf :: Core.Module -> [Core.Expr]
exprsOf modul =
  map Core._bindValue (Core._moduleDefs modul)
    ++ concatMap (converters . Core._portFlow) (Core._modulePorts modul)
    ++ [Core._convCode c | Just (Core.MainProgram c) <- [Core._moduleMain modul]]
  where
    converters fl =
      case fl of
        Core.PortOut c -> [Core._convCode c]
        Core.PortIn c -> [Core._convCode c]
        Core.PortTask i o -> map Core._convCode (maybe [] pure i ++ [o])

-- SUBSTITUTION

-- | Replace witness parameters by the witnesses a call site handed over.
--
-- Only 'Core.AST.EWitLam' can shadow one: a witness parameter is named @$wN@ by
-- @Type.Resolve.localNames@ and @$@ cannot appear in a Gren name, so no pattern,
-- lambda or @let@ binds one. Capture is impossible for the same reason a
-- substitution is safe at all here — a witness that this pass substitutes is
-- closed, so it has no free local to capture.
subst :: Map Name Core.Expr -> Core.Expr -> Core.Expr
subst env e
  | Map.null env = e
  | otherwise =
      case Core._exprValue e of
        Core.EVar name
          | Just replacement <- Map.lookup name env -> replacement
        Core.EWitLam binders body ->
          let inner = foldr Map.delete env (map Core._binderName binders)
           in Core.Expr (Core.EWitLam binders (subst inner body)) (Core.typeOf e) (Core.spanOf e)
        _ -> runIdentity (childrenA (Identity . subst env) e)

-- THE CHILD WALK

-- | Every immediate subexpression, rebuilt. One traversal for the three walks
-- above, so a node added to 'Core.AST.Expr_' is a compile error here once rather
-- than three silently-incomplete cases.
childrenA :: (Applicative f) => (Core.Expr -> f Core.Expr) -> Core.Expr -> f Core.Expr
childrenA f (Core.Expr value tipe sp) = rebuild <$> go value
  where
    rebuild v = Core.Expr v tipe sp
    bind (Core.Bind b v) = Core.Bind b <$> f v
    alt (Core.Alt p b) = Core.Alt p <$> f b
    field (n, v) = (,) n <$> f v
    go v =
      case v of
        Core.EVar _ -> pure v
        Core.EGlobal _ -> pure v
        Core.ELit _ -> pure v
        Core.ECrash _ -> pure v
        Core.ELam bs body -> Core.ELam bs <$> f body
        Core.EApp fn args -> Core.EApp <$> f fn <*> traverse f args
        Core.ELet binds body -> Core.ELet <$> traverse bind binds <*> f body
        Core.ELetRec binds body -> Core.ELetRec <$> traverse bind binds <*> f body
        Core.EJoin binds body -> Core.EJoin <$> traverse bind binds <*> f body
        Core.EJump name args -> Core.EJump name <$> traverse f args
        Core.ECase scrut alts fallback ->
          Core.ECase <$> f scrut <*> traverse alt alts <*> traverse f fallback
        Core.ECtor name tag args -> Core.ECtor name tag <$> traverse f args
        Core.ERecord fields -> Core.ERecord <$> traverse field fields
        Core.EUpdate base fields -> Core.EUpdate <$> f base <*> traverse field fields
        Core.EAccess base name -> (`Core.EAccess` name) <$> f base
        Core.EArray elems -> Core.EArray <$> traverse f elems
        Core.EPrim op args -> Core.EPrim op <$> traverse f args
        Core.ETyLam vars body -> Core.ETyLam vars <$> f body
        Core.ETyApp body types -> (`Core.ETyApp` types) <$> f body
        Core.EWitLam bs body -> Core.EWitLam bs <$> f body
        Core.EWitApp body args -> Core.EWitApp <$> f body <*> traverse f args

-- | A read-only walk, for 'sites'. 'Const' turns the rebuild above into a fold
-- without a second case analysis to keep in step with it.
children_ :: (Monoid m) => (Core.Expr -> m) -> Core.Expr -> m
children_ f e = getConst (childrenA (Const . f) e)
