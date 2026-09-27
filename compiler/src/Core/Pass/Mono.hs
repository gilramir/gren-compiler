{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | Monomorphization by shape (@docs/m3-native.md@ §NA3, §NA19; D491–D493).
--
-- R2 gives native no uniform representation, so a definition used at two types
-- that lay out differently is two definitions. This pass makes them, for the
-- native target, and after it no binding a program reaches has a type
-- variable in it: the C backend never sees one (D491).
--
-- __Core drives it without 'Core.AST.ETyLam' or 'Core.AST.ETyApp'__, which
-- nothing produces. Every node carries its type (C2), so a use of a polymorphic
-- global carries the type it is used at, and matching the definition's type
-- against it is the instantiation. Quantification is implicit
-- (@Core.Lower.Expression@ leaves binder types unquantified): a top-level
-- definition's variables are the free variables of its type, and a local's are
-- what is still free in its type once the enclosing copy's substitution is
-- applied.
--
-- __A copy is keyed by shape, not by type__ (D492). After "Core.Pass.Specialize"
-- a polymorphic definition does nothing with a value of type @a@ but move it —
-- anything that inspects one does it through a witness, whose copies are per
-- type already — so what its code depends on is the value's size and register
-- class. Each variable is keyed by one of eight shapes ('Shape'), and a row
-- variable by the record's layout, each field's name and shape, since that fixes
-- the offsets of the fields beside it. The copy's body is the definition's with
-- every variable replaced by its shape's type: @$I4@, @$P@ and the rest, which
-- are @Basics@ names no source can write, or @{}@ for 'U'. So a copy of
-- @Array.map@ for @Array Token@ and for @Array { name : String }@ is one
-- definition, @map$kPP@, whose types say @Array $P@.
--
-- That makes a type in the program either concrete or a shape, and __a backend
-- lays out both by the same rule__: a type's representation is a function of
-- its shape, a datatype's layout of the shapes of its arguments, a record's of
-- its fields' names and shapes. 'shapeOf' is that rule's half on this side, and
-- the backend's layout has to agree with it: were @Low@ to unbox a
-- one-constructor, one-field datatype, its shape would stop being 'P' here too.
--
-- __What nothing determines is @{}@__ (D493): a variable still free once every
-- enclosing instantiation is applied — the error type of a task that never
-- fails, the element of an @[]@ never added to — is given 'U', in every node,
-- which is consistent because no value of such a type is ever built.
--
-- __Shape keys are finite__, so the demand set is too, and polymorphic
-- recursion terminates here where copying by type would not (D9): at worst a
-- definition gets one copy per combination of eight shapes. A row variable's
-- layout is the one key that can grow, and only with the records a program
-- writes.
--
-- __Where the copies live__ is "Core.Pass.Specialize"'s answer: in the module
-- that defines the generic binding, beside it, named by the key (@f$kI4P@), and
-- the generic binding stays for 'Core.Program.link' to drop. A binding with no
-- variable is rewritten where it is, and it is where the walk starts: every
-- closed top-level binding, reached or not, since this pass is not told the
-- roots, and every @main@, whose variables nothing can determine. An @\@extern@ the target has a row for is not copied, since the
-- backend calls the host's implementation and never the Geng body.
module Core.Pass.Mono
  ( run,

    -- * The shape rule
    Shape (..),
    shapeOf,

    -- * What @GENG_MONO_STRICT@ asks
    monomorphic,
  )
where

import Control.Monad.Trans.State.Strict (State, gets, modify', runState)
import Core.AST qualified as Core
import Core.Pass.Specialize qualified as Specialize
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set (Set)
import Data.Set qualified as Set
import Gren.Fingerprint qualified as FP
import Gren.ModuleName qualified as ModuleName

-- SHAPES

-- | What a type variable's instantiation means to code that only moves the
-- value (§NA3): its size and register class. 'P' is every pointer — a record,
-- a datatype with a field, a closure, a string, an array — and stays apart
-- from 'I8' although the two are one size under Boehm, so that a precise
-- collector could still be given a pointer map (@DESIGN.md@ §4.3c). 'Row' is
-- a row variable's, and only a row variable's.
data Shape
  = I1
  | I2
  | I4
  | I8
  | F4
  | F8
  | U
  | P
  | Row ![(Core.Field, Shape)]
  deriving (Eq, Ord, Show)

-- | The shape of a closed type.
--
-- The scalars are @core@'s: @Int@, @UInt32@ and @Char@ are four bytes, the
-- 64-bit integers eight, the narrow ones one or two, @Float@ and @Float32@ the
-- two float classes. A datatype whose every constructor has no field is its
-- tag, as the spike made it, so 'I4', unless it is one of the runtime's own
-- ('provided'). The empty record is 'U'. Everything else is 'P', and so is a
-- shape type itself read back.
shapeOf :: Set Core.QualName -> Core.Type -> Shape
shapeOf enums tipe =
  case tipe of
    Core.TCon q@(Core.QualName home name) []
      | home == ModuleName.basics, Just s <- Map.lookup name scalars -> s
      | home == ModuleName.char, name == "Char" -> I4
      | Set.member q enums -> I4
    Core.TCon q _
      | Set.member q enums -> I4
    Core.TRecord [] Nothing -> U
    _ -> P

scalars :: Map Name Shape
scalars =
  Map.fromList
    ( [ ("Int", I4),
        ("UInt32", I4),
        ("Int64", I8),
        ("UInt64", I8),
        ("Int16", I2),
        ("UInt16", I2),
        ("Int8", I1),
        ("UInt8", I1),
        ("Float", F8),
        ("Float32", F4)
      ]
        ++ [(shapeName s, s) | s <- [I1, I2, I4, I8, F4, F8, P]]
    )

-- | The types whose values the runtime provides, which @core@ declares with a
-- constructor nothing builds (@type String = String -- NOTE: The compiler
-- provides the real implementation@) so that the declaration parses. Read as
-- declared, one looks like an enum, and it is not: each is a pointer to
-- something the runtime made. The scalars are in 'scalars', ahead of this.
provided :: Set Core.QualName
provided =
  Set.fromList
    [ Core.QualName ModuleName.string "String",
      Core.QualName ModuleName.array "Array",
      Core.QualName ModuleName.arrayTransient "Transient",
      Core.QualName ModuleName.bytes "Bytes",
      Core.QualName ModuleName.bytesTransient "Transient",
      Core.QualName ModuleName.taskInternal "Task",
      Core.QualName ModuleName.source "Source",
      Core.QualName ModuleName.process "Id"
    ]

-- | The type a variable of this shape becomes in a copy.
shapeType :: Shape -> Core.Type
shapeType s =
  case s of
    U -> unit
    Row fields -> Core.TRecord [(f, shapeType x) | (f, x) <- fields] Nothing
    _ -> Core.TCon (Core.QualName ModuleName.basics (shapeName s)) []

-- | @$I4@, @$P@: a name in @Basics@ that no source can write, since @$@ cannot
-- appear in one.
shapeName :: Shape -> Name
shapeName s = Name.fromChars ('$' : code s)

-- | A shape's letters in a copy's name. Each is self-delimiting, so a key's
-- codes run together: @map$kPP@, @foldl$kI4P@. A row is @R@ and eight hex
-- digits of its layout, which is the one shape too long to spell.
code :: Shape -> String
code s =
  case s of
    Row fields -> 'R' : take 8 (FP.toHex (foldl field FP.empty fields))
    _ -> show s
  where
    field fp (name, x) = FP.chars (code x) (FP.chars (Name.toChars name) fp)

unit :: Core.Type
unit = Core.TRecord [] Nothing

-- THE PASS

-- | A polymorphic top-level binding: its variables, sorted, and its type with
-- any quantifier taken off.
data Generic = Generic
  { _genVars :: ![Name],
    _genType :: !Core.Type
  }

-- | A definition at the shapes of its variables, in '_genVars' order. A
-- closed definition's key has no shapes, and keeps its name.
type Key = (Core.QualName, [Shape])

data Program = Program
  { _enums :: !(Set Core.QualName),
    _generics :: !(Map Core.QualName Generic)
  }

-- | The pass. The extern language and whether bodies are forced are the
-- target's (@Core.Program.chooseExterns@ reads the same two), since a
-- declaration the backend implements in the host language is left alone.
run :: Core.ExternLanguage -> Bool -> Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
run language bodies cores =
  let taken =
        Set.fromList
          [ Core.QualName home (Core._binderName (Core._externBinder e))
          | not bodies,
            (home, m) <- Map.toAscList cores,
            e <- Core._moduleExterns m,
            any ((== language) . Core._implLanguage) (Core._externImpls e)
          ]
      defs =
        Map.fromList
          [ (q, bind)
          | (home, m) <- Map.toAscList cores,
            bind@(Core.Bind b _) <- Core._moduleDefs m,
            let q = Core.QualName home (Core._binderName b),
            not (Set.member q taken)
          ]
      enums =
        Set.fromList
          [ Core._dataName d
          | m <- Map.elems cores,
            d <- Core._moduleData m,
            not (Set.member (Core._dataName d) provided),
            not (null (Core._dataCtors d)),
            all (null . Core._ctorFields) (Core._dataCtors d)
          ]
      -- A @main@ is a root nothing instantiates, so a variable its type still
      -- has — @Task x {}@, unannotated — is one nothing determines, and it is
      -- rewritten where it is with that variable @{}@, as a closed binding is.
      mains =
        Set.fromList
          [ Core.QualName home "main"
          | (home, m) <- Map.toAscList cores,
            Just _ <- [Core._moduleMain m]
          ]
      generics =
        Map.fromList
          [ (q, Generic (Set.toAscList vars) tipe)
          | (q, Core.Bind b _) <- Map.toAscList defs,
            not (Set.member q mains),
            let tipe = Specialize.unquantified (Core._binderType b),
            let vars = freeVars tipe,
            not (Set.null vars)
          ]
      prog = Program enums generics
      seeds = [(q, []) | q <- Map.keys defs, not (Map.member q generics)]
      built = close prog defs Map.empty seeds
      copies =
        Map.fromListWith
          (++)
          [(Core._qnHome q, [bind]) | ((q, shapes), bind) <- Map.toDescList built, not (null shapes)]
   in Map.mapWithKey (module_ built copies) cores

-- | Every key the closed bindings ask for, to a fixed point.
close :: Program -> Map Core.QualName Core.Bind -> Map Key Core.Bind -> [Key] -> Map Key Core.Bind
close prog defs = go
  where
    go built pending =
      case pending of
        [] -> built
        key : rest
          | Map.member key built -> go built rest
          | otherwise ->
              let (bind, asked) = instance_ prog defs key
               in go (Map.insert key bind built) (asked ++ rest)

-- | One definition at one key, and the keys its body asks for.
instance_ :: Program -> Map Core.QualName Core.Bind -> Key -> (Core.Bind, [Key])
instance_ prog defs key@(q, shapes) =
  let Core.Bind binder value = defs Map.! q
      vars = maybe [] _genVars (Map.lookup q (_generics prog))
      sub = Map.fromList (zip vars (map shapeType shapes))
      ctx = Ctx sub Map.empty
      (value', st) = runState (walk prog ctx value) (St 0 Map.empty [])
      binder' =
        binder
          { Core._binderName = Core._qnName (copyName key),
            Core._binderType = fixT sub (Core._binderType binder)
          }
   in (Core.Bind binder' value', reverse (_asked st))

-- | A module with its closed bindings rewritten and its copies added.
module_ :: Map Key Core.Bind -> Map ModuleName.Canonical [Core.Bind] -> ModuleName.Canonical -> Core.Module -> Core.Module
module_ built copies home modul =
  let rewritten =
        [ Map.findWithDefault bind (Core.QualName home (Core._binderName b), []) built
        | bind@(Core.Bind b _) <- Core._moduleDefs modul
        ]
      new = Map.findWithDefault [] home copies
   in if null new
        then modul {Core._moduleDefs = rewritten}
        else
          let ordered = Specialize.reorder home (rewritten ++ new)
           in modul
                { Core._moduleDefs = concat ordered,
                  Core._moduleDefsRec =
                    [ map (Core.QualName home . Core._binderName . Core._bindBinder) g
                    | g <- ordered,
                      length g > 1
                    ]
                }

copyName :: Key -> Core.QualName
copyName (Core.QualName home name, shapes) =
  Core.QualName home (suffixed name shapes)

suffixed :: Name -> [Shape] -> Name
suffixed name shapes
  | null shapes = name
  | otherwise = Name.fromChars (Name.toChars name ++ "$k" ++ concatMap code shapes)

-- THE WALK

-- | A local whose type still has a variable once the enclosing copy's
-- substitution is applied: a @let@ that generalized, or one whose type holds
-- a variable nothing determines. Its uses are instantiated as a global's are,
-- and each key is a copy bound where it was.
data Local = Local
  { _localId :: !Int,
    _localVars :: ![Name],
    _localType :: !Core.Type,
    _localValue :: !Core.Expr,
    _localBinder :: !Core.Binder,
    _localSub :: !(Map Name Core.Type),
    _localEnv :: Map Name Local
  }

data Ctx = Ctx
  { _sub :: !(Map Name Core.Type),
    _env :: !(Map Name Local)
  }

data St = St
  { _nextId :: !Int,
    -- | The keys each local has been asked for.
    _localAsked :: !(Map Int (Set [Shape])),
    -- | The top-level keys this definition asks for, latest first.
    _asked :: ![Key]
  }

type M a = State St a

walk :: Program -> Ctx -> Core.Expr -> M Core.Expr
walk prog ctx e@(Core.Expr value tipe sp) =
  case value of
    Core.EVar name
      | Just local <- Map.lookup name (_env ctx) ->
          do
            let shapes = instantiate prog (_localVars local) (_localType local) ty
            modify' (\s -> s {_localAsked = Map.insertWith Set.union (_localId local) (Set.singleton shapes) (_localAsked s)})
            node (Core.EVar (suffixed name shapes))
    Core.EGlobal q
      | Just gen <- Map.lookup q (_generics prog) ->
          do
            let key = (q, instantiate prog (_genVars gen) (_genType gen) ty)
            modify' (\s -> s {_asked = key : _asked s})
            node (Core.EGlobal (copyName key))
    Core.ELam bs body ->
      node . Core.ELam (map binder bs) =<< walk prog (hide (map Core._binderName bs)) body
    Core.EWitLam bs body ->
      node . Core.EWitLam (map binder bs) =<< walk prog (hide (map Core._binderName bs)) body
    Core.ELet binds body -> scope prog ctx False binds body tipe sp
    Core.ELetRec binds body -> scope prog ctx True binds body tipe sp
    Core.EJoin binds body ->
      do
        binds' <- mapM (\(Core.Bind b v) -> Core.Bind (binder b) <$> walk prog ctx v) binds
        body' <- walk prog ctx body
        node (Core.EJoin binds' body')
    Core.ECase scrut alts fallback ->
      do
        scrut' <- walk prog ctx scrut
        alts' <-
          mapM
            ( \(Core.Alt p b) ->
                Core.Alt (pattern_ p) <$> walk prog (hide (Set.toList (patternNames p))) b
            )
            alts
        fallback' <- traverse (walk prog ctx) fallback
        node (Core.ECase scrut' alts' fallback')
    _ ->
      do
        rebuilt <- Specialize.childrenA (walk prog ctx) e
        node (Core._exprValue rebuilt)
  where
    ty = fixT (_sub ctx) tipe
    node v = return (Core.Expr v ty sp)
    binder = fixBinder (_sub ctx)
    pattern_ = fixPattern (_sub ctx)
    hide names = ctx {_env = foldr Map.delete (_env ctx) names}

-- | A @let@ or @letrec@ group: the bindings whose type is closed under the
-- substitution are walked where they are, and each of the others is replaced
-- by one copy per key its uses ask for — none, if nothing uses it — bound in
-- the same place, so what it captured is in scope for every copy.
scope :: Program -> Ctx -> Bool -> [Core.Bind] -> Core.Expr -> Core.Type -> Core.Span -> M Core.Expr
scope prog ctx recursive binds body tipe sp =
  do
    first <- gets _nextId
    let sub = _sub ctx
        numbered = zip [first ..] binds
        isGeneric (Core.Bind b _) = not (Set.null (freeVars (substT sub (Core._binderType b))))
        local env i (Core.Bind b v) =
          let t = substT sub (Specialize.unquantified (Core._binderType b))
           in Local i (Set.toAscList (freeVars t)) t v b sub env
        -- The environment each binding sees, and the body's: in a @let@ a
        -- binding sees those before it, in a @letrec@ all of them.
        step env (i, bind@(Core.Bind b _))
          | isGeneric bind = Map.insert (Core._binderName b) (local (if recursive then final else env) i bind) env
          | otherwise = Map.delete (Core._binderName b) env
        envs = scanl step (_env ctx) numbered
        final = last envs
    modify' (\s -> s {_nextId = first + length binds})
    plain <-
      mapM
        ( \((_, bind@(Core.Bind b v)), env) ->
            if isGeneric bind
              then return Nothing
              else Just . Core.Bind (fixBinder sub b) <$> walk prog ctx {_env = if recursive then final else env} v
        )
        (zip numbered envs)
    body' <- walk prog ctx {_env = final} body
    let locals = Map.fromList [(_localId l, l) | l <- Map.elems final, _localId l >= first, _localId l < first + length binds]
    copies <- build prog locals Map.empty
    let bound =
          concat
            [ case p of
                Just bind -> [bind]
                Nothing -> [c | ((j, _), c) <- Map.toAscList copies, j == i]
            | ((i, _), p) <- zip numbered plain
            ]
        rebuild =
          if null bound
            then return body'
            else return (Core.Expr ((if recursive then Core.ELetRec else Core.ELet) bound body') (fixT sub tipe) sp)
    rebuild

-- | Every copy a group's locals are asked for, to a fixed point: a copy's body
-- can ask for another of its group's locals, or for itself.
build :: Program -> Map Int Local -> Map (Int, [Shape]) Core.Bind -> M (Map (Int, [Shape]) Core.Bind)
build prog locals built =
  do
    asked <- gets _localAsked
    let pending =
          [ (i, shapes)
          | (i, set) <- Map.toAscList (Map.restrictKeys asked (Map.keysSet locals)),
            shapes <- Set.toAscList set,
            not (Map.member (i, shapes) built)
          ]
    case pending of
      [] -> return built
      _ ->
        do
          made <- mapM (copyLocal prog locals) pending
          build prog locals (Map.union built (Map.fromList (zip pending made)))

copyLocal :: Program -> Map Int Local -> (Int, [Shape]) -> M Core.Bind
copyLocal prog locals (i, shapes) =
  do
    let l = locals Map.! i
        sub = Map.union (Map.fromList (zip (_localVars l) (map shapeType shapes))) (_localSub l)
        b = _localBinder l
    value <- walk prog (Ctx sub (_localEnv l)) (_localValue l)
    return
      ( Core.Bind
          b
            { Core._binderName = suffixed (Core._binderName b) shapes,
              Core._binderType = fixT sub (Core._binderType b)
            }
          value
      )

-- INSTANTIATION

-- | The shapes a use asks of a definition: its type matched against the
-- closed type the use carries, each variable read as a shape, a row variable
-- as its record's layout, and a variable the match leaves unbound as 'U'.
instantiate :: Program -> [Name] -> Core.Type -> Core.Type -> [Shape]
instantiate prog vars declared used =
  let bound = match (Set.fromList vars) declared used Map.empty
      rows = rowVars declared
      shapeFor v
        | Set.member v rows =
            Row
              ( case Map.lookup v bound of
                  Just (Core.TRecord fields _) -> [(f, shapeOf (_enums prog) t) | (f, t) <- fields]
                  _ -> []
              )
        | otherwise = maybe U (shapeOf (_enums prog)) (Map.lookup v bound)
   in map shapeFor vars

-- | Bind the given variables in a declared type so that it is the used one.
--
-- A use site's function type need not be in the definition's arity shape
-- (§NA3): @Task.mapError@ uses @composeL@, declared @(b -> c), (a -> b), a -> c@,
-- at @(b -> c), (a -> b) -> (a -> c)@, and a variable bound to a function
-- collapses into the arrow around it (C3). So arrows are flattened before they
-- are compared. The first binding of a variable stands; a second that differs
-- would be the class of defect D494 fixed, which "Core.Pass.Mono"'s census
-- counts at none.
match :: Set Name -> Core.Type -> Core.Type -> Map Name Core.Type -> Map Name Core.Type
match vars declared used acc =
  case declared of
    Core.TVar v
      | Set.member v vars -> Map.insertWith (\_ old -> old) v used acc
      | otherwise -> acc
    Core.TCon q ps
      | Core.TCon q' ts <- used,
        q == q',
        length ps == length ts ->
          foldl (\a (p, t) -> match vars p t a) acc (zip ps ts)
    Core.TFun _ _
      | Core.TFun _ _ <- used ->
          let (pa, pr) = flatten declared
              (ta, tr) = flatten used
              n = min (length pa) (length ta)
              acc' = foldl (\a (p, t) -> match vars p t a) acc (zip pa ta)
           in case compare (length pa) (length ta) of
                EQ -> match vars pr tr acc'
                GT -> match vars (Core.TFun (drop n pa) pr) tr acc'
                LT -> match vars pr (Core.TFun (drop n ta) tr) acc'
    Core.TRecord pfs prow
      | Core.TRecord tfs _ <- used ->
          let acc' = foldl (\a (f, p) -> maybe a (\t -> match vars p t a) (lookup f tfs)) acc pfs
           in case prow of
                Just r
                  | Set.member r vars ->
                      Map.insertWith
                        (\_ old -> old)
                        r
                        (Core.TRecord [(f, t) | (f, t) <- tfs, f `notElem` map fst pfs] Nothing)
                        acc'
                _ -> acc'
    Core.TForall _ _ body -> match vars body used acc
    _ -> acc

flatten :: Core.Type -> ([Core.Type], Core.Type)
flatten tipe =
  case tipe of
    Core.TFun args result ->
      let (more, final) = flatten result
       in (args ++ more, final)
    _ -> ([], tipe)

-- TYPES

-- | A type under a copy's substitution, with what is still free made @{}@
-- (D493): a variable becomes the empty record and a row variable closes the
-- record it extends. The quantifier goes too, since nothing is left for it to
-- bind.
fixT :: Map Name Core.Type -> Core.Type -> Core.Type
fixT sub = closeT . substT sub

closeT :: Core.Type -> Core.Type
closeT tipe =
  case tipe of
    Core.TVar _ -> unit
    Core.TCon q args -> Core.TCon q (map closeT args)
    Core.TFun args result -> Core.TFun (map closeT args) (closeT result)
    Core.TRecord fields _ -> Core.TRecord [(f, closeT t) | (f, t) <- fields] Nothing
    Core.TForall _ _ body -> closeT body

-- | Substitution with rows: a row variable bound to a record extends the record
-- it is the row of, whose fields stay alphabetical.
substT :: Map Name Core.Type -> Core.Type -> Core.Type
substT sub tipe
  | Map.null sub = tipe
  | otherwise =
      case tipe of
        Core.TVar v -> Map.findWithDefault tipe v sub
        Core.TCon q args -> Core.TCon q (map (substT sub) args)
        Core.TFun args result -> Core.TFun (map (substT sub) args) (substT sub result)
        Core.TRecord fields row ->
          let fields' = [(f, substT sub t) | (f, t) <- fields]
           in case row >>= (`Map.lookup` sub) of
                Just (Core.TRecord more row') -> Core.TRecord (List.sortOn fst (fields' ++ more)) row'
                Just (Core.TVar r) -> Core.TRecord fields' (Just r)
                _ -> Core.TRecord fields' row
        Core.TForall vars constraints body ->
          let inner = foldr Map.delete sub vars
           in Core.TForall vars [Core.CClass c (substT inner t) | Core.CClass c t <- constraints] (substT inner body)

freeVars :: Core.Type -> Set Name
freeVars tipe =
  case tipe of
    Core.TVar v -> Set.singleton v
    Core.TCon _ args -> Set.unions (map freeVars args)
    Core.TFun args result -> Set.unions (map freeVars (result : args))
    Core.TRecord fields row -> Set.unions (maybe Set.empty Set.singleton row : map (freeVars . snd) fields)
    Core.TForall vars _ body -> foldr Set.delete (freeVars body) vars

rowVars :: Core.Type -> Set Name
rowVars tipe =
  case tipe of
    Core.TVar _ -> Set.empty
    Core.TCon _ args -> Set.unions (map rowVars args)
    Core.TFun args result -> Set.unions (map rowVars (result : args))
    Core.TRecord fields row -> Set.unions (maybe Set.empty Set.singleton row : map (rowVars . snd) fields)
    Core.TForall _ _ body -> rowVars body

fixBinder :: Map Name Core.Type -> Core.Binder -> Core.Binder
fixBinder sub b = b {Core._binderType = fixT sub (Core._binderType b)}

fixPattern :: Map Name Core.Type -> Core.Pattern -> Core.Pattern
fixPattern sub = go
  where
    go p =
      case p of
        Core.PVar b -> Core.PVar (fixBinder sub b)
        Core.PCtor q t ps -> Core.PCtor q t (map go ps)
        Core.PRecord fs -> Core.PRecord [(f, go q) | (f, q) <- fs]
        Core.PArray ps tl -> Core.PArray (map go ps) (fmap (fixBinder sub) tl)
        Core.PAs b q -> Core.PAs (fixBinder sub b) (go q)
        other -> other

patternNames :: Core.Pattern -> Set Name
patternNames p =
  case p of
    Core.PVar b -> Set.singleton (Core._binderName b)
    Core.PCtor _ _ ps -> Set.unions (map patternNames ps)
    Core.PRecord fs -> Set.unions (map (patternNames . snd) fs)
    Core.PArray ps tl -> Set.unions (maybe Set.empty (Set.singleton . Core._binderName) tl : map patternNames ps)
    Core.PAs b q -> Set.insert (Core._binderName b) (patternNames q)
    _ -> Set.empty

-- STRICT

-- | Whether a binding has no type variable anywhere: its own type, every
-- node's and every binder's. @GENG_MONO_STRICT@ asks it of every binding a
-- linked program reaches, as @GENG_SPECIALIZE_STRICT@ asks
-- 'Core.AST.isSpecialized'.
monomorphic :: Core.Bind -> Bool
monomorphic (Core.Bind b value) =
  closed (Core._binderType b) && expr value
  where
    closed = Set.null . freeVars
    expr e =
      closed (Core.typeOf e)
        && all closed (binderTypes (Core._exprValue e))
        && all expr (Specialize.children_ (: []) e)
    binderTypes v =
      case v of
        Core.ELam bs _ -> map Core._binderType bs
        Core.EWitLam bs _ -> map Core._binderType bs
        Core.ELet bs _ -> map (Core._binderType . Core._bindBinder) bs
        Core.ELetRec bs _ -> map (Core._binderType . Core._bindBinder) bs
        Core.EJoin bs _ -> map (Core._binderType . Core._bindBinder) bs
        Core.ECase _ alts _ -> concatMap (patternTypes . Core._altPattern) alts
        _ -> []
    patternTypes p =
      case p of
        Core.PVar pb -> [Core._binderType pb]
        Core.PCtor _ _ ps -> concatMap patternTypes ps
        Core.PRecord fs -> concatMap (patternTypes . snd) fs
        Core.PArray ps tl -> maybe [] (pure . Core._binderType) tl ++ concatMap patternTypes ps
        Core.PAs pb q -> Core._binderType pb : patternTypes q
        _ -> []
