{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | An @Array@ a loop only appends to, grown through C7's transient (geng-lang
-- D656, D697, D699; @m3-pushlast.md@ §PL5, §PL16, §PL17).
--
-- > rec i n acc = if i > n then acc else rec (i + 1) n (Array.pushLast (next i) acc)
-- >   ⟹ rec i n acc = tr_to_array (rec$at i n (tr_from_array acc))
-- >      rec$at i n acc = if i > n then acc else rec$at (i + 1) n (tr_push acc (next i))
--
-- __Which loops__: D583's ("Core.Pass.Transient"): a top-level function that
-- calls itself, every use of its own name a saturated call outside any
-- lambda, so a fold "Core.Pass.FoldSpec" has copied for its lambda is one. Its
-- /version/ is a parameter that is an @Array a@ (D697's rule A) or a closed
-- record with an @Array a@ field (rule B), or either inside @Result e@ or
-- @Maybe@ (rule C), and the loop answers that same type.
--
-- __The rule__: in the loop's body the version, and each name a @let@ binds it
-- to or binds a growth of it to, is used only
--
--   * __grown__: as the array of @Array.pushLast@, or the left operand of
--     @++@ (and @Array.append@'s second, @Array.prepend@'s first) whose right
--     one is an array literal;
--   * __read__ by @Array.length@, anywhere;
--   * __handed back__ to the loop in the parameter's place, or __answered__;
--   * for rule B, as the record whose field that is: its other fields read,
--     and a record built or updated with a growth of the field in its place;
--   * for rule C, as the @Result@ or @Maybe@ around it: matched by a @when@
--     whose @Ok@ or @Just@ binds the array (or record) inside, built as
--     @Ok@ of a growth, or handed to @Result.map@ or @andThen@ (@Maybe@'s
--     likewise) with a lambda whose parameter is then the array inside. A
--     lambda handed to one of those over some other @Result@ may grow an
--     array a @when@ bound, since it is applied once, there and then:
--     @check x |> Result.map (\\v -> Array.pushLast v built)@;
--   * __popped and pushed back__ (D699): the subject of
--     @when Array.popLast a is Just { last, initial } -> …; Nothing -> …@,
--     where a push onto @initial@ is a write of the slot @last@ was in
--     ('popCase'). That one is a safety rule: nothing after the write may
--     read the array it wrote.
--
-- Anything else — handed to another function, captured by a lambda, put in a
-- constructor, or a self call whose answer is used as a value — refuses the
-- loop. The copy, @…$at@, takes and answers a transient in the version's
-- place; the loop keeps its name as the entry, which hands the copy
-- @tr_from_array@ of the array and turns its answer back with @tr_to_array@.
--
-- __A cost rule, not a safety rule__ (§PL5), unlike D583's. Natively and on
-- JavaScript a write through a transient that has been written through or
-- handed out copies first, and on the BEAM a transient is Erlang's persistent
-- @array@; so a version used twice costs a copy, never a wrong answer, and
-- nothing here checks that a version is used once. What the rule must refuse
-- is a version that leaves the loop each step, where the entry's
-- @tr_to_array@ would add a copy to the one it saves.
--
-- __The BEAM's whole__ (D703): natively and on JavaScript an @Array@ is a
-- slice, on which a push already writes in place, so 'Core.Pass.defaults'
-- runs all of this on the BEAM alone, whose @Array@ is a tuple every push
-- copies. Elsewhere it runs as @arraypop@ (D713), taking only a loop that pops
-- and pushes back, which a slice leaves quadratic (D708). A list naming
-- @arraytr@ in @GENG_CORE_PASSES@ runs all of it anywhere, which is how the
-- corpus holds it on node.
module Core.Pass.ArrayTransient
  ( run,
  )
where

import Core.AST qualified as Core
import Core.Pass.Inline qualified as Inline
import Core.Pass.Specialize qualified as Specialize
import Core.Pass.Transient qualified as Transient
import Core.Prim qualified as Prim
import Core.Refs qualified as Refs
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Monoid (All (..), Any (..))
import Data.Name (Name)
import Data.List qualified as List
import Data.Name qualified as Name
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName
import System.Environment qualified as Env
import System.IO.Unsafe (unsafePerformIO)

-- | The pass; with 'True', @arraypop@, it takes only a loop that pops the
-- last element and pushes back (D699, D713), the one shape a slice leaves
-- quadratic natively and on JavaScript (D708).
run :: Bool -> Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
run popsOnly = Map.mapWithKey (module_ popsOnly)

module_ :: Bool -> ModuleName.Canonical -> Core.Module -> Core.Module
module_ popsOnly home modul =
  let results = [(b, v, loop popsOnly (Core.QualName home (Core._binderName b)) v) | Core.Bind b v <- Core._moduleDefs modul]
   in logged home modul results $
        if null [() | (_, _, Just _) <- results]
        then modul
        else
          let defs =
                concat
                  [ case found of
                      Nothing -> [Core.Bind b v]
                      Just (entry, copy) -> [Core.Bind b entry, copy]
                  | (b, v, found) <- results
                  ]
              ordered = Inline.reorder home defs
           in modul
                { Core._moduleDefs = concat ordered,
                  Core._moduleDefsRec =
                    [ map (Core.QualName home . Core._binderName . Core._bindBinder) grp
                    | grp <- ordered,
                      length grp > 1
                    ]
                }

-- THE CENSUS

census :: Maybe FilePath
census = unsafePerformIO (Env.lookupEnv "GENG_ARRAYTR_CENSUS")
{-# NOINLINE census #-}

-- | With @GENG_ARRAYTR_CENSUS=<file>@, what the step-4 warning would see
-- (geng-lang @m3-pushlast.md@ §PL18, D708): a @loop@ line for each parameter
-- of a loop D583 sees whose type offers an @Array@ to the rules, @taken@,
-- @refused@ while something in the loop grows what is made of it, or @reads@;
-- a @step@ line for each parameter holding an @Array@ of a function that
-- does not call itself and grows what is made of it, the step a fold, a
-- @Parser.loop@ or a library's helper calls (§PL10); and a @fork@ line for each @let@ or array literal that grows one name in
-- two of its bindings or elements, the shape D708 leaves quadratic under the
-- slice. A report only: the Core is the pass's either way.
logged :: ModuleName.Canonical -> Core.Module -> [(Core.Binder, Core.Expr, Maybe a)] -> b -> b
logged home@(ModuleName.Canonical _ m) modul results out =
  case census of
    Nothing -> out
    Just path ->
      unsafePerformIO $ do
        appendFile path $
          unlines $
            [ List.intercalate "\t" ["loop", Name.toChars m, Name.toChars (Core._binderName b), Name.toChars (Core._binderName p), shapeName ws, outcome]
            | (b, Core.Expr (Core.ELam ps body) _ _, found) <- results,
              let q = Core.QualName home (Core._binderName b),
              Transient.selfOnly q (length ps) body,
              Transient.calls q body,
              p <- ps,
              ws@(_ : _) <- [wrappedShapes (Core._binderType p)],
              let outcome
                    | Just _ <- found = "taken"
                    | grownFrom (Core._binderName p) body = "refused"
                    | otherwise = "reads"
            ]
              ++ [ List.intercalate "\t" ["step", Name.toChars m, Name.toChars (Core._binderName b), Name.toChars (Core._binderName p), shapeName ws]
                 | (b, Core.Expr (Core.ELam ps body) _ _, _) <- results,
                   not (Transient.calls (Core.QualName home (Core._binderName b)) body),
                   p <- ps,
                   ws <- [stepShapes (Core._binderType p)],
                   not (null ws),
                   grownFrom (Core._binderName p) body
                 ]
              ++ [ List.intercalate "\t" ["fork", Name.toChars m, Name.toChars (Core._binderName b), Name.toChars x, show n, kind]
                 | Core.Bind b v <- Core._moduleDefs modul,
                   (x, n, kind) <- forks v
                 ]
        return out
  where
    shapeName ws =
      case ws of
        (Unwrapped, Bare _) : _ -> "bare"
        (Unwrapped, Field {}) : _ -> "field"
        (InResult _, _) : _ -> "result"
        _ -> "maybe"

-- | A step's parameter the census follows: what a loop's may be, or an
-- @Array@ inside any constructor or record.
stepShapes :: Core.Type -> [(Wrap, Shape)]
stepShapes t =
  case wrappedShapes t of
    [] -> [(Unwrapped, Bare e) | e <- arraysIn t]
    ws -> ws
  where
    arraysIn ty =
      case ty of
        Core.TCon a [e] | a == arrayType -> [e]
        Core.TCon _ args -> take 1 (concatMap arraysIn args)
        Core.TRecord fs _ -> take 1 (concatMap (arraysIn . snd) fs)
        _ -> []

-- | Whether a growth in the expression grows the name's array itself: the
-- name, a name a @let@ binds to it or to its field, what a @when@ on it binds,
-- or the parameter of a lambda handed it, as @Result.map@'s is. A value
-- computed from it, its elements among them, is not followed.
grownFrom :: Name -> Core.Expr -> Bool
grownFrom p body =
  let made = aliases (Set.singleton p) body
   in hasGrowth made body
  where
    hasGrowth d e =
      case Core._exprValue e of
        Core.EApp fn args
          | Just (arrayAt, _) <- growth fn,
            length args == 2,
            isAlias d (args !! arrayAt) ->
              True
          | isPopLast fn || isPushFirst fn,
            any (isAlias d) args ->
              True
        _ -> getAny (Specialize.children_ (Any . hasGrowth d) e)
    aliases d e =
      let d' = Set.union d (bindsFrom d e)
       in if d' == d then d else aliases d' e
    bindsFrom d e =
      Set.union (here d e) (Specialize.children_ (bindsFrom d) e)
    here d e =
      case Core._exprValue e of
        Core.ELet binds _ -> Set.fromList [Core._binderName bb | Core.Bind bb x <- binds, isAlias d x]
        Core.ECase scrut alts _
          | isAlias d scrut -> Set.unions [Refs.patternBinders pat | Core.Alt pat _ <- alts]
        Core.EApp _ args
          | any (isAlias d) args -> Set.fromList [Core._binderName bb | Core.Expr (Core.ELam bs _) _ _ <- args, bb <- bs]
        _ -> Set.empty
    isAlias d x =
      case Core._exprValue x of
        Core.EVar n -> Set.member n d
        Core.EAccess r _ -> isAlias d r
        _ -> False

-- | Each name a @let@ grows in two of its bindings, or an array literal in two
-- of its elements, and how many.
forks :: Core.Expr -> [(Name, Int, String)]
forks e =
  case Core._exprValue e of
    Core.ELet _ _ ->
      -- A chain of lets is one: the lowering nests each binding's.
      let (values, end) = chain e
       in counted "let" values ++ concatMap forks values ++ forks end
    Core.EArray xs -> counted "list" xs ++ concatMap forks xs
    _ -> concat (Specialize.children_ (\c -> [forks c]) e)
  where
    chain x =
      case Core._exprValue x of
        Core.ELet binds body -> let (vs, end) = chain body in (map Core._bindValue binds ++ vs, end)
        _ -> ([], x)
    counted kind xs =
      [ (x, n, kind)
      | (x, n) <- Map.toList (Map.fromListWith (+) [(x, 1 :: Int) | v <- xs, x <- Set.toList (grownNames v)]),
        n > 1
      ]
    grownNames v =
      case Core._exprValue v of
        Core.EApp fn args
          | Just (arrayAt, _) <- growth fn,
            length args == 2,
            Core.EVar x <- Core._exprValue (args !! arrayAt) ->
              Set.insert x (Set.unions (map grownNames args))
        Core.ELam _ _ -> Set.empty
        _ -> Specialize.children_ grownNames v

isPushFirst :: Core.Expr -> Bool
isPushFirst fn =
  case Core._exprValue fn of
    Core.EGlobal (Core.QualName home name) -> home == ModuleName.array && takeWhile (/= '$') (Name.toChars name) == "pushFirst"
    _ -> False

-- SHAPES

-- | What the version is: an array of the element type (rule A), or a closed
-- record whose named field is one (rule B), with all its fields.
data Shape
  = Bare Core.Type
  | Field Name Core.Type [(Name, Core.Type)]

-- | What a name the rule follows stands for: the version itself, or, under
-- rule B, the version's array field.
data Kind
  = Whole
  | Part
  | Outer
  | -- | D699: the @initial@ of a @popLast@ of the version's array, which is
    -- that array less its last slot. Only a push onto it, which writes the
    -- slot, and its length are allowed. It carries the popped array, as the
    -- transient's, and its length.
    Popped Core.Expr Core.Expr
  deriving (Eq)

-- | Rule C: what the version is inside, if anything. A @Result@ carries its
-- error type.
data Wrap
  = Unwrapped
  | InResult Core.Type
  | InMaybe
  deriving (Eq)

wrapType :: Wrap -> Core.Type -> Core.Type
wrapType w t =
  case w of
    Unwrapped -> t
    InResult err -> Core.TCon (Core.QualName ModuleName.result "Result") [err, t]
    InMaybe -> Core.TCon (Core.QualName ModuleName.maybe "Maybe") [t]

-- | The shapes a loop parameter's type offers, under rule C as well.
wrappedShapes :: Core.Type -> [(Wrap, Shape)]
wrappedShapes t =
  [(Unwrapped, s) | s <- shapes t]
    ++ case t of
      Core.TCon (Core.QualName home "Result") [err, x] | home == ModuleName.result -> [(InResult err, s) | s <- shapes x]
      Core.TCon (Core.QualName home "Maybe") [x] | home == ModuleName.maybe -> [(InMaybe, s) | s <- shapes x]
      _ -> []

-- | The constructor that holds the version (@Ok@, @Just@, tag 0 in @core@'s
-- declarations) and the one that does not (@Err@, @Nothing@, tag 1).
holding :: Wrap -> Core.QualName
holding w =
  case w of
    InMaybe -> Core.QualName ModuleName.maybe "Just"
    _ -> Core.QualName ModuleName.result "Ok"

empty_ :: Wrap -> Core.QualName
empty_ w =
  case w of
    InMaybe -> Core.QualName ModuleName.maybe "Nothing"
    _ -> Core.QualName ModuleName.result "Err"

outerVersion :: Ck -> Core.Type
outerVersion ck = wrapType (_wrap ck) (versionType (_shape ck))

outerTransient :: Ck -> Core.Type
outerTransient ck = wrapType (_wrap ck) (transientType (_shape ck))

-- | The shapes a parameter's type offers.
shapes :: Core.Type -> [Shape]
shapes t =
  case t of
    Core.TCon a [e] | a == arrayType -> [Bare e]
    Core.TRecord fs Nothing -> [Field f e fs | (f, Core.TCon a [e]) <- fs, a == arrayType]
    _ -> []

versionType :: Shape -> Core.Type
versionType s =
  case s of
    Bare e -> Core.TCon arrayType [e]
    Field _ _ fs -> Core.TRecord fs Nothing

transientType :: Shape -> Core.Type
transientType s =
  case s of
    Bare e -> tTransient e
    Field f e fs -> Core.TRecord [(g, if g == f then tTransient e else t) | (g, t) <- fs] Nothing

element :: Shape -> Core.Type
element s =
  case s of
    Bare e -> e
    Field _ e _ -> e

kindType :: Ck -> Kind -> Core.Type
kindType ck k =
  case k of
    Whole -> transientType (_shape ck)
    Part -> tTransient (element (_shape ck))
    Popped _ _ -> tTransient (element (_shape ck))
    Outer -> outerTransient ck

tTransient :: Core.Type -> Core.Type
tTransient e = Core.TCon (Core.QualName ModuleName.arrayTransient "Transient") [e]

arrayType :: Core.QualName
arrayType = Core.QualName ModuleName.array "Array"

tInt :: Core.Type
tInt = Core.TCon (Core.QualName ModuleName.basics "Int") []

-- THE LOOP

-- | A loop's entry and its copy, when one of its parameters passes the rule.
loop :: Bool -> Core.QualName -> Core.Expr -> Maybe (Core.Expr, Core.Bind)
loop popsOnly q value =
  case value of
    Core.Expr (Core.ELam ps body) (Core.TFun ts r) sp
      | Transient.selfOnly q (length ps) body,
        Transient.calls q body ->
          firstJust
            [ attempt popsOnly q ps ts r sp body i w s
            | (i, p) <- zip [0 ..] ps,
              (w, s) <- wrappedShapes (Core._binderType p),
              wrapType w (versionType s) == r
            ]
    _ -> Nothing

firstJust :: [Maybe a] -> Maybe a
firstJust xs = case [x | Just x <- xs] of
  x : _ -> Just x
  [] -> Nothing

attempt :: Bool -> Core.QualName -> [Core.Binder] -> [Core.Type] -> Core.Type -> Core.Span -> Core.Expr -> Int -> Wrap -> Shape -> Maybe (Core.Expr, Core.Bind)
attempt popsOnly q ps ts r sp body pos w s =
  let qt = Core.QualName (Core._qnHome q) (Name.fromChars (Name.toChars (Core._qnName q) ++ "$at"))
      tt = wrapType w (transientType s)
      copyType = Core.TFun [if j == pos then tt else t | (j, t) <- zip [0 ..] ts] tt
      p = ps !! pos
      ck = Ck q qt copyType (length ps) pos s w
   in do
        body' <- top ck (Map.singleton (Core._binderName p) (topKind ck)) body
        if grows body' && (not popsOnly || writes body')
          then
            let ps' = [if j == pos then b {Core._binderType = tt} else b | (j, b) <- zip [0 :: Int ..] ps]
                copy = Core.Expr (Core.ELam ps' body') copyType sp
                args = [if j == pos then enterTop ck (var b) else var b | (j, b) <- zip [0 ..] ps]
                entered = Core.Expr (Core.EApp (Core.Expr (Core.EGlobal qt) copyType sp) args) tt sp
                entry = Core.Expr (Core.ELam ps (leaveTop ck entered)) (Core.TFun ts r) sp
             in Just (entry, Core.Bind (Core.Binder (Core._qnName qt) copyType sp) copy)
          else Nothing
  where
    var b = Core.Expr (Core.EVar (Core._binderName b)) (Core._binderType b) (Core._binderSpan b)

-- | Whether the copy grows its transient anywhere: a loop that only reads and
-- threads its array is left alone.
grows :: Core.Expr -> Bool
grows e =
  case Core._exprValue e of
    Core.EPrim (Prim.TransientOp Prim.TrPush) _ -> True
    _ -> getAny (Specialize.children_ (Any . grows) e)

-- | Whether the copy writes a popped slot (D699): only a pop makes a
-- 'Prim.TrSet' here.
writes :: Core.Expr -> Bool
writes e =
  case Core._exprValue e of
    Core.EPrim (Prim.TransientOp Prim.TrSet) _ -> True
    _ -> getAny (Specialize.children_ (Any . writes) e)

data Ck = Ck
  { _loop :: Core.QualName,
    _copy :: Core.QualName,
    _copyType :: Core.Type,
    _arity :: Int,
    _pos :: Int,
    _shape :: Shape,
    _wrap :: Wrap
  }

-- | The rule at the loop's own type: rule A's or B's, or rule C's around it.
top :: Ck -> Names -> Core.Expr -> Maybe Core.Expr
top ck =
  case _wrap ck of
    Unwrapped -> conv ck
    _ -> convOuter ck

topKind :: Ck -> Kind
topKind ck = if _wrap ck == Unwrapped then Whole else Outer

enterTop :: Ck -> Core.Expr -> Core.Expr
enterTop ck = if _wrap ck == Unwrapped then enter (_shape ck) else enterOuter ck

leaveTop :: Ck -> Core.Expr -> Core.Expr
leaveTop ck = if _wrap ck == Unwrapped then leave (_shape ck) else leaveOuter ck

-- | A value of the wrapped version's type that does not mention it, made the
-- transient's: @Ok x@ as @Ok@ of @x@ entered, @Err e@ as it is, and anything
-- else matched and rebuilt.
enterOuter :: Ck -> Core.Expr -> Core.Expr
enterOuter ck e =
  case Core._exprValue e of
    Core.ECtor c tag [x] | c == holding (_wrap ck) -> Core.Expr (Core.ECtor c tag [enter (_shape ck) x]) (outerTransient ck) (Core.spanOf e)
    Core.ECtor c _ _ | c == empty_ (_wrap ck) -> e {Core._exprType = outerTransient ck}
    _ -> rewrap ck e (versionType (_shape ck)) (outerTransient ck) (enter (_shape ck))

-- | The copy's wrapped answer made the version's type again.
leaveOuter :: Ck -> Core.Expr -> Core.Expr
leaveOuter ck e = rewrap ck e (transientType (_shape ck)) (outerVersion ck) (leave (_shape ck))

-- | @when e is Ok x -> Ok (f x); Err y -> Err y@, or @Maybe@'s.
rewrap :: Ck -> Core.Expr -> Core.Type -> Core.Type -> (Core.Expr -> Core.Expr) -> Core.Expr
rewrap ck e inner t f =
  let sp = Core.spanOf e
      x = Core.Binder "$atW" inner sp
      held = Core.Alt (Core.PCtor (holding (_wrap ck)) 0 [Core.PVar x]) (Core.Expr (Core.ECtor (holding (_wrap ck)) 0 [f (Core.Expr (Core.EVar "$atW") inner sp)]) t sp)
      other =
        case _wrap ck of
          InResult err ->
            let y = Core.Binder "$atE" err sp
             in Core.Alt (Core.PCtor (empty_ (_wrap ck)) 1 [Core.PVar y]) (Core.Expr (Core.ECtor (empty_ (_wrap ck)) 1 [Core.Expr (Core.EVar "$atE") err sp]) t sp)
          _ -> Core.Alt (Core.PCtor (empty_ (_wrap ck)) 1 []) (Core.Expr (Core.ECtor (empty_ (_wrap ck)) 1 []) t sp)
   in Core.Expr (Core.ECase e [held, other] Nothing) t sp

-- | A value of the version's type that does not mention it, made the
-- transient's.
enter :: Shape -> Core.Expr -> Core.Expr
enter s e =
  case s of
    Bare el -> prim Prim.TrFromArray [e] (tTransient el)
    Field f el fs ->
      rebuild "$atIn" e fs (transientType s) $ \g get ->
        if g == f then prim Prim.TrFromArray [get] (tTransient el) else get

-- | The copy's answer made the version's type again.
leave :: Shape -> Core.Expr -> Core.Expr
leave s e =
  case s of
    Bare el -> prim Prim.TrToArray [e] (Core.TCon arrayType [el])
    Field f _ fs ->
      rebuild "$atOut" e fs (versionType s) $ \g get ->
        if g == f then prim Prim.TrToArray [get] (Core.TCon arrayType [element s]) else get

-- | @let x = e in { g = h g x.g, … }@.
rebuild :: Name -> Core.Expr -> [(Name, Core.Type)] -> Core.Type -> (Name -> Core.Expr -> Core.Expr) -> Core.Expr
rebuild x e fs t h =
  let sp = Core.spanOf e
      xe = Core.Expr (Core.EVar x) (Core.typeOf e) sp
      fieldOf g = case [ft | (n, ft) <- recordFields (Core.typeOf e) ++ fs, n == g] of
        ft : _ -> ft
        [] -> Core.typeOf e
      body = Core.Expr (Core.ERecord [(g, h g (Core.Expr (Core.EAccess xe g) (fieldOf g) sp)) | (g, _) <- fs]) t sp
   in Core.Expr (Core.ELet [Core.Bind (Core.Binder x (Core.typeOf e) sp) e] body) t sp

recordFields :: Core.Type -> [(Name, Core.Type)]
recordFields t =
  case t of
    Core.TRecord fs _ -> fs
    _ -> []

-- | A transient primitive applied, at its first argument's place.
prim :: Prim.TransientPrim -> [Core.Expr] -> Core.Type -> Core.Expr
prim op args t =
  case args of
    a : _ -> Core.Expr (Core.EPrim (Prim.TransientOp op) args) t (Core.spanOf a)
    [] -> error "Core.Pass.ArrayTransient: a primitive with no argument"

-- THE RULE

type Names = Map Name Kind

mentions :: Names -> Core.Expr -> Bool
mentions v = Transient.mentions (Map.keysSet v)

-- | An expression where the version goes on — the loop's answer, the array a
-- growth grows, a @let@'s binding that is a version, or the loop's argument
-- in the parameter's place — rewritten to the transient's type.
--
-- A call to the loop is the copy's whatever it is handed, before anything
-- else: one that mentions no version, @loop (i + 1) []@, made a value of the
-- entry's, would be a call to the entry that is not a tail call, a stack
-- frame each time round.
conv :: Ck -> Names -> Core.Expr -> Maybe Core.Expr
conv ck v e
  | Core.EApp (Core.Expr (Core.EGlobal g) _ fsp) args <- Core._exprValue e,
    g == _loop ck,
    length args == _arity ck =
      do
        args' <- sequence [if j == _pos ck then top ck v a else plain ck v a | (j, a) <- zip [0 ..] args]
        return (Core.Expr (Core.EApp (Core.Expr (Core.EGlobal (_copy ck)) (_copyType ck) fsp) args') (outerTransient ck) (Core.spanOf e))
  | not (mentions v e) = Just (enter (_shape ck) e)
  | otherwise =
      case Core._exprValue e of
        Core.EVar x | Map.lookup x v == Just Whole -> Just (retype ck Whole e)
        Core.ELet binds body -> lets ck v binds body (conv ck)
        Core.ECase scrut alts fallback
          | Just popped <- popCase ck v e scrut alts fallback (conv ck) (transientType (_shape ck)) -> popped
          | otherwise ->
              do
                (scrut', alts', fallback') <- matched ck v scrut alts fallback (conv ck)
                return (retyped (Core.ECase scrut' alts' fallback'))
        _ ->
          case _shape ck of
            Bare _ -> grow ck v e
            Field f _ _ ->
              case Core._exprValue e of
                Core.ERecord fields ->
                  do
                    fields' <- sequence [(,) g <$> (if g == f then grow ck v x else plain ck v x) | (g, x) <- fields]
                    return (retyped (Core.ERecord fields'))
                Core.EUpdate base fields ->
                  do
                    -- The fields are evaluated after the base, and a pop in
                    -- it would have written the slot the field's growth reads.
                    if pops v base then Nothing else Just ()
                    base' <- conv ck v base
                    fields' <- sequence [(,) g <$> (if g == f then grow ck v x else plain ck v x) | (g, x) <- fields]
                    return (retyped (Core.EUpdate base' fields'))
                _ -> Nothing
  where
    retyped x = Core.Expr x (transientType (_shape ck)) (Core.spanOf e)

-- | An expression of the array's type that is a growth of the version's
-- array, or the array itself, rewritten to the transient's: a push of each
-- element, or a name the rule follows.
grow :: Ck -> Names -> Core.Expr -> Maybe Core.Expr
grow ck v e
  | not (mentions v e) = Just (prim Prim.TrFromArray [e] tt)
  | otherwise =
      case Core._exprValue e of
        _ | Just src <- source ck v e -> Just src
        Core.ELet binds body -> lets ck v binds body (grow ck)
        Core.ECase scrut alts fallback
          | Just popped <- popCase ck v e scrut alts fallback (grow ck) tt -> popped
          | otherwise ->
              do
                (scrut', alts', fallback') <- matched ck v scrut alts fallback (grow ck)
                return (Core.Expr (Core.ECase scrut' alts' fallback') tt (Core.spanOf e))
        Core.EApp fn args
          | Just (arrayAt, itemsAt) <- growth fn,
            length args == 2,
            Core.EVar i <- Core._exprValue (args !! arrayAt),
            Just (Popped src n) <- Map.lookup i v ->
              -- D699: the first element pushed onto what a pop left is
              -- written into the popped slot.
              do
                items <- grownBy ck v fn arrayAt itemsAt (args !! itemsAt)
                case items of
                  first : more ->
                    let set = Core.Expr (Core.EPrim (Prim.TransientOp Prim.TrSet) [src, minusOne n, first]) tt (Core.spanOf e)
                     in return (foldl (\t x -> prim Prim.TrPush [t, x] tt) set more)
                  [] -> Nothing
        Core.EApp fn args
          | Just (arrayAt, itemsAt) <- growth fn,
            length args == 2 ->
              do
                arr <- grow ck v (args !! arrayAt)
                items <- grownBy ck v fn arrayAt itemsAt (args !! itemsAt)
                return (foldl (\t x -> prim Prim.TrPush [t, x] tt) arr items)
        _ -> Nothing
  where
    tt = tTransient (element (_shape ck))

-- | The elements a growth adds: @pushLast@'s one, or an array literal's.
grownBy :: Ck -> Names -> Core.Expr -> Int -> Int -> Core.Expr -> Maybe [Core.Expr]
grownBy ck v fn arrayAt itemsAt other =
  if arrayAt == 1 && itemsAt == 0 && isPushLast fn
    then (: []) <$> plain ck v other
    else case Core._exprValue other of
      Core.EArray xs -> traverse (plain ck v) xs
      _ -> Nothing

-- | @n - 1@, at @Int@.
minusOne :: Core.Expr -> Core.Expr
minusOne n =
  let sp = Core.spanOf n
   in Core.Expr (Core.EPrim (Prim.IntOp Prim.I32 Prim.ISub) [n, Core.Expr (Core.ELit (Core.LInt 1)) tInt sp]) tInt sp

-- | The version's array where the expression names it: a name for the array
-- itself, or, under rule B, the field of a name for the record.
source :: Ck -> Names -> Core.Expr -> Maybe Core.Expr
source ck v e =
  case (_shape ck, Core._exprValue e) of
    (Bare _, Core.EVar x) | Map.lookup x v == Just Whole -> Just (retype ck Whole e)
    (Field {}, Core.EVar x) | Map.lookup x v == Just Part -> Just (retype ck Part e)
    (Field f _ _, Core.EAccess r@(Core.Expr (Core.EVar x) _ _) g)
      | g == f,
        Map.lookup x v == Just Whole ->
          Just (Core.Expr (Core.EAccess (retype ck Whole r) g) (kindType ck Part) (Core.spanOf e))
    _ -> Nothing

-- | A function that grows an array at its end, with which argument is the
-- array and which the element or the array of them: @pushLast x a@, @a ++ b@
-- as @Appendable@'s instance has it, @Array.append b a@ and
-- @Array.prepend a b@.
growth :: Core.Expr -> Maybe (Int, Int)
growth fn =
  case Core._exprValue fn of
    Core.EGlobal (Core.QualName home name)
      | home == ModuleName.array ->
          case takeWhile (/= '$') (Name.toChars name) of
            "pushLast" -> Just (1, 0)
            "append" -> Just (1, 0)
            "prepend" -> Just (0, 1)
            "" | Name.toChars name == "$i$Appendable$Array$append" -> Just (0, 1)
            _ -> Nothing
    _ -> Nothing

isPushLast :: Core.Expr -> Bool
isPushLast fn =
  case Core._exprValue fn of
    Core.EGlobal (Core.QualName _ name) -> takeWhile (/= '$') (Name.toChars name) == "pushLast"
    _ -> False

-- | Whether the function reads an array's length.
isLength :: Core.Expr -> Bool
isLength fn =
  case Core._exprValue fn of
    Core.EGlobal (Core.QualName home name) ->
      home == ModuleName.array && takeWhile (/= '$') (Name.toChars name) `elem` ["length", "unsafeLength"]
    _ -> False

-- | An expression whose value is not the version: it may read the version's
-- length, and under rule B the record's other fields, and nothing else of it.
plain :: Ck -> Names -> Core.Expr -> Maybe Core.Expr
plain ck v e
  | not (mentions v e) = Just e
  | otherwise =
      case Core._exprValue e of
        Core.EApp fn [Core.Expr (Core.EVar i) _ _]
          | isLength fn,
            Just (Popped _ n) <- Map.lookup i v ->
              Just (minusOne n)
        Core.EApp fn [a]
          | isLength fn,
            Just src <- source ck v a ->
              Just (Core.Expr (Core.EPrim (Prim.TransientOp Prim.TrLength) [src]) tInt (Core.spanOf e))
        Core.EAccess r@(Core.Expr (Core.EVar x) _ _) g
          | Field f _ _ <- _shape ck,
            g /= f,
            Map.lookup x v == Just Whole ->
              Just (e {Core._exprValue = Core.EAccess (retype ck Whole r) g})
        Core.EVar _ -> Nothing
        Core.ELam _ _ -> Nothing
        Core.ELetRec _ _ -> Nothing
        Core.EWitLam _ _ -> Nothing
        Core.EApp (Core.Expr (Core.EGlobal g) _ _) _ | g == _loop ck -> Nothing
        Core.ELet binds body -> lets ck v binds body (plain ck)
        Core.ECase scrut alts fallback ->
          do
            (scrut', alts', fallback') <- matched ck v scrut alts fallback (plain ck)
            return (e {Core._exprValue = Core.ECase scrut' alts' fallback'})
        _ -> Specialize.childrenA (plain ck v) e

-- | A @let@'s bindings in order, then its body with what they bind: a binding
-- that names the version, or grows it, is a name the rule follows, with its
-- binder the transient's; any other is read as 'plain'.
lets :: Ck -> Names -> [Core.Bind] -> Core.Expr -> (Names -> Core.Expr -> Maybe Core.Expr) -> Maybe Core.Expr
lets ck v0 binds0 body0 inBody = go v0 [] binds0
  where
    go v acc binds =
      case binds of
        [] ->
          do
            body' <- inBody v body0
            return (Core.Expr (Core.ELet (reverse acc) body') (Core.typeOf body') (Core.spanOf body0))
        Core.Bind b r : rest ->
          let name = Core._binderName b
              without = Map.delete name v
              as k r' = go (Map.insert name k v) (Core.Bind b {Core._binderType = kindType ck k} r' : acc) rest
           in if not (mentions v r)
                then go without (Core.Bind b r : acc) rest
                else
                  -- D699: what follows a binding that pops may not read the
                  -- slot the pop gave up, through any name.
                  if pops v r && not (all (safeAfter ck without) (map Core._bindValue rest ++ [body0]))
                    then Nothing
                    else case wholeOrPart v r of
                      Just (k, r') -> as k r'
                      Nothing ->
                        do
                          r' <- plain ck v r
                          go without (Core.Bind b r' : acc) rest
    wholeOrPart v r
      | _wrap ck /= Unwrapped, Core.typeOf r == outerVersion ck, Just r' <- convOuter ck v r = Just (Outer, r')
      | Core.typeOf r == versionType (_shape ck), Just r' <- conv ck v r = Just (Whole, r')
      | Field {} <- _shape ck, Core.typeOf r == Core.TCon arrayType [element (_shape ck)], Just r' <- grow ck v r = Just (Part, r')
      | otherwise = Nothing

-- | The names a pattern binds are not the version's any more.
shadow :: Core.Pattern -> Names -> Names
shadow p v = foldr Map.delete v (Set.toList (Refs.patternBinders p))

-- | A name the rule follows, given the transient's type.
retype :: Ck -> Kind -> Core.Expr -> Core.Expr
retype ck k e = e {Core._exprType = kindType ck k}

-- D699: POP, THEN PUSH

-- | @when Array.popLast s is Just { last, initial } -> b1; Nothing -> b2@ where
-- @s@ is the version's array, rewritten to read its length and its last slot,
-- with a push onto @initial@ in @b1@ written into that slot:
--
-- > let n = tr_length s in case n of 0 -> b2; _ -> let last = tr_get s (n - 1) in b1
--
-- A pop pushed back is a write of the last slot, which 'Prim.TrSet' already
-- is on every backend, so no primitive is new (D712).
--
-- __A safety rule, not a cost rule__ (§PL5): the write lands in a slot @s@
-- itself still reads. A version made from @s@ by a push has written through
-- it, so the write copies first; one made before @s@ is shorter and never
-- reads the slot. What must not happen is a read of @s@, or of anything that
-- may be @s@, after the write: so a path through @b1@ that pushes onto
-- @initial@ ('safeIn'), and whatever a @let@ evaluates after the @when@, may
-- name the version only as 'safeAfter' allows.
popCase :: Ck -> Names -> Core.Expr -> Core.Expr -> [Core.Alt] -> Maybe Core.Expr -> (Names -> Core.Expr -> Maybe Core.Expr) -> Core.Type -> Maybe (Maybe Core.Expr)
popCase ck v e scrut alts fallback k t =
  case (Core._exprValue scrut, alts, fallback) of
    (Core.EApp fn [s], [a1, a2], Nothing)
      | isPopLast fn,
        Just src <- source ck v s ->
          case (justAlt a1, justAlt a2) of
            (Just j, Nothing) | emptyAlt a2 -> Just (rewrite src j (Core._altBody a2) (Core._altPattern a2))
            (Nothing, Just j) | emptyAlt a1 -> Just (rewrite src j (Core._altBody a1) (Core._altPattern a1))
            _ -> Nothing
    _ -> Nothing
  where
    sp = Core.spanOf e
    justAlt (Core.Alt (Core.PCtor c _ [Core.PRecord fs]) b)
      | c == Core.QualName ModuleName.maybe "Just",
        Just initial <- named "initial" fs,
        Just final <- named "last" fs =
          Just (initial, final, b)
    justAlt _ = Nothing
    named f fs =
      case [p | (g, p) <- fs, g == f] of
        [Core.PVar b] -> Just (Just b)
        [Core.PWild] -> Just Nothing
        [] -> Just Nothing
        _ -> Nothing
    emptyAlt (Core.Alt p _) =
      case p of
        Core.PWild -> True
        Core.PCtor c _ [] -> c == Core.QualName ModuleName.maybe "Nothing"
        _ -> False
    rewrite src (initial, final, b1) b2 p2 =
      let bound = [Core._binderName b | Just b <- [initial, final]]
          v1 = foldr Map.delete v bound
          nName = Name.fromChars ("$atN" ++ maybe "" (Name.toChars . Core._binderName) initial)
          n = Core.Expr (Core.EVar nName) tInt sp
          v1' = case initial of
            Just b -> Map.insert (Core._binderName b) (Popped src n) v1
            Nothing -> v1
          elT = element (_shape ck)
       in if not (maybe True (\b -> safeIn ck v1 (Core._binderName b) b1) initial)
            then Nothing
            else do
              b1' <- k v1' b1
              b2' <- k (shadow p2 v) b2
              let withLast = case final of
                    Just b ->
                      Core.Expr (Core.ELet [Core.Bind b (Core.Expr (Core.EPrim (Prim.TransientOp Prim.TrGet) [src, minusOne n]) elT sp)] b1') t sp
                    Nothing -> b1'
                  cased = Core.Expr (Core.ECase n [Core.Alt (Core.PLit (Core.LInt 0)) b2', Core.Alt Core.PWild withLast] Nothing) t sp
                  len = Core.Expr (Core.EPrim (Prim.TransientOp Prim.TrLength) [src]) tInt sp
              return (Core.Expr (Core.ELet [Core.Bind (Core.Binder nName tInt sp) len] cased) t sp)

isPopLast :: Core.Expr -> Bool
isPopLast fn =
  case Core._exprValue fn of
    Core.EGlobal (Core.QualName home name) -> home == ModuleName.array && takeWhile (/= '$') (Name.toChars name) == "popLast"
    _ -> False

-- | Whether a pop's @Just@ branch reads nothing that may be the popped array
-- after the write: a path that never pushes onto @initial@ writes nothing,
-- and a @when@'s subject is evaluated before its branches; anything else is
-- 'safeAfter'.
safeIn :: Ck -> Names -> Name -> Core.Expr -> Bool
safeIn ck v initial e
  | not (Transient.mentions (Set.singleton initial) e) = True
  | otherwise =
      case Core._exprValue e of
        Core.ECase scrut alts fallback
          | not (Transient.mentions (Set.singleton initial) scrut) ->
              all (\(Core.Alt p b) -> safeIn ck (shadow p v) initial b) alts && maybe True (safeIn ck v initial) fallback
        _ -> safeAfter ck v e

-- | Whether the expression pops the version's array.
pops :: Names -> Core.Expr -> Bool
pops v e =
  case Core._exprValue e of
    Core.EApp fn [s] | isPopLast fn, mentions v s -> True
    _ -> getAny (Specialize.children_ (Any . pops v) e)

-- | Whether the expression, evaluated after a pop's write, reads nothing that
-- may be the popped array: the version's names appear only under
-- @Array.length@, whose answer the write does not change, and under rule B as
-- the record whose other fields are read, or which is updated with its array
-- field replaced.
safeAfter :: Ck -> Names -> Core.Expr -> Bool
safeAfter ck v e =
  case Core._exprValue e of
    Core.EVar x -> not (Map.member x v)
    Core.EApp fn [a] | isLength fn, named a -> True
    Core.EAccess (Core.Expr (Core.EVar r) _ _) g
      | Field f _ _ <- _shape ck,
        Map.member r v ->
          g /= f
    Core.EUpdate (Core.Expr (Core.EVar r) _ _) fields
      | Field f _ _ <- _shape ck,
        Map.member r v ->
          f `elem` map fst fields && all (safeAfter ck v . snd) fields
    _ -> getAll (Specialize.children_ (All . safeAfter ck v) e)
  where
    named a =
      case Core._exprValue a of
        Core.EVar _ -> True
        Core.EAccess (Core.Expr (Core.EVar _) _ _) _ -> True
        _ -> False

-- RULE C

-- | An expression of the wrapped version's type where the version goes on,
-- rewritten to the transient's: 'conv' one level out.
convOuter :: Ck -> Names -> Core.Expr -> Maybe Core.Expr
convOuter ck v e
  | Core.EApp (Core.Expr (Core.EGlobal g) _ _) _ <- Core._exprValue e,
    g == _loop ck =
      conv ck v e
  | not (mentions v e) = Just (enterOuter ck e)
  | otherwise =
      case Core._exprValue e of
        Core.EVar x | Map.lookup x v == Just Outer -> Just (retype ck Outer e)
        Core.ELet binds body -> lets ck v binds body (convOuter ck)
        Core.ECase scrut alts fallback
          | Just popped <- popCase ck v e scrut alts fallback (convOuter ck) (outerTransient ck) -> popped
          | otherwise ->
              do
                (scrut', alts', fallback') <- matched ck v scrut alts fallback (convOuter ck)
                return (outer (Core.ECase scrut' alts' fallback'))
        Core.ECtor c tag [x]
          | c == holding (_wrap ck) ->
              do
                x' <- conv ck v x
                return (outer (Core.ECtor c tag [x']))
        Core.ECtor c tag xs
          | c == empty_ (_wrap ck) ->
              do
                xs' <- traverse (plain ck v) xs
                return (outer (Core.ECtor c tag xs'))
        Core.EApp fn [f, r]
          | Just _ <- through (_wrap ck) fn,
            Core.EApp g [x] <- Core._exprValue f,
            Just (1, 0) <- growth g,
            Core.TFun [arrT] _ <- Core.typeOf f ->
              -- @Result.map (Array.pushLast x) acc@: the partial application
              -- as a lambda, its argument bound first, where it was evaluated.
              let sp = Core.spanOf f
                  xv = Core.Expr (Core.EVar "$atX") (Core.typeOf x) (Core.spanOf x)
                  pv = Core.Binder "$atP" arrT sp
                  lam = Core.Expr (Core.ELam [pv] (Core.Expr (Core.EApp g [xv, Core.Expr (Core.EVar "$atP") arrT sp]) arrT sp)) (Core.typeOf f) sp
               in convOuter ck v (Core.Expr (Core.ELet [Core.Bind (Core.Binder "$atX" (Core.typeOf x) (Core.spanOf x)) x] (e {Core._exprValue = Core.EApp fn [lam, r]})) (Core.typeOf e) (Core.spanOf e))
        Core.EApp fn [f, r]
          | Just bound <- through (_wrap ck) fn,
            Core.ELam [p] body <- Core._exprValue f ->
              let name = Core._binderName p
                  inner = if bound then convOuter ck else conv ck
                  applied p' body' r' =
                    let lamType = Core.TFun [Core._binderType p'] (Core.typeOf body')
                        fn' = fn {Core._exprType = Core.TFun [lamType, Core.typeOf r'] (outerTransient ck)}
                     in outer (Core.EApp fn' [Core.Expr (Core.ELam [p'] body') lamType (Core.spanOf f), r'])
               in if mentions v r
                    then
                      -- The version mapped: the parameter is the array (or
                      -- record) inside, and the lambda may name no other.
                      if mentions (Map.delete name v) body
                        then Nothing
                        else do
                          r' <- convOuter ck v r
                          body' <- inner (Map.singleton name Whole) body
                          return (applied p {Core._binderType = kindType ck Whole} body' r')
                    else do
                      -- Another Result mapped, by a lambda applied once and
                      -- at once, which may grow what a `when` bound.
                      body' <- inner (Map.delete name v) body
                      return (applied p body' r)
        _ -> Nothing
  where
    outer x = Core.Expr x (outerTransient ck) (Core.spanOf e)

-- | @Result.map@ or @Maybe.map@ (False), @andThen@ (True), at the version's
-- wrapper.
through :: Wrap -> Core.Expr -> Maybe Bool
through w fn =
  case Core._exprValue fn of
    Core.EGlobal (Core.QualName home name)
      | home == (if w == InMaybe then ModuleName.maybe else ModuleName.result),
        w /= Unwrapped ->
          case takeWhile (/= '$') (Name.toChars name) of
            "map" -> Just False
            "andThen" -> Just True
            _ -> Nothing
    _ -> Nothing

-- | A @when@'s subject and branches: when the subject is a wrapped version,
-- each pattern is @Ok@ or @Just@ of a name, which is then the array (or record)
-- inside, @Err@ or @Nothing@, a wildcard, or a name for the version itself;
-- otherwise the subject is read as 'plain'.
matched :: Ck -> Names -> Core.Expr -> [Core.Alt] -> Maybe Core.Expr -> (Names -> Core.Expr -> Maybe Core.Expr) -> Maybe (Core.Expr, [Core.Alt], Maybe Core.Expr)
matched ck v scrut alts fallback k
  | Core.EVar x <- Core._exprValue scrut,
    Map.lookup x v == Just Outer =
      do
        alts' <- traverse (\(Core.Alt p b) -> do (p', v') <- unwrapped (shadow p v) p; Core.Alt p' <$> k v' b) alts
        fallback' <- traverse (k v) fallback
        return (retype ck Outer scrut, alts', fallback')
  | otherwise =
      do
        scrut' <- plain ck v scrut
        alts' <- traverse (\(Core.Alt p b) -> Core.Alt p <$> k (shadow p v) b) alts
        fallback' <- traverse (k v) fallback
        return (scrut', alts', fallback')
  where
    unwrapped v' p =
      case p of
        Core.PWild -> Just (p, v')
        Core.PVar b -> Just (Core.PVar b {Core._binderType = outerTransient ck}, Map.insert (Core._binderName b) Outer v')
        Core.PCtor c tag [Core.PVar b]
          | c == holding (_wrap ck) ->
              Just (Core.PCtor c tag [Core.PVar b {Core._binderType = kindType ck Whole}], Map.insert (Core._binderName b) Whole v')
        Core.PCtor c _ [Core.PWild] | c == holding (_wrap ck) -> Just (p, v')
        Core.PCtor c _ _ | c == empty_ (_wrap ck) -> Just (p, v')
        _ -> Nothing
