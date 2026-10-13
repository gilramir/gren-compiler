{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | An @Array@ a loop only appends to, grown through C7's transient (geng-lang
-- D656, D697; @m3-pushlast.md@ §PL5, §PL16).
--
-- > rec i n acc = if i > n then acc else rec (i + 1) n (Array.pushLast (next i) acc)
-- >   ⟹ rec i n acc = tr_to_array (rec$at i n (tr_from_array acc))
-- >      rec$at i n acc = if i > n then acc else rec$at (i + 1) n (tr_push acc (next i))
--
-- __Which loops__: D583's ("Core.Pass.Transient"): a top-level function that
-- calls itself, every use of its own name a saturated call outside any
-- lambda, so a fold "Core.Pass.FoldSpec" has copied for its lambda is one. Its
-- /version/ is a parameter that is an @Array a@ (D697's rule A) or a closed
-- record with an @Array a@ field (rule B), and the loop answers that same
-- type.
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
--     and a record built or updated with a growth of the field in its place.
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
-- __The BEAM's__ (D703): natively and on JavaScript an @Array@ is a slice, on
-- which a push already writes in place, so 'Core.Pass.defaults' runs this on
-- the BEAM alone, whose @Array@ is a tuple every push copies. A list naming
-- @arraytr@ in @GENG_CORE_PASSES@ runs it anywhere, which is how the corpus
-- holds it on node.
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
import Data.Monoid (Any (..))
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName

run :: Map ModuleName.Canonical Core.Module -> Map ModuleName.Canonical Core.Module
run = Map.mapWithKey module_

module_ :: ModuleName.Canonical -> Core.Module -> Core.Module
module_ home modul =
  let results = [(b, v, loop (Core.QualName home (Core._binderName b)) v) | Core.Bind b v <- Core._moduleDefs modul]
   in if null [() | (_, _, Just _) <- results]
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

-- SHAPES

-- | What the version is: an array of the element type (rule A), or a closed
-- record whose named field is one (rule B), with all its fields.
data Shape
  = Bare Core.Type
  | Field Name Core.Type [(Name, Core.Type)]

-- | What a name the rule follows stands for: the version itself, or, under
-- rule B, the version's array field.
data Kind = Whole | Part
  deriving (Eq)

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

kindType :: Shape -> Kind -> Core.Type
kindType s k =
  case k of
    Whole -> transientType s
    Part -> tTransient (element s)

tTransient :: Core.Type -> Core.Type
tTransient e = Core.TCon (Core.QualName ModuleName.arrayTransient "Transient") [e]

arrayType :: Core.QualName
arrayType = Core.QualName ModuleName.array "Array"

tInt :: Core.Type
tInt = Core.TCon (Core.QualName ModuleName.basics "Int") []

-- THE LOOP

-- | A loop's entry and its copy, when one of its parameters passes the rule.
loop :: Core.QualName -> Core.Expr -> Maybe (Core.Expr, Core.Bind)
loop q value =
  case value of
    Core.Expr (Core.ELam ps body) (Core.TFun ts r) sp
      | Transient.selfOnly q (length ps) body,
        Transient.calls q body ->
          firstJust
            [ attempt q ps ts r sp body i s
            | (i, p) <- zip [0 ..] ps,
              s <- shapes (Core._binderType p),
              versionType s == r
            ]
    _ -> Nothing

firstJust :: [Maybe a] -> Maybe a
firstJust xs = case [x | Just x <- xs] of
  x : _ -> Just x
  [] -> Nothing

attempt :: Core.QualName -> [Core.Binder] -> [Core.Type] -> Core.Type -> Core.Span -> Core.Expr -> Int -> Shape -> Maybe (Core.Expr, Core.Bind)
attempt q ps ts r sp body pos s =
  let qt = Core.QualName (Core._qnHome q) (Name.fromChars (Name.toChars (Core._qnName q) ++ "$at"))
      tt = transientType s
      copyType = Core.TFun [if j == pos then tt else t | (j, t) <- zip [0 ..] ts] tt
      p = ps !! pos
      ck = Ck q qt copyType (length ps) pos s
   in do
        body' <- conv ck (Map.singleton (Core._binderName p) Whole) body
        if grows body'
          then
            let ps' = [if j == pos then b {Core._binderType = tt} else b | (j, b) <- zip [0 :: Int ..] ps]
                copy = Core.Expr (Core.ELam ps' body') copyType sp
                args = [if j == pos then enter s (var b) else var b | (j, b) <- zip [0 ..] ps]
                entered = Core.Expr (Core.EApp (Core.Expr (Core.EGlobal qt) copyType sp) args) tt sp
                entry = Core.Expr (Core.ELam ps (leave s entered)) (Core.TFun ts r) sp
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

data Ck = Ck
  { _loop :: Core.QualName,
    _copy :: Core.QualName,
    _copyType :: Core.Type,
    _arity :: Int,
    _pos :: Int,
    _shape :: Shape
  }

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
        args' <- sequence [if j == _pos ck then conv ck v a else plain ck v a | (j, a) <- zip [0 ..] args]
        return (Core.Expr (Core.EApp (Core.Expr (Core.EGlobal (_copy ck)) (_copyType ck) fsp) args') (transientType (_shape ck)) (Core.spanOf e))
  | not (mentions v e) = Just (enter (_shape ck) e)
  | otherwise =
      case Core._exprValue e of
        Core.EVar x | Map.lookup x v == Just Whole -> Just (retype ck Whole e)
        Core.ELet binds body -> lets ck v binds body (conv ck)
        Core.ECase scrut alts fallback ->
          do
            scrut' <- plain ck v scrut
            alts' <- traverse (\(Core.Alt p b) -> Core.Alt p <$> conv ck (shadow p v) b) alts
            fallback' <- traverse (conv ck v) fallback
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
        Core.ECase scrut alts fallback ->
          do
            scrut' <- plain ck v scrut
            alts' <- traverse (\(Core.Alt p b) -> Core.Alt p <$> grow ck (shadow p v) b) alts
            fallback' <- traverse (grow ck v) fallback
            return (Core.Expr (Core.ECase scrut' alts' fallback') tt (Core.spanOf e))
        Core.EApp fn args
          | Just (arrayAt, itemsAt) <- growth fn,
            length args == 2 ->
              do
                arr <- grow ck v (args !! arrayAt)
                let other = args !! itemsAt
                items <-
                  if arrayAt == 1 && itemsAt == 0 && isPushLast fn
                    then (: []) <$> plain ck v other
                    else case Core._exprValue other of
                      Core.EArray xs -> traverse (plain ck v) xs
                      _ -> Nothing
                return (foldl (\t x -> prim Prim.TrPush [t, x] tt) arr items)
        _ -> Nothing
  where
    tt = tTransient (element (_shape ck))

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
          Just (Core.Expr (Core.EAccess (retype ck Whole r) g) (kindType (_shape ck) Part) (Core.spanOf e))
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
            scrut' <- plain ck v scrut
            alts' <- traverse (\(Core.Alt p b) -> Core.Alt p <$> plain ck (shadow p v) b) alts
            fallback' <- traverse (plain ck v) fallback
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
              as k r' = go (Map.insert name k v) (Core.Bind b {Core._binderType = kindType (_shape ck) k} r' : acc) rest
           in if not (mentions v r)
                then go without (Core.Bind b r : acc) rest
                else case wholeOrPart v r of
                  Just (k, r') -> as k r'
                  Nothing ->
                    do
                      r' <- plain ck v r
                      go without (Core.Bind b r' : acc) rest
    wholeOrPart v r
      | Core.typeOf r == versionType (_shape ck), Just r' <- conv ck v r = Just (Whole, r')
      | Field {} <- _shape ck, Core.typeOf r == Core.TCon arrayType [element (_shape ck)], Just r' <- grow ck v r = Just (Part, r')
      | otherwise = Nothing

-- | The names a pattern binds are not the version's any more.
shadow :: Core.Pattern -> Names -> Names
shadow p v = foldr Map.delete v (Set.toList (Refs.patternBinders p))

-- | A name the rule follows, given the transient's type.
retype :: Ck -> Kind -> Core.Expr -> Core.Expr
retype ck k e = e {Core._exprType = kindType (_shape ck) k}
