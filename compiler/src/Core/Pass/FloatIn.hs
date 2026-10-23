{-# OPTIONS_GHC -Wall #-}

-- | A @let@ binding that one alternative of a @case@ reads moves into that
-- alternative, and one that nothing reads goes (geng-lang @docs/m3-floatin.md@,
-- D878–D884):
--
-- > let x = e in case s of A -> …x… ; B -> …     ⟹     case s of A -> (let x = e in …x…) ; B -> …
--
-- A step that pushes onto one @Array@ twice in a @let@ and keeps one with an
-- @if@ then pushes once, and is linear where it was quadratic (§FI2).
--
-- __Where a binding moves__ (§FI3). Only a binding of a non-recursive
-- 'Core.ELet', and only through what is evaluated exactly once whenever the
-- @let@'s body is: a nested @let@'s body, a @case@'s scrutinee, and the
-- operands of a call, a constructor, a record, an update, an access, an array
-- literal and a primitive. It goes into the one alternative of a @case@ that
-- reads it, when no other alternative, the scrutinee and the fallback do not;
-- a walk that ends anywhere else moves nothing. It never enters a lambda, a
-- recursive group or a join, which could run it a different number of times.
-- Nothing it passes may bind its name or a name its right-hand side reads.
--
-- __What may move__ (§FI4, C2). Core is strict, so a binding is evaluated
-- whether or not it is read; moving it is unobservable only when evaluating it
-- writes nothing. C2's barrier is @debug_log@: no pass may eliminate one. A
-- binding moves, or goes, only if its right-hand side is a lambda (making a
-- closure runs none of it), or else it:
--
--   * contains no @debug_log@, inside a lambda or not, since a lambda it makes
--     may be called while it is evaluated;
--   * names no global from which a @debug_log@ is reachable ('logging'); and
--   * names no local value whose type can hold a function ('holdsFunction'):
--     whatever it hands that value to may call it, and its body is unknown.
--
-- The last is not relaxed for a program that never logs: the passes see every
-- module but not the roots, so they cannot tell, and a log added in one place
-- would change what moves everywhere else (D880).
--
-- __Crashes__ (D884). A binding that would crash with @Debug.todo@ or by
-- running out of stack or memory crashes only where it is read: a program that
-- finished before finishes with the same answer.
--
-- With @GENG_FLOATIN_CENSUS=<file>@ it appends a line for each binding it
-- looks at: module, definition, binding, outcome, and @grows@ when the binding
-- grows an @Array@. A report only; the Core is the pass's either way.
module Core.Pass.FloatIn
  ( Program,
    program,
    run,
  )
where

import Core.AST qualified as Core
import Core.Pass.Specialize qualified as Specialize
import Core.Prim qualified as Prim
import Core.Refs qualified as Refs
import Data.Functor.Identity (Identity (..))
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Monoid (Any (..))
import Data.Name (Name)
import Data.Name qualified as Name
import Data.Set (Set)
import Data.Set qualified as Set
import Gren.ModuleName qualified as ModuleName
import System.Environment qualified as Env
import System.IO.Unsafe (unsafePerformIO)

-- THE PROGRAM

-- | What the pass needs to know of every module: the globals from which a
-- @debug_log@ is reachable, and the data types whose values can hold a
-- function whatever their arguments are.
data Program = Program
  { _logging :: !(Set Core.QualName),
    _functional :: !(Set Core.QualName)
  }

program :: Map ModuleName.Canonical Core.Module -> Program
program cores =
  Program (logging (Map.elems cores)) (functional (Map.elems cores))

-- | Every global whose definition contains a @debug_log@, and every global
-- that names one of those, to a fixed point.
logging :: [Core.Module] -> Set Core.QualName
logging modules =
  let defs =
        [ (Core.QualName (Core._moduleName m) (Core._binderName b), v)
        | m <- modules,
          Core.Bind b v <- Core._moduleDefs m
        ]
      direct = Set.fromList [q | (q, v) <- defs, hasLog v]
      users =
        Map.fromListWith
          Set.union
          [(g, Set.singleton q) | (q, v) <- defs, g <- Set.toList (Refs._refGlobals (Refs.refsIn v))]
      grow seen frontier =
        case frontier of
          [] -> seen
          q : rest ->
            let new = Set.toList (Set.difference (Map.findWithDefault Set.empty q users) seen)
             in grow (foldr Set.insert seen new) (new ++ rest)
   in grow direct (Set.toList direct)

-- | The data types one of whose constructors has a field that can hold a
-- function apart from the type's own parameters: a function, a type variable
-- that is not a parameter, an open record, or a type in this set. A
-- parameter is answered by the argument where the type is used.
functional :: [Core.Module] -> Set Core.QualName
functional modules =
  let decls = concatMap Core._moduleData modules
      holds known decl =
        let params = Set.fromList (Core._dataParams decl)
         in any (any (fieldHolds known params) . Core._ctorFields) (Core._dataCtors decl)
      fixed known =
        let next = Set.fromList [Core._dataName d | d <- decls, holds known d]
         in if next == known then known else fixed next
   in fixed Set.empty

fieldHolds :: Set Core.QualName -> Set Name -> Core.Type -> Bool
fieldHolds known params t =
  case t of
    Core.TVar n -> not (Set.member n params)
    Core.TFun _ _ -> True
    Core.TCon q args -> Set.member q known || any (fieldHolds known params) args
    Core.TRecord fields row -> row /= Nothing || any (fieldHolds known params . snd) fields
    Core.TForall _ _ body -> fieldHolds known params body

-- | Whether a value of a type can hold a function: one of its own, or one
-- inside it. A type variable can stand for one.
holdsFunction :: Program -> Core.Type -> Bool
holdsFunction p t =
  case t of
    Core.TVar _ -> True
    Core.TFun _ _ -> True
    Core.TCon q args -> Set.member q (_functional p) || any (holdsFunction p) args
    Core.TRecord fields row -> row /= Nothing || any (holdsFunction p . snd) fields
    Core.TForall _ _ body -> holdsFunction p body

hasLog :: Core.Expr -> Bool
hasLog e =
  case Core._exprValue e of
    Core.EPrim Prim.DebugLog _ -> True
    _ -> getAny (Specialize.children_ (Any . hasLog) e)

-- | Why a binding's right-hand side may not move, if it may not.
refusal :: Program -> Core.Expr -> Maybe String
refusal p e
  | Core.ELam _ _ <- Core._exprValue e = Nothing
  | hasLog e = Just "log"
  | not (Set.disjoint (_logging p) (Refs._refGlobals (Refs.refsIn e))) = Just "logging-global"
  | any (holdsFunction p) (freeVarTypes e) = Just "function-value"
  | otherwise = Nothing

-- | The types of the locals an expression reads that it does not bind.
freeVarTypes :: Core.Expr -> [Core.Type]
freeVarTypes e =
  let free = Refs.freeLocals e
      go x =
        case Core._exprValue x of
          Core.EVar n | Set.member n free -> [Core.typeOf x]
          _ -> Specialize.children_ go x
   in go e

-- THE PASS

run :: Program -> Core.Module -> Core.Module
run p m =
  let ModuleName.Canonical _ home = Core._moduleName m
      done = [topLevel p home b | b <- Core._moduleDefs m]
   in report (concatMap snd done) (m {Core._moduleDefs = map fst done})

type Line = [String]

topLevel :: Program -> Name -> Core.Bind -> (Core.Bind, [Line])
topLevel p home (Core.Bind b v) =
  let (v', lines_) = walk p v
      tag l = Name.toChars home : Name.toChars (Core._binderName b) : l
   in (Core.Bind b v', map tag lines_)

-- | Top down: a binding moved into an alternative is looked at again there,
-- and so goes as deep as it can.
walk :: Program -> Core.Expr -> (Core.Expr, [Line])
walk p e =
  case Core._exprValue e of
    Core.ELet binds body ->
      let (kept, body', lines1) = sinkRun p binds body
          (body'', lines2) = walk p body'
          walked = [let (v', l) = walk p v in (Core.Bind x v', l) | Core.Bind x v <- kept]
          e' = if null kept then body'' else e {Core._exprValue = Core.ELet (map fst walked) body''}
       in (e', lines1 ++ concatMap snd walked ++ lines2)
    _ ->
      ( runIdentity (Specialize.childrenA (Identity . fst . walk p) e),
        Specialize.children_ (snd . walk p) e
      )

-- | A run's bindings, last first, each moved into the body or dropped when it
-- may be. C14's order is kept among those that stay.
--
-- What the bindings already kept read and bind is carried as two sets, and
-- whether the body reads a name is 'occursFree', which stops at the first
-- read: a chain of N one-binding @let@s, each reading the last, is then
-- looked at in time linear in N, where building the free set of the rest at
-- each level was N² (@source/let@'s probe, §FI12).
sinkRun :: Program -> [Core.Bind] -> Core.Expr -> ([Core.Bind], Core.Expr, [Line])
sinkRun p binds body =
  let (kept, _, _, body', lines_) = foldr step ([], Set.empty, Set.empty, body, []) binds
   in (kept, body', lines_)
  where
    step b (after, afterNames, afterReads, body0, lines_) =
      let x = name b
          rhs = Core._bindValue b
          rhsFree = Refs.freeLocals rhs
          readAfter = Set.member x afterReads
          crossesAfter = Set.member x afterNames || not (Set.disjoint rhsFree afterNames)
          line outcome = [Name.toChars x, outcome, if growsArray rhs then "grows" else "-"]
          keep why =
            ( b : after,
              Set.insert x afterNames,
              Set.union rhsFree afterReads,
              body0,
              maybe lines_ (\w -> line w : lines_) why
            )
       in if readAfter
            then keep Nothing
            else
              if not (occursFree x body0)
                then case refusal p rhs of
                  Nothing -> (after, afterNames, afterReads, body0, line "dropped" : lines_)
                  Just why -> keep (Just ("refused-" ++ why))
                else
                  if crossesAfter
                    then keep Nothing
                    else case sink b rhsFree body0 of
                      Nothing -> keep (Just "stays")
                      Just body1 ->
                        case refusal p rhs of
                          Just why -> keep (Just ("refused-" ++ why))
                          Nothing -> (after, afterNames, afterReads, body1, line "moved" : lines_)
    name = Core._binderName . Core._bindBinder

-- | Whether a local is read, unbound, in an expression: 'Refs.freeLocals'
-- asked about one name, stopping at the first read it finds.
occursFree :: Name -> Core.Expr -> Bool
occursFree x e =
  case Core._exprValue e of
    Core.EVar n -> n == x
    Core.ELam binders body -> not (binds binders) && occursFree x body
    Core.EWitLam binders body -> not (binds binders) && occursFree x body
    Core.ELet bs body ->
      any (occursFree x . Core._bindValue) bs
        || (not (binds (map Core._bindBinder bs)) && occursFree x body)
    Core.ELetRec bs body -> letrec bs body
    Core.EJoin bs body -> letrec bs body
    Core.ECase scrut alts fallback ->
      occursFree x scrut
        || any alt alts
        || any (occursFree x) fallback
    _ -> getAny (Specialize.children_ (Any . occursFree x) e)
  where
    binds = any ((== x) . Core._binderName)
    letrec bs body =
      not (binds (map Core._bindBinder bs))
        && (occursFree x body || any (occursFree x . Core._bindValue) bs)
    alt (Core.Alt pattern body) =
      not (Set.member x (Refs.patternBinders pattern)) && occursFree x body

-- | The expression with the binding pushed into the one alternative that reads
-- it, or 'Nothing' when the walk does not end in one.
sink :: Core.Bind -> Set Name -> Core.Expr -> Maybe Core.Expr
sink b rhsFree e =
  case Core._exprValue e of
    Core.ELet inner body
      | not (any (readsX . Core._bindValue) inner),
        not (any (clash . Core._binderName . Core._bindBinder) inner) -> do
          body' <- sink b rhsFree body
          Just e {Core._exprValue = Core.ELet inner body'}
    Core.ECase scrut alts fallback
      | not (readsX scrut),
        not (any readsX fallback),
        [(i, alt)] <- [(i, a) | (i, a) <- zip [0 :: Int ..] alts, readsX (Core._altBody a)],
        not (any clash (Set.toList (Refs.patternBinders (Core._altPattern alt)))) ->
          let body = Core._altBody alt
              placed = maybe (wrap body) id (sink b rhsFree body)
              alts' = [if j == i then alt {Core._altBody = placed} else a | (j, a) <- zip [0 ..] alts]
           in Just e {Core._exprValue = Core.ECase scrut alts' fallback}
    Core.ECase scrut alts fallback
      | not (any (readsX . Core._altBody) alts),
        not (any readsX fallback) -> do
          scrut' <- sink b rhsFree scrut
          Just e {Core._exprValue = Core.ECase scrut' alts fallback}
    v
      | Just (operands, rebuild) <- once v,
        [i] <- [i | (i, c) <- zip [0 :: Int ..] operands, readsX c] -> do
          c' <- sink b rhsFree (operands !! i)
          Just e {Core._exprValue = rebuild [if j == i then c' else c | (j, c) <- zip [0 ..] operands]}
    _ -> Nothing
  where
    x = Core._binderName (Core._bindBinder b)
    readsX = occursFree x
    clash n = n == x || Set.member n rhsFree
    wrap inner = Core.Expr (Core.ELet [b] inner) (Core.typeOf inner) (Core.spanOf inner)

-- | The operands evaluated exactly once whenever their node is, and the node
-- rebuilt from them.
once :: Core.Expr_ -> Maybe ([Core.Expr], [Core.Expr] -> Core.Expr_)
once v =
  case v of
    Core.EApp fn args -> Just (fn : args, \cs -> case cs of f : as -> Core.EApp f as; [] -> v)
    Core.ECtor q t args -> Just (args, Core.ECtor q t)
    Core.ERecord fields -> Just (map snd fields, Core.ERecord . zip (map fst fields))
    Core.EUpdate base fields -> Just (base : map snd fields, \cs -> case cs of r : fs -> Core.EUpdate r (zip (map fst fields) fs); [] -> v)
    Core.EAccess base f -> Just ([base], \cs -> case cs of r : _ -> Core.EAccess r f; [] -> v)
    Core.EArray items -> Just (items, Core.EArray)
    Core.EPrim op args -> Just (args, Core.EPrim op)
    _ -> Nothing

-- THE CENSUS

census :: Maybe FilePath
census = unsafePerformIO (Env.lookupEnv "GENG_FLOATIN_CENSUS")
{-# NOINLINE census #-}

report :: [Line] -> a -> a
report lines_ out =
  case census of
    Nothing -> out
    Just path ->
      unsafePerformIO $ do
        appendFile path (unlines (map (List.intercalate "\t") lines_))
        return out

growsArray :: Core.Expr -> Bool
growsArray e =
  case Core._exprValue e of
    Core.EPrim (Prim.ArrOp op) _ | op `elem` [Prim.AAppend, Prim.AInsert] -> True
    Core.EGlobal (Core.QualName (ModuleName.Canonical _ m) n)
      | Name.toChars m == "Array",
        Name.toChars n `elem` ["pushLast", "pushFirst", "append", "prepend", "insertAt"] ->
          True
    _ -> getAny (Specialize.children_ (Any . growsArray) e)
