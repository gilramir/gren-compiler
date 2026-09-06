{-# OPTIONS_GHC -Wall #-}

-- | What an expression refers to, and what it leaves free.
--
-- Two walks over Core, kept together because they answer the same shape of
-- question and because three callers need one or the other: the linker asks
-- what a binding refers to ('refsIn'), and both binding orders — a module's
-- definitions and a @let@ run's bindings — ask which of a group's own names a
-- value uses ('refsIn' at the top level, 'freeLocals' inside an expression).
-- The order those two produce is @docs/core.md@ C14's, and "Core.Order" is the
-- algorithm; this module is the input to it.
module Core.Refs
  ( Refs (..),
    global,
    ctor,
    refsIn,
    portRefs,
    mainRefs,
    strictIn,
    strictPort,
    freeLocals,
    patternBinders,
  )
where

import Core.AST qualified as Core
import Data.Name (Name)
import Data.Set (Set)
import Data.Set qualified as Set

-- | What one expression refers to. One traversal, three answers, because the
-- linker needs all three of them for every binding.
data Refs = Refs
  { _refGlobals :: Set Core.QualName,
    _refCtors :: Set Core.QualName,
    _refFields :: Set Name
  }

instance Semigroup Refs where
  Refs a1 b1 c1 <> Refs a2 b2 c2 =
    Refs (Set.union a1 a2) (Set.union b1 b2) (Set.union c1 c2)

instance Monoid Refs where
  mempty = Refs Set.empty Set.empty Set.empty

global :: Core.QualName -> Refs
global q = mempty {_refGlobals = Set.singleton q}

ctor :: Core.QualName -> Refs
ctor q = mempty {_refCtors = Set.singleton q}

field :: Name -> Refs
field f = mempty {_refFields = Set.singleton f}

refsIn :: Core.Expr -> Refs
refsIn (Core.Expr value _ _) =
  case value of
    Core.EVar _ -> mempty
    Core.EGlobal q -> global q
    Core.ELit _ -> mempty
    Core.ECrash _ -> mempty
    Core.ELam _ body -> refsIn body
    Core.EApp fn args -> foldMap refsIn (fn : args)
    Core.ELet binds body -> foldMap bindRefs binds <> refsIn body
    Core.ELetRec binds body -> foldMap bindRefs binds <> refsIn body
    Core.EJoin binds body -> foldMap bindRefs binds <> refsIn body
    Core.EJump _ args -> foldMap refsIn args
    Core.ECase scrut alts fallback ->
      refsIn scrut <> foldMap altRefs alts <> foldMap refsIn fallback
    Core.ECtor q _ args -> ctor q <> foldMap refsIn args
    Core.ERecord fields -> foldMap (\(f, e) -> field f <> refsIn e) fields
    Core.EUpdate base fields -> refsIn base <> foldMap (\(f, e) -> field f <> refsIn e) fields
    Core.EAccess base f -> refsIn base <> field f
    Core.EArray items -> foldMap refsIn items
    Core.EPrim _ args -> foldMap refsIn args
    Core.ETyLam _ body -> refsIn body
    Core.ETyApp body _ -> refsIn body
    Core.EWitLam _ body -> refsIn body
    Core.EWitApp body args -> foldMap refsIn (body : args)

-- | What evaluating an expression reads __immediately__: the globals it names
-- outside any lambda.
--
-- The other half of C14. 'refsIn' answers "what must exist", which is the order
-- a program is emitted in; this answers "what must already have a value", which
-- is the order it may be evaluated in. The two agree everywhere except inside a
-- cycle, and a cycle is exactly where they have to be told apart: @Array.length@
-- and the kernel @Array@ module are mutually reachable, so one of them is
-- emitted first, and if it is the one whose right-hand side /reads/ the other
-- the program throws on load.
--
-- Shallow on purpose. @f x@ at the top level reads @f@ now and whatever @f@'s
-- body reads when it is called, and following that through would be asking which
-- values a program computes rather than which names it reads. A genuine
-- evaluation cycle is a different problem, and the one @Opt.Cycle@'s @$cyclic$@
-- thunks and its dev-mode \"infinite recursion\" message exist for.
strictIn :: Core.Expr -> Set Core.QualName
strictIn (Core.Expr value _ _) =
  case value of
    -- A lambda body does not run until the lambda is called, which is the whole
    -- distinction this function draws.
    Core.ELam _ _ -> Set.empty
    Core.EGlobal q -> Set.singleton q
    Core.EVar _ -> Set.empty
    Core.ELit _ -> Set.empty
    Core.ECrash _ -> Set.empty
    Core.EApp fn args -> foldMap strictIn (fn : args)
    Core.ELet binds body -> foldMap strictBind binds <> strictIn body
    Core.ELetRec binds body -> foldMap strictBind binds <> strictIn body
    Core.EJoin binds body -> foldMap strictBind binds <> strictIn body
    Core.EJump _ args -> foldMap strictIn args
    Core.ECase scrut alts fallback ->
      strictIn scrut <> foldMap (\(Core.Alt _ b) -> strictIn b) alts <> foldMap strictIn fallback
    Core.ECtor _ _ args -> foldMap strictIn args
    Core.ERecord fields -> foldMap (strictIn . snd) fields
    Core.EUpdate base fields -> strictIn base <> foldMap (strictIn . snd) fields
    Core.EAccess base _ -> strictIn base
    Core.EArray items -> foldMap strictIn items
    Core.EPrim _ args -> foldMap strictIn args
    Core.ETyLam _ body -> strictIn body
    Core.ETyApp body _ -> strictIn body
    Core.EWitLam _ _ -> Set.empty
    Core.EWitApp body args -> foldMap strictIn (body : args)
  where
    strictBind = strictIn . Core._bindValue

-- | A @port@'s converters are evaluated when the port is: a runtime's port
-- constructor takes the converter as a value, so the declaration is as strict as
-- an ordinary binding with the same right-hand side.
strictPort :: Core.Port -> Set Core.QualName
strictPort (Core.Port _ flow) =
  case flow of
    Core.PortOut c -> strictConv c
    Core.PortIn c -> strictConv c
    Core.PortTask input output -> foldMap strictConv input <> strictConv output
  where
    strictConv = strictIn . Core._convCode

-- | What a @port@ declaration refers to: its converters, and nothing else.
--
-- A port is a declaration rather than an expression (C18), so the linker cannot
-- reach its dependencies by walking a body. This is the body it does not have —
-- and it is why a port needs no rule of its own to stay alive, unlike an effect
-- manager: something in the program refers to the port's /name/, and the name
-- is defined here.
portRefs :: Core.Port -> Refs
portRefs (Core.Port _ flow) =
  case flow of
    Core.PortOut c -> converterRefs c
    Core.PortIn c -> converterRefs c
    Core.PortTask input output -> foldMap converterRefs input <> converterRefs output

-- | What a module's @main@ declaration refers to: its flags decoder, and
-- nothing else (C19).
--
-- The same shape as 'portRefs' and for the same reason. It is why @main@ needs
-- no rule of its own either: @main@ is a root, and these are edges out of it, so
-- the decoder is reachable exactly when the program has an entry point.
mainRefs :: Core.Main -> Refs
mainRefs m =
  case m of
    Core.MainString -> mempty
    Core.MainHtml -> mempty
    Core.MainProgram c -> converterRefs c

converterRefs :: Core.Converter -> Refs
converterRefs = refsIn . Core._convCode

bindRefs :: Core.Bind -> Refs
bindRefs = refsIn . Core._bindValue

altRefs :: Core.Alt -> Refs
altRefs (Core.Alt pattern body) = patternRefs pattern <> refsIn body

patternRefs :: Core.Pattern -> Refs
patternRefs pattern =
  case pattern of
    Core.PVar _ -> mempty
    Core.PWild -> mempty
    Core.PLit _ -> mempty
    Core.PCtor q _ args -> ctor q <> foldMap patternRefs args
    Core.PRecord fields -> foldMap (\(f, p) -> field f <> patternRefs p) fields
    Core.PArray items _ -> foldMap patternRefs items
    Core.PAs _ inner -> patternRefs inner

-- FREE LOCALS

-- | The local names an expression uses and does not itself bind.
--
-- Scoping is honoured rather than assumed: a binder shadowing an outer name
-- would otherwise show up as a use of it. @syntax.md@ D63 forbids shadowing in
-- source, so today the two answers agree everywhere — but the lowering invents
-- binders of its own (accessors, @if@ chains), and a walk that only collected
-- 'Core.EVar' names would make the guarantee depend on those inventions never
-- colliding.
--
-- 'Core.ELet' is treated as if its binds were sequential and 'Core.ELetRec' as
-- if all of its were in scope throughout, which is what C2 means by the two
-- nodes.
freeLocals :: Core.Expr -> Set Name
freeLocals (Core.Expr value _ _) =
  case value of
    Core.EVar n -> Set.singleton n
    Core.EGlobal _ -> Set.empty
    Core.ELit _ -> Set.empty
    Core.ECrash _ -> Set.empty
    Core.ELam binders body -> without binders (freeLocals body)
    Core.EApp fn args -> Set.unions (map freeLocals (fn : args))
    Core.ELet binds body ->
      Set.unions (map (freeLocals . Core._bindValue) binds)
        `Set.union` without (map Core._bindBinder binds) (freeLocals body)
    Core.ELetRec binds body ->
      without (map Core._bindBinder binds) $
        Set.unions (freeLocals body : map (freeLocals . Core._bindValue) binds)
    -- A join name is not a local: it cannot be referred to except by 'EJump',
    -- and it is in scope in the join's own body only through the jumps there.
    Core.EJoin binds body ->
      without (map Core._bindBinder binds) $
        Set.unions (freeLocals body : map (freeLocals . Core._bindValue) binds)
    Core.EJump _ args -> Set.unions (map freeLocals args)
    Core.ECase scrut alts fallback ->
      Set.unions
        ( freeLocals scrut
            : map altFree alts
            ++ map freeLocals (maybe [] pure fallback)
        )
    Core.ECtor _ _ args -> Set.unions (map freeLocals args)
    Core.ERecord fields -> Set.unions (map (freeLocals . snd) fields)
    Core.EUpdate base fields -> Set.unions (freeLocals base : map (freeLocals . snd) fields)
    Core.EAccess base _ -> freeLocals base
    Core.EArray items -> Set.unions (map freeLocals items)
    Core.EPrim _ args -> Set.unions (map freeLocals args)
    Core.ETyLam _ body -> freeLocals body
    Core.ETyApp body _ -> freeLocals body
    Core.EWitLam binders body -> without binders (freeLocals body)
    Core.EWitApp body args -> Set.unions (map freeLocals (body : args))

altFree :: Core.Alt -> Set Name
altFree (Core.Alt pattern body) =
  Set.difference (freeLocals body) (patternBinders pattern)

without :: [Core.Binder] -> Set Name -> Set Name
without binders = (`Set.difference` Set.fromList (map Core._binderName binders))

patternBinders :: Core.Pattern -> Set Name
patternBinders pattern =
  case pattern of
    Core.PVar b -> Set.singleton (Core._binderName b)
    Core.PWild -> Set.empty
    Core.PLit _ -> Set.empty
    Core.PCtor _ _ args -> Set.unions (map patternBinders args)
    Core.PRecord fields -> Set.unions (map (patternBinders . snd) fields)
    Core.PArray items tail_ ->
      Set.unions (maybe Set.empty (Set.singleton . Core._binderName) tail_ : map patternBinders items)
    Core.PAs b inner -> Set.insert (Core._binderName b) (patternBinders inner)
