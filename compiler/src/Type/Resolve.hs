{-# OPTIONS_GHC -Wall #-}

-- | Pick an instance for every class-method call (@docs/m1b-classes.md@ §G23).
--
-- This is verb 3's last step and the one with no existing shape to copy. What
-- it does is small, and it is small because of where it runs.
--
-- __It runs after the solve, because the type at the call is the input.__
-- `size x` resolves to whatever instance `x`'s type has, and the canonicalizer
-- does not know that type — a method use canonicalizes to a
-- 'AST.Canonical.VarMethod' naming its class and nothing else. The solver
-- records what each use's class parameter came out as ('Type.Solve.MethodUse'),
-- so the question here is a map lookup rather than a search.
--
-- __It runs before the lowering, because a bad program is a program.__
-- @Core.Lower@ is total and reports nothing; the answer to `size` on a type
-- with no instance is an error a person reads, so it has to be produced by a
-- phase that can produce one. The lowering then reads the answers and is
-- total, exactly as it is with node types.
--
-- __What it produces is a name.__ D123: an instance method is a Core binding
-- with a compiler-made name, so a resolved call is an ordinary reference to an
-- ordinary definition and every pass, DCE and backend already knows what to do
-- with it. The name is on the 'AST.Canonical.InstanceHead' the lookup returns,
-- which is why nothing here has to agree with anything elsewhere about how to
-- spell one.
module Type.Resolve
  ( Resolutions,
    run,
  )
where

import AST.Canonical qualified as Can
import AST.Utils.Type qualified as Type
import Data.Map.Strict qualified as Map
import Data.Name qualified as Name
import Data.NonEmptyList qualified as NE
import Gren.ModuleName qualified as ModuleName
import Reporting.Error.Instance qualified as E
import Type.Solve qualified as Solve

-- | Where each class-method call goes: the module the instance is declared in,
-- and the name of the method's binding in it.
type Resolutions =
  Map.Map Can.NodeId (ModuleName.Canonical, Name.Name)

-- | Resolve every use, or report every use that cannot be.
--
-- Every one of them, rather than the first: they are independent questions
-- about independent call sites, and a person fixing one wants to see the rest.
run ::
  Map.Map Can.InstanceKey Can.InstanceHead ->
  Map.Map Can.NodeId Solve.MethodUse ->
  Either (NE.List E.Error) Resolutions
run instances uses =
  let answers = Map.map (resolve instances) uses
   in -- In node order, which is the order the canonicalizer numbered them in
      -- and so the order they were written in.
      case [err | Left err <- Map.elems answers] of
        [] ->
          Right (Map.mapMaybe (either (const Nothing) Just) answers)
        err : errs ->
          Left (NE.List err errs)

resolve ::
  Map.Map Can.InstanceKey Can.InstanceHead ->
  Solve.MethodUse ->
  Either E.Error (ModuleName.Canonical, Name.Name)
resolve instances (Solve.MethodUse useRegion cls method param) =
  case Type.iteratedDealias param of
    Can.TVar name ->
      Left (E.NotResolved useRegion cls method name)
    Can.TType home name _ ->
      case Map.lookup (Can.InstanceKey cls home name) instances of
        Just head_ ->
          Right (Can._ih_home head_, Can.instanceMethodName head_ method)
        Nothing ->
          Left (E.NoInstance useRegion cls method param)
    _ ->
      -- A function or a record. An instance head is a type constructor applied
      -- to arguments (§G22.1), so neither can ever have one and the answer is
      -- the same "there is no instance" a missing declaration gets.
      Left (E.NoInstance useRegion cls method param)
