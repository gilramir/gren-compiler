module Deps.Diff
  ( diff,
    Verdict (..),
    Verdicts,
    refinementCandidates,
    PackageChanges (..),
    ModuleChanges (..),
    Changes (..),
    moduleChangeMagnitude,
    toMagnitude,
    bump,
  )
where

import Control.Monad (zipWithM)
import Data.Function (on)
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Monoid qualified as Monoid
import Data.Name qualified as Name
import Data.Set qualified as Set
import Gren.Compiler.Type qualified as Type
import Gren.Docs qualified as Docs
import Gren.Magnitude qualified as M
import Gren.ModuleName qualified as ModuleName
import Gren.Version qualified as V

-- CHANGES

data PackageChanges = PackageChanges
  { _modules_added :: [ModuleName.Raw],
    _modules_changed :: Map.Map ModuleName.Raw ModuleChanges,
    _modules_removed :: [ModuleName.Raw]
  }

data ModuleChanges = ModuleChanges
  { _unions :: Changes Name.Name Docs.Union,
    _aliases :: Changes Name.Name Docs.Alias,
    _values :: Changes Name.Name Docs.Value,
    _binops :: Changes Name.Name Docs.Binop,
    -- | The verdict on each changed value whose erased type is the same and
    -- whose refinements are not (D855). A changed value not here is MAJOR.
    _valueVerdicts :: Map.Map Name.Name Verdict
  }

-- | What the refinement checker says of a value whose erased type did not
-- change and whose signature's names did (geng-lang @m4-refine.md@ §RF29,
-- D855): the magnitude entailment gives it (D807), and a line for each
-- predicate that changed, saying how.
data Verdict = Verdict M.Magnitude [String]

-- | The verdicts, by module and value.
type Verdicts =
  Map.Map (ModuleName.Raw, Name.Name) Verdict

-- | The values the type comparison cannot decide: exposed in both versions,
-- their erased types equivalent, and the names their signatures give, with
-- their predicates, not the same. The refinement checker decides each (D810).
refinementCandidates :: Docs.Documentation -> Docs.Documentation -> [(ModuleName.Raw, Name.Name)]
refinementCandidates oldDocs newDocs =
  [ (home, name)
  | (home, (Docs.Module _ _ _ _ oldValues _, Docs.Module _ _ _ _ newValues _)) <- Map.toList (Map.intersectionWith (,) oldDocs newDocs),
    (name, (old, new)) <- Map.toList (Map.intersectionWith (,) oldValues newValues),
    isEquivalentValue old new,
    not (sameNamed old new)
  ]

sameNamed :: Docs.Value -> Docs.Value -> Bool
sameNamed (Docs.Value _ _ n1) (Docs.Value _ _ n2) =
  map key n1 == map key n2
  where
    key (Docs.Named path name source) = (path, name, source)

data Changes k v = Changes
  { _added :: Map.Map k v,
    _changed :: Map.Map k (v, v),
    _removed :: Map.Map k v
  }

getChanges :: (Ord k) => (v -> v -> Bool) -> Map.Map k v -> Map.Map k v -> Changes k v
getChanges isEquivalent old new =
  let overlap = Map.intersectionWith (,) old new
      changed = Map.filter (not . uncurry isEquivalent) overlap
   in Changes (Map.difference new old) changed (Map.difference old new)

-- DIFF

-- | The changes from one version's documentation to the next. A value whose
-- erased type is the same and whose refinements are not has the magnitude its
-- verdict gives, and is no change at all when that is PATCH (D855).
diff :: Verdicts -> Docs.Documentation -> Docs.Documentation -> PackageChanges
diff verdicts oldDocs newDocs =
  let filterOutPatches chngs =
        Map.filter (\chng -> moduleChangeMagnitude chng /= M.PATCH) chngs

      (Changes added changed removed) =
        getChanges (\_ _ -> False) oldDocs newDocs
   in PackageChanges
        (Map.keys added)
        (filterOutPatches (Map.mapWithKey (diffModule verdicts) changed))
        (Map.keys removed)

diffModule :: Verdicts -> ModuleName.Raw -> (Docs.Module, Docs.Module) -> ModuleChanges
diffModule verdicts home (Docs.Module _ _ u1 a1 v1 b1, Docs.Module _ _ u2 a2 v2 b2) =
  let verdictOf name old new
        | not (isEquivalentValue old new) = Nothing
        | sameNamed old new = Just (Verdict M.PATCH [])
        | otherwise =
            Just $
              Map.findWithDefault
                (Verdict M.MAJOR ["The refinement checker did not compare this signature's refinements."])
                (home, name)
                verdicts

      equivalent name old new =
        case verdictOf name old new of
          Just (Verdict M.PATCH _) -> True
          _ -> False

      values =
        getChangesWithKey equivalent v1 v2

      valueVerdicts =
        Map.mapMaybeWithKey (\name (old, new) -> verdictOf name old new) (_changed values)
   in ModuleChanges
        (getChanges isEquivalentUnion u1 u2)
        (getChanges isEquivalentAlias a1 a2)
        values
        (getChanges isEquivalentBinop b1 b2)
        valueVerdicts

getChangesWithKey :: (Ord k) => (k -> v -> v -> Bool) -> Map.Map k v -> Map.Map k v -> Changes k v
getChangesWithKey isEquivalent old new =
  let overlap = Map.intersectionWith (,) old new
      changed = Map.filterWithKey (\k (o, n) -> not (isEquivalent k o n)) overlap
   in Changes (Map.difference new old) changed (Map.difference old new)

-- EQUIVALENCE

isEquivalentUnion :: Docs.Union -> Docs.Union -> Bool
isEquivalentUnion (Docs.Union oldComment oldVars oldCtors) (Docs.Union newComment newVars newCtors) =
  length oldCtors == length newCtors
    && and (zipWith (==) (map fst oldCtors) (map fst newCtors))
    && and (Map.elems (Map.intersectionWith equiv (Map.fromList oldCtors) (Map.fromList newCtors)))
  where
    equiv :: [Type.Type] -> [Type.Type] -> Bool
    equiv oldTypes newTypes =
      let allEquivalent =
            zipWith
              isEquivalentAlias
              (map (Docs.Alias oldComment oldVars) oldTypes)
              (map (Docs.Alias newComment newVars) newTypes)
       in length oldTypes == length newTypes
            && and allEquivalent

isEquivalentAlias :: Docs.Alias -> Docs.Alias -> Bool
isEquivalentAlias (Docs.Alias _ oldVars oldType) (Docs.Alias _ newVars newType) =
  case diffType oldType newType of
    Nothing ->
      False
    Just renamings ->
      length oldVars == length newVars
        && isEquivalentRenaming (zip oldVars newVars ++ renamings)

isEquivalentValue :: Docs.Value -> Docs.Value -> Bool
isEquivalentValue (Docs.Value c1 t1 _) (Docs.Value c2 t2 _) =
  isEquivalentAlias (Docs.Alias c1 [] t1) (Docs.Alias c2 [] t2)

isEquivalentBinop :: Docs.Binop -> Docs.Binop -> Bool
isEquivalentBinop (Docs.Binop c1 t1 a1 p1) (Docs.Binop c2 t2 a2 p2) =
  isEquivalentAlias (Docs.Alias c1 [] t1) (Docs.Alias c2 [] t2)
    && a1 == a2
    && p1 == p2

-- DIFF TYPES

diffType :: Type.Type -> Type.Type -> Maybe [(Name.Name, Name.Name)]
diffType oldType newType =
  case (oldType, newType) of
    (Type.Var oldName, Type.Var newName) ->
      Just [(oldName, newName)]
    (Type.Lambda a b, Type.Lambda a' b') ->
      (++)
        <$> diffType a a'
        <*> diffType b b'
    (Type.Type oldName oldArgs, Type.Type newName newArgs) ->
      if not (isSameName oldName newName) || length oldArgs /= length newArgs
        then Nothing
        else concat <$> zipWithM diffType oldArgs newArgs
    (Type.Record fields maybeExt, Type.Record fields' maybeExt') ->
      case (maybeExt, maybeExt') of
        (Nothing, Just _) ->
          Nothing
        (Just _, Nothing) ->
          Nothing
        (Nothing, Nothing) ->
          diffFields fields fields'
        (Just oldExt, Just newExt) ->
          (:) (oldExt, newExt) <$> diffFields fields fields'
    (_, _) ->
      Nothing

-- handle very old docs that do not use qualified names
isSameName :: Name.Name -> Name.Name -> Bool
isSameName oldFullName newFullName =
  let dedot name =
        reverse (Name.splitDots name)
   in case (dedot oldFullName, dedot newFullName) of
        (oldName : [], newName : _) ->
          oldName == newName
        (oldName : _, newName : []) ->
          oldName == newName
        _ ->
          oldFullName == newFullName

diffFields :: [(Name.Name, Type.Type)] -> [(Name.Name, Type.Type)] -> Maybe [(Name.Name, Name.Name)]
diffFields oldRawFields newRawFields =
  let sort = List.sortBy (compare `on` fst)
      oldFields = sort oldRawFields
      newFields = sort newRawFields
   in if length oldRawFields /= length newRawFields
        then Nothing
        else
          if or (zipWith ((/=) `on` fst) oldFields newFields)
            then Nothing
            else concat <$> zipWithM (diffType `on` snd) oldFields newFields

-- TYPE VARIABLES

isEquivalentRenaming :: [(Name.Name, Name.Name)] -> Bool
isEquivalentRenaming varPairs =
  let renamings =
        Map.toList (foldr insert Map.empty varPairs)

      insert (old, new) dict =
        Map.insertWith (++) old [new] dict

      verify (old, news) =
        case news of
          [] ->
            Nothing
          new : rest ->
            if all (new ==) rest
              then Just (old, new)
              else Nothing

      allUnique list =
        length list == Set.size (Set.fromList list)
   in case mapM verify renamings of
        Nothing ->
          False
        Just verifiedRenamings ->
          all compatibleVars verifiedRenamings
            && allUnique (map snd verifiedRenamings)

-- | Whether renaming a published signature's type variable is a breaking
-- change.
--
-- __It is not, ever.__ This had four categories and now has none.
-- `comparable` and `compappend` went when `core` declared `Ord`
-- (`docs/m1b-classes.md` §G29) and `number` and `appendable` go with D135, so
-- every type variable in a published signature is an ordinary name that can be
-- renamed to any other. What a variable is constrained by is written in the
-- __context__ now, and a context is part of the signature this compares — so
-- the question this function used to answer is asked somewhere it can be
-- answered exactly, instead of being guessed from a spelling.
compatibleVars :: (Name.Name, Name.Name) -> Bool
compatibleVars _ =
  True

-- MAGNITUDE

bump :: PackageChanges -> V.Version -> V.Version
bump changes version =
  case toMagnitude changes of
    M.PATCH ->
      V.bumpPatch version
    M.MINOR ->
      V.bumpMinor version
    M.MAJOR ->
      V.bumpMajor version

toMagnitude :: PackageChanges -> M.Magnitude
toMagnitude (PackageChanges added changed removed) =
  let addMag = if null added then M.PATCH else M.MINOR
      removeMag = if null removed then M.PATCH else M.MAJOR
      changeMags = map moduleChangeMagnitude (Map.elems changed)
   in maximum (addMag : removeMag : changeMags)

moduleChangeMagnitude :: ModuleChanges -> M.Magnitude
moduleChangeMagnitude (ModuleChanges unions aliases values binops verdicts) =
  maximum
    [ unionChangeMagnitude unions,
      changeMagnitude aliases,
      valueChangeMagnitude values verdicts,
      changeMagnitude binops
    ]

-- | A changed value is MAJOR unless the refinement checker's verdict on it
-- says less (D855).
valueChangeMagnitude :: Changes Name.Name Docs.Value -> Map.Map Name.Name Verdict -> M.Magnitude
valueChangeMagnitude (Changes added changed removed) verdicts
  | Map.size removed > 0 = M.MAJOR
  | otherwise =
      maximum
        ( (if Map.size added > 0 then M.MINOR else M.PATCH)
            : [ maybe M.MAJOR (\(Verdict m _) -> m) (Map.lookup name verdicts)
              | name <- Map.keys changed
              ]
        )

changeMagnitude :: Changes k v -> M.Magnitude
changeMagnitude (Changes added changed removed)
  | Map.size removed > 0 || Map.size changed > 0 = M.MAJOR
  | Map.size added > 0 = M.MINOR
  | otherwise = M.PATCH

unionChangeMagnitude :: Changes Name.Name Docs.Union -> M.Magnitude
unionChangeMagnitude (Changes added changed removed)
  | Map.size removed > 0 = M.MAJOR
  | Map.size changed > 0 = unionChangesMagnitude changed
  | Map.size added > 0 = M.MINOR
  | otherwise = M.PATCH

unionChangesMagnitude :: Map.Map Name.Name (Docs.Union, Docs.Union) -> M.Magnitude
unionChangesMagnitude unionChanges =
  if Monoid.getAll $
    Map.foldMapWithKey
      ( \_ (Docs.Union _ _ oldConstructors, Docs.Union _ _ newConstructors) ->
          Monoid.All (List.null oldConstructors && not (List.null newConstructors))
      )
      unionChanges
    then M.MINOR
    else M.MAJOR
