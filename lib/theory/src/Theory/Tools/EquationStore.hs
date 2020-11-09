{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ViewPatterns               #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt, Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
-- Support for reasoning with and about disjunctions of substitutions.
module Theory.Tools.EquationStore (
  -- * Equations
    SplitId(..)
  , StoreEntry(..)

  , EqStore(..)
  , emptyEqStore
  , eqsSubst
  , eqsConj

  -- ** Equalitiy constraint conjunctions
  , falseEqConstrConj

  -- ** Queries
  , eqsIsFalse
  , rawSubtermRel
  , isNatSubterm


  -- ** Adding equalities
  , addEqs
  , addSubterm
  , addRuleVariants
  , addEntries

  -- ** Case splitting
  , performSplit
  , dropNameHintsBound

  , splits
  , splitSize
  , splitExists

  -- * Simplification
  , simp
  , simpDisjunction

  -- ** Pretty printing
  , prettyEqStore
) where

import           GHC.Generics          (Generic)
import           Logic.Connectives
import           Term.Unification
import           Theory.Text.Pretty
import           Term.Builtin.Convenience
import           Term.Subsumption

import           Control.Monad.Fresh
import           Control.Monad.Bind
import           Control.Monad.Reader
import           Extension.Prelude

import           Debug.Trace

import           Control.Basics
import           Control.DeepSeq
import           Control.Monad.State   hiding (get, modify, put)
import qualified Control.Monad.State   as MS
import           Data.Array.ST
import           Data.Array
import qualified Data.Graph            as G
import qualified Data.Tree             as T
import qualified Data.Either           as E



import           Data.Binary
import qualified Data.Foldable         as F
import           Data.List          (delete,find,intersect,intersperse,nub,(\\))
import           Data.Maybe
import qualified Data.Set              as S
import qualified Data.Map              as M
import           Extension.Data.Label  hiding (for, get)
import qualified Extension.Data.Label  as L
-- import           Extension.Data.Monoid

------------------------------------------------------------------------------
-- Equation Store                                                --
------------------------------------------------------------------------------

-- | Index of disjunction in equation store
newtype SplitId = SplitId { unSplitId :: Integer }
  deriving( Eq, Ord, Show, Enum, Binary, NFData )

instance HasFrees SplitId where
    foldFrees    _   = const mempty
    foldFreesOcc _ _ = const mempty
    mapFrees     _   = pure

data StoreEntry = SubtermE (LNTerm, LNTerm)
                | NatSubtermE ((LNTerm, LNTerm), S.Set (Either LNSubstVFresh ((LNTerm, LNTerm), S.Set LNSubstVFresh)))
                | SubstE LNSubstVFresh
  deriving( Eq, Ord, Generic, Show )

instance NFData StoreEntry
instance Binary StoreEntry

-- FIXME: Make comment parse.
--
-- The semantics of an equation store
-- > EqStore sigma_free
-- >         [ [sigma_i1,..,sigma_ik_i] | i <- [1..l] ]
-- where sigma_free = {t1/x1, .., tk/xk} is
-- >    (x1 = t1 /\ .. /\ xk = tk)
-- > /\_{i in [1..l]}
-- >    ([|sigma_i1|] \/ .. \/ [|sigma_ik_1|] \/ [|mtinfo_i|]
-- where @[|{t_1/x_1,..,t_l/x_l}|] = EX vars(t1,..,tl). x_1 = t1 /\ .. /\ x_l = t_l@.
-- Note that the 'LVar's in the range of a substitution are interpreted as
-- fresh variables, i.e., different by construction from the x_i which are
-- free variables.
--
-- The variables in the domain of the substitutions sigma_ij and all
-- variables in sigma_free are free (usually globally existentially quantified).
-- We use Conj [] as a normal form to denote True and Conj [Disj []]
-- as a normal form to denote False.
-- We say a variable @x@ is constrained by a disjunction if there is a substition
-- @s@ in the disjunction with @x `elem` dom s@.
data EqStore = EqStore {
      _eqsSubst       :: LNSubst
    , _eqsConj        :: Conj (SplitId, S.Set StoreEntry)
    , _eqsNextSplitId :: SplitId
    }
  deriving( Eq, Ord, Generic )

instance NFData EqStore
instance Binary EqStore

$(mkLabels [''EqStore])

-- | @emptyEqStore@ is the empty equation store.
emptyEqStore :: EqStore
emptyEqStore = EqStore emptySubst (Conj []) (SplitId 0)

-- | @contradictoryEqStore@ is the smallest possible contradictory equation store.
contradictoryEqStore :: EqStore
contradictoryEqStore = EqStore emptySubst falseEqConstrConj (SplitId 0)

-- | If @True@ then the 'EqStore' is contradictory.
eqsIsFalse :: EqStore -> Bool
eqsIsFalse = any ((S.empty == ) . snd) . getConj . L.get eqsConj

{-
-- | Implements the CR-rule S_nat-chain (putting all nat-subterms together and testing unifiability)
-- This is used in @simp@ and not (as one would think) in @contradictions@ because we have a MonadFresh in @simp@
hasInvalidNatChain :: MonadFresh m => MaudeHandle -> EqStore -> m Bool
hasInvalidNatChain hnd = liftM unifiersEmpty . mapM getNewVarEquation . rawNatSubtermRel
  where
    unifiersEmpty :: [Equal LNTerm] -> Bool
    unifiersEmpty list = null (unifyLNTerm list `runReader` hnd)
    getNewVarEquation :: MonadFresh m => (LNTerm, LNTerm) -> m (Equal LNTerm)
    getNewVarEquation (small, big) = do
        v <- freshLVar "newVarrrrrrrrThisVariableShouldNeverOccurInTheProof" LSortNat  -- generate a new variable
        let term = fAppAC NatPlus [small, varTerm v]  -- build the term = small + newVar
        return $ Equal term big  -- small + newVar = big
-}

-- | true if x can be removed given the other conjunctions
-- more specifically, x can be removed iff ∃y. y implies x ∧ (id_x<id_y or x!=y)
-- the latter condition ensures that not two equivalent entries are both removed
impliedByAny :: (SplitId, S.Set StoreEntry) -> EqStore -> Bool
impliedByAny x store = any (x `impliedBy`) $ L.get eqsConj store
  where
    impliedBy (id1, e1) (id2, e2) = subset e2 e1 &&
      (id1 < id2 || not (subset e1 e2))  -- ¬subset e1 e2 is here morally equivalent to e1≠e2
    
    subset e1 e2 = S.map mapSubsts e1 `S.isSubsetOf` S.map mapSubsts e2
    
    mapSubsts :: StoreEntry -> StoreEntry
    mapSubsts (SubtermE st) = SubtermE st
    mapSubsts (SubstE s) = SubstE $ canonizeSubst s
    mapSubsts (NatSubtermE (st, set)) = NatSubtermE (st, S.map mapEither set)
    mapEither (Left s) = Left $ canonizeSubst s
    mapEither (Right (st, set)) = Right (st, S.map canonizeSubst set)
    
-- | The false conjunction. It is always identified with split number -1.
falseEqConstrConj :: Conj (SplitId, S.Set StoreEntry)
falseEqConstrConj = Conj [ (SplitId (-1), falseDisj) ]

dropNameHintsBound :: EqStore -> EqStore
dropNameHintsBound = modify eqsConj (Conj . map (second (S.map dropNameHintsEntry)) . getConj)
  where
    mapSubsts f (Left a) = Left $ f a
    mapSubsts f (Right (b,ss)) = Right (b, S.map f ss)

    dropNameHintsEntry :: StoreEntry -> StoreEntry
    dropNameHintsEntry (SubtermE st) = SubtermE st
    dropNameHintsEntry (NatSubtermE (st, substs)) = NatSubtermE (st, S.map (mapSubsts dropNameHintsLNSubstVFresh) substs)
    dropNameHintsEntry (SubstE subst) = SubstE $ dropNameHintsLNSubstVFresh subst

    dropNameHintsLNSubstVFresh :: LNSubstVFresh -> LNSubstVFresh
    dropNameHintsLNSubstVFresh subst = substFromListVFresh $ zip (map fst slist)
                                       ((`evalFresh` nothingUsed) . (`evalBindT` noBindings) $ renameDropNamehint (map snd slist))
      where
        slist = substToListVFresh subst
  
-- | @(from,to)@ is in @rawSubtermRel@ iff $SubtermE(from,to)$ is in a singleton-disjunction in @eqsConj@
rawSubtermRel :: EqStore -> [(LNTerm,LNTerm)]
rawSubtermRel store = [ st | [SubtermE st] <- entryLists]
   where entryLists = [S.toList $ snd disj | disj <- getConj $ L.get eqsConj store]

-- | @(from,to)@ is in @rawNatSubtermRel@ iff $NatSubtermE((from,to),_)$ is in a singleton-disjunction in @eqsConj@
rawNatSubtermRel :: EqStore -> [(LNTerm,LNTerm)]
rawNatSubtermRel store = [ st | [NatSubtermE (st,_)] <- entryLists]
   where entryLists = [S.toList $ snd disj | disj <- getConj $ L.get eqsConj store]

isNatSubterm :: EqStore -> SplitId -> Bool
isNatSubterm eqs id = case find ((id ==) . fst) $ getConj $ L.get eqsConj $ eqs of
                        Just (_, S.toList -> [NatSubtermE _]) -> True
                        _                                     -> False

-- Instances
------------

instance Apply SplitId where
    apply _ = id

instance Apply StoreEntry where
    apply subst (SubtermE (a,b)) = SubtermE (apply subst a, apply subst b)
    apply subst (NatSubtermE ((a,b), substs)) = NatSubtermE ((apply subst a, apply subst b), S.map (mapSubsts (`composeVFresh` subst)) substs)
      where
        mapSubsts f (Left s) = Left $ f s
        mapSubsts f (Right (st,ss)) = Right (st, S.map f ss)
    apply subst (SubstE s) = SubstE (composeVFresh s subst)


instance HasFrees StoreEntry where
    foldFrees f (SubtermE st) = foldFrees f st
    foldFrees f (NatSubtermE st) = foldFrees f st
    foldFrees f (SubstE subst) = foldFrees f subst
    foldFreesOcc _ _ = const mempty
    mapFrees f (SubtermE st) = SubtermE <$> mapFrees f st
    mapFrees f (NatSubtermE st) = NatSubtermE <$> mapFrees f st
    mapFrees f (SubstE subst) = SubstE <$> mapFrees f subst

instance HasFrees EqStore where
    foldFrees f (EqStore subst substs nextSplitId) =
        foldFrees f subst <> foldFrees f substs <> foldFrees f nextSplitId
    foldFreesOcc  _ _ = const mempty
    mapFrees f (EqStore subst substs nextSplitId) =
        EqStore <$> mapFrees f subst
                <*> mapFrees f substs
                <*> mapFrees f nextSplitId


instance Apply EqStore where
    apply subst (EqStore a b c) = EqStore (compose subst a) (fmap (fmap $ S.map $ apply subst) b) (apply subst c)


-- Equation Store
----------------------------------------------------------------------

-- | We use the empty set (disjunction) to denote false.
falseDisj :: S.Set StoreEntry
falseDisj = S.empty


-- Dealing with equations
----------------------------------------------------------------------

-- | Returns the list of all @SplitId@s valid for the given equation store
-- sorted by the size of the disjunctions. note: not used
splits :: EqStore -> [SplitId]
splits eqs = map fst (nub $ sortOn snd
    [ (idx, S.size conj) | (idx, conj) <- getConj $ L.get eqsConj eqs ])
    \\ onlySingleSubtermSplits eqs
    
-- | Returns the list of @SplitId@s where the set of storeEntries is a singleton and @SubtermE@
-- This is used for finding new Split Goals that arise if these singletons are expanded 
onlySingleSubtermSplits :: EqStore -> [SplitId]
onlySingleSubtermSplits eqs = [ idx | (idx, [SubtermE _]) <- map (second S.toList) conjs]
  where
    conjs = getConj $ L.get eqsConj eqs

-- | Returns 'True' if the 'SplitId' is valid.
splitExists :: EqStore -> SplitId -> Bool
splitExists eqs idx = isJust (splitSize eqs idx)
                        && idx `notElem` onlySingleSubtermSplits eqs

-- | Returns the number of cases for a given 'SplitId'.
splitSize :: EqStore -> SplitId -> Maybe Int
splitSize eqs sid =
    (S.size . snd) <$> (find ((sid ==) . fst) $ getConj $ L.get eqsConj $ eqs)

-- | Add a disjunction to the equation store at the beginning
addEntries :: EqStore -> (S.Set StoreEntry) -> (EqStore, SplitId)
addEntries eqStore disj = if not $ impliedByAny (SplitId(-2), disj) eqStore then
    (   modify eqsConj ((Conj [(sid, disj)]) `mappend`)
      $ modify eqsNextSplitId succ
      $ eqStore
    , sid)
    else (eqStore, SplitId(-2))   --a Maybe would be more beautiful;)
  where
    sid = L.get eqsNextSplitId eqStore

-- | Add a disjunction to the equation store at the beginning
addDisj :: EqStore -> (S.Set LNSubstVFresh) -> (EqStore, SplitId)
addDisj eqStore disj =
    (   modify eqsConj ((Conj [(sid, S.map SubstE disj)]) `mappend`)
      $ modify eqsNextSplitId succ
      $ eqStore
    , sid
    )
  where
    sid = L.get eqsNextSplitId eqStore

-- | @performSplit eqs i@ performs a case-split on the first disjunction
-- with the given 'SplitId'.
performSplit :: EqStore -> SplitId -> Maybe [(EqStore, SplitId)]
performSplit eqStore idx =
    case break ((idx ==) . fst) (getConj $ L.get eqsConj eqStore) of
        (_, [])                   -> Nothing
        (before, (_, disj):after) -> case S.toList disj of
          [SubtermE _] -> Nothing  -- if it is just a subterm, it cannot be split
          disjList -> Just $ mkNewEqStore before after <$> case disjList of
              [NatSubtermE (_, innerDisj)] -> map splitNatSubterm $ S.toList innerDisj
              normalDisj | null [True | SubtermE _ <- normalDisj]  -- no Subterm present -> split normally
                                           -> map S.singleton normalDisj
              normalDisj                   -> splitSubterms normalDisj [] S.empty  -- Subterm present -> split only subterms
  where
    mkNewEqStore before after entries =
        addEntries (set eqsConj (Conj (before ++ after)) eqStore) entries

    splitSubterms :: [StoreEntry] -> [S.Set StoreEntry] -> S.Set StoreEntry -> [S.Set StoreEntry]
    splitSubterms ((SubtermE st) : rest) accList acc = splitSubterms rest (S.singleton (SubtermE st) : accList) acc
    splitSubterms (substOrNat : rest)    accList acc = splitSubterms rest accList (substOrNat `S.insert` acc)
    splitSubterms []                     accList acc = acc : accList

    splitNatSubterm :: Either LNSubstVFresh ((LNTerm, LNTerm), S.Set LNSubstVFresh) -> S.Set StoreEntry
    splitNatSubterm (Left a) = S.singleton (SubstE a)
    splitNatSubterm (Right ((a,b),s)) = S.singleton $ NatSubtermE ((a,b), S.map Left s)


addEqs :: MonadFresh m
       => MaudeHandle -> [Equal LNTerm] -> EqStore -> m (EqStore, Maybe SplitId, [SplitId])
addEqs hnd eqs0 eqStore =
    case unifyLNTermFactored eqs `runReader` hnd of
        (_, []) ->
            return (set eqsConj falseEqConstrConj eqStore, Nothing, [])
        (subst, [substFresh]) | substFresh == emptySubstVFresh -> do
            (newStore, ids) <- applyEqStore hnd subst eqStore
            return (newStore, Nothing, ids)
        (subst, substs) -> do
            (newStore, ids) <- applyEqStore hnd subst eqStore
            let (eqStore', sid) = addDisj newStore (S.fromList substs)
            return (eqStore', Just sid, ids)
            {-
            case splitStrat of
                SplitLater ->
                    return [ addDisj (applyEqStore hnd subst eqStore) (S.fromList substs) ]
                SplitNow ->
                    addEqsAC (modify eqsSubst (compose subst) eqStore)
                        <$> simpDisjunction hnd (const False) (Disj substs)
            -}
  where
    eqs = apply (L.get eqsSubst eqStore) eqs0 --- $ trace (unlines ["addEqs: ", show eqs0]) $ eqs0
    {-
    addEqsAC eqSt (sfree, Nothing)   = [ applyEqStore hnd sfree eqSt ]
    addEqsAC eqSt (sfree, Just disj) =
      fromMaybe (error "addEqsSplit: impossible, splitAtPos failed")
                (splitAtPos (applyEqStore hnd sfree (addDisj eqSt (S.fromList disj))) 0)
-}

-- | Add a subterm predicate to the equation store.
--   Returns the split identifier of the disjunction in resulting equation store.
addSubterm :: MonadFresh m => MaudeHandle -> (LNTerm, LNTerm) -> EqStore -> m (EqStore, Maybe SplitId)
addSubterm hnd st0 eqStore = do
    entries <- recurseSubterms hnd st
    let (finalStore, splitId) = addEntries eqStore entries
    return $ if splitExists finalStore splitId then
        (finalStore, Just splitId)
      else
        (finalStore, Nothing)
  where
    st = apply (L.get eqsSubst eqStore) st0

-- | apply CR-rules S_subterm-ac-recurse and S_subterm-recurse iteratively while applying S_invalid in each step
recurseSubterms :: MonadFresh m => MaudeHandle -> (LNTerm, LNTerm) -> m (S.Set StoreEntry)
recurseSubterms hnd subterm = do
    deconstructed <- splitSubterm reducible subterm
    return $ S.fromList $ concatMap toStoreEntry deconstructed
  where
    reducible = reducibleFunSyms $ mhMaudeSig hnd

    toStoreEntry :: SubtermSplit -> [StoreEntry]
    toStoreEntry TrueD                   = [SubstE emptySubstVFresh]
    toStoreEntry (SubtermD st)           = [SubtermE st]
    toStoreEntry (NatSubtermD (s, t, v)) = [NatSubtermE ((s,t), S.fromList $ unifNatSubterm True (s, t, v))]
    toStoreEntry (EqualD (a,b))          = map SubstE $ getUnifiers (Equal a b)
    toStoreEntry (ACNewVarD (a, b, v))   = map SubstE $ unifWithoutNewVar (Equal a b) v

    unifNatSubterm :: Bool -> (LNTerm, LNTerm, LVar) -> [Either LNSubstVFresh ((LNTerm, LNTerm), S.Set LNSubstVFresh)]
    unifNatSubterm _ (small, big, v) | fAppNatOne `elem` flattenedACTerms NatPlus big
                                  && flattenedACTerms NatPlus big /= [fAppNatOne]
      = map Left (getUnifiers $ Equal small bigMinus1) ++ unifNatSubterm False (small, bigMinus1, v)
        where bigMinus1 = fAppAC NatPlus $ delete fAppNatOne $ flattenedACTerms NatPlus big
    unifNatSubterm True (small, big, v) = map Left $ unifWithoutNewVar (Equal (small ++: varTerm v) big) v
    unifNatSubterm False (small, big, v) = [Right ((small, big), S.fromList $ unifWithoutNewVar (Equal (small ++: varTerm v) big) v)]

    unifWithoutNewVar :: Equal LNTerm -> LVar -> [LNSubstVFresh]
    unifWithoutNewVar eq newVar = map (restrictVFresh filterDomain) unif
      where
        unif = getUnifiers eq
        filterDomain = [x | x <- concatMap domVFresh unif, x /= newVar]

    getUnifiers :: Equal LNTerm -> [LNSubstVFresh]
    getUnifiers eq = unifyLNTerm [eq] `runReader` hnd



-- | Apply a substitution to an equation store and bring resulting equations into
--   normal form again by using unification. The application can "reactivate" subterm constraints.
--   If this happens, they are expanded again (by recurseSubterms) which might create new splitGoals.
--   These splitGoals are then returned in a list (along with the changed EqStore)
applyEqStore :: MonadFresh m => MaudeHandle -> LNSubst -> EqStore -> m (EqStore, [SplitId])
applyEqStore hnd asubst eqStore
    | dom asubst `intersect` varsRange asubst /= [] --- || trace (show ("applyEqStore", asubst, eqStore)) False
    = error $ "applyEqStore: dom and vrange not disjoint for `"++show asubst++"'"
    | otherwise
    = do 
      newConjs <- mapM modifyOneConj $ L.get eqsConj eqStore
      let newEqStore = EqStore newsubst newConjs $ L.get eqsNextSplitId eqStore
      let newSplitGoals = onlySingleSubtermSplits eqStore \\ onlySingleSubtermSplits newEqStore
      return $ (newEqStore, newSplitGoals)
    -- FIXME maybe this is more performant with modify and second instead of making a new EqStore
    -- old code (without fresh monad):
    -- modify eqsConj (fmap (second (S.fromList . concatMap applyBound . S.toList))) $
    --          set eqsSubst newsubst eqStore
  where
    modifyOneConj :: MonadFresh m => (SplitId, S.Set StoreEntry) -> m (SplitId, S.Set StoreEntry)
    modifyOneConj (splitId, entries) = do
      newEntries <- fmap (S.fromList . concat) (mapM applyBound $ S.toList entries)
      return (splitId, newEntries)
    
    newsubst = asubst `compose` L.get eqsSubst eqStore
    
    applyBound :: MonadFresh m => StoreEntry -> m [StoreEntry]
    applyBound (SubstE s) = map SubstE <$> applyBoundSubst s
    applyBound (SubtermE (small, big)) = S.toList <$> recurseSubterms hnd (apply newsubst small, apply newsubst big)
    applyBound (NatSubtermE ((small, big), _)) = S.toList <$> recurseSubterms hnd (apply newsubst small, apply newsubst big)
    applyBoundSubst :: MonadFresh m => LNSubstVFresh -> m [LNSubstVFresh]
    applyBoundSubst s = return $ map (restrictVFresh (varsRange newsubst ++ domVFresh s)) $
        (`runReader` hnd) $ unifyLNTerm
          [ Equal (apply newsubst (varTerm lv)) t
          | let slist = substToListVFresh s,
            -- variables in the range are fresh, so we have to rename
            -- them away from all other variables in unification problem
            -- NOTE: these variables never enter the global context
            let ran = renameAvoiding (map snd slist)
                                     (domVFresh s ++ varsRange newsubst),
            (lv,t) <- zip (map fst slist) ran
          ]

{- NOTES for @applyEqStore tau@ to a fresh substitution sigma:
[ FIXME: extend explanation to multiple unifiers ]
Let dom(sigma) = x1,..,xk, vrange(sigma) = y1, .. yl, vrange(tau) = z1,..,zn
Fresh substitution denotes formula
  exists #y1, .., #yl. x1 = t1 /\ .. /\ xk = tk
for variables #yi that do not clash with xi and zi [renameAwayFrom]
and with vars(ti) `subsetOf` [#y1, .. #yl].
We apply tau with vrange(tau) = z1,..,zn to the formula to obtain
  exists ##y1, .., ##yl. tau(x1) = t1 /\ .. /\ tau(xk) = tk
unification then yields a lemma
  forall xi zi #yi.
    tau(x1) = t1 /\ .. /\ tau(xk) = tk
    <-> exists vars(s1,..sm). x1 = .. /\ z1 = .. /\ #y1 = ..
So we have
  exists #y1, .., #yl.
    exists vars(s1,..sm). x1 = .. /\ z1 = .. /\ #y1 = ..
<=>
  exists vars(s1,..sm). x1 = .. /\ z1 = ..
      /\  (exists #y1, .., #yl. #y1 = ..)
<=> [restric]
  exists vars(s1,..sm). x1 = .. /\ z1 = .. /\ True
-}

-- | Add the given rule variants.
addRuleVariants :: Disj LNSubstVFresh -> EqStore -> (EqStore, SplitId)
addRuleVariants (Disj substs) eqStore
    | dom freeSubst `intersect` concatMap domVFresh substs /= []
    = error $ "addRuleVariants: Nonempty intersection between domain of variants and free substitution. "
              ++"This case has not been implemented, add rule variants earlier."
    | otherwise = addDisj eqStore (S.fromList substs)
  where
    freeSubst = L.get eqsSubst eqStore


{-
-- | Return the set of variables that is constrained by disjunction at give position.
constrainedVarsPos :: EqStore -> Int -> [LVar]
constrainedVarsPos eqStore k
    | k < length conj = frees (conj!!k)
    | otherwise       = []
  where
    conj = getConj . L.get eqsConj $ eqStore
-}

-- Simplifying disjunctions
----------------------------------------------------------------------

-- | Simplify given disjunction via EqStore simplification. Obtains fresh
--   names for variables from the underlying 'MonadFresh'.
simpDisjunction :: MonadFresh m
                => MaudeHandle
                -> (LNSubst -> LNSubstVFresh -> Bool)
                -> Disj LNSubstVFresh
                -> m (LNSubst, Maybe [LNSubstVFresh])
simpDisjunction hnd isContr disj0 = do
    (eqStore', _) <- simp hnd isContr eqStore  -- there cannot be a new split goal in simp if there are no subterms
    return (L.get eqsSubst eqStore', wrap $ L.get eqsConj eqStore')
  where
    eqStore = fst $ addDisj emptyEqStore (S.fromList $ getDisj $ disj0)
    wrap (Conj [])          = Nothing
    wrap (Conj [(_, disj)]) = Just $ [x | SubstE x <- S.toList disj]
    wrap conj               =
        error ("simplifyDisjunction: imposible, unexpected conjunction `"
               ++ show conj ++ "'")


-- Simplification
----------------------------------------------------------------------

-- | @simp eqStore@ simplifies the equation store.
simp :: MonadFresh m => MaudeHandle -> (LNSubst -> LNSubstVFresh -> Bool) -> EqStore -> m (EqStore, [SplitId])
simp hnd isContr eqStore = swap <$> runStateT (loopSimp1 []) eqStore
  where
    loopSimp1 oldSplits = do
      newMaysplits <- simp1 hnd isContr
      case newMaysplits of
        Nothing -> return $ oldSplits
        Just newSplits -> loopSimp1 $ oldSplits ++ newSplits   
        


-- | @simp1@ tries to execute one simplification step
--   for the equation store. It returns @Nothing@ if
--   the equation store was not modified.
--   If it returns @Just list@ it was modified and new split goals arose at the split id's in the list 
simp1 :: MonadFresh m => MaudeHandle -> (LNSubst -> LNSubstVFresh -> Bool) -> StateT EqStore m (Maybe [SplitId])
simp1 hnd isContr = do
    eqs <- MS.get
    if eqsIsFalse eqs
        then return Nothing
        else do
          b1 <- simpMinimize (isContr (L.get eqsSubst eqs))
          b2 <- simpRemoveRenamings
          b3 <- simpEmptyNat
          b4 <- simpEmptyDisj
          b5 <- simpIdentical
          b6 <- simpRemoveDuplicates
          let ids1 = [Just [] | b1 || b2 || b3 || b4 || b5 || b6]
          ids2 <- (: ids1) <$> simpSingleton hnd
          ids3 <- (: ids2) <$> foreachDisj hnd simpAbstractSortedVar
          ids4 <- (: ids3) <$> foreachDisj hnd simpIdentify
          ids5 <- (: ids4) <$> foreachDisj hnd simpAbstractFun
          ids6 <- (: ids5) <$> foreachDisj hnd simpAbstractName
          ids7 <- (: ids6) <$> insertImpliedNatEq hnd
          return $ if all isNothing ids7 then Nothing else (Just . concat . catMaybes) ids7


simpRemoveDuplicates :: MonadFresh m => StateT EqStore m Bool
simpRemoveDuplicates = do
    eqs <- MS.get
    Conj conj <- getM eqsConj
    let newConj = filter (\x -> not $ impliedByAny x eqs) conj
    eqsConj =: Conj newConj
    return $ length newConj < length conj


-- | Remove variable renamings in fresh substitutions.
simpRemoveRenamings :: MonadFresh m => StateT EqStore m Bool
simpRemoveRenamings = do
    Conj conj <- getM eqsConj
    let list = concat [getSubsts y | x <- conj, y <- S.toList $ snd x]  --all substitutions in all disjunctions
    if F.any (\subst -> domVFresh subst /= domVFresh (removeRenamings subst)) list
      then modM eqsConj (fmap (second $ S.map remove)) >> return True
      else return False
    where
      getSubsts :: StoreEntry -> [LNSubstVFresh]
      getSubsts (SubstE s) = [s]
      getSubsts (NatSubtermE (_, S.toList -> substs)) = E.lefts substs ++ concatMap (S.toList . snd) (E.rights substs)
      getSubsts (SubtermE _) = []

      mapSubsts f (Left a) = Left $ f a
      mapSubsts f (Right (b,ss)) = Right (b, S.map f ss)
      remove (SubstE x) = SubstE (removeRenamings x)
      remove (NatSubtermE (x, substs)) = NatSubtermE (x, S.map (mapSubsts removeRenamings) substs)
      remove (SubtermE x) = SubtermE x


-- | If a NatSubtermE with an empty set of substitutions is found, this can be removed
simpEmptyNat :: MonadFresh m => StateT EqStore m Bool
simpEmptyNat = do
    conj <- getM eqsConj
    if F.any (any isEmptyNat . snd) conj
      then eqsConj =: (Conj . map (second (S.filter (not . isEmptyNat))) . getConj) conj
        >> return True
      else return False
    where
      isEmptyNat :: StoreEntry -> Bool
      isEmptyNat (NatSubtermE (_, substs)) = substs == S.empty
      isEmptyNat _ = False

-- | If empty disjunction is found, the whole conjunct
--   can be simplified to False.
simpEmptyDisj :: MonadFresh m => StateT EqStore m Bool
simpEmptyDisj = do
    conj <- getM eqsConj
    if F.any ((== falseDisj) . snd) conj && conj /= falseEqConstrConj
      then eqsConj =: falseEqConstrConj >> return True
      else return False


-- | If there is a singleton disjunction, it can be
--   composed with the free substitution.
simpSingleton :: forall m. MonadFresh m => MaudeHandle -> StateT EqStore m (Maybe [SplitId])
simpSingleton hnd = go [] =<< gets (getConj . L.get eqsConj)
  where
    go :: [(SplitId, S.Set StoreEntry)] -> [(SplitId, S.Set StoreEntry)] -> StateT EqStore m (Maybe [SplitId])
    go _     []               = return Nothing
    go lefts ((idx,d):rights) = do
      case getSingletonSubst (S.toList d) of
        Nothing -> go ((idx,d):lefts) rights
        Just s -> do
          subst <- freshToFree s
          eqsConj =: Conj (reverse lefts ++ rights)
          oldStore <- MS.get
          (newStore, splitIds) <- applyEqStore hnd subst oldStore
          MS.put newStore  -- FIXME maybe this is more performant with with modify instead of get -> put
          return $ Just splitIds

    -- gives the substitution if the list of StoreEntry is a singleton substitution (could also be in NatSubtermE)
    getSingletonSubst :: [StoreEntry] -> Maybe LNSubstVFresh
    getSingletonSubst [SubstE s] = Just s
    getSingletonSubst [NatSubtermE (_,ss)] = case S.toList ss of
       [Left s]                    -> onlySimpleSubst s
       [Right (_,S.toList -> [s])] -> onlySimpleSubst s  -- I guess, this cannot happen, but it does not hurt
       _                           -> Nothing
    getSingletonSubst _ = Nothing

    -- returns Just s if the substitution does not introduce more variables, otherwise, it returns Nothing
    onlySimpleSubst :: LNSubstVFresh -> Maybe LNSubstVFresh
    onlySimpleSubst s | (S.size . S.fromList . varsRangeVFresh) s < (S.size . S.fromList . domVFresh) s = Just s
    onlySimpleSubst _                                                                                    = Nothing

-- | Filter out identical substitutions
--   which are not covered by the set data structure because they are split in NatSubtermE and SubstE.
--   Then, the one in SubstE can be removed.
--   If we would remove the one in NatSubtermE, we might loose the subterm information which makes the prover slower.
simpIdentical :: forall m. MonadFresh m => StateT EqStore m Bool
simpIdentical = go [] =<< gets (getConj . L.get eqsConj)
  where
    go :: [(SplitId, S.Set StoreEntry)] -> [(SplitId, S.Set StoreEntry)] -> StateT EqStore m Bool
    go _     []               = return False
    go lefts ((idx,d):rights) = do
      -- newD is d without any SubstE of which the substitution appears in a NatSubtermE
      let newD = d `S.difference` S.map SubstE (S.unions $ S.unions [S.map getSubsts x | NatSubtermE (_, x) <- S.toList d])
      (if S.size d == S.size newD then
        go ((idx, d) : lefts) rights
       else
        eqsConj =: Conj (reverse lefts ++ [(idx, newD)] ++ rights) >> return True)
      where
        getSubsts (Left s) = S.singleton s
        getSubsts (Right ((_,_), ss)) = ss

-- | If all substitutions @si@ map a variable @v@ to terms with the same
--   outermost function symbol @f@, then they all contain the common factor
--   @{v |-> f(x1,..,xk)}@ for fresh variables xi and we can replace
--   @x |-> ..@ by @{x1 |-> ti1, x2 |-> ti2, ..}@ in all substitutions @si@.
simpAbstractFun :: MonadFresh m
                => [LNSubstVFresh]
                -> m (Maybe (LNSubst, [LNSubstVFresh]))
simpAbstractFun []             = return Nothing
simpAbstractFun (subst:others) = case commonOperators of
    [] -> return Nothing
    -- abstract all arguments
    (v, o, argss@(args:_)):_ | all ((==length args) . length) argss -> do
        fvars <- mapM (\_ -> freshLVar "x" LSortMsg) args
        let substs' = zipWith (abstractAll v fvars) (subst:others) argss
            fsubst  = substFromList [(v, fApp o (map varTerm fvars))]
        return $ Just (fsubst, substs')
    -- abstract first two arguments
    (v, o@(AC _), argss):_ -> do
        fv1 <- freshLVar "x" LSortMsg
        fv2 <- freshLVar "x" LSortMsg
        let substs' = zipWith (abstractTwo o v fv1 fv2) (subst:others) argss
            fsubst  = substFromList [(v, fApp o (map varTerm [fv1,fv2]))]
        return $ Just (fsubst, substs')
    (_, _ ,_):_ ->
        error "simpAbstract: impossible, invalid arities or List operator encountered."
  where
    commonOperators = do
        (v, viewTerm -> FApp o args) <- substToListVFresh subst
        let images = map (`imageOfVFresh` v) others
            argss  = [ args' | Just (viewTerm -> FApp o' args') <- images, o' == o ]
        guard (length argss == length others)
        return (v, o, args:argss)

    abstractAll v freshVars s args = substFromListVFresh $
        filter ((/= v) . fst) (substToListVFresh s) ++ zip freshVars args

    abstractTwo o v fv1 fv2 s args = substFromListVFresh $
        filter ((/= v) . fst) (substToListVFresh s) ++ newMappings args
      where
        newMappings []      =
            error "simpAbstract: impossible, AC symbols must have arity >= 2."
        newMappings [a1,a2] = [(fv1, a1), (fv2, a2)]
        -- here we always abstract from left to right and do not
        -- take advantage of the AC property of o
        newMappings (a:as)  = [(fv1, a),  (fv2, fApp o as)]


-- | If all substitutions @si@ map a variable @v@ to the same name @n@,
--   then they all contain the common factor
--   @{v |-> n}@ and we can remove @{v -> n}@ from all substitutions @si@
simpAbstractName :: MonadFresh m
                 => [LNSubstVFresh]
                 -> m (Maybe (LNSubst, [LNSubstVFresh]))
simpAbstractName []             = return Nothing
simpAbstractName (subst:others) = case commonNames of
    []           -> return Nothing
    (v, c):_     ->
        return $ Just (substFromList [(v, c)]
                      , map (\s -> restrictVFresh (delete v (domVFresh s)) s) (subst:others))
  where
    commonNames = do
        (v, c@(viewTerm -> Lit (Con _))) <- substToListVFresh subst
        let images = map (`imageOfVFresh` v) others
        guard (length images == length [ () | Just c' <- images, c' == c])
        return (v, c)


-- | If all substitutions @si@ map a variable @v@ to variables @xi@ of the same
--   sort @s@ then they all contain the common factor
--   @{v |-> y}@ for a fresh variable of sort @s@
--   and we can replace @{v -> xi}@ by @{y -> xi}@ in all substitutions @si@
simpAbstractSortedVar :: MonadFresh m
                      => [LNSubstVFresh]
                      -> m (Maybe (LNSubst, [LNSubstVFresh]))
simpAbstractSortedVar []             = return Nothing
simpAbstractSortedVar (subst:others) = case commonSortedVar of
    []            -> return Nothing
    (v, s, lvs):_ -> do
        fv <- freshLVar (lvarName v) s
        return $ Just (substFromList [(v, varTerm fv)]
                      , zipWith (replaceMapping v fv) lvs (subst:others))
  where
    commonSortedVar = do
        (v, viewTerm -> Lit (Var lx)) <- substToListVFresh subst
        guard (sortCompare (lvarSort v)  (lvarSort lx) == Just GT)
        let images = map (`imageOfVFresh` v) others
            -- FIXME: could be generalized to choose topsort s of all images if s < sortOf v
            --        could also be generalized to terms of a given sort
            goodImages = [ ly | Just (viewTerm -> Lit (Var ly)) <- images, lvarSort lx == lvarSort ly]
        guard (length images == length goodImages)
        return (v, lvarSort lx, lx:goodImages)
    replaceMapping v fv lv sigma =
        substFromListVFresh $ filter ((/= v) . fst) (substToListVFresh sigma) ++ [(fv, varTerm lv)]

-- | If all substitutions @si@ map two variables @x@ and @y@ to identical terms @ti@,
--   then they all contain the common factor @{x |-> y}@ for a fresh variable @z@
--   and we can remove @{x |-> ti}@ from all @si@.
simpIdentify :: MonadFresh m
             => [LNSubstVFresh]
             -> m (Maybe (LNSubst, [LNSubstVFresh]))
simpIdentify []             = return Nothing
simpIdentify (subst:others) = case equalImgPairs of
    []         -> return Nothing
    ((v,v'):_) -> do
        let (vkeep, vremove) = case sortCompare (lvarSort v) (lvarSort v') of
                                 Just GT -> (v', v)
                                 Just _  -> (v, v')
                                 Nothing -> error $ "EquationStore.simpIdentify: impossible, variables with incomparable sorts: "
                                                    ++ show v ++" and "++ show v'
        return $ Just (substFromList [(vremove, varTerm vkeep)],
                       map (removeMappings [vkeep]) (subst:others))
  where
    equalImgPairs = do
        (v,t)    <- substToListVFresh subst
        (v', t') <- substToListVFresh subst
        guard (t == t' && v < v' && all (agrees_on v v') others)
        return (v,v')
    agrees_on v v' s =
        imageOfVFresh s v == imageOfVFresh s v' && isJust (imageOfVFresh s v)
    removeMappings vs s = restrictVFresh (domVFresh s \\ vs) s


-- | Simplify by removing substitutions that occur twice in a disjunct.
--   We could generalize this function by using AC-equality or subsumption.
--   Comment by Philip: This description is not correct !!!
--   The doubled substitutions are already removed by the set structure and @simpIdentical@.
--   This function removes disjunctions that have @emptySubst@ inside.
--   Additionally, it filters out substitutions with @isContr (= substCreatesNonNormalTerms)@.
simpMinimize :: MonadFresh m => (LNSubstVFresh -> Bool) -> StateT EqStore m Bool
simpMinimize isContr = do
    Conj conj <- gets (L.get eqsConj)
    let list = concat [getSubsts y | x <- conj, y <- S.toList $ snd x]  --all substitutions in all disjunctions
    if F.any check list
      then MS.modify (set eqsConj (second minimize <$> Conj conj)) >> return True
      else return False
  where
    getSubsts :: StoreEntry -> [LNSubstVFresh]
    getSubsts (SubstE s) = [s]
    getSubsts (NatSubtermE (_, ss)) = concatMap getSubstsEither $ S.toList ss
      where
        getSubstsEither (Left s) = [s]
        getSubstsEither (Right ((_,_), sss)) = S.toList sss
    getSubsts (SubtermE _) = []

    minimize :: S.Set StoreEntry -> S.Set StoreEntry
    minimize entries
      | emptySubstVFresh `elem` concatMap getSubsts entries = S.singleton (SubstE emptySubstVFresh)
      | otherwise                                           = S.fromList $ concatMap filterContr entries
    filterContr (NatSubtermE (st, substs)) = [NatSubtermE (st, S.fromList $ concatMap (filterSubsts (not . isContr)) substs)]
      where
        filterSubsts f (Left a)        | f a                 = [Left a]
        filterSubsts f (Right (b, ss)) | any f (S.toList ss) = [Right (b, S.filter f ss)]
        filterSubsts _ _                                     = []
    filterContr (SubstE x) = [SubstE x | not (isContr x)]
    filterContr x = [x]
    check subst = subst == emptySubstVFresh || isContr subst


-- | Traverse the disjunctions that do not contain (noNat-)Subterms and execute @f@
--   until it returns @Just (mfreeSubst, disjs)@.
--   Then the @disjs@ is inserted at the current position, and @freesubst@ is applied to the equation store.
--   It is crucial, that @f@ does not change the order of the substitutions.
--   It should output them (or their modified version) in the exact same order as it got them.
--   See the description of @zipWithFlattened@ for more details.
--   @Nothing@ is returned if no modification took place
--   If @Just splits@ is returned, new split goals have to be inserted at @splits@ (possibly empty)
foreachDisj :: forall m. MonadFresh m
            => MaudeHandle
            -> ([LNSubstVFresh] -> m (Maybe (LNSubst, [LNSubstVFresh])))
            -> StateT EqStore m (Maybe [SplitId])
foreachDisj hnd f =
    go [] =<< gets (getConj . L.get eqsConj)
  where
    go :: [(SplitId, S.Set StoreEntry)] -> [(SplitId, S.Set StoreEntry)] -> StateT EqStore m (Maybe [SplitId])
    go _     []               = return Nothing
    go lefts ((idx,d):rights) = do
        b <- if not (null [x | SubtermE x <- S.toList d] &&  --ensures that no (noNat-)Subterms are in this disjunction
                     null [x | NatSubtermE x <- S.toList d])  -- I enabled it initially (not having this line), but it does non-helpful things (especially when simpSingleton is disabled for NatSubtermE)
          then return Nothing
          else lift $ f (flatten $ S.toAscList d)  --toAscList ensures that the order is the same
        case b of
          Nothing              -> go ((idx,d):lefts) rights
          Just (msubst, disjs) -> do
              let modified = S.fromList $ zipWithFlattened (S.toAscList d) disjs  --toAscList ensures that the order is the same
              eqsConj =: Conj (reverse lefts ++ [(idx, modified)] ++ rights)
              oldStore <- MS.get
              (newStore, splitIds) <- applyEqStore hnd msubst oldStore
              MS.put newStore
              -- FIXME maybe this is more performant with with modify instead of get -> put
              -- old code (without fresh monad):
              -- maybe (return ()) (\s -> MS.modify (applyEqStore hnd s)) msubst
              return $ Just splitIds

    flatten :: [StoreEntry] -> [LNSubstVFresh]
    flatten (SubstE s :xs) = s : flatten xs
    flatten (NatSubtermE (_,substs) :xs) = concatMap flattenEither (S.toList substs) ++ flatten xs
      where
        flattenEither (Left s) = [s]
        flattenEither (Right (_,ss)) = S.toList ss
    flatten [] = []
    flatten _ = error "at this stage, there should be no subterms"
    -- The complication here is that substitutions can also occur in NatSubtermE.
    -- These substitutions need to be passed to f as well (all together in a flattened list of substitutions).
    -- The returned list of substitutions should be inserted exactly where the old substitutions were taken from.
    -- This is what this function does.
    -- Especially, the following holds: zipWithFlattened entries (flatten entries) == entries
    zipWithFlattened :: [StoreEntry] -> [LNSubstVFresh] -> [StoreEntry]
    zipWithFlattened (SubstE _ :xs) (snew:ys)     = SubstE snew : zipWithFlattened xs ys
    zipWithFlattened n@(NatSubtermE (st,ss) :xs) ys = let l = length $ flatten n in
                                                      NatSubtermE (st, S.fromList $ zipEithers (S.toList ss) (take l ys))
                                                      : zipWithFlattened xs (drop l ys)
      where
        zipEithers (Left _:es) (s:sss) = Left s : zipEithers es sss
        zipEithers (Right (subterm, oldss):es) sss = let ll = length oldss in Right (subterm, S.fromList $ take ll sss) : zipEithers es sss
        zipEithers [] [] = []
        zipEithers _ _ = error "error in zipWithFlattened>zipEithers; read the comment to understand this procedure"
    zipWithFlattened [] []                        = []
    zipWithFlattened (SubtermE _ : _) _           = error "error zipWithFlattened: at this stage, there should be no subterms"
    zipWithFlattened _ _                          = error "error in zipWithFlattened; read the comment to understand this procedure"

{-
testImpliedNatEq :: String
testImpliedNatEq = show ("testImpliedNat", length tests, tests, map natSubtermEqualities tests)
  where
    e = fAppNatOne
    e2 = e ++: e
    e3 = e2 ++: e
    e4 = e3 ++: e
    tests = [[(n1, n2 ++: e3),
              (n1 ++: n2 ++: e, e),  -- should yield Nothing
              (e4, n1 ++: n3 ++: e),
              (n3, n1 ++: e4)],
             [(n1, e2)],  -- should yield Just n1=1
             [(n1, n2 ++: e),
              (e3, n1 ++: n2),
              (n2, e3)  -- should yield n1=n2=2
             ],
             [(e, e)]  -- should yield Just []  -- partialAtomValuation cares for this case!
      ]
-}

insertImpliedNatEq :: MonadFresh m => MaudeHandle -> StateT EqStore m (Maybe [SplitId])
insertImpliedNatEq hnd = do
    eqs <- MS.get
    let meq = natSubtermEqualities $ rawNatSubtermRel eqs
    case meq of
      Nothing -> MS.put contradictoryEqStore >> return (Just [])
      Just eq -> if null eq then
                   return Nothing
                 else do
                   (eqs2, maysplit, splitlist) <- addEqs hnd eq eqs
                   MS.put eqs2
                   return $ Just (splitlist ++ maybeToList maysplit)

-- This procedure generates some (not all) equalities that are implied by the natSubterm relation.
-- It filters the relation for UTVPI's (≤ 2 vars) and performs the algorithm from the following paper:
-- "An Efficient Decision Procedure for UTVPI Constraints"
natSubtermEqualities :: [(LNTerm, LNTerm)] -> Maybe [Equal LNTerm]
natSubtermEqualities relation = {-trace (show (("natSubtermEqualities"
                                      ,"relation", relation
                                      ,"realEdges", realEdges
                                      ,"vertices", vertices
                                      ,"oneEdges", oneEdges)
                                      ,("floydWarshall", floydWarshall
                                      ,"tightenedEdges", tightenedEdges
                                      ,"bellmanFord", bellmanFord
                                      ,"slackEdges", slackEdges
                                      ,"sccs", sccs
                                      ,"equalities", equalities
                                      ))) $-} if null bellmanFord then Nothing else Just equalities
      where

      --True = positive
      --False = negative
      formatEdge :: (LNTerm, LNTerm) -> [(((Bool,LVar), (Bool,LVar)), Int)]  -- 0 elements for invalid (>2 vars); otherwise 1 or 2 elements
      formatEdge (a, b) = case (flattenedACTerms NatPlus a, flattenedACTerms NatPlus b) of
        (l, r) | length (getVars l ++ getVars r) == 1 -> [((from, to), d)]
          where
            d = 2 * (countOnes r - countOnes l - 1)
            from = head $ map (True,) (getVars l) ++ map (False,) (getVars r)
            to = first not from
        (l, r) | length (getVars l ++ getVars r) == 2 -> zip (zip froms tos) ds
          where
            ds = replicate 2 (countOnes r - countOnes l - 1)
            froms = map (True,) (getVars l) ++ map (False,) (getVars r)
            tos = map (first not) (reverse froms)
        _ -> []
       where
        getVars :: [LNTerm] -> [LVar]
        getVars = mapMaybe getVar . filter (/= fAppNatOne)
        countOnes :: [LNTerm] -> Int
        countOnes = length . filter (== fAppNatOne)


      realEdges :: [(((Bool,LVar), (Bool,LVar)), Int)]
      realEdges = concatMap formatEdge relation

      vertices :: [(Bool,LVar)]
      vertices = S.toList $ S.fromList $ concatMap (\x -> [fst $ fst x, snd $ fst x]) realEdges

      --intToVertex i = fromJust $ M.lookup i $ M.fromList $ zip [0 .. length vertices - 1] vertices
      vertexToInt v = fromJust $ M.lookup v $ M.fromList $ zip vertices [0 .. length vertices - 1]

      oneEdges :: [(((Bool,LVar), (Bool,LVar)), Int)]
      oneEdges = map (\(_,x) -> (((False, x), (True, x)), -2)) $ filter fst vertices

      rawEdges :: [(((Bool,LVar), (Bool,LVar)), Int)]
      rawEdges = realEdges ++ oneEdges

      inf :: Int
      inf = (maxBound :: Int) `div` (2 :: Int)

      floydWarshall :: Array Int Int
      floydWarshall = {- trace (show ("fwSolution", getSolution)) -} getSolution
        where
          getSolution :: Array Int Int
          getSolution = runSTArray $ do
            let n = length vertices
            solution <- newArray (0, (n * n) - 1) inf  --initialize solution to ∞
            forM_ rawEdges $ \((from, to), w) -> do
              writeArray solution (vertexToInt from * n + vertexToInt to) w  -- initialize edges to w
            forM_ [0.. n - 1] $ \i -> do
              writeArray solution (i*n + i) 0  -- initialize solution[i][i] to 0

            forM_ [0.. n - 1] $ \k -> do  -- execute Floyd Warshall
              forM_ [0.. n - 1] $ \i -> do
                forM_ [0.. n - 1] $ \j -> do
                  ij <- readArray solution (i*n + j)
                  ik <- readArray solution (i*n + k)
                  kj <- readArray solution (k*n + j)
                  writeArray solution (i*n + j) (min ij $ ik + kj)
            return solution

      tightenedEdges :: [(((Bool,LVar), (Bool,LVar)), Int)]
      tightenedEdges = mapMaybe buildEdge $ filter fst vertices
        where
          distToNeg v = floydWarshall ! (vertexToInt v * length vertices + vertexToInt (first not v))
          buildEdge v = if even (distToNeg v) && (distToNeg v < inf `div` 2) then Nothing else Just $ ((v, first not v), distToNeg v - 1)

      edges :: [(((Bool,LVar), (Bool,LVar)), Int)]
      edges = rawEdges ++ tightenedEdges

      bellmanFord :: Maybe (Array Int Int)
      bellmanFord = {- trace (show ("bfSolution", getSolution)) $ -} if solvable getSolution then Just getSolution else Nothing
       where
        getSolution :: Array Int Int
        getSolution = runSTArray $ do
          solution <- newArray (0, length vertices - 1) 0
          forM_ [0.. length vertices - 1] $ \_ -> do
            forM_ edges $ \((from, to), w) -> do
              distFrom <- readArray solution (vertexToInt from)
              distTo <- readArray solution (vertexToInt to)
              writeArray solution (vertexToInt to) (min distTo $ w + distFrom)
          return solution

        solvable :: Array Int Int -> Bool
        solvable solution = and $ flip map edges $ \((from, to), w) -> let
          distFrom = solution ! vertexToInt from
          distTo = solution ! vertexToInt to
          in w + distFrom >= distTo




      slackEdges :: [((Bool,LVar), (Bool,LVar))]
      slackEdges = case bellmanFord of
        Nothing -> []
        Just solution -> map fst $ flip filter edges $ \((from, to), w) -> let
          distFrom = solution ! vertexToInt from
          distTo = solution ! vertexToInt to
          in w + distFrom == distTo

      -- compute strongly connected components of slackEdges
      sccs :: [[(Bool,LVar)]]
      sccs = map (map ((\(a,_,_)->a) . nodeFromVertex) . T.flatten) (G.scc graph)
        where
          preparedEdges :: [((Bool,LVar), Int, [Int])]
          preparedEdges = flip map vertices $ \v -> (
            v,
            vertexToInt v,
            map (vertexToInt . snd) $ filter (\(from, _) -> from == v) slackEdges)
          (graph, nodeFromVertex, _) = G.graphFromEdges preparedEdges

      equalities :: [Equal LNTerm]
      equalities = relationEqs ++ absoluteEqs  -- get equalities from scc and the graph
        where
          getValue vertex = case bellmanFord of
            Nothing -> 0
            Just solution -> solution ! vertexToInt vertex
          smallest = map (foldr1 (\x y -> if getValue x < getValue y then x else y) ) sccs  -- finds the smallest variable for each scc
          zipped = smallest `zip` map (filter fst) sccs  -- zips this smallest variable to the rest of the list
          removedEq = map (\(x,ys) -> (x, delete x ys)) zipped  -- removes equal variables -> no equations like x=x arise
          addN y n = iterate (++: fAppNatOne) (varTerm y) !! n  -- helper that adds n ones to a variable y
          buildEq x y = Equal (varTerm (snd x)) $ addN (snd y) (getValue y - getValue x)  -- helper that builds x=y+n
          relationEqs = concatMap (\(x,ys) -> map (buildEq x) ys) removedEq -- end result

          duplicates = concatMap ((\xs -> xs \\ S.toList (S.fromList xs)) . map snd) sccs  --variables that occur with + and - in any scc
          termN n = iterate (++: fAppNatOne) fAppNatOne !! (n-1)  -- the term that represents n (with n>0)
          buildAbsoluteEq v = Equal (varTerm v) $ termN $ (getValue (False, v) - getValue (True, v)) `div` 2  -- helper that builds x=n
          absoluteEqs = map buildAbsoluteEq duplicates  -- end result





------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Pretty print an 'EqStore'.
prettyEqStore :: HighlightDocument d => EqStore -> d
prettyEqStore eqs@(EqStore substFree (Conj disjs) _nextSplitId) = vcat $
  [if eqsIsFalse eqs then text "CONTRADICTORY" else emptyDoc] ++
  map combine
    [ ("subst", vcat $ prettySubst (text . show) (text . show) substFree)
    , ("conj",  vcat $ map ppDisj disjs)
    ]
  where
    combine (header, d) = fsep [keyword_ header <> colon, nest 2 d]
    ppDisj (idx, entries) =
        text (show (unSplitId idx) ++ ".") <-> numbered' conjs
      where
        conjs = map ppEntry $ S.toList entries

    ppEq (a,b) =
      prettyNTerm (lit (Var a)) $$ nest (6::Int) (opEqual <-> prettyNTerm b)

    ppEntry (SubstE subst) = sep
      [ hsep (opExists : map prettyLVar (varsRangeVFresh subst)) <> opDot
      , nest 2 $ fsep $ intersperse opLAnd $ map ppEq $ substToListVFresh subst
      ]
    ppEntry (SubtermE (a,b)) = prettyNTerm a $$ nest (6::Int) (opSubterm <-> prettyNTerm b)
    ppEntry (NatSubtermE ((a,b),substs)) = prettyNTerm a $$ nest (6::Int) (opSubterm <-> prettyNTerm b)
                                                <-> numbered' (map ppNatSub $ S.toList substs)
      where
        ppNatSub (Left s) = (ppEntry . SubstE) s
        ppNatSub (Right ((s,t),_)) = prettyNTerm s $$ nest (6::Int) (opSubterm <-> prettyNTerm t)


-- Derived and delayed instances
--------------------------------

instance Show EqStore where
    show = render . prettyEqStore
