{-# LANGUAGE TypeOperators, TemplateHaskell, DeriveDataTypeable, ScopedTypeVariables, TupleSections #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
-- Support for reasoning with and about disjunctions of substitutions.
module Theory.Proof.EquationStore (

  -- * Transformation
    simp
  , addEqs
  , addRuleVariants
  , splitAtPos
  , eqSplits
  , constrainedVarsPos

  , SplitStrategy(..)

  -- * simplify a disjunction
  , simpDisjunction

) where

import Term.Unification
import Logic.Connectives
import Theory.Proof.Types

import Control.Monad.Reader
import Control.Monad.Fresh
import Utils.Misc
import Extension.Prelude

-- import qualified Debug.Trace as DT

import Debug.Trace.Ignore

import Data.List
import Data.Label hiding ( for )
import Data.Maybe
import Data.Monoid
import Data.Traversable hiding ( mapM )
import qualified Data.Foldable as F
import Control.Basics
import Control.Monad.State hiding (get, modify)
import qualified Control.Monad.State as MS


-- Equation Store
----------------------------------------------------------------------

-- | We use an empty disjunction to denote false.
falseDisj :: Disj (LNSubstVFresh)
falseDisj = Disj []

data SplitStrategy = SplitNow | SplitLater

-- Dealing with equations
----------------------------------------------------------------------

-- | Returns the list of all @SplitId@s corresponding equation disjunctions.
eqSplits :: EqStore -> [SplitId]
eqSplits eqs = [0.. length (getConj . get eqsConj $ eqs) -1 ]

-- | Add a list of term equalities to the equation store.
--   Returns the resulting equation store(s) depending
--   on the split strategy.
addEqs :: MonadFresh m => SplitStrategy -> MaudeHandle
                       -> [Equal LNTerm] -> EqStore -> m [EqStore]
addEqs splitStrat hnd eqs0 eqStore =
    case unifyLNTermFactored eqs `runReader` hnd of
      (_, [])         -> return [set eqsConj falseEqConstrConj eqStore]
      (subst, substs) ->
        case splitStrat of
          SplitLater ->
            return $ [addDisj (applyEqStore hnd subst eqStore) (Disj substs)]
          SplitNow -> 
            addEqsAC (modify eqsSubst (compose subst) eqStore)
              <$> simpDisjunction hnd (Disj substs)
  where
    eqs = apply (get eqsSubst eqStore) $ trace (unlines ["addEqs: ", show eqs0]) $ eqs0
    addEqsAC eqSt (sfree, Nothing)   = [applyEqStore hnd sfree eqSt]
    addEqsAC eqSt (sfree, Just disj) =
      fromMaybe (error "addEqsSplit: impossible, splitAtPos failed")
                (splitAtPos (applyEqStore hnd sfree (addDisj eqSt (Disj disj))) 0)

-- | Apply a substitution to an equation store and bring resulting equations into
--   normal form again by using unification.
applyEqStore :: MaudeHandle -> LNSubst -> EqStore -> EqStore
applyEqStore hnd asubst eqStore
    | dom asubst `intersect` varsRange asubst /= [] || trace (show ("applyEqStore", asubst, eqStore)) False
    = error $ "applyS2EqStore: dom and vrange not disjoint for `"++show asubst++"'"
    | otherwise
    = modify eqsConj (fmap ((Disj . concatMap applyBound . getDisj))) $
        set eqsSubst newsubst eqStore
  where
    newsubst = asubst `compose` get eqsSubst eqStore
    applyBound s = map (restrictVFresh (varsRange newsubst ++ domVFresh s)) $ 
        (`runReader` hnd) $ unifyLNTerm
          [ Equal (apply newsubst (varTerm $ lv)) t
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
addRuleVariants :: (Disj (LNSubstVFresh)) -> EqStore -> EqStore
addRuleVariants (Disj substs) eqStore
    | dom freeSubst `intersect` concatMap domVFresh substs /= []
    = error $ "addRuleVariants: Nonempty intersection between domain of variants and free substitution. "
              ++"This case has not been implemented, add rule variants earlier."
    | otherwise = addDisj eqStore (Disj substs)
  where
    freeSubst = get eqsSubst eqStore

-- | Return the set of variables that is constrained by disjunction at give position.
constrainedVarsPos :: EqStore -> Int -> [LVar]
constrainedVarsPos eqStore k
    | k < length conj = frees (conj!!k)
    | otherwise       = []
  where
    conj = getConj . get eqsConj $ eqStore

-- Internal functions
----------------------------------------------------------------------

-- | Add a disjunction to the equation store at the beginning
addDisj :: EqStore -> (Disj (LNSubstVFresh)) -> EqStore
addDisj eqStore disj = modify eqsConj ((Conj [disj]) `mappend`) eqStore


-- | @splitEqStoreAt eqs i@ takes the disjunction at position @i@ in @eqs@
--   and returns a list of resulting substitutions and the equality store
--   with the remaining equations.
splitAtPos :: EqStore -> Int -> Maybe [EqStore]
splitAtPos eqStore i
    | i `notElem` eqSplits eqStore = Nothing
    | otherwise = Just $ map (\d -> set eqsConj (conjNew d) eqStore) disj
  where
    conj = getConj $ get eqsConj eqStore
    disj = getDisj $ conj !! i
    conjNew d = Conj $ take i conj ++ [Disj [d]] ++ drop (i+1) conj

-- Simplifying disjunctions
----------------------------------------------------------------------

-- | Simplify given disjunction via EqStore simplification. Obtains fresh
--   names for variables from the underlying 'MonadFresh'.
simpDisjunction :: MonadFresh m
                => MaudeHandle
                -> Disj (LNSubstVFresh)
                -> m (LNSubst, Maybe [LNSubstVFresh])
simpDisjunction hnd disj0 = do
    eqStore' <- simp hnd eqStore
    return (get eqsSubst eqStore', wrap $ get eqsConj eqStore')
  where
    eqStore = set eqsConj (Conj [disj0]) $ emptyEqStore
    wrap (Conj [])          = Nothing
    wrap (Conj [Disj disj]) = Just $ disj
    wrap conj               =
        error ("simplifyDisjunction: imposible, unexpected conjuction `"
               ++ show conj ++ "'")

-- Simplification
----------------------------------------------------------------------

-- | @simp eqStore@ simplifies the equation store.
simp :: MonadFresh m => MaudeHandle -> EqStore -> m EqStore
simp hnd eqStore = (`execStateT` (trace (show ("eqStore", eqStore)) eqStore)) $ whileTrue (simp1 hnd)


-- | @simp1@ tries to execute one simplification step
--   for the equation store. It returns @True@ if
--   the equation store was modified.
simp1 :: MonadFresh m => MaudeHandle -> StateT EqStore m Bool
simp1 hnd = do
    s <- MS.get
    b1 <- simpMinimize
    b2 <- simpRemoveRenamings
    b3 <- simpEmptyDisj
    b4 <- foreachDisj hnd simpSingleton
    b5 <- foreachDisj hnd simpAbstractSortedVar
    b6 <- foreachDisj hnd simpIdentify
    b7 <- foreachDisj hnd simpAbstractFun
    b8 <- foreachDisj hnd simpAbstractName
    s' <- MS.get
    (trace (show ("simp:", [b1, b2, b3, b4, b5, b6, b7, b8], s, s'))) $ return $ (or [b1, b2, b3, b4, b5, b6, b7, b8])

-- | Remove variable renamings in fresh substitutions.
simpRemoveRenamings :: MonadFresh m => StateT EqStore m Bool
simpRemoveRenamings = do
    conj <- gets (get eqsConj)
    let (conj',changed) =
           runState (traverse (traverse rmRenamings) conj) False
    when changed $ MS.modify (set eqsConj conj')
    return changed
  where 
    rmRenamings :: LNSubstVFresh -> State Bool LNSubstVFresh
    rmRenamings subst = do
        let subst' = removeRenamings subst
        when (domVFresh subst /= domVFresh subst') $ put True
        return subst'

-- | If empty disjunction is found, the whole conjunct
--   can be simplified to False.
simpEmptyDisj :: MonadFresh m => StateT EqStore m Bool
simpEmptyDisj = do
    conj <- gets (get eqsConj)
    if (F.any (==falseDisj) conj && conj /= falseEqConstrConj)
      then MS.modify (set eqsConj falseEqConstrConj) >> return True
      else return False

-- | If there is a singleton disjunction, it can be
--   composed with the free substitution.
simpSingleton :: MonadFresh m => Disj LNSubstVFresh
                              -> m (Maybe (Maybe LNSubst, [Disj LNSubstVFresh]))
simpSingleton (Disj [subst0]) = do
    subst <- freshToFree subst0
    return (Just (Just subst, []))
simpSingleton _               = return Nothing


-- | If all substitutions @si@ map a variable @v@ to terms with the same
--   outermost function symbol @f@, then they all contain the common factor
--   @{v |-> f(x1,..,xk)}@ for fresh variables xi and we can replace
--   @x |-> ..@ by @{x1 |-> ti1, x2 |-> ti2, ..}@ in all substitutions @si@.
simpAbstractFun :: MonadFresh m => Disj LNSubstVFresh
                             -> m (Maybe (Maybe LNSubst, [Disj LNSubstVFresh]))
simpAbstractFun (Disj [])             = return Nothing
simpAbstractFun (Disj (subst:others)) = case commonOperators of
    []           -> return Nothing
    -- abstract all arguments
    (v, o, argss@(args:_)):_ | all ((==length args) . length) argss -> do
        fvars <- mapM (\_ -> freshLVar "x" LSortMsg) args
        let substs' = zipWith (abstractAll v fvars) (subst:others) argss
            fsubst  = substFromList [(v, FApp o (map varTerm fvars))]
        return $ Just (Just $ fsubst, [Disj substs'])
    -- abstract first two arguments
    (v, o@(AC _), argss):_ -> do
        fv1 <- freshLVar "x" LSortMsg
        fv2 <- freshLVar "x" LSortMsg
        let substs' = zipWith (abstractTwo o v fv1 fv2) (subst:others) argss
            fsubst  = substFromList [(v, FApp o (map varTerm [fv1,fv2]))]
        return $ Just (Just $ fsubst, [Disj substs'])
    (_, _ ,_):_ ->
      error "simpAbstract: impossible, invalid arities or List operator encountered."
  where
    commonOperators = do
        (v, FApp o args) <- substToListVFresh subst
        let images = map (\s -> imageOfVFresh s v) others
            argss  = [ args' | Just (FApp o' args') <- images, o' == o ]
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
        newMappings (a:as)  = [(fv1, a),  (fv2, FApp o as)]


-- | If all substitutions @si@ map a variable @v@ to the same name @n@,
--   then they all contain the common factor 
--   @{v |-> n}@ and we can remove @{v -> n} from all substitutions @si@
simpAbstractName :: MonadFresh m => Disj LNSubstVFresh
                                 -> m (Maybe (Maybe LNSubst, [Disj LNSubstVFresh]))
simpAbstractName (Disj [])             = return Nothing
simpAbstractName (Disj (subst:others)) = case commonNames of
    []           -> return Nothing
    (v, c):_     ->
        return $ Just (Just $ substFromList [(v, c)]
                      , [Disj (map (\s -> restrictVFresh (delete v (domVFresh s)) s) (subst:others))])
        
  where
    commonNames = do
        (v, c@(Lit (Con _))) <- substToListVFresh subst
        let images = map (\s -> imageOfVFresh s v) others
        guard (length images == length [ () | Just c' <- images, c' == c])
        return (v, c)

-- | If all substitutions @si@ map a variable @v@ to variables @xi@ of the same
--   sort @s@ then they all contain the common factor 
--   @{v |-> y}@ for a fresh variable of sort @s@
--   and we can replace @{v -> xi}@ by @{y -> xi} in all substitutions @si@
simpAbstractSortedVar :: MonadFresh m => Disj LNSubstVFresh
                                      -> m (Maybe (Maybe LNSubst, [Disj LNSubstVFresh]))
simpAbstractSortedVar (Disj [])             = return Nothing
simpAbstractSortedVar (Disj (subst:others)) = case commonSortedVar of
    []            -> return Nothing
    (v, s, lvs):_ -> do
        fv <- freshLVar (lvarName v) s
        return $ Just (Just $ substFromList [(v, varTerm fv)]
                      , [Disj (zipWith (replaceMapping v fv) lvs (subst:others))])
  where
    commonSortedVar = do
        (v, (Lit (Var lx))) <- substToListVFresh subst
        guard (sortCompare (lvarSort v)  (lvarSort lx) == Just GT)
        let images = map (\s -> imageOfVFresh s v) others
            -- FIXME: could be generalized to choose topsort s of all images if s < sortOf v
            --        could also be generalized to terms of a given sort
            goodImages = [ ly | Just (Lit (Var ly)) <- images, lvarSort lx == lvarSort ly]
        guard (length images == length goodImages)
        return (v, lvarSort lx, (lx:goodImages))
    replaceMapping v fv lv sigma =
        substFromListVFresh $ (filter ((/=v) . fst) $ substToListVFresh sigma) ++ [(fv, varTerm lv)]



-- | If all substitutions @si@ map two variables @x@ and @y@ to identical terms @ti@,
--   then they all contain the common factor @{x |-> y} for a fresh variable @z@
--   and we can remove @{x |-> ti}@ from all @si@.
simpIdentify :: MonadFresh m => Disj (LNSubstVFresh)
                             -> m (Maybe (Maybe LNSubst, [Disj LNSubstVFresh]))
simpIdentify (Disj [])             = return Nothing
simpIdentify (Disj (subst:others)) = case equalImgPairs of
    []         -> return Nothing
    ((v,v'):_) -> do
      let (vkeep, vremove) = case sortCompare (lvarSort v) (lvarSort v') of
                               Just GT -> (v', v)
                               Just _  -> (v, v')
                               Nothing -> error $ "EquationStore.simpIdentify: impossible, variables with incomparable sorts: "
                                                  ++ show v ++" and "++ show v'
      return $ Just (Just  (substFromList [(vremove, varTerm vkeep)]),
                     [Disj (map (removeMappings [vkeep]) (subst:others))])
  where
    equalImgPairs = do
        (v,t)    <- substToListVFresh subst
        (v', t') <- substToListVFresh subst
        guard (t == t' && v < v' && all (agrees_on v v') others)
        return (v,v')
    agrees_on v v' s =
        imageOfVFresh s v == imageOfVFresh s v' && isJust (imageOfVFresh s v)
    removeMappings vs s = restrictVFresh (domVFresh s \\ vs) s

-- | Traverse disjunctions without msgBefore fact in conjunction and
--   execute @f@ until it returns @Just (mfreeSubst, disjs)@.
--   Then the @disjs@ is inserted at the current position, if @mfreeSubst@ is
--   @Just freesubst@, then it is applied to the equation store. @True@ is
--   returned if any modifications took place.
foreachDisj :: MonadFresh m
            => MaudeHandle
            -> (Disj (LNSubstVFresh) -> m (Maybe (Maybe LNSubst, [Disj LNSubstVFresh])))
            -> StateT EqStore m Bool
foreachDisj hnd f = do
    conj <- gets (get eqsConj)
    go [] (getConj conj)
  where
    go _     []         = return False
    go lefts (d:rights) = do
        b <- lift $ f d
        case b of
          Nothing              -> go (d:lefts) rights
          Just (msubst, disjs) -> do
            MS.modify (set eqsConj (Conj (reverse lefts ++ disjs ++ rights)))
            maybe (return ()) (\s -> MS.modify (applyEqStore hnd s)) msubst
            return True


-- Renaming and subsumption
----------------------------------------------------------------------

-- | Simplify by removing substitutions that occur twice in a disjunct.
--   We could generalize this function by using AC-equality or subsumption.
simpMinimize :: MonadFresh m => StateT EqStore m Bool
simpMinimize = do
    eqs <- MS.get
    let eqs' = modify eqsConj (fmap (Disj . sortednub . getDisj)) eqs
    MS.put eqs'
    return (eqs /= eqs')

{-

        
t2 = simpAbstract (Disj (map substFromListVFresh [s1,s2])) `evalFresh` nothingUsed
  where s1 = [(lx1,pair(y1,y2))]
        s2 = [(lx1,pair(inv(y1),inv(y2)))]


t3 = simpAbstract (Disj (map substFromListVFresh [s1,s2,s3])) `evalFresh` nothingUsed
  where s1 = [(lx1, mult [y1,y2] )]
        s2 = [(lx1, mult [inv(y1), inv(y2), inv(y3)])]
        s3 = [(lx1, mult[y5, y6, y7, y8])]


t4 = simpIdentify (Disj (map substFromListVFresh [s1,s2])) `evalFresh` nothingUsed
  where s1 = [(lx1, mult [y1,y2,y3] ), (lx2, mult [y1,y2,y3] )]
        s2 = [(lx1, mult [inv(y1), inv(y2), inv(y3)]), (lx2, mult [inv(y1), inv(y2), inv(y3)])]

-}

{-
t5 = simpAbstractFun (Disj (map substFromListVFresh [s1,s2,s3])) `evalFresh` nothingUsed
  where s1 = [(lx1, mult [y1,y2] )]
        s2 = [(lx1, x3)]
        s3 = [(lx1, mult[y5, y6, y7, y8])]

t6 = simpIdentify (Disj (map substFromListVFresh [s1,s2,s3])) `evalFresh` nothingUsed
  where s1 = [(lx1, mult [y1,y2,y3] ), (lx2, mult [y1,y2,y3] )]
        s2 = [(lx1, mult [inv(y1), inv(y2), inv(y3)]), (lx2, mult [inv(y1), inv(y2), inv(y3)])]
        s3 = [(lx1, y1), (lx2, y2)]

-}