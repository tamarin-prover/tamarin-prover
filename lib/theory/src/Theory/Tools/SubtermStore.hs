{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE DeriveAnyClass             #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt, Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
-- Support for reasoning with and about subterms.
module Theory.Tools.SubtermStore (
  -- ** Construction
    SubtermStore(..)
  , emptySubtermStore

  -- ** Accessors
  , addNegSubterm
  , addSubterm
  , simpSubtermStore

  -- ** Computation
  , hasSubtermCycle
  , SubtermSplit(..)
  , splitSubterm

  -- ** Pretty printing
  , prettySubtermStore
) where

import           GHC.Generics          (Generic)
--import           Logic.Connectives
import           Term.Unification
import           Theory.Text.Pretty
import           Theory.Constraint.System.Constraints
import           Theory.Model

import           Control.Monad.Fresh
import           Control.Monad.Bind
import           Control.Monad.Reader
--import           Extension.Prelude
--import           Utils.Misc

--import           Debug.Trace

import           Control.Basics
import           Control.DeepSeq
--import           Control.Monad.State   hiding (get, modify, put)
--import qualified Control.Monad.State   as MS

import           Data.Binary
--import qualified Data.Foldable         as F
import           Data.List             (sort, length)
import           Data.Maybe            (isNothing, fromMaybe)
import qualified Data.Set              as S
import           Extension.Data.Label  hiding (for, get)
import qualified Extension.Data.Label  as L
import           Data.Data
-- import           Extension.Data.Monoid

------------------------------------------------------------------------------
-- Subterm Store
------------------------------------------------------------------------------

data SubtermStore = SubtermStore {
      _negSubterms     :: S.Set (LNTerm, LNTerm)  -- negative subterms
    , _subterms :: S.Set (LNTerm, LNTerm)  -- subterms
    , _solvedSubterms  :: S.Set (LNTerm, LNTerm)  -- subterms that have been split
    , _isContradictory :: Bool
    , _oldNegSubterms  :: S.Set (LNTerm, LNTerm)  -- copy of negSubterms that is not changed by apply/HasFrees/add[Neg]Subterm
    --TODO: evaluate wether oldNegSubterms helps at all
    }
  deriving( Eq, Ord, Generic )

instance NFData SubtermStore
instance Binary SubtermStore

$(mkLabels [''SubtermStore])

-- | @emptyEqStore@ is the empty equation store.
emptySubtermStore :: SubtermStore
emptySubtermStore = SubtermStore S.empty S.empty S.empty False S.empty

addSubterm :: (LNTerm, LNTerm) -> SubtermStore -> SubtermStore
addSubterm st sst = if st `elem` L.get solvedSubterms sst
                      then sst
                      else modify subterms (S.insert st) sst  --TODO-BIG do apply stuff as in eqStore???

addNegSubterm :: (LNTerm, LNTerm) -> SubtermStore -> SubtermStore
addNegSubterm st = modify negSubterms (S.insert st)  --TODO-BIG do apply stuff as in eqStore???





-- Simplification
------------

-- does also some "cleaning up", i.e., generating goals and new equations
simpSubtermStore :: MonadFresh m => FunSig -> SubtermStore -> m (SubtermStore, [LNGuarded], [Goal])
simpSubtermStore reducible sst = do
    (sst1, newGuarded) <- simpSplitNegSt reducible sst  -- split negative subterms
    (sst2, goals) <- simpSplitSt reducible sst1  -- split positive subterms
    let sst3 = modify isContradictory (|| hasSubtermCycle reducible sst2) sst2  -- CR-rule S_chain
    -- CR-rule S_neg (negativeSubtermVars)

    return (sst3, newGuarded, goals)


    -- NOT resolve constants (already done by splitting)
    -- split negSubterms (returning equations - and ∀x.x+a=b formulas?)
    -- split level 1 of subterms (Advantage: goals do not need to be updated but only added)
    -- hasSubtermCycle
    -- set isContradictory if needed

-- | simplifies constants and returns all splitSubterm goals (even if they were present before)
-- it splits all subterms and does the following:
-- - cope with [] -> contradiction
-- - cope with [SubtermD] -> ignore
-- - cope with [TrueD] -> remove this subterm as it's true anyways
-- - cope with lists of [ACNewVarD, SubtermD...] or [EqualD...,SubtermD...] -> indicate possible split
-- 
-- if the goals are [] then no goals have to be removed (as subterms cannot go from splittable to unsplittable)
-- otherwise, all SubtermG should be removed and then replaced by this list
simpSplitSt :: MonadFresh m => FunSig -> SubtermStore -> m (SubtermStore, [Goal])
simpSplitSt reducible sst = do
    let subts = S.toList $ L.get subterms sst
    splits <- mapM (splitSubterm reducible True) subts  --recurse only one level (noRecurse = True)
    --let toIgnoreAsTheyHaveNoSplits = [ x | (x, [SubtermD y]) <- zip changedSubterms splits, x==y]
    let splittableSubterms = [ x | (x, splitCases) <- zip subts splits, length splitCases > 1]
    let toRemoveAsTrue = S.fromList [ x | (x, [TrueD]) <- zip subts splits]
    
    let sst1 = modify subterms (`S.difference` toRemoveAsTrue) sst
    let sst2 = modify isContradictory (|| [] `elem` splits) sst1
    
    return (sst2, [])  -- TODO-BIG take care that goals contain SubtermG with all splittableSubterms



simpSplitNegSt :: MonadFresh m => FunSig -> SubtermStore -> m (SubtermStore, [LNGuarded])
simpSplitNegSt reducible sst = do
    let changedNegSubterms = S.toList (L.get negSubterms sst `S.difference` L.get oldNegSubterms sst)
    splits <- concat <$> mapM (splitSubterm reducible False) changedNegSubterms
    let splitSubterms = S.fromList [eq | SubtermD eq <- splits]
    let eqFormulas = S.toList $ S.fromList [gnotAtom $ EqE (lTermToBTerm x) (lTermToBTerm y) | EqualD (x,y) <- splits]  -- ¬ x=y
    let acFormulas = S.toList $ S.fromList [closeGuarded All [newVar] [EqE smallPlus big] gfalse | ACNewVarD (smallPlus, big, newVar) <- splits] -- ∀ newVar. x+newVar=y ⇒ ⊥

    let sst1 = modify negSubterms (`S.union` splitSubterms) sst
    let sst2 = set oldNegSubterms (L.get negSubterms sst1) sst1
    let sst3 = modify isContradictory (|| TrueD `elem` splits) sst2

    return (sst3, eqFormulas ++ acFormulas)
    -- TODO-BIG take care acFormulas are not inserted twice with different newVar's !!!!!!!
    --          if z ⊏ x+y is substituted to z ⊏ x+y'+y'' then
    --          the formula ∀newVar... in the LNGuarded formulas is updated automatically correctly.
    --          We only have to add z ⊏ y', z ⊏ y'' and could remove z ⊏ y'+y'' (formerly z ⊏ y)
    --          However, I'm not sure wether removing z ⊏ y'+y'' and the corresponding ∀newVar is beneficial:
    --            ∀n. n+z ≠ y'+y'' is clearly subsumed by ∀n. n+z ≠ x+y'+y''
    --            but it is hard to search for these collisions.





-- Computation
------------


-- | Computes whether there is a cycle @t0 ⊏ x0, ..., tn ⊏ xn@ in @dag@ such that
-- @xi@ is syntactically in @t_i+1@ and not below a reducible function symbol, see @elemNotBelowReducible@
hasSubtermCycle :: FunSig -> SubtermStore -> Bool
hasSubtermCycle reducible store = isNothing $ foldM visitForest S.empty dag
  where
    -- extract dag from store
    dag :: [(LNTerm, LNTerm)]
    dag = S.toList $ L.get subterms store

    -- adapted from cyclic in Simple.hs but using tuples of LNTerm instead of LNTerm
    visitForest :: S.Set (LNTerm, LNTerm) -> (LNTerm, LNTerm) -> Maybe (S.Set (LNTerm, LNTerm))
    visitForest visited x
      | x `S.member` visited = return visited
      | otherwise            = findLoop S.empty visited x

    findLoop :: S.Set (LNTerm, LNTerm) -> S.Set (LNTerm, LNTerm) -> (LNTerm, LNTerm) -> Maybe (S.Set (LNTerm, LNTerm))
    findLoop parents visited x
      | x `S.member` parents = mzero
      | x `S.member` visited = return visited
      | otherwise            =
          S.insert x <$> foldM (findLoop parents') visited next
      where
        next     = [ (e,e') | (e,e') <- dag, elemNotBelowReducible reducible (snd x) e]
        parents' = S.insert x parents



data SubtermSplit = SubtermD    (LNTerm, LNTerm)
                  | NatSubtermD (LNTerm, LNTerm, LVar)  -- small, big, newVar
                  | EqualD      (LNTerm, LNTerm)
                  | ACNewVarD   (LNTerm, LNTerm, LVar)  -- small+newVar, big, newVar
                  | TrueD
  deriving (Eq, Ord, Show, Typeable, Data, Generic, NFData, Binary)

-- | Deconstructs a subterm according to the CR-rules S_subterm-[ac-]recurse, S_invalid and stops destructing for S_nat / S_neg-nat
-- Returns @set@ such that @small ⊏ big@ is equivalent to the disjunction of @set@
-- If the subterm is trivially false, [] is returned as the empty disjunction
splitSubterm :: MonadFresh m => FunSig -> Bool -> (LNTerm, LNTerm) -> m [SubtermSplit]
splitSubterm reducible noRecurse subterm = S.toList <$> (if noRecurse then singleStep else recurse) (SubtermD subterm)
  where
    singleStep :: MonadFresh m => SubtermSplit -> m (S.Set SubtermSplit)
    singleStep std@(SubtermD st) = fromMaybe (S.singleton std) <$> step st
    singleStep _ = error "singleStep can only be called with SubtermD"

    recurse :: MonadFresh m => SubtermSplit -> m (S.Set SubtermSplit)
    recurse std@(SubtermD st) = do
      res <- step st
      case res of
        Just entries -> S.unions <$> mapM recurse (S.toList entries)  --TODO: think wether std should be added as well [intermediate results] (for negSplit)
        Nothing -> return $ S.singleton std
    recurse x = return $ S.singleton x  -- for everything except SubtermD we stop the recursion

    -- @step@ returns nothing if @small ⊏ big@ cannot be further destructed.
    -- Else it returns @Just list@ if @small ⊏ big@ can be replaced by the disjunction of the list.
    -- It especially returns @Just []@ if @small ⊏ big@ is trivially false.
    step :: MonadFresh m => (LNTerm, LNTerm) -> m (Maybe (S.Set SubtermSplit))
    step (small, big)
      --- | onlyOnes small && l small < l big && sortOfLNTerm big == LSortNat =  -- terms like 1+1 < x+y+z
      --  return $ Just $ S.singleton TrueD  -- true
      --- | (sortOfLNTerm small == LSortNat || isMsgVar small) && sortOfLNTerm big == LSortNat = do  -- CR-rule S_nat (delayed)
      --  ac <- processAC NatPlus (small, big)
      --  return $ case ac of
      --    Right False -> Just S.empty
      --    Right True -> Just $ S.singleton TrueD
      --    Left tuple -> Just $ S.singleton $ NatSubtermD tuple
      | big `redElem` small =  -- trivially false (big == small included)
        return $ Just S.empty  -- false
      | small `redElem` big =  -- trivially true
        return $ Just $ S.singleton TrueD  -- true
      --    where
      --      onlyOnes t = all (fAppNatOne ==) $ flattenedACTerms NatPlus t
      --      l t = length $ flattenedACTerms NatPlus t
    step (_, viewTerm -> Lit (Con _)) =  -- nothing can be a strict subterm of a constant
        return $ Just S.empty  -- false
    step (small, big@(viewTerm -> Lit (Var _)))
      | isPubVar big || isFreshVar big {--|| (not (sortOfLNTerm small == LSortNat || isMsgVar small) && sortOfLNTerm big == LSortNat)-} =  -- CR-rule S_invalid
        return $ Just S.empty  -- false
    step (_, viewTerm -> Lit (Var _)) =  -- variable: do not recurse further
        return Nothing
    step (small, big@(viewTerm -> FApp (AC f) _))  -- apply CR-rule S_subterm-ac-recurse
      | AC f `S.notMember` reducible = do
        ac <- processAC f (small, big)
        return $ case ac of
          Right False -> Just S.empty
          Right True -> Just $ S.singleton TrueD
          Left (nSmall, nBig, newVar) ->
            let acSpecial = ACNewVarD (fAppAC f [nSmall, varTerm newVar], nBig, newVar)
            in Just $ acSpecial `S.insert` S.fromList (map (curry SubtermD small) (flattenedACTerms f big))
    step (small, viewTerm -> FApp (NoEq f) ts)  -- apply CR-rule S_subterm-recurse
      | NoEq f `S.notMember` reducible = do
        return $ Just $ S.unions (map (eqOrSubterm small) ts)
    step (_, viewTerm -> FApp (C _) _) =  -- we treat commutative but not associative symbols as reducible functions
        return Nothing
    step (_, viewTerm -> FApp List _) =  -- list seems to be unused (?)
        return Nothing
    step _ =  -- reducible function symbol observed (when applying subterm-[ac-]recurse)
        return Nothing

    redElem = elemNotBelowReducible reducible
    eqOrSubterm :: LNTerm -> LNTerm -> S.Set SubtermSplit
    eqOrSubterm s t = S.fromList [SubtermD (s, t), EqualD (s, t)]  -- the unifiers for the equation

    -- returns the triple @((nSmall, nBig), newVar, ac)@
    -- nSmall, nBig are small, big where terms are removed that were on both sides
    -- newVar is for the CR-rule S_neg-ac-recurse
    processAC :: MonadFresh m => ACSym -> (LNTerm, LNTerm) -> m (Either (LNTerm, LNTerm, LVar) Bool)
    processAC f (small, big) = do
        newVar <- freshLVar "newVar" (sortOfLNTerm big)  -- generate a new variable
        return $ case lists of
          (_, []) -> Right False
          ([], _) -> Right True
          (lSmall, lBig) -> Left (fAppAC f lSmall, fAppAC f lBig, newVar)
        --let term = fAppAC f [nSmall, varTerm newVar]  -- build the term = small + newVar
      where
        -- removes terms that are on both sides of the subterm
        -- lists have to be sorted before removeSame works
        removeSame (a:as, b:bs) | a == b = removeSame (as,   bs)
        removeSame (a:as, b:bs) | a < b  = first (a:) $ removeSame (as, b:bs)
        removeSame (a:as, b:bs) | a > b  = second (b:) $ removeSame (a:as, bs)
        removeSame x = x  -- one of the lists is empty

        lists = removeSame (sort $ flattenedACTerms f small, sort $ flattenedACTerms f big)


{-
-- | CR-rule *S_subterm-neg*: @s ¬⊏ x, t ⊏ x --insert--> s ¬⊏ t, s ≠ t@
negativeSubtermVars :: Reduction ChangeIndicator
negativeSubtermVars = do
  formulas <- getM sFormulas
  changelists <- mapM (\f -> case f of
      (GGuarded All [] [Subterm i j] gf) | gf == gfalse && isMsgVar (bTermToLTerm j) -> do
          subtermRel <- liftM rawSubtermRel $ getM sEqStore
          let matching = filter ((bTermToLTerm j ==) . snd) subtermRel
          mapM (\(small, _) -> do
            let smallB = lTermToBTerm small
            c1 <- insertFormula (gnotAtom $ Subterm i smallB)
            c2 <- insertFormula (gnotAtom $ EqE i smallB)
            return [c1, c2]
            ) matching
      _ -> return []
    ) (S.toList formulas)
  let changed = Changed `elem` concat (concat changelists)
  return $ if changed then Changed else Unchanged
-}


-- Instances
------------


instance HasFrees SubtermStore where
    foldFrees f (SubtermStore negSt st solvedSt _ _) =
        foldFrees f negSt <> foldFrees f st <> foldFrees f solvedSt
    foldFreesOcc  _ _ = const mempty
    mapFrees f (SubtermStore negSt st solvedSt contr oldNegSt) =
        SubtermStore <$> mapFrees f negSt
                <*> mapFrees f st
                <*> mapFrees f solvedSt
                <*> pure contr
                <*> pure oldNegSt


instance Apply SubtermStore where
    apply subst (SubtermStore a b c d e) = SubtermStore (apply subst a) (apply subst b) (apply subst c) d e


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Pretty print an 'EqStore'.
prettySubtermStore :: HighlightDocument d => SubtermStore -> d
prettySubtermStore (SubtermStore negSt st solvedSt contr _) = vcat $
  map combine $
    [("Contradictory", text "SubtermStore !!") | contr] ++
    [ ("Subterms", numbered' $ map ppSt (S.toList st))
    , ("Negative Subterms", numbered' $ map ppSt (S.toList negSt))
    , ("Solved Subterms", numbered' $ map ppSt (S.toList solvedSt))
    ]
  where
    combine (header, d) = fsep [keyword_ header <> colon, nest 2 d]

    ppSt (a,b) =
      prettyNTerm (lit (Var a)) $$ nest (3::Int) (opSubterm <-> prettyNTerm b)



-- Derived and delayed instances
--------------------------------

instance Show SubtermStore where
    show = render . prettySubtermStore