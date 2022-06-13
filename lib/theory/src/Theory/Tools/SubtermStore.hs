{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
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
  , negSubterms
  , posSubterms
  , solvedSubterms
  , isContradictory
  , oldNegSubterms
  , emptySubtermStore
  , isNatSubterm
  , rawSubtermRel

  -- ** Accessors
  , addNegSubterm
  , addSubterm
  , simpSubtermStore

  -- ** Computation
  , hasSubtermCycle
  , SubtermSplit(..)
  , splitSubterm
  , isTrueFalse

  -- ** Pretty printing
  , prettySubtermStore
) where

import           GHC.Generics          (Generic)
--import           Logic.Connectives
import           Term.Unification
import           Theory.Text.Pretty
import           Theory.Constraint.System.Constraints
import           Theory.Model
import           Term.Builtin.Convenience

import           Control.Monad.Fresh
--import           Control.Monad.Bind
--import           Control.Monad.Reader
--import           Extension.Prelude
--import           Utils.Misc

--import           Debug.Trace

import           Control.Basics
import           Control.DeepSeq
--import           Control.Monad.State   hiding (get, modify, put)
--import qualified Control.Monad.State   as MS

import           Data.Binary
--import qualified Data.Foldable         as F
import           Data.List             (sort, (\\), delete)
import           Data.Maybe            (isNothing, fromMaybe, fromJust, mapMaybe)
import qualified Data.Set              as S
import qualified Data.Map              as M
import           Extension.Data.Label  hiding (for, get)
import qualified Extension.Data.Label  as L
import           Data.Data

import           Data.Array.ST
import           Data.Array
import qualified Data.Graph            as G
import qualified Data.Tree             as T


------------------------------------------------------------------------------
-- Subterm Store
------------------------------------------------------------------------------

data SubtermStore = SubtermStore {
      _negSubterms     :: S.Set (LNTerm, LNTerm)  -- negative subterms
    , _posSubterms     :: S.Set (LNTerm, LNTerm)  -- subterms
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

isNatSubterm :: (LNTerm, LNTerm) -> Bool
isNatSubterm (small, big) = (sortOfLNTerm small == LSortNat || isMsgVar small) && sortOfLNTerm big == LSortNat

-- | used only in freshOrdering in "Simplify.hs"
-- does not include solved subterms as they are not needed for freshOrdering
rawSubtermRel :: SubtermStore -> [(LNTerm, LNTerm)]
rawSubtermRel sst = S.toList (L.get posSubterms sst)

addSubterm :: (LNTerm, LNTerm) -> SubtermStore -> SubtermStore
addSubterm st sst = if st `elem` L.get solvedSubterms sst
                      then sst
                      else modify posSubterms (S.insert st) sst  --TODO-BIG do apply stuff as in eqStore???

addNegSubterm :: (LNTerm, LNTerm) -> SubtermStore -> SubtermStore
addNegSubterm st = modify negSubterms (S.insert st)  --TODO-BIG do apply stuff as in eqStore???





-- Simplification
------------

-- does some "cleaning up" as well, i.e., generating goals and new equations
simpSubtermStore :: MonadFresh m => FunSig -> SubtermStore -> m (SubtermStore, [LNGuarded], [Goal])
simpSubtermStore reducible sst = do
    let sst0 = modify posSubterms (`S.difference` L.get solvedSubterms sst) sst  -- when a subterm gets substituted to one which is already solved
    (sst1, newFormulas) <- simpSplitNegSt reducible sst0  -- split negative subterms
    (sst2, arity1Equations, goals) <- simpSplitPosSt reducible sst1  -- split positive subterms
    let (sst3, newNegEqs) = negativeSubtermVars sst2  -- CR-rule S_neg
    let sst4 = modify isContradictory (|| hasSubtermCycle reducible sst3) sst3  -- CR-rule S_chain
    let (sst5, newNatEqs) = simpNatCycles sst4

    let allSubterms = S.toList (L.get posSubterms sst5 `S.union` L.get negSubterms sst5 `S.union` L.get solvedSubterms sst5)
    let topIsNotReducible term = case viewTerm term of
                                      FApp f _ -> f `S.notMember` reducible
                                      _        -> True
    let allSound = all (topIsNotReducible . snd) allSubterms
    
    if allSound
      then return (sst5, newFormulas ++ arity1Equations ++ newNegEqs ++ newNatEqs, goals)
      else error "there are some reducible operators on the right side of a subterm"

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
simpSplitPosSt :: MonadFresh m => FunSig -> SubtermStore -> m (SubtermStore, [LNGuarded], [Goal])
simpSplitPosSt reducible sst = do
    let subts = S.toList $ L.get posSubterms sst
    splits <- mapM (splitSubterm reducible True) subts  --recurse only one level (noRecurse = True)
    let splittableSubterms = [ SubtermG x | (x, splitCases) <- zip subts splits, splitCases `notElem` [[TrueD],[SubtermD x]] ]
    --let toIgnoreAsTheyHaveNoSplits = [ x | (x, [SubtermD y]) <- zip changedSubterms splits, x==y]
    let toRemoveAsTrue = S.fromList [ x | (x, [TrueD]) <- zip subts splits]
    let arity1Eq = [eq | [SubtermD st, EqualD eq] <- map sort splits, st `elem` L.get negSubterms sst]  --arity-one-deduction
    let arity1Formulas = [GAto $ EqE (lTermToBTerm l) (lTermToBTerm r) | (l,r) <- arity1Eq]

    let sst1 = modify posSubterms (`S.difference` toRemoveAsTrue) sst
    let sst2 = modify isContradictory (|| [] `elem` splits) sst1

    return (sst2, arity1Formulas, splittableSubterms)



simpSplitNegSt :: MonadFresh m => FunSig -> SubtermStore -> m (SubtermStore, [LNGuarded])
simpSplitNegSt reducible sst = do
    let changedNegSubterms = S.toList (L.get negSubterms sst `S.difference` L.get oldNegSubterms sst)
    splits <- concat <$> mapM (splitSubterm reducible False) changedNegSubterms
    let splitSubterms = S.fromList $ [st | SubtermD st <- splits] ++ [st | NatSubtermD st <- splits]
    let flippedNatSubterms = S.fromList [(t, s ++: fAppNatOne) | NatSubtermD (s, t) <- splits, isNatSubterm (s,t)]  -- isNatSubterm is necessary to exclude that s is a msgVar!!!
    let eqFormulas = S.toList $ S.fromList [gnotAtom $ EqE (lTermToBTerm x) (lTermToBTerm y) | EqualD (x,y) <- splits]  -- ¬ x=y
    let acFormulas = S.toList $ S.fromList [closeGuarded All [newVar] [EqE smallPlus big] gfalse | ACNewVarD ((smallPlus, big), newVar) <- splits] -- ∀ newVar. x+newVar=y ⇒ ⊥
    zippedIsFalse <- zip changedNegSubterms <$> mapM (liftM null . splitSubterm reducible False) changedNegSubterms
    let alreadyFalseNegSt = S.fromList [st | (st, True) <- zippedIsFalse]

    let sst1 = modify posSubterms (`S.union` flippedNatSubterms) sst
    let sst2 = modify negSubterms (`S.union` splitSubterms) sst1
    let sst3 = modify negSubterms (`S.difference` alreadyFalseNegSt) sst2
    let sst4 = set oldNegSubterms (L.get negSubterms sst1) sst3
    let sst5 = modify isContradictory (|| TrueD `elem` splits) sst4

    return (sst5, eqFormulas ++ acFormulas)

simpNatCycles :: SubtermStore -> (SubtermStore, [LNGuarded])
simpNatCycles sst = (sst1, equalities)
  where
    maybeEqual = natSubtermEqualities $ S.toList $ L.get posSubterms sst
    equalities = [GAto $ EqE (lTermToBTerm l) (lTermToBTerm r) | (Equal l r) <- concat maybeEqual]
    sst1 = modify isContradictory (|| isNothing maybeEqual) sst





-- Computation
------------


-- | Computes whether there is a cycle @t0 ⊏ x0, ..., tn ⊏ xn@ in @dag@ such that
-- @xi@ is syntactically in @t_i+1@ and not below a reducible function symbol, see @elemNotBelowReducible@
hasSubtermCycle :: FunSig -> SubtermStore -> Bool
hasSubtermCycle reducible store = isNothing $ foldM visitForest S.empty dag
  where
    -- extract dag from store
    dag :: [(LNTerm, LNTerm)]
    dag = S.toList $ L.get posSubterms store

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



-- if you ever want to reorder these data-names, make sure the sorting in simpSplitPosSt still works
-- i.e. SubtermD is defined before EqualD
data SubtermSplit = SubtermD    (LNTerm, LNTerm)
                  | NatSubtermD (LNTerm, LNTerm)
                  | EqualD      (LNTerm, LNTerm)
                  | ACNewVarD   ((LNTerm, LNTerm), LVar)  -- small+newVar, big, newVar
                  | TrueD
  deriving (Eq, Ord, Show, Typeable, Data, Generic, NFData, Binary)

-- | Deconstructs a subterm according to the CR-rules S_subterm-[ac-]recurse, S_invalid and stops destructing for S_nat / S_neg-nat
-- Returns a @list@ such that @small ⊏ big@ is equivalent to the disjunction of this @list@
-- If the subterm is trivially false, [] is returned as the empty disjunction
-- If the subterm is trivially true, [TrueD] is returned
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
    -- Otherwise, it returns @Just list@ if @small ⊏ big@ can be replaced by the disjunction of the list.
    -- It especially returns @Just []@ if @small ⊏ big@ is trivially false.
    step :: MonadFresh m => (LNTerm, LNTerm) -> m (Maybe (S.Set SubtermSplit))
    step (isTrueFalse reducible Nothing -> Just True) = return $ Just $ S.singleton TrueD
    step (isTrueFalse reducible Nothing -> Just False) = return $ Just S.empty
    step (small, big)
      | (sortOfLNTerm small == LSortNat || isMsgVar small) && sortOfLNTerm big == LSortNat = do  -- CR-rule S_nat (delayed)
        return $ case processACSubterm NatPlus (small, big) of
          Right _ -> error "somehow, isTrueFalse did not catch this case 1"
          Left (s, t) -> Just $ S.singleton $ NatSubtermD (s, t)
    step (_, viewTerm -> Lit (Var _)) =  -- variable: do not recurse further
        return Nothing
    step (small, big@(viewTerm -> FApp (AC f) _))  -- apply CR-rule S_subterm-ac-recurse
      | AC f `S.notMember` reducible = do
        case processACSubterm f (small, fAppAC f $ flattenedACTerms f big) of
          Right _ -> error "somehow, isTrueFalse did not catch this case 2"
          Left (nSmall, nBig) -> do
            newVar <- freshLVar "newVar" (sortOfLNTerm big)  -- generate a new variable
            let acSpecial = ACNewVarD ((fAppAC f [nSmall, varTerm newVar], nBig), newVar)
            return $ Just $ acSpecial `S.insert` S.fromList (map (curry SubtermD small) (flattenedACTerms f big))
    step (small, viewTerm -> FApp (NoEq f) ts)  -- apply CR-rule S_subterm-recurse
      | NoEq f `S.notMember` reducible = do
        return $ Just $ S.unions (map (eqOrSubterm small) ts)
    step (_, viewTerm -> FApp (C _) _) =  -- we treat commutative but not associative symbols as reducible functions
        return Nothing
    step (_, viewTerm -> FApp List _) =  -- list seems to be unused (?)
        return Nothing
    step _ =  -- reducible function symbol observed (when applying subterm-[ac-]recurse)
        return Nothing

    eqOrSubterm :: LNTerm -> LNTerm -> S.Set SubtermSplit
    eqOrSubterm s t = S.fromList [SubtermD (s, t), EqualD (s, t)]  -- the unifiers for the equation

-- | returns the triple @(nSmall, nBig, newVar)@
-- @nSmall@, @nBig@ are @small@, @big@ where terms are removed that were on both sides
-- @newVar@ is for the CR-rule S_neg-ac-recurse
-- If the subterm is trivially true or false, a corresponding boolean is returned
processACSubterm :: ACSym -> (LNTerm, LNTerm) -> Either (LNTerm, LNTerm) Bool
processACSubterm f (small, big) =
    case lists of
      (_, []) -> Right False
      ([], _) -> Right True
      (lSmall, lBig) -> Left (fAppAC f lSmall, fAppAC f lBig)
    --let term = fAppAC f [nSmall, varTerm newVar]  -- build the term = small + newVar
  where
    -- removes terms that are on both sides of the subterm
    -- lists have to be sorted before removeSame works
    removeSame (a:as, b:bs) | a == b = removeSame (as, bs)
    removeSame (a:as, b:bs) | a < b  = first (a:) $ removeSame (as, b:bs)
    removeSame (a:as, b:bs) | a > b  = second (b:) $ removeSame (a:as, bs)
    removeSame x = x  -- one of the lists is empty

    lists = removeSame (sort $ flattenedACTerms f small, sort $ flattenedACTerms f big)


-- | evaluates wether the the subterm reduces to True/False under all substitutions
-- If the correctness of the subterm depends on the substitutions, "Nothing" is returned
-- If a subtermStore is given, possible cycles are checked as well (more computation time)
isTrueFalse :: FunSig -> Maybe SubtermStore -> (LNTerm, LNTerm) -> Maybe Bool
isTrueFalse reducible Nothing (small, big)
      | onlyOnes small && l small < l big && sortOfLNTerm big == LSortNat = Just True -- terms like 1+1 < x+y+z
      | (sortOfLNTerm small == LSortNat || isMsgVar small) && sortOfLNTerm big == LSortNat = do  -- CR-rule S_nat (delayed)
              case processACSubterm NatPlus (small, big) of
                Right res -> Just res  -- false or true
                Left _    -> Nothing
      | big `redElem` small = Just False -- trivially false (big == small included)
      | small `redElem` big = Just True -- trivially true (small /= big because of the previous condition)
          where
            onlyOnes t = all (fAppNatOne ==) $ flattenedACTerms NatPlus t
            l t = length $ flattenedACTerms NatPlus t
            redElem = elemNotBelowReducible reducible
isTrueFalse _ Nothing (_, viewTerm -> Lit (Con _)) = Just False -- nothing can be a strict subterm of a constant
isTrueFalse _ Nothing (small, big@(viewTerm -> Lit (Var _)))
      | isPubVar big || isFreshVar big || (not (sortOfLNTerm small == LSortNat || isMsgVar small) && sortOfLNTerm big == LSortNat) = Just False -- CR-rule S_invalid
isTrueFalse reducible Nothing (small, big@(viewTerm -> FApp (AC f) _))  -- apply CR-rule S_subterm-ac-recurse
      | AC f `S.notMember` reducible =
        case processACSubterm f (small, fAppAC f $ flattenedACTerms f big) of
          Right res -> Just res
          Left _    -> Nothing
isTrueFalse _ Nothing _ = Nothing
isTrueFalse reducible (Just sst) st =
      case isTrueFalse reducible Nothing st of
        Just res -> Just res
        Nothing -> if isInside && not isNegatedInside      then Just True
                   else if isNegatedInside && not isInside then Just False
                   else if cyclic || natCyclic             then Just False
                   else                                         Nothing
          where
            sstInserted = modify posSubterms (S.insert st) sst
            cyclic = hasSubtermCycle reducible sstInserted
            natCyclic = isNothing $ natSubtermEqualities $ S.toList $ L.get posSubterms sstInserted

            negSt = L.get negSubterms sst
            posSt = L.get posSubterms sst `S.union` L.get solvedSubterms sst
            isNegatedInside = st `S.member` negSt
            isInside = st `S.member` posSt




-- | CR-rule *S_subterm-neg*: @s ¬⊏ r, t ⊏ r --insert--> s ¬⊏ t, s ≠ t@
negativeSubtermVars :: SubtermStore -> (SubtermStore, [LNGuarded])
negativeSubtermVars sst = (sst1, equations)
  where
    negSt = S.toList $ L.get negSubterms sst
    posSt = S.toList (L.get posSubterms sst `S.union` L.get solvedSubterms sst)
    pairs = [(x, y) | x@(_,a) <- negSt, y@(_,b) <- posSt, a == b]
    equations = [gnotAtom $ EqE (lTermToBTerm x) (lTermToBTerm y) | ((x,_),(y,_)) <- pairs]
    newSubterms = S.fromList [(x,y) | ((x,_),(y,_)) <- pairs]
    sst1 = modify negSubterms (`S.union` newSubterms) sst



-- | This procedure generates some (not all!) equalities that are implied by the natSubterm relation.
-- It filters the relation for UTVPI's (≤ 2 vars) and performs the algorithm from the following paper:
-- "An Efficient Decision Procedure for UTVPI Constraints"
-- It returns @Nothing@ if the list of UTVPI's leads to a contradiction
-- Otherwise it returns @Just eqns@ where eqns is the list of equations implied by the UTVPI's
-- @eqns@ may be empty
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
      formatEdge :: (LNTerm, LNTerm) -> [(((Bool,LVar), (Bool,LVar)), Int)]  -- empty list for invalid (>2 vars, nonNat); otherwise 1 or 2 elements
      formatEdge st | not $ isNatSubterm st = []
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


instance Apply LNSubst SubtermStore where
    apply subst (SubtermStore a b c d e) = SubtermStore (apply subst a) (apply subst b) (apply subst c) d e


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Pretty print an 'EqStore'.
prettySubtermStore :: HighlightDocument d => SubtermStore -> d
prettySubtermStore (SubtermStore negSt posSt solvedSt contr _) = vcat $
  map combine $
    [("Contradictory", text "yes") | contr] ++
    [ ("Negative Subterms", numbered' $ map ppSt (S.toList negSt)) | not allEmpty] ++
    [ ("Subterms", numbered' $ map ppSt (S.toList posSt)) | not allEmpty] ++
    [ ("Solved Subterms", numbered' $ map ppSt (S.toList solvedSt)) | not allEmpty]
  where
    allEmpty = negSt == S.empty && posSt == S.empty && solvedSt == S.empty
    combine (header, d) = fsep [keyword_ header <> colon, nest 2 d]

    ppSt (a,b) =
      prettyNTerm a $$ nest (3::Int) (opSubterm <-> prettyNTerm b)



-- Derived and delayed instances
--------------------------------

instance Show SubtermStore where
    show = render . prettySubtermStore
