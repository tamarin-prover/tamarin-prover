{-# LANGUAGE TypeOperators   #-}

-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- System simplification functions that were originally contained in the Dot module 
-- but which we now do on a System when generating an abstract graph.
module Theory.Constraint.System.Graph.Simplification (
      simplifySystem
    , compressSystem
  )
  where

import qualified Data.Map                 as M
import           Data.Maybe
import qualified Data.Set                 as S
import           Data.List                (foldl')
import           Control.Basics
import           Extension.Data.Label
-- import           Theory.Constraint.System
import           Theory                   
import qualified Data.DAG.Simple          as Dag
import           Data.Monoid              (Any(..))
import           Utils.Misc

------------------------------------------------------------------------------
-- Compressed versions of a sequent (originally from Dot module)
------------------------------------------------------------------------------

-- | Drop 'Less' atoms entailed by the edges of the 'System'.
dropEntailedOrdConstraints :: System -> System
dropEntailedOrdConstraints se =
    modify sLessAtoms (S.filter (not . entailed)) se
  where
    edges               = rawEdgeRel se
    entailed (from, to, _) = to `S.member` Dag.reachableSet [from] edges

-- | Unsound compression of the sequent that drops fully connected learns and
-- knows nodes.
compressSystem :: System -> System
compressSystem se0 =
    foldl' (flip tryHideNodeId) se (frees (get sLessAtoms se, get sNodes se))
  where
    se = dropEntailedOrdConstraints se0

-- | Simplify the system up to the sent level, 
-- | for level 3, we will simplify the lesses of system by transitive reduction
-- | for level 2, we will apply the transitive reduction but keep the 
-- | formula constraint 
-- | for level 1, there's no transitive reduction applied
simplifySystem :: Int -> System -> System
simplifySystem i sys
    | i==2 = transitiveReduction sys False
    | i==3 = transitiveReduction sys True
    | otherwise = sys

-- | Simplify the system by transitive reduction (constraint of formula won't  
-- | be applied if totalRed is False) but not for a system which has a graph cyclic
transitiveReduction :: System -> Bool -> System
transitiveReduction sys totalRed=
    if Dag.cyclic oldLesses
        then sys
        else   modify sLessAtoms
            ( S.intersection ( S.fromList newLesses) ) sys
    where
        oldLessesWithR = S.toList $ get sLessAtoms sys
        oldLesses = rawLessRel sys
        newLesses = if totalRed
            then [(x,y,z)| (x,y,z)<- oldLessesWithR,
                            (x,y) `elem` (Dag.transRed oldLesses) ]
            else [(x,y,z)| (x,y,z)<- oldLessesWithR,
                            (x,y) `elem` (Dag.transRed oldLesses) || z == Formula || z == Adversary ]


-- | @hideTransferNode v se@ hides node @v@ in sequent @se@ if it is a
-- transfer node; i.e., a node annotated with a rule that is one of the
-- special intruder rules or a rule with with at most one premise and
-- at most one conclusion and both premises and conclusions have incoming
-- respectively outgoing edges.
--
-- The compression is chosen such that unly uninteresting nodes are that have
-- no open goal are suppressed.
tryHideNodeId :: NodeId -> System -> System
tryHideNodeId v se = fromMaybe se $ do
    guard $  (lvarSort v == LSortNode)
          && notOccursIn unsolvedChains
          && notOccursIn (get sFormulas)
    maybe hideAction hideRule (M.lookup v $ get sNodes se)
  where
    selectPart :: (System :-> S.Set a) -> (a -> Bool) -> [a]
    selectPart l p = filter p $ S.toList $ get l se

    notOccursIn :: HasFrees a => (System -> a) -> Bool
    notOccursIn proj = not $ getAny $ foldFrees (Any . (v ==)) $ proj se

    -- hide KU-actions deducing pairs, inverses, and simple terms
    hideAction = do
        guard $  not (null kuActions)
              && all eligibleTerm kuActions
              && all (\(i, j, _) -> not (i == j)) lNews
              && notOccursIn (standardActionAtoms)
              && notOccursIn (get sLastAtom)
              && notOccursIn (get sEdges)

        return $ modify sLessAtoms ( (`S.union` S.fromList lNews)
                                   . (`S.difference` S.fromList lIns)
                                   . (`S.difference` S.fromList lOuts)
                                   )
               $ modify sGoals (\m -> foldl' removeAction m kuActions)
               $ se
      where
        kuActions            = [ x | x@(i,_,_) <- kuActionAtoms se, i == v ]
        eligibleTerm (_,_,m) =
            isPair m || isInverse m || sortOfLNTerm m == LSortPub || sortOfLNTerm m == LSortNat

        removeAction m (i, fa, _) = M.delete (ActionG i fa) m

        lIns  = selectPart sLessAtoms ((v ==) . snd3)
        lOuts = selectPart sLessAtoms ((v ==) . fst3)
        lNews = [ (i, j, r) | (i, _, _) <- lIns, (_, j, r) <- lOuts ]

    -- hide a rule, if it is not "too complicated"
    hideRule :: RuleACInst -> Maybe System
    hideRule ru = do
        guard $  eligibleRule
              && ( length eIns  == length (get rPrems ru) )
              && ( length eOuts == length (get rConcs ru) )
              && ( all (not . selfEdge) eNews             )
              && notOccursIn (get sLastAtom)
              && notOccursIn (get sLessAtoms)
              && notOccursIn (unsolvedActionAtoms)

        return $ modify sEdges ( (`S.union` S.fromList eNews)
                               . (`S.difference` S.fromList eIns)
                               . (`S.difference` S.fromList eOuts)
                               )
               $ modify sNodes (M.delete v)
               $ se
      where
        eIns  = selectPart sEdges ((v ==) . nodePremNode . eTgt)
        eOuts = selectPart sEdges ((v ==) . nodeConcNode . eSrc)
        eNews = [ Edge cIn pOut | Edge cIn _ <- eIns, Edge _ pOut <- eOuts ]

        selfEdge (Edge cIn pOut) = nodeConcNode cIn == nodePremNode pOut

        eligibleRule =
             any ($ ru) [isISendRule, isIRecvRule, isCoerceRule, isFreshRule]
          || ( null (get rActs ru) &&
               all (\l -> length (get l ru) <= 1) [rPrems, rConcs]
             )
