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
import           Theory                   
import qualified Data.DAG.Simple          as Dag
import           Data.Monoid              (Any(..))

------------------------------------------------------------------------------
-- Compressed versions of a sequent (originally from Dot module)
------------------------------------------------------------------------------

-- | Drop 'Less' atoms entailed by the edges of the 'System'.
dropEntailedOrdConstraints :: System -> System
dropEntailedOrdConstraints se =
    modify sLessAtoms (S.filter (not . entailed)) se
  where
    edges               = rawEdgeRel se
    entailed (LessAtom from to _) = to `S.member` Dag.reachableSet [from] edges

-- | Unsound compression of the sequent that drops fully connected learns and
-- knows nodes.
compressSystem :: System -> System
compressSystem se0 =
    foldl' (flip tryHideNodeId) se (frees (get sLessAtoms se, get sNodes se))
  where
    se = dropEntailedOrdConstraints se0

-- | Simplify the system by applying different levels of simplification.
-- Level 3: Transitive reduction + collapse adversary subgraphs
-- Level 2: Transitive reduction preserving Formula and Adversary constraints
-- Level 1 or other: No simplification
simplifySystem :: Int -> System -> System
simplifySystem i sys
    | i == 2    = transitiveReduction sys False
    | i == 3    = collapseAllAdversarySubgraphs (transitiveReduction sys True)
    | otherwise = sys

-- | Simplify the system by transitive reduction.
-- If totalRed is False, Formula and Adversary constraints are preserved.
-- Does not apply if the graph has cycles.
transitiveReduction :: System -> Bool -> System
transitiveReduction sys totalRed =
    if Dag.cyclic oldLesses
        then sys
        else modify sLessAtoms (S.intersection (S.fromList newLesses)) sys
    where
        oldLessesWithR = S.toList $ get sLessAtoms sys
        oldLesses = rawLessRel sys
        newLesses = if totalRed
            then [ la | la@(LessAtom x y _) <- oldLessesWithR,
                        (x,y) `elem` Dag.transRed oldLesses ]
            else [ la | la@(LessAtom x y z) <- oldLessesWithR,
                        (x,y) `elem` Dag.transRed oldLesses || z == Formula || z == Adversary ]

-- | Collapse the adversary subgraph by replacing it with direct edges from sources to sinks.
-- This simplification removes internal adversary cluster nodes while preserving sinks.
-- Sinks are kept because they may have outgoing edges to non-adversary nodes.
collapseAdversarySubgraph :: System -> System
collapseAdversarySubgraph sys =
    let adversaryCluster = findAdversaryCluster sys
    in if S.null adversaryCluster
       then sys
       else
           let sinks = getSinkNodesInSubset sys adversaryCluster
               (sourceEdges, sourceLessAtoms) = getEdgesIntoSubset sys adversaryCluster
               edgesToSinks = S.fromList
                   [ Edge src (sinkNode, tgtPremIdx)
                   | Edge src (_, tgtPremIdx) <- S.toList sourceEdges
                   , sinkNode <- S.toList sinks
                   ]
               lessAtomsToSinks = S.fromList
                   [ LessAtom smaller sinkNode reason
                   | LessAtom smaller _ reason <- S.toList sourceLessAtoms
                   , sinkNode <- S.toList sinks
                   ]
               nodesToRemove = adversaryCluster `S.difference` sinks
               reducedSystem = removeSubgraph sys nodesToRemove
           in set sLessAtoms (S.union (get sLessAtoms reducedSystem) lessAtomsToSinks) $
              set sEdges (S.union (get sEdges reducedSystem) edgesToSinks) reducedSystem

-- | Repeatedly collapse adversary subgraphs until a fixpoint is reached.
-- Stops when no more internal nodes can be removed.
collapseAllAdversarySubgraphs :: System -> System
collapseAllAdversarySubgraphs sys =
    let collapsed = collapseAdversarySubgraph sys
    in if M.size (get sNodes sys) == M.size (get sNodes collapsed)
       then sys
       else collapseAllAdversarySubgraphs collapsed


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
              && all (\(LessAtom i j _) -> i /= j) lNews
              && notOccursIn standardActionAtoms
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

        lIns  = selectPart sLessAtoms ((v ==) . get laLarger)
        lOuts = selectPart sLessAtoms ((v ==) . get laSmaller)
        lNews = [ LessAtom i j r | (LessAtom i _ _) <- lIns, (LessAtom _ j r) <- lOuts ]

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
