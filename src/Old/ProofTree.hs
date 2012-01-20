{-# LANGUAGE TypeSynonymInstances,PatternGuards,FlexibleInstances,DeriveDataTypeable,OverloadedStrings #-}
module ProofTree where

import SymbolicDerivationGraph

import qualified Data.Set as S
import Data.List
import Control.Monad
import Debug.Trace
import Term hiding ( Rule )
import Data.Ord

-- ***************************************************************************
-- Proof Tree (or Search Tree)
-- ***************************************************************************

data ProofTree = Explored TransRule SDG [ProofTree]
               | Unexplored SDG
 deriving (Show,Eq,Ord)

getUnexplored :: ProofTree -> [SDG]
getUnexplored (Unexplored sdg) = [sdg]
getUnexplored (Explored _ _ sdgs) = concatMap getUnexplored sdgs

getExplored :: ProofTree -> [([Int],TransRule,SDG)]
getExplored pt0 = go [] pt0
 where go _pos (Unexplored _) = []
       go pos (Explored trule sdg sdgs) = (reverse pos,trule,sdg):(concat $ zipWith (\ansdg i -> go (i:pos) ansdg) sdgs [1..])

-- TODO: add positions to output of contradictions
showProofTreeStats :: ProofTree -> String
showProofTreeStats pt = "Contradictions: \n"++unlines contradiction++
                        "states: "++(show $ length expl + length unexpl)++" unexplored: "++(show $ length unexpl)++"\n"
                        ++"realized: "++(show realizedL)
                        ++ " solveAssms:"++(show solveAssmsL)
                        ++ " solveChain:"++(show solveChainL)++"\n"
                        ++ "stepUnique:"++(show stepUniqueL)
                        ++ " concKnowUnique:"++(show concKnowUniqueL)
                        ++ " contradiction:"++(show contradictionL)++"\n"       
 where expl = getExplored pt
       unexpl = getUnexplored pt
       realizedL       = length [ () | (_,Realized,_sdg) <- expl ]
       solveAssmsL     = length [ () | (_,SolveAssm _,_sdg) <- expl ]
       solveChainL     = length [ () | (_,SolveChain,_sdg) <- expl ]
       stepUniqueL     = length [ () | (_,StepUnique,_sdg) <- expl ]
       concKnowUniqueL = length [ () | (_,ConcKnowUnique,_sdg) <- expl ]
       contradictionL = length [ () | (_,Contradiction _,_sdg) <- expl ]
       contradiction = [ (show p++" "++c) | (p,Contradiction c,_sdg) <- expl, not ("Not strictly atomic" `isPrefixOf` c) ]

-- | @getRootSDG pt@ returns the @sdg@ associated to the root of @pt@
getRootSDG :: ProofTree -> SDG
getRootSDG (Explored _ sdg _) = sdg
getRootSDG (Unexplored sdg) = sdg

getSDGAt :: [Int] -> ProofTree -> Maybe SDG
getSDGAt [] (Explored _ sdg _) = Just sdg
getSDGAt [] (Unexplored sdg) = Just sdg
getSDGAt (i:is) (Explored _ _ pts) | length pts <= i = getSDGAt is (pts!!i)
                                   | otherwise = Nothing
getSDGAt _ (Unexplored _) = Nothing

gotoPos :: [Int] -> ZProofTree -> Maybe ZProofTree
gotoPos pos0 zpt0 = go pos0 (root zpt0)
 where
  go [] zpt = Just zpt
  go (i:is) zpt =
    case downLeft zpt of
     Just zpt' -> goRight is zpt' i
     Nothing -> Nothing
  goRight is zpt 1 = go is zpt
  goRight is zpt k =
    case right zpt of
      Just zpt' -> goRight is zpt' (k-1)
      Nothing -> Nothing

-- | @isUnexplored pt@ returns @True@ if @pt@ is unexplored
isUnexplored :: ProofTree -> Bool
isUnexplored (Unexplored _) = True
isUnexplored _ = False

-- | @isUnexplored pt@ returns @True@ if @pt@ is unexplored
isRealized :: ProofTree -> Bool
isRealized (Explored Realized _ []) = True
isRealized _ = False

-- | @showStatus pt@ returns a string representation of @pt@s status
showStatus :: ProofTree -> String
showStatus (Explored rule _ _) = show rule
showStatus (Unexplored _) = "Unexplored"

-- ^ a path in a ProofTree
data Path = Top
          | Node (TransRule,SDG) [ProofTree] Path [ProofTree]
 deriving (Show,Eq,Ord)

-- | A zipper into a proof tree
data ZProofTree = ZPT ProofTree Path
 deriving (Show,Eq,Ord)

-- | @getFocused zpt@ returns the focused ProofTree in @zpt@
getFocused :: ZProofTree -> ProofTree
getFocused (ZPT pt _) = pt

-- | @proofTreeToZipper pt@ returns a zipper focusing on the root of @pt@
proofTreeToZipper :: ProofTree -> ZProofTree
proofTreeToZipper pt = ZPT pt Top

-- | @zipperToProofTree zpt@ returns the ProofTree represented by the zipper
zipperToProofTree :: ZProofTree -> ProofTree
zipperToProofTree (ZPT pt Top) = pt
zipperToProofTree zpt =
  case up zpt of
    Nothing -> error "impossible"
    Just zpt' -> zipperToProofTree zpt'

-- * Zipper navigation

root :: ZProofTree -> ZProofTree
root = proofTreeToZipper . zipperToProofTree

-- | @up zpt@ moves the focus in @zpt@ up if possible
up :: ZProofTree -> Maybe ZProofTree
up (ZPT _ Top) = Nothing
up (ZPT pt (Node (tr,sdg) ls pathUp rs)) =
  Just (ZPT (Explored tr sdg (reverse ls++(pt:rs))) pathUp)

-- | @downLeft zpt@ moves the focus in @zpt@ down to the leftmost element if possible
downLeft :: ZProofTree -> Maybe ZProofTree
downLeft (ZPT (Unexplored _)  _) = Nothing
downLeft (ZPT (Explored _ _ []) _) = Nothing
downLeft (ZPT (Explored tr sdg (pt:pts)) p) = Just (ZPT pt (Node (tr,sdg) [] p pts))

-- | @downRight zpt@ moves the focus in @zpt@ down to the rightmost element if possible
downRight :: ZProofTree -> Maybe ZProofTree
downRight (ZPT (Unexplored _) _) = Nothing
downRight (ZPT (Explored _ _ []) _) = Nothing
downRight (ZPT (Explored tr sdg pts) p) = Just (ZPT (last pts) (Node (tr,sdg) (reverse (init pts)) p []))

-- | @right zpt@ moves the focus in @zpt@ to the right if possible
right :: ZProofTree -> Maybe ZProofTree
right (ZPT _ Top) = Nothing
right (ZPT pt (Node sdg ls pathUp (r:rs))) =
  Just (ZPT r (Node sdg (pt:ls) pathUp rs))
right _ = Nothing

-- | @left zpt@ moves the focus in @zpt@ to the left if possible
left :: ZProofTree -> Maybe ZProofTree
left (ZPT _ Top) = Nothing
left (ZPT pt (Node sdg (l:ls) pathUp rs)) =
  Just (ZPT l (Node sdg ls pathUp (pt:rs)))
left _ = Nothing

-- | @nextWhere test zpt@ goes to the next (according to the preorder) position where @test@ holds for
--   the focused ProofTree
nextWhere :: (ProofTree -> Bool) -> ZProofTree -> Maybe ZProofTree
nextWhere test pt0 =
  case downLeft pt0 of
    Just pt' -> if test (getFocused pt') then Just pt' else nextWhere test pt'
    Nothing -> goRight pt0
 where
  goRight pt =
    case right pt of
      Just pt' -> if isUnexplored (getFocused pt') then Just pt' else nextWhere test pt'
      Nothing -> goUp pt
  -- go up until going right is possible again
  goUp pt = case up pt of
              Nothing -> Nothing
              Just pt' -> goRight pt'

-- | @prevWhere test zpt@ goes to the previous (according to the preorder) position where @test@ holds for
--   the focused ProofTree
prevWhere :: (ProofTree -> Bool) -> ZProofTree -> Maybe ZProofTree
prevWhere test pt0 =
  case left pt0 of
    Just pt' -> goDownRight pt'
    Nothing -> goUp pt0
 where
  goDownRight pt =
    case downRight pt of
      Just pt' -> goDownRight pt'
      Nothing -> if test (getFocused pt) then Just pt else prevWhere test pt
  goUp pt = case up pt of
              Nothing -> Nothing
              Just pt' -> if test (getFocused pt') then Just pt' else prevWhere test pt'

firstWhere :: (ProofTree -> Bool) -> ZProofTree -> Maybe ZProofTree
firstWhere test zpt0 | test (getFocused zpt0) = Just zpt0
firstWhere test zpt0 | otherwise = nextWhere test zpt0

nextRealized :: ZProofTree -> Maybe ZProofTree
nextRealized = nextWhere isRealized

nextUnexplored :: ZProofTree -> Maybe ZProofTree
nextUnexplored = nextWhere isUnexplored

nthUnexplored :: Int -> ZProofTree -> Maybe ZProofTree
nthUnexplored k zpt0 = do
  zpt <- (firstWhere isUnexplored (root zpt0))
  foldM (\azpt () -> nextUnexplored azpt) zpt  $ replicate k ()

prevUnexplored :: ZProofTree -> Maybe ZProofTree
prevUnexplored = prevWhere isUnexplored

prevRealized :: ZProofTree -> Maybe ZProofTree
prevRealized = prevWhere isRealized

next :: ZProofTree -> Maybe ZProofTree
next = nextWhere (const True)

prev :: ZProofTree -> Maybe ZProofTree
prev = prevWhere (const True)

-- ***************************************************************************
-- Tactics that transform a proof tree
-- ***************************************************************************

-- TODO: might generalize this, can also be useful to transform a dead or explored
--       ProofTree as long as it is model-preserving
transformCurrent :: (SDG -> Either String (TransRule,[SDG])) -> ZProofTree -> Either String ZProofTree
transformCurrent _ (ZPT (Explored _ _ _) _)  = Left "exploreCurrent: already explored"
transformCurrent tr (ZPT (Unexplored sdg) path) =
  case tr sdg of
    Right (rule, sdgs) -> Right $ ZPT (Explored rule sdg (map Unexplored sdgs)) path
    Left err -> Left err

-- | @solveCurrent ruleSet i zpt@ applies either forward or source to the assumption
--   or chain pointed to by @i@ for the given @ruleSet@
solveCurrent :: RuleSet -> Int -> ZProofTree -> Either String ZProofTree
solveCurrent ruleSet i zpt =
 case drop i (nonTrivialAssms sdg) of
   assm:_ -> transformCurrent (solveAssm ruleSet assm) zpt
   [] ->
     case drop (i-length (nonTrivialAssms sdg)) (S.toList (sChains sdg)) of
       chain:_ -> transformCurrent (solveChain ruleSet chain) zpt
       _ -> Left "invalid goal index"
 where sdg = getRootSDG. getFocused $ zpt

-- | @stepUniqueAuto zpt@ selects two protocol steps (not thread creation) with the
--   same threadid (const or var) and step number and applies stepUnique
stepUniqueAuto :: ZProofTree -> Either String ZProofTree
stepUniqueAuto zpt = 
  case filter noDisjAssm $ equalStepPairs sdg of
    (protoStep1,protoStep2):_ ->
--        trace (show (protoStep1, protoStep2)) $
        transformCurrent (stepUnique protoStep1 protoStep2) zpt
    [] -> Left "not applicable to any protocol steps"
 where sdg = getRootSDG . getFocused $ zpt
       noDisjAssm (r1,r2) = null [() | Disj _ <- rAssms r1 ] && null [() | Disj _ <- rAssms r2 ]

-- | @stepUniqueAuto zpt@ selects two protocol steps (not thread creation) with the
--   same threadid (const or var) and step number and applies stepUnique
premiseSourceUniqueAuto :: ZProofTree -> Either String ZProofTree
premiseSourceUniqueAuto zpt = 
  case duplicatePremiseSources sdg of
    (e1,e2):_ ->
--        trace (show (protoStep1, protoStep2)) $
        transformCurrent (premiseSourceUnique e1 e2) zpt
    [] -> Left "premiseSourceUnique not applicable"
 where sdg = getRootSDG . getFocused $ zpt


-- | @conclusionKnowsUniqueAuto@ selects two nodes with the same knowledge conclusion
--   and applies conclusionKnowsUnique
conclusionKnowsUniqueAuto :: ZProofTree -> Either String ZProofTree
conclusionKnowsUniqueAuto zpt = 
  case equalKnowsConclusionPairs sdg of
    (protoStep1,protoStep2):_ ->
--        trace (show (protoStep1, protoStep2)) $
        transformCurrent (stepUnique protoStep1 protoStep2) zpt
    [] -> Left "not applicable to any protocol steps"
 where sdg = getRootSDG . getFocused $ zpt

-- | @solveChainAuto ruleSet zpt@ selects the first chain and solves it
solveChainAuto :: RuleSet -> ZProofTree -> Either String ZProofTree
solveChainAuto ruleSet zpt =
  case S.toList . sChains . getRootSDG . getFocused $ zpt of
    chain:_ -> transformCurrent (solveChain ruleSet chain) zpt
    _ -> Left "no chains found, rule not applicable"

solveAssmAutoBy :: ([Assm] -> [Assm]) -> RuleSet -> ZProofTree -> Either String ZProofTree
solveAssmAutoBy f ruleSet zpt =
  case f . nonTrivialAssms . getRootSDG . getFocused $ zpt of
    assm:_ -> transformCurrent (solveAssm ruleSet assm) zpt
    _ -> Left "solveAssmsAutoBy open premise found that matches, rule not applicable"

solveAssmProtoAuto :: RuleSet -> ZProofTree -> Either String ZProofTree
solveAssmProtoAuto = solveAssmAutoBy (filter (isProto . uncurry getAssm))

solveAssmEqAuto :: RuleSet -> ZProofTree -> Either String ZProofTree
solveAssmEqAuto = solveAssmAutoBy (filter (isEq . uncurry getAssm))

solveAssmDisjAuto :: RuleSet -> ZProofTree -> Either String ZProofTree
solveAssmDisjAuto = solveAssmAutoBy (filter (isDisj . uncurry getAssm))

solveAssmKnowsAuto :: RuleSet -> ZProofTree -> Either String ZProofTree
solveAssmKnowsAuto = solveAssmAutoBy (sortAssms . filter (isKnows . uncurry getAssm))
 where sortAssms = sortBy (comparing (\(r,i) -> rankFact $ getAssm r i))
       rankFact (K (N (Op2 tg1 (Atom (Const _)) (Op1 tg2 _))))
        | tg1 == nonTag && tg2 == tidTag = 0
        | otherwise = (7::Int)
       rankFact (K (N (Op2 tg1 (Atom (Var _)) (Atom (Var _))))) 
         | tg1 == nonTag = 0
         | otherwise = 7
       rankFact (K (N (Op2 tg _ _)))
         | tg `elem` [encATag,encSTag,signTag] =  5
         | otherwise = 7
       rankFact (K (N (Op1 tg1 (Atom (Var _)))))
         | tg1 == skTag = 10
         | otherwise = 7
       rankFact (K (N (Op1 tg1 (Op1 tg2 (Atom (Var _))))))
         | tg1 == skTag && tg2 == agentTag = 10
         | otherwise = 7
       rankFact _ = 7

solveAssmSKHonestAuto :: RuleSet -> ZProofTree -> Either String ZProofTree
solveAssmSKHonestAuto = solveAssmAutoBy (filter (isHonestSK . uncurry getAssm))
 where isHonestSK (K (N (Op1 tg1 (Op1 tg2 (Op1 tg3 _)))))
           | tg1 == skTag && tg2 == agentTag && tg3 == honTag = True
           | otherwise = False
       isHonestSK _ = False

solveAssmPairAuto :: RuleSet -> ZProofTree -> Either String ZProofTree
solveAssmPairAuto = solveAssmAutoBy (filter (isPair . uncurry getAssm))

-- * Tacticals

anywhere :: (ZProofTree -> Either String ZProofTree) -> ZProofTree -> Either String ZProofTree
anywhere trans zpt0 = go mzpt
 where rzpt = root zpt0
       mzpt = if isUnexplored (getFocused rzpt) then Just rzpt else nextUnexplored rzpt
       go Nothing = Left "not applicable anywhere"
       go (Just zpt) = case trans zpt of
                         Left _err -> go (nextUnexplored zpt)
                         Right zpt' -> Right zpt'

iterateRule :: (ZProofTree -> Either String ZProofTree) -> ZProofTree -> Either String ZProofTree
iterateRule trans zpt0 = go True zpt0
 where go firstCall zpt = case trans zpt of
                            Right zpt' -> go False zpt'
                            Left err -> if firstCall then Left err else Right zpt

iterateRuleUpTo :: Int -> (ZProofTree -> Either String ZProofTree) -> ZProofTree -> Either String ZProofTree
iterateRuleUpTo k trans zpt0 = go k zpt0
 where go 0 zpt = Right zpt
       go l zpt = case trans zpt of
                    Right zpt' -> go (l-1) zpt'
                    Left err -> if l==k then Left err else Right zpt

orRule :: (ZProofTree -> Either String ZProofTree) -> (ZProofTree -> Either String ZProofTree)
       -> ZProofTree -> Either String ZProofTree
orRule trans1 trans2 zpt =
  case trans1 zpt of
    Left _err -> trans2 zpt
    Right zpt' -> Right zpt'

here :: (ZProofTree -> Either String ZProofTree) -> ZProofTree -> Either String ZProofTree
here trans (ZPT zpt path) =
  case trans (proofTreeToZipper zpt) of
    Right zpt' -> Right $ ZPT (zipperToProofTree zpt') path
    Left err -> Left err

-- * Combined tactics

auto :: RuleSet -> ZProofTree -> Either String ZProofTree
auto ruleSet = iterateRule (step ruleSet)

step :: RuleSet -> ZProofTree -> Either String ZProofTree
step ruleSet = anywhere (eagerRule ruleSet)

eagerRule :: RuleSet -> ZProofTree -> Either String ZProofTree
eagerRule ruleSet =
  (transformCurrent contradictionSDG `orRule`
   premiseSourceUniqueAuto `orRule`
   conclusionKnowsUniqueAuto `orRule`
--   solveAssmDisjAuto ruleSet `orRule`
   solveAssmEqAuto ruleSet `orRule`
   stepUniqueAuto `orRule`
   transformCurrent realizedSDG `orRule`
   solveChainAuto ruleSet `orRule`
   solveAssmProtoAuto ruleSet `orRule`
   solveAssmPairAuto ruleSet `orRule`
   solveAssmSKHonestAuto ruleSet)

selectFst :: RuleSet -> ZProofTree -> Either String ZProofTree
selectFst ruleSet = eagerRule ruleSet `orRule` solveAssmKnowsAuto ruleSet

fullAuto :: RuleSet -> ZProofTree -> Either String ZProofTree
fullAuto ruleSet = iterateRule (anywhere (selectFst ruleSet))

eagerRule' :: RuleSet -> ZProofTree -> Either String ZProofTree
eagerRule' ruleSet =
  ((trace "foo" (transformCurrent contradictionSDG)) `orRule`
   conclusionKnowsUniqueAuto `orRule`
   premiseSourceUniqueAuto `orRule`
   stepUniqueAuto `orRule`
   transformCurrent realizedSDG `orRule`
   solveChainAuto ruleSet `orRule`
   solveAssmProtoAuto ruleSet `orRule`
   solveAssmPairAuto ruleSet `orRule`
   solveAssmSKHonestAuto ruleSet)
