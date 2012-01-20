{-# LANGUAGE TypeSynonymInstances,PatternGuards,FlexibleInstances,DeriveDataTypeable,OverloadedStrings #-}
module SymbolicDerivationGraph where

import Term hiding ( Rule )
import Substitution
import Utils
import UnifyACMaude

import qualified Data.Set as S
import Data.Set ( Set )
import Data.List
import qualified Data.Map as M
import Data.Maybe
-- import Debug.Trace
import Control.Monad

-- *****************************************************************************
-- * Common Definitions
-- *****************************************************************************

-- | The name of a rule is a String
type RuleName = String

-- | An @NVTerm@ denotes either a term @norm(t)@ or a term @t@ such
--   that t\sigma is in normal form for all normalized substitutions \sigma
data NVTerm = T VTerm  -- ^ @norm(t)@
            | N VTerm  -- ^ @t@ in normal form
 deriving (Eq,Ord)

-- ***************************************************************************
-- * Facts and rules
-- ***************************************************************************

-- ** Facts

-- | There are three different types of facts
data Fact = K NVTerm          -- ^ a knowledge fact
          | S NVTerm         -- ^ a protocol sends a term
          | F String [NVTerm] -- ^ a protocol state
 deriving (Ord, Eq)

isSend :: Fact -> Bool
isSend (S {}) = True
isSend _      = False

isKnows :: Fact -> Bool
isKnows (K {}) = True
isKnows _      = False

isFact :: Fact -> Bool
isFact (F _) = True
isFact _ = False

-- | @unifyFactAux f1 f2@ returns @Nothing@ if there is no unifier for f1 and f2
--   or @Just eq@ such that the set of unifiers of @f1@ and @f2@ is equal to the
--   set of unifiers of @eq@
unifyFactAux :: Fact -> Fact -> Maybe (Equal VTerm)
unifyFactAux (S (N s)) (S (N t)) = Just (Equal s t)
unifyFactAux (S _) (S _) = error "cannot unify norm(t)"
unifyFactAux (K (N s)) (K (N t)) = Just (Equal s t)
unifyFactAux (K _) (K _) = error "cannot unify norm(t)"
unifyFactAux (P rn1 rs1 xs) (P rn2 rs2 ys)
  | not $ null ([True | T _ <- xs]++[True | T _ <- ys]) = error "cannot unify norm(t)"
  | rn1 /= rn2 || rs1 /= rs2 || length xs /= length ys = Nothing
  | otherwise = Just (Equal (listToTerm ms1) (listToTerm ms2))
     where ms1 = [t | N t <- xs]
           ms2 = [t | N t <- ys]
unifyFactAux _ _  = Nothing


-- | @unifyFact f1 f2@ returns a (minimal?) complete set of unifiers for f1 and f2
unifyFact :: Fact -> Fact -> [Subst]
unifyFact f1 f2 = case unifyFactAux f1 f2 of
                    Just (Equal s t) -> unify' s t
                    Nothing -> []

-- | @unifyFacts eqs@ returns a (minimal?) complete set of unifiers for eqs
unifyFacts :: [Equal Fact] -> [Subst]
unifyFacts feqs = case mapM (\(Equal s t) -> unifyFactAux s t) feqs of
                    Just eqs -> unifyMultiple eqs
                    Nothing -> []

-- ** Rules and Edges

data Existential = EVar Int | EFresh Int
  deriving (Ord,Eq)

-- | A @Rule@ denotes a set rewriting rule with existential variables
data Rule = Rule {rName :: RuleName,
                  rAssms :: [Fact],
                  rEx :: [Existential],
                  rConcs :: [Fact]}
 deriving (Ord, Eq)

-- | @assmIndices r@ returns the valid assumption indices for @r@
assmIndices :: Rule -> [Int]
assmIndices r = [0 .. length (rAssms r) - 1]

-- | @concIndices r@ returns the valid conclusion indices for @r@
concIndices :: Rule -> [Int]
concIndices r = [0 .. length (rConcs r) - 1]

-- | @getAssm r i@ returns the @i@-th assumption of @r@
getAssm :: Rule -> Int -> Fact
getAssm r i = if not $ i < length (rAssms r) then error ("getAssm: "++ show (r,i)) else rAssms r !! i

-- | @getConc r i@ returns the @i@-th conclusion of @r@
getConc :: Rule -> Int -> Fact
getConc r i = if not $ i < length (rConcs r) then error ("getConc: "++ show (r,i)) else rConcs r !! i

-- | @unifyRule r1 r2@ returns a (minimal?) complete set of unifiers for r1 and r2
unifyRule :: Rule -> Rule -> [Subst]
unifyRule  r1 r2
  | rName r1 /= rName r2 = []
  | length (rAssms r1) /= length (rAssms r2) || length (rConcs r1) /= length (rConcs r2)
    = error "rule name equal, but different premise and conclusion list"
  | not (null $ rEx r1) || not (null $ rEx r2) = error "cannot unify rules with existentials"
  | otherwise = unifyFacts (zipWith Equal (rAssms r1++rConcs r1) (rAssms r2++rConcs r2))

renameRuleAwayFromSDG :: SDG -> Rule -> Rule
renameRuleAwayFromSDG sdg rule = renameRuleAwayFrom (varsOf sdg++varsOf rule) rule

renameRuleAwayFrom :: [Int] -> Rule -> Rule
renameRuleAwayFrom vs rule = apply subst rule
 where
  subst    = substFromListS "renameTermAwayFrom" [(i,Atom (Var (mapVar i))) | i <- ruleVars]
  ruleVars = varsOf rule \\ (varsOf (rEx rule)) -- do not rename existentially bound variables
  mapVar = mapping ruleVars vs

getStep :: Rule -> Maybe Step
getStep (Rule _ ((P _rname step _):_) _ _) = Just step
getStep _ = Nothing

getThreadId ::  Rule -> Maybe NVTerm
getThreadId (Rule _ ((P _rname _ (atid:_)):_) _ _) = Just atid
getThreadId _ = Nothing

-- ***************************************************************************
-- * Symbolic derivation graphs
-- ***************************************************************************

-- | an assumption occurence in a rule
--   TODO: might use a phantom type/GADT for Assm/Conc and Edge/Chain.
type Assm = (Rule, Int)

-- | a conclusion occurence in a rule
type Conc = (Rule,Int)

-- | An @Edge@ has a source conclusion @(rs,is)@ and a target assumption @(rt,it)@
data Edge = Edge Conc Assm
 deriving (Ord, Eq)

-- | A @Chain@ is an @Edge@ with a special meaning.
type Chain = Edge

-- | A symbolic derivation graph represents a set of derivation graphs, its
--   models. The models of a symbolic derivation graph are denoted [|sdg|].
--   Invariant: source and target in edges and chains must be in nodes.
--   TODO: think about using sNodes only for unconnected nodes
data SDG = SDG {sNodes :: Set Rule, sEdges :: Set Edge, sChains :: Set Chain}
 deriving (Ord, Eq)

-- | returns all the thread ids used in the given SDG
threadIdsSDG :: SDG -> [Int]
threadIdsSDG sdg = [atid | Rule _ruleName [] _ [P _roleName 0 [N (Op1 _tidTag (Atom (Const atid)))]]
                           <- S.toList $ sNodes sdg ]

threadId :: Int -> VTerm
threadId i = Op1 tidTag (Atom (Const i))

-- | returns a fresh thread id for the given SDG
freshThreadIdSDG :: SDG -> Int
freshThreadIdSDG sdg = (maximum (0:threadIdsSDG sdg)) + 1

-- ** some accessor utility functions for SDGs

-- | @assmSDG sdg@ returns all assumptions of rules in @sdg@
assmsSDG :: SDG -> [Fact]
assmsSDG sdg = [ getAssm r i |  r <- S.toList $ sNodes sdg, i <- assmIndices r ]

-- | @concsSDG sdg@ returns all conclusions of rules in @sdg@
concsSDG :: SDG -> [Fact]
concsSDG sdg = [ getConc r i |  r <- S.toList $ sNodes sdg, i <- concIndices r ]

-- | @sourceFactsSDG sdg@ returns all source conclusions of edges in @sdg@
sourceFactsSDG :: SDG -> [Fact]
sourceFactsSDG sdg = [ getConc r1 i1 | Edge (r1,i1) (_r2,_i2) <- S.toList $ sEdges sdg ]

-- | @targetFactsSDG sdg@ returns all target assumptions of edges in @sdg@
targetFactsSDG :: SDG -> [Fact]
targetFactsSDG sdg = [ getAssm r2 i2 | Edge (_r1,_i1) (r2,i2) <- S.toList $ sEdges sdg ]

-- | @sourceFactsChainsSDG sdg@ returns all source conclusions of chains in @sdg@
sourceFactsChainsSDG :: SDG -> [Fact]
sourceFactsChainsSDG sdg = [ getConc r1 i1 | Edge (r1,i1) (_r2,_i2) <- S.toList $ sChains sdg ]

-- | @targetFactsChainsDG sdg@ returns all target assumptions of chains in @sdg@
targetFactsChainsSDG :: SDG -> [Fact]
targetFactsChainsSDG sdg = [ getAssm r2 i2 | Edge (_r1,_i1) (r2,i2) <- S.toList $ sChains sdg ]

-- | @targetsSDG sdg@ returns all target assumption occurences of edges in @sdg@
targetsSDG :: SDG -> [Assm]
targetsSDG sdg = [ (r2,i2) | Edge (_r1,_i1) (r2,i2) <- S.toList $ sEdges sdg ]

-- | @sourcesSDG sdg@ returns all source conclusion occurences of edges in @sdg@
sourcesSDG :: SDG -> [Conc]
sourcesSDG sdg = [ (r1,i1) | Edge (r1,i1) (_r2,_i2) <- S.toList $ sEdges sdg ]

-- | @targetsChainsSDG sdg@ returns all target assumption occurences of chains in @sdg@
targetsChainsSDG :: SDG -> [Assm]
targetsChainsSDG sdg = [ (r2,i2) | Edge (_r1,_i1) (r2,i2) <- S.toList $ sChains sdg ]

-- | @sourcesChainsSDG sdg@ returns all source conclusion occurences of chains in @sdg@
sourcesChainsSDG :: SDG -> [Conc]
sourcesChainsSDG sdg = [ (r1,i1) | Edge (r1,i1) (_r2,_i2) <- S.toList $ sChains sdg ]

-- ** some modification functions for SDGs

-- | @insertNode r sdg@ inserts the rule instance @r@ into @sdg@
insertNode :: Rule -> SDG -> SDG
insertNode r sdg = sdg {sNodes = S.insert r (sNodes sdg)}

-- | @insertEdge e sdg@ inserts the edge @e@ into @sdg@
insertEdge :: Edge -> SDG -> SDG
insertEdge e sdg = sdg {sEdges = S.insert e (sEdges sdg)}

-- | @insertChain c sdg@ inserts the edge @c@ into @sdg@
insertChain :: Edge -> SDG -> SDG
insertChain e sdg = sdg {sChains = S.insert e (sChains sdg)}

-- | @removeChain c sdg@ inserts the edge @c@ into @sdg@
deleteChain :: Edge -> SDG -> SDG
deleteChain e sdg = sdg {sChains = S.delete e (sChains sdg)}

-- | @removeChain c sdg@ inserts the edge @c@ into @sdg@
deleteNode :: Rule -> SDG -> SDG
deleteNode n sdg = sdg {sNodes = S.delete n (sNodes sdg)}

-- | emptySDG is an empty @SDG@
emptySDG :: SDG
emptySDG = SDG S.empty S.empty S.empty

-- | @sdgFromGoal rs@ transforms the rule @rs@ into an $SDG@
sdgFromGoal :: Rule -> SDG
sdgFromGoal goalRule = SDG (S.fromList [goalRule]) S.empty S.empty

nodeWithIndex :: Int -> SDG -> Maybe Rule
nodeWithIndex i sdg = lookup i $ zip [1..] (S.toList $ sNodes sdg)

-- ***************************************************************************
-- SDG transformations
-- ***************************************************************************

-- * Transformation Rules
--   A rule takes an SDG and returns all the resulting SDG such that
--   [| inputSDG |] = UNION_{sdg \in outputSDGs} [| sdg |].
--   Don't care choices are given as arguments, nondeterministic choices
--   are handled by the list monad in the functions.
--   There are four main transformation rules:
--   solveAssm, solveChain, stepUnique, and conclusionKnowsUnique.

data TransRule = SolveAssm String | SolveInvertible | SolveChain | StepUnique | ConcKnowUnique
               | PremiseSourceUnique | Realized | Contradiction String 
 deriving (Show,Eq,Ord)

-- | a rule set with rules of different types
data RuleSet = RS { forwardRules :: [Rule],  -- ^ forward rules, includes learn
                    backwardRules :: [Rule], -- ^ backward rules (includes initial intruder knowledge rules)
                    stepRules :: [Rule],     -- ^ protocol step rules
                    threadRules :: [Rule],   -- ^ thread creation rules
                    ikRules :: [Rule]        -- ^ initial intruder knowledge rules (no premises)
                  }
  deriving (Ord,Show,Eq)

-- | map a function @f@ over every rule in the given ruleset
mapRuleSet :: (Rule -> Rule) -> RuleSet -> RuleSet
mapRuleSet f (RS as bs cs ds iks) = RS (map f as) (map f bs) (map f cs) (map f ds) (map f iks)

-- * solveAssm transformation:
--   try to find the source of a message or a protocol state by resolving backwards with a rule
--   or adding a chain from a send event.

-- | @solveAssm ruleSet assm sdg@ returns all patterns where the open
--   assumption @assm@ is closed.
solveAssm :: RuleSet -> Assm -> SDG -> Either String (TransRule,[SDG])
solveAssm ruleSet0 assm@(r,i) sdg
  -- eagerly apply backwards Pair rule (TODO: we assume that there is no other rule that unifies here)
  | K m <- getAssm r i, isPair (K m) = Right (SolveInvertible,bwK)
  | K m <- getAssm r i = Right (SolveAssm (show m),bwK ++ chs)
  | P _ 0 _ <- getAssm r i = Right (SolveAssm "thread",threads)
  | P _ _ _ <- getAssm r i = Right (SolveAssm "bwStep",bwP)
  | Eq (N t1) (N t2) <- getAssm r i = Right (SolveAssm "EQ",solveEq t1 t2 sdg)
  | Disj fs <- getAssm r i = Right (SolveAssm "splitDisj", splitDisjs assm fs sdg)
  | otherwise = Left "solveAssm: invalid argument"
 where
  bwK = resolveBackward (backwardRules ruleSet) assm sdg
  bwP = resolveBackward (stepRules ruleSet) assm sdg
  threads = threadCreation (threadRules ruleSet) assm sdg
  chs = addChains (stepRules ruleSet ++ ikRules ruleSet) assm sdg
  ruleSet = mapRuleSet (renameRuleAwayFromSDG sdg) ruleSet0

isPair :: Fact -> Bool
isPair (K (N (Op2 tg _ _)))
  | tg == pairTag = True
  | otherwise = False
isPair _ = False

splitDisjs :: Assm -> [Fact] -> SDG -> [SDG]
splitDisjs (r,i) fs sdg  = do
  f <- fs
  let r' = r {rAssms = take i assms ++ [f]++drop (i+1) assms}
  return $ sdg {sNodes  = S.map (replaceBy r') (sNodes sdg),
                sChains = S.map (mapEdge (replaceBy r')) (sChains sdg),
                sEdges  = S.map (mapEdge (replaceBy r')) (sEdges sdg)}
 where replaceBy r' n | n == r = r'
                      | otherwise = n
       mapEdge f (Edge (n1,i1) (n2,i2)) = Edge (f n1,i1) (f n2,i2)
       assms = rAssms r

solveEq :: VTerm -> VTerm -> SDG -> [SDG]
solveEq t1 t2 sdg = do
  subst <- unify' t1 t2
  return $ apply subst sdg
  
-- | Unifies conclusions of given rules with assm
resolveBackward :: [Rule] -> Assm -> SDG -> [SDG]
resolveBackward rbw assm@(ra,ai) sdg = do
  let assmFact = getAssm ra ai
  r <- rbw
  i <- concIndices r
  let concFact = getConc r i
  sigma <- unifyFact assmFact concFact
  return $ apply sigma $ insertEdge (Edge (r,i) assm) (insertNode r sdg)

-- | creates a chain for every send conclusion of a given rule to the assm
addChains :: [Rule] -> Assm -> SDG -> [SDG]
addChains rstep assm sdg = do
  r <- rstep
  i <- concIndices r
  guard (isSend (getConc r i) || isKnows (getConc r i))
  return $ insertChain (Edge (r,i) assm) (insertNode r sdg)

-- | Return all patterns where the open protocol step assumption
--   with step number 0 is closed by either adding a new thread
--   creation event or using an existing one. In the second case,
--   it might be useful to apply threadStepUnique afterwards to
--   identifiy steps that must be identical now.
threadCreation :: [Rule] -> Assm ->  SDG -> [SDG]
threadCreation tRules assm@(ar,ai) sdg = newThreads ++ oldThreads
 where
  assmFact = getAssm ar ai
  freshTid = freshThreadIdSDG sdg
  newThreads = do
    (Rule ruleName [] [_tid] [P roleName 0 [_tid']]) <- tRules
    let concFact = P roleName 0 [N $ threadId freshTid]
        r = Rule ruleName [] [EFresh freshTid] [concFact] -- instantiate threadId
    sigma <- unifyFact assmFact concFact
    return $ apply sigma $ insertEdge (Edge (r,0) assm) (insertNode r sdg)
  oldThreads = do
    r@(Rule _ruleName [] [_atid'] [concFact@(P _roleName 0 [(N (Op1 _tidtag (Atom (Const _atid))))])])
      <- S.toList $ sNodes sdg
    sigma <- unifyFact assmFact concFact
    return $ apply sigma $ insertEdge (Edge (r,0) assm) sdg

-- * Forward transformation:
--   try to solve a chain constraint by forward search.
--   Note that there is no overlap between resolveForward
--   and solveDirect since open assumptions are never from
--   forward rules which are the rules exclusively used for
--   resolveForward.

solveChain :: RuleSet -> Chain -> SDG -> Either String (TransRule,[SDG])
solveChain ruleSet0 chain sdg = Right (SolveChain,sdirect ++ fws)
 where
  fws = resolveForward (forwardRules ruleSet) chain sdg
  sdirect = solveDirect chain sdg
  ruleSet = mapRuleSet (renameRuleAwayFromSDG sdg) ruleSet0
  -- TODO: add initial intruder rules without assumptions,
  --       they might contain decryptable messages

resolveForward :: [Rule] -> Chain -> SDG -> [SDG]
resolveForward rfw chain@(Edge (cr,ci) assm) sdg = do
  r <- rfw
  let i = 0 -- TODO: first assm is main assumption
      assmFact = getAssm r 0
      concFact = getConc cr ci
  sigma <- unifyFact assmFact concFact
  let sdg' = insertChain (Edge (r,i) assm)
               (insertEdge (Edge (cr,ci) (r,i))
                 (insertNode r (deleteChain chain sdg)))
  return $ apply sigma $ sdg'

solveDirect :: Chain -> SDG -> [SDG]
solveDirect chain@(Edge (cr,ci) (ar,ai)) sdg = do
  let concFact = getConc cr ci
      assmFact = getAssm ar ai
  sigma <- unifyFact concFact assmFact
  return $ apply sigma $ insertEdge chain (deleteChain chain sdg)

-- * threadStepUnique
--   ensures that a thread id and step number uniquely identifies a
--   protocol step

-- | @threadStepUnique r1 r2@ takes rules @r1@ and @r2@ with identical
--   thread id (constant or variable) and step numbers and returns all
--   possible patterns where they are identified.
--   TODO: check that r1 and r2 are rule instances with the same thread and step id
stepUnique :: Rule -> Rule -> SDG -> Either String (TransRule,[SDG])
stepUnique r1 r2 sdg
  | getStep r1 == getStep r1 && isJust (getStep r1) && getThreadId r1 == getThreadId r2 && isJust (getThreadId r1)
    && null [() | Disj _ <- rAssms r1 ] && null [() | Disj _ <- rAssms r2 ] -- have to split disjunctions first
  = Right (StepUnique, [ apply sigma sdg | sigma <- unifyRule r1 r2 ])
  | otherwise
  = Left "stepUnique not applicable"



-- | Unify two (non-pair) rule instances have the same knowledge conclusion.
--   Note that if both are instances of Pair, then they are always equal if the
--   conclusion is equal.
conclusionKnowsUnique :: Conc -> Conc -> SDG -> Either String (TransRule,[SDG])
conclusionKnowsUnique (r1,i1) (r2,i2) sdg
    | (getConc r1 i1 /= getConc r2 i2) || (rName r1) == "Pair" || (rName r2) == "pair"
    = Left $ "invalid argument, cannot apply conclusionKnowsUnique when conclusions"
             ++" are not equal or one is Pair"
    | otherwise
    = Right (ConcKnowUnique, [ apply sigma sdg | sigma <- unifyRule r1 r2 ])

-- | unify two rule instances that are sources for the same premise
premiseSourceUnique :: Edge -> Edge -> SDG -> Either String (TransRule,[SDG])
premiseSourceUnique e1@(Edge conc1@(rc1,_) assm1) e2@(Edge conc2@(rc2,_) assm2) sdg
  | assm1 == assm2 && conc1 /= conc2 && e1 `S.member` sEdges sdg && e2 `S.member` sEdges sdg
  = Right (PremiseSourceUnique, [ apply sigma sdg | sigma <- unifyRule rc1 rc2 ])
  | otherwise = Left "premiseSourceUnique: invalidArguments"

-- ***************************************************************************
-- SDG dead and realized checks
-- ***************************************************************************

openAssms :: SDG -> [Assm]
openAssms (SDG nodes edges chains) = assumptions \\ targets
 where
  targets = [ (tgt,j) | Edge (_src,_i) (tgt,j) <- S.toList edges ]
            ++[ (tgt,j) | Edge (_src,_i) (tgt,j) <- S.toList chains ]
  assumptions = [ (r,i) | r <- S.toList nodes, i <- assmIndices r ]

isTrivialAssm :: Fact -> Bool
isTrivialAssm (K (N (Atom _))) = True -- vars and consts are trivial
-- TODO: this is somewhat ad-hoc
isTrivialAssm (K (N (Op1 tg1 (Op1 tg2 (Op1 tg3 (Atom _))))))
 | tg1 == pkTag && tg2 == agentTag && (tg3 == intTag || tg3 == honTag) = True
 | tg1 == skTag && tg2 == agentTag && (tg3 == intTag) = True
 | otherwise = False
isTrivialAssm (K (N (Op1 tg1 (Op1 tg2 (Atom _)))))
 | tg1 == agentTag && (tg2 == intTag || tg2 == honTag) = True
 | otherwise = False
isTrivialAssm (K (N (Op1 tg1 (Atom _))))
 | tg1 == agentTag || tg1 == honTag || tg1 == intTag = True
 | otherwise = False
isTrivialAssm (Eq t1 t2)
 | t1 == t2 = True
 | otherwise = False
isTrivialAssm _ = False

nonTrivialAssms :: SDG -> [Assm]
nonTrivialAssms sdg = filter (not . isTrivialAssm . uncurry getAssm) $ openAssms sdg

-- | @isAtomic nvt@ returns @True@ if @nvt@ is considered atomic
isAtomic :: NVTerm -> Bool
isAtomic (N (Atom _)) = True     -- consts and vars are atomic
isAtomic (N (Op2 tg _ _))
  | tg == nonTag = True  -- nonces are considered atomic
  | otherwise = False
isAtomic (N (Op1 tg _))
  | tg `elem` [tidTag, agentTag] = True  -- thread ids and agents are atomic
  | otherwise = False
isAtomic (N _) = False           -- everything else is not atomic
isAtomic (T _) = error "not supported yet"

-- | @checkStrictlyAtomic sdg@ checks if all protocol variables in @sdg@
--   are instantiated with atomic values.
checkStrictlyAtomic :: SDG -> Maybe String
checkStrictlyAtomic sdg =
  case find (\t -> not (isAtomic t)) varInsts of
    Just t -> Just ("Not strictly atomic: "++show t)
    Nothing -> Nothing
 where
  varInsts = [ t | P _ _ terms <- concsSDG sdg, t <- terms]

-- | Check that there is no cycle in the symbolic derivation graph.
--   This would yield a cycle in all models
checkAcyclic :: SDG -> Maybe String
checkAcyclic sdg =
  if isCyclic edges
    then --trace (show edges++"\n"++unlines (map show $ M.toList $ nodesIndex)) $
      Just "Cyclic"
    else Nothing
 where edges = S.map (\(Edge (sr,_si) (tr,_ti)) -> (getInd sr,getInd tr))
                 $ S.union (sEdges sdg) (sChains sdg)
       nodesIndex = M.fromList $ zip (S.toList $ sNodes sdg) [(0::Int)..]
       getInd r = M.findWithDefault (error "checkAcyclic: impossible") r nodesIndex

-- we have three properties that our normal forms ensure:
--   uniqueKnowledgeConclusion (for rname /= pair): we use this in the transformation rule that unifies
--                                                  two rules
--   forcedPair: we use this in solveAssm for facts solvable by Pair
--   proof-Terms normalized wrt. DH:
--     we can use uniqueKnowledgeConclusion and checkForcedPair to get rid of two incoming arrows,
--     extract a recipe starting from the Recv assumptions and check that it is in normal form.
--     The proof terms of all models contain an instance of this term, so if the term has a redex,
--     then all instances also have.
--

-- | Check that all terms @N t@ in facts are in normal form. Reason: "NoNormalForm"
checkTermsNormalForm :: SDG -> Maybe String
checkTermsNormalForm _sdg = Nothing

-- | Check that a non Snd/Fst rule never uses a pair conclusion from a non-Pair rule
--   Sketch: in all instances, the rule name is the same and the conclusion is still
--           a pair
checkForcedPair :: SDG -> Maybe String
checkForcedPair _sdg = Nothing

checkNoLearnBefore :: SDG -> Maybe String
checkNoLearnBefore sdg =
  case violations of
    []  -> Nothing
    m:_ -> Just ("learnBefore: "++ show m)
 where deps = transClosure (S.map (\(Edge (r1,_i1) (r2,_i2)) -> (r1,r2)) $ S.union (sChains sdg) (sEdges sdg))
       violations = [ m | (Rule _ assms1 _ [K (N _)], Rule rname2 _ _ [conc2@(K (N m))]) <- S.toList deps,
                           rname2 /= "pair", conc2 `elem` assms1 ]

-- | Check if the SDG is realized.
realizedSDG :: SDG -> Either String (TransRule,[SDG])
realizedSDG sdg =
  if null (nonTrivialAssms sdg) && uniqueSteps sdg
     && uniqueKnowledgeConcs sdg -- && uniquePremiseSources sdg
     && S.null (sChains sdg)
    then Right (Realized, [])
    else Left "not realized"

equalStepPairs :: SDG -> [(Rule, Rule)]
equalStepPairs sdg =
  [(ps1,ps2) | ps1@(Rule _ ((P _ step1 (tid1:_)):_) _ _) <- nodes,
               ps2@(Rule _ ((P _ step2 (tid2:_)):_) _ _) <- nodes \\ [ps1],
               step1 == step2 && tid1 == tid2 ]
 where nodes = S.toList . sNodes $ sdg

uniquePremiseSources :: SDG -> Bool
uniquePremiseSources sdg = null $ duplicatePremiseSources sdg

duplicatePremiseSources :: SDG -> [(Edge,Edge)]
duplicatePremiseSources sdg =
  [(e1, e2) | e1@(Edge (_rc1,_ic1) (ra1,ia1)) <- edges,
              e2@(Edge (_rc2,_ic2) (ra2,ia2)) <- edges \\ [e1],
              ra1 == ra2, ia1 == ia2]
 where edges = S.toList $ sEdges sdg

uniqueSteps :: SDG -> Bool
uniqueSteps sdg = null $ equalStepPairs sdg

equalKnowsConclusionPairs :: SDG -> [(Rule,Rule)]
equalKnowsConclusionPairs sdg =
  [(ps1,ps2) | ps1@(Rule rname1 _ _ [c1]) <- nodes,
               ps2@(Rule rname2 _ _ [c2]) <- nodes \\ [ps1],
               c1 == c2 && (rname1 /= "pair" && rname2 /= "pair")]
 where nodes = S.toList . sNodes $ sdg


uniqueKnowledgeConcs :: SDG -> Bool
uniqueKnowledgeConcs sdg = null $ equalKnowsConclusionPairs sdg

-- | Returns the status of the given SDG.
contradictionSDG :: SDG -> Either String (TransRule,[SDG])
contradictionSDG sdg =
  case dropWhile (isNothing) $ map (\check -> check sdg) checksDead of
    [] -> Left "No contradiction applicable"
    (Just x:_) -> Right (Contradiction x,[])
    _ -> error "impossible"
 where
  checksDead = [-- checkStrictlyAtomic,
                checkTermsNormalForm,checkAcyclic,checkNoLearnBefore]

-- ***************************************************************************
-- Substitution application and variable occurences
-- ***************************************************************************

class Apply a where
  apply :: Subst -> a -> a

instance Apply VTerm where
  apply = applyS2T

instance Apply a => Apply [a] where
  apply subst xs = map (apply subst) xs

instance Apply NVTerm where
  apply subst (N t) = N $ apply subst t
  apply subst (T t) = T $ apply subst t

instance Apply Fact where
  apply subst (K t) = K $ apply subst t
  apply subst (S t) = S $ apply subst t
  apply subst (P rn sn t) = P rn sn $ apply subst t
  apply subst (Eq a b) = Eq (apply subst a) (apply subst b)
  apply subst (Disj fs) = Disj $ apply subst fs
  apply subst (C t) = C $ apply subst t

instance Apply Rule where
  apply sigma0 (Rule rn accs exts concs) =
    Rule rn (map (apply sigma) accs) exts (map (apply sigma) concs)
   where sigma = restrictS (domS sigma0 \\ (varsOf exts)) sigma0
         -- restrict sigma to variables that are not existentially quantified

instance Apply Edge where
  apply subst (Edge (r1,i) (r2,j)) = Edge (apply subst r1,i) (apply subst r2,j)

instance Apply SDG where
  apply sigma0 sdg@(SDG nodes edges chains) = SDG nodes' edges' chains'
   where
    sigma = renameSubstAwayFrom sigma0 (varsOf sdg)
    nodes' = S.map (apply sigma) nodes
    edges' = S.map (apply sigma) edges
    chains' = S.map (apply sigma) chains

-- * varsOf returns the variables that occur in the given argument
--   this is often required for renaming variables that occur
--   in the range of substitutions to prevent clashes

class Vars a where
  varsOf :: a -> [Int]

instance Vars VTerm where
  varsOf = vars

instance Vars a => Vars [a] where
  varsOf ts = S.toList (S.unions $ map (S.fromList.varsOf) ts)

instance Vars NVTerm where
  varsOf (N t) = vars t
  varsOf (T t) = vars t

instance Vars Fact where
  varsOf (K t) = varsOf t
  varsOf (C t) = varsOf t
  varsOf (S t) = varsOf t
  varsOf (P _ _ t) = varsOf t
  varsOf (Eq a b) = snub (varsOf a ++ varsOf b)
  varsOf (Disj fs) = varsOf fs

instance Vars Existential where
  varsOf (EVar i) = [i]
  varsOf (EFresh _) = []

instance Vars Rule where
  varsOf (Rule _ assms exts concs) = snub (varsOf exts++varsOf (assms++concs))

instance Vars SDG where
  varsOf sdg = varsOf $ S.toList $ sNodes sdg


-- ***************************************************************************
-- Show instances
-- ***************************************************************************

instance Show NVTerm where
  show (N t) = show t
  show (T t) = "|"++show t ++ "|v"

instance Show Fact where
 show (P rn i ts) = "P["++rn++","++show i++"]("++(intercalate ",".map show $ ts)++")"
 show (K t) = "K("++show t++")"
 show (C t) = "C("++show t++")"
 show (S t) = "S("++show t++")"
 show (Eq a b) = "EQ("++show a++","++show b++")"
 show (Disj fs) = "OR("++intercalate "," (map show fs)++")"

instance Show Existential where
  show (EVar x) = show . var $ x
  show (EFresh i) = show . threadId $ i

instance Show Rule where
  show (Rule rn assms ex concs) =
    (if null sassms then "" else sassms++"\n")++line++"\n"++sconcs
    where
      sconcs = intercalate "   " $ map show concs
      sassms = intercalate "   " $ map show assms
      len    = max (length sconcs) (length sassms)
      line   = (replicate len '-')++" "++rn++" ["++intercalate "," (map show ex)++"]"

instance Show SDG where
  show (SDG nodes edges chains) =
    (unlines (map (\(i,s) -> "#"++show i++"\n"++s) nodesInd))++"\n"++
    (unlines (map (\(r1,r2,(i,j)) -> "#"++show r1++" ["++show i++"]-->["++show j++"] #"++show r2) edgesInd))++"\n"++
    (unlines (map (\(r1,r2,(i,j)) -> "#"++show r1++" ["++show i++"]~~>["++show j++"] #"++show r2) chainsInd))
   where
    nodesInd = zip [(1::Int)..] (map show $ S.toList nodes)
    indNodes = zip (S.toList nodes) [(1::Int)..]
    edgesInd = map g (S.toList edges)
    chainsInd = map g (S.toList chains)
    g e@(Edge (r1,i) (r2,j)) =
      (fromMaybe (errMissing "source") $ lookup r1 indNodes,
       fromMaybe (errMissing "target") $ lookup r2 indNodes,
       (i,j))
     where
      errMissing missing =
        error $ "sdgToFgl: edge\n" ++ show e++ "\nin sdg, but "++missing++" not. nodes: \n"
                ++unlines (map show (S.toList nodes))

instance Show Edge where
  show (Edge (r1,i1) (r2,i2)) = show r1++"\n ["++show i1++"]-->["++show i2++"]\n"++show r2

-- ***************************************************************************
-- Tests
-- ***************************************************************************

test1 :: Bool
test1 = (apply (SC [(1,x3),(2,x4)]) (Rule "" [] [EVar 1] [K $ N x1,K $ N x2]))
        == (Rule "" [] [EVar 1] [K $ N x1,K $ N x4])

-- TODO:
-- add support for Claim facts
--     custom and predefined WeaklyAtomic, StrictlyAtomic, WeaklyTyped, StrictlyTyped, Varname.
--     Varname String ThreadId NVTerm -- to keep human-readable names of variables
--     WeaklyAtomic NVTerm
--     StrictlyAtomic NVTerm
--     WeaklyTyped (NVTerm, [Type])  where Type is a term with variables which are assumed to be atomic
--                                   and the list stands for the disjunction
--     Pruning Rules:
--     type = ground term with fixed constants for const/atom/agent where atoms are allowed
--     StrictlyAtomic t ==> prune if t is not atomic
--     WeaklyAtomic t ==> prune if t is learned after
--     StrictlyTyped (t,types) ==> prune if t does not have one of the given types
--     "type checking" = replace atoms in t with distinct variables, match t with type
--     WeaklyTyped (t,types) ==> prune if t does not have any of the given types *and* is learned after
-- Add variants of dec and fst/snd rules to intruder theory that produce error terms.
-- might miss some pruning, because I consider them free for now in the checkRecipes normalization,
-- but that should all be handled by uniqueKnowsConclusion.
--
-- How to split the rules automatically into forward, backward, and ikrules and prove the correctness:
-- Take all rules without assumptions, these are ikrules.
-- Take all rules with k(x) as conclusion where x is a variable. These must be forward rules because
-- they cannot be uses in a backwards fashion.
-- Then take other rules and show that forward/backward has chain property:
--   take proof term corresponding to fw(bw(x1,..,xk),y2,..yl), show that it is not in normal form
--   remove instances that are already subsumed by other rules: yield constants, yield one of the premises
-- TODO: write some more tests for tricky cases