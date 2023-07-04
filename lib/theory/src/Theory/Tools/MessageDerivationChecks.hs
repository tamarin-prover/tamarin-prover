module Theory.Tools.MessageDerivationChecks (
      checkVariableDeducability
    , diffCheckVariableDeducability
) where

import  Theory.Model.Formula
import  qualified Data.Label as L
import Theory (OpenTranslatedTheory, OpenDiffTheory)
import Items.RuleItem
import TheoryObject
import Theory.Model
import Theory.Proof
import Prover
import Data.Maybe ( fromJust, fromMaybe, maybeToList )
import Data.List
import Theory.Tools.Wellformedness (WfErrorReport)
import Text.PrettyPrint.Class
import qualified Text.PrettyPrint.Class as Pretty
import ClosedTheory
import qualified Debug.Trace as Debug
import qualified Data.List as List

-----------------------------------------------
-- DerivationChecks
-----------------------------------------------

checkVariableDeducability :: OpenTranslatedTheory -> SignatureWithMaude -> Bool -> Prover -> IO WfErrorReport
checkVariableDeducability thy sig sources prover =
    return $ reportVars (map checkProofStatuses provenTheories) originalRules freeVars
    where
        originalRules = theoryRules thy
        provenTheories =  map (proveTheory (\_ -> True) prover) closedTheories
        closedTheories = map (\t -> closeTheoryWithMaude sig t sources) modifiedTheories
        modifiedTheories =  zipWith3 (\r l t -> (addRules [r] . addLemmas l ) t)  newRules newLemmas (cycle [emptyPublicThy])
        emptyPublicThy = makeFunsPublic (toSignaturePure sig) $ deleteRulesAndLemmasFromTheory thy
        newRules =  zipWith3 (\idx freevs prems -> generateRule freevs (premisesToOut prems) idx) [0..] freeVars premises
        newLemmas =  zipWith3 (\idx freevs prems-> generateSeparatedLemmas idx freevs (map lntermToKUFact (map lvarToLnterm freevs))) [0..] freeVars premises
        premises = map (map (fmap replacePrivate)) $ premsOfThyRules thy
        freeVars = freesInThyRules thy

diffCheckVariableDeducability :: OpenDiffTheory -> SignatureWithMaude -> Bool -> Prover -> DiffProver -> IO WfErrorReport
diffCheckVariableDeducability thy sig sources prover diffprover =
    return $ reportDiffVars (map checkDiffProofStatuses provenTheories) originalRules freeVars
    where
        originalRules = diffTheoryDiffRules thy
        provenTheories =  map (proveDiffTheory (\_ -> True) prover diffprover) closedTheories
        closedTheories = map (\t -> closeDiffTheoryWithMaude sig t sources) modifiedTheories
        modifiedTheories =  map (\(r,l,t) -> (addDiffRules [r] . addDiffLemmas l ) t) (zip3 newrules newlemmas (cycle [emptyPublicThy]))
        emptyPublicThy = diffmakeFunsPublic (toSignaturePure sig) $ diffdeleteRulesAndLemmasFromTheory thy
        newrules =  map (\(idx, freevs, prems )-> generateRule freevs (premisesToOut prems) idx) freesAndPrems
        newlemmas =  map (\(idx, freevs, prems) -> generateSeparatedLemmas idx freevs (map lntermToKUFact (map lvarToLnterm freevs))) freesAndPrems
        freesAndPrems = freesAndPremsLHS ++ freesAndPremsRHS
        freesAndPremsRHS = zip3 [0..] (difffreesInThyRules closedThy RHS) (map (map (fmap replacePrivate)) $ diffpremsOfThyRules closedThy RHS)
        freesAndPremsLHS = zip3  [0..] (difffreesInThyRules closedThy LHS) (map (map (fmap replacePrivate)) $ diffpremsOfThyRules closedThy LHS)
        freeVars = difffreesInThyRules closedThy LHS ++ difffreesInThyRules closedThy RHS
        closedThy = openDiffTheory ( closeDiffTheoryWithMaude sig thy True )

-----------------------------------------------
-- Manipulating Theories
-----------------------------------------------

diffdeleteRulesAndLemmasFromTheory :: DiffTheory sig c r r2 p p2 -> DiffTheory sig c r r2 p p2
diffdeleteRulesAndLemmasFromTheory thy = L.modify diffThyItems deleteDiffRules thy
    where
        deleteDiffRules items = concatMap (maybeToList . delRules) items
        delRules (DiffRuleItem _) = Nothing
        delRules (EitherRuleItem _) = Nothing
        delRules (DiffLemmaItem _ ) = Nothing
        delRules (EitherLemmaItem _) = Nothing
        delRules sth = Just sth

deleteRulesAndLemmasFromTheory :: Theory sig c r p s -> Theory sig c r p s
deleteRulesAndLemmasFromTheory thy = L.modify thyItems deleteRules thy
    where
        deleteRules items = concatMap (maybeToList . delRules) items
        delRules (RuleItem _) = Nothing
        delRules (LemmaItem _) = Nothing
        delRules sth = Just sth

replacePrivate :: Term t -> Term t
replacePrivate t = case viewTerm t of
    FApp (NoEq (num,(name,Private,constr))) term  -> termViewToTerm $ FApp (NoEq (num, (name, Public, constr))) (map replacePrivate term)
    FApp sym as -> termViewToTerm $ FApp sym (map replacePrivate as)
    x -> termViewToTerm x

makeFunsPublic ::  sig -> Theory sig c r p s  -> Theory sig c r p s
makeFunsPublic  sig thy  = L.set thySignature sig thy

diffmakeFunsPublic :: a -> DiffTheory a c r r2 p p2 -> DiffTheory a c r r2 p p2
diffmakeFunsPublic  sig thy  = L.set diffThySignature sig thy

addLemmas :: Foldable t =>t (Lemma p) -> Theory sig c r p s -> Theory sig c r p s
addLemmas lemmas thy = fromMaybe thy $ foldl ( \fm lemma -> addLemma lemma (fromJust fm)) (Just thy) lemmas

addDiffRules :: [OpenProtoRule] -> DiffTheory sig c DiffProtoRule r2 p p2-> DiffTheory sig c DiffProtoRule r2 p p2
addDiffRules rules thy = L.modify diffThyItems (++ map (DiffRuleItem . (\t -> DiffProtoRule (L.get oprRuleE t) (Just (t,t)))) rules) thy

addRules :: [r] -> Theory sig c r p s -> Theory sig c r p s
addRules rules thy = L.modify thyItems (++ map (RuleItem) rules) thy

addDiffLemmas :: Foldable t =>t (Lemma p2)-> DiffTheory sig c r r2 p p2 -> DiffTheory sig c r r2 p p2
addDiffLemmas lemmas thy = fromMaybe thy $ foldl ( \fm lemma ->  addLemmaDiff LHS lemma (fromJust fm)) (Just thy) lemmas

-----------------------------------------------
-- Generating error reports
-----------------------------------------------

reportVars :: [[ProofStatus]] -> [OpenProtoRule] -> [[LVar]] -> WfErrorReport
reportVars analysisresults rules vars = concat $ zipWith3  (\results rule vars -> maybeToList $ if List.any ( /= TraceFound) results &&(List.all ( /= IgnoreDerivChecks) $ ruleAttributes $ L.get oprRuleE rule) then Just $ generateError results rule vars else Nothing) analysisresults rules vars
    where
        generateError results rule vars = ("The variables of the follwing rule(s) are not derivable from their premises, you may be performing unintended pattern matching", text $ ( (Pretty.render . prettyProtoRuleName) $ L.get preName (L.get rInfo (L.get oprRuleE rule)) ) ++ "\nFailed to derive Variable(s): " ++ (intercalate ", " $ map (show . snd) $ filter ((/= TraceFound) . fst) (zip results vars)))

reportDiffVars :: [[ProofStatus]] -> [DiffProtoRule] -> [[LVar]] -> WfErrorReport
reportDiffVars analysisresults rules vars = concat $ zipWith3 (\results rule vars-> maybeToList $ if List.any ( /=TraceFound) results &&(List.all ( /= IgnoreDerivChecks) $ ruleAttributes $ L.get dprRule rule) then Just $ generateError results rule vars else Nothing) analysisresults rules vars
    where
        generateError results rule vars = ("The variables of the follwing rule(s) are not derivable from their premises, you may be performing unintended pattern matching", text $ ( (Pretty.render . prettyProtoRuleName) $ L.get preName (L.get rInfo (L.get dprRule rule)) ) ++ "\nFailed to derive Variable(s): " ++ (intercalate ", " $ map (show . snd) $ filter ((/= TraceFound) . fst) (zip results vars)))

checkProofStatuses :: ClosedTheory -> [ProofStatus]
checkProofStatuses thy =  map ((foldProof proofStepStatus) . (L.get lProof)) $ theoryLemmas thy

checkDiffProofStatuses :: ClosedDiffTheory -> [ProofStatus]
checkDiffProofStatuses thy = map ((foldProof proofStepStatus) . (L.get lProof) . snd) $ diffTheoryLemmas thy

-----------------------------------------------
-- Convenience getter functions
-----------------------------------------------

freesInThyRules :: Theory sig c OpenProtoRule p s -> [[LVar]]
freesInThyRules thy = map (frees . L.get oprRuleE) $ theoryRules thy

premsOfThyRules :: Theory sig c OpenProtoRule p s -> [[LNFact]]
premsOfThyRules thy = map (L.get rPrems . L.get oprRuleE) $ theoryRules thy

concsOfThyRules :: Theory sig c OpenProtoRule p s -> [[LNFact]]
concsOfThyRules thy = map (L.get rConcs . L.get oprRuleE ) $ theoryRules thy

difffreesInThyRules :: DiffTheory sig c r OpenProtoRule p p2 -> Side -> [[LVar]]
difffreesInThyRules thy side = map (frees . L.get oprRuleE) $ diffTheorySideRules side thy

diffpremsOfThyRules :: DiffTheory sig c r OpenProtoRule p p2 -> Side -> [[LNFact]]
diffpremsOfThyRules thy side = map (L.get rPrems . L.get oprRuleE) $ diffTheorySideRules side  thy

diffconcsOfThyRules :: DiffTheory sig c r OpenProtoRule p p2 -> Side -> [[LNFact]]
diffconcsOfThyRules thy side = map (L.get rConcs . L.get oprRuleE ) $ diffTheorySideRules side thy

----------------------------------------------------
-- Helper functions for rule and lemma generation
----------------------------------------------------

generateRule ::  [LVar] -> [LNFact] -> Int -> OpenProtoRule
generateRule freevars premises idx =  OpenProtoRule (Rule (ProtoRuleEInfo (StandRule (show idx)) ([]) ([])) (freesToFresh . deleteGlobals $ freevars) (premisesToOut premises ) ([generateAction (deleteGlobals freevars) idx]) ([])) []

generateDiffRule :: Side -> [LVar] -> [LNFact] -> Int -> OpenProtoRule
generateDiffRule side freevars premises idx =  OpenProtoRule (Rule (ProtoRuleEInfo (StandRule (show side ++ show idx)) ([]) ([])) (freesToFresh . deleteGlobals $ freevars) (premisesToOut premises ) ([generateAction (deleteGlobals freevars) idx]) ([])) []

generateAction :: [LVar] ->Int -> LNFact
generateAction vars idx = protoFact Persistent ("Generated_" ++ show idx) (map lvarToLnterm (deleteGlobals vars))

generateLemma :: Int -> [LVar]-> [LNFact]-> ProtoLemma (ProtoFormula Unit2 (String, LSort) Name LVar) (Proof ())
generateLemma idx vars kus = Lemma (show idx) ExistsTrace (existsTimeFormula $ existFormula $ landFormula $ (generateAction vars idx) : (kus)) [] (unproven ())

generateSeparatedLemmas :: Int -> [LVar]-> [LNFact]-> [ProtoLemma (ProtoFormula Unit2 (String, LSort) Name LVar) (Proof ())]
generateSeparatedLemmas idx vars kus = map (\v -> Lemma (show v) ExistsTrace (existsTimeFormula $ existFormula $ landFormula $ (generateAction vars idx) : [v]) [] (unproven ())) kus

generateDiffLemma :: Side -> Int -> [LVar]-> [LNFact]-> ProtoLemma     (ProtoFormula Unit2 (String, LSort) Name LVar) (Proof ())
generateDiffLemma side idx vars kus = Lemma (show side ++ show idx) ExistsTrace (existsTimeFormula $ existFormula $ landFormula $ (generateAction vars idx) : (kus)) [] (unproven ())

deleteGlobals :: [LVar] -> [LVar]
deleteGlobals = filter (\v -> lvarSort v /= LSortPub)

-- Exists-quantifies every non-time LVar of a formula
existFormula ::  ProtoFormula Unit2 (String,LSort) Name LVar -> ProtoFormula Unit2 (String,LSort) Name LVar
existFormula formula = foldl (\formula -> \var -> exists (((lvarName var)), (lvarSort var)) var formula) formula (frees formula)

-- Assumes function passed only has free time variables anymore and exists-quantifies them
existsTimeFormula :: ProtoFormula Unit2 (String,LSort) Name LVar -> ProtoFormula Unit2 (String,LSort) Name LVar
existsTimeFormula fm = foldl (\formula -> \var -> exists (((lvarName var)), LSortNode) var formula) fm (frees fm)

-- Takes a list of facts and logically ands them into a formula that can be used for a lemma
landFormula :: [LNFact] -> ProtoFormula Unit2 (String,LSort) Name  LVar
landFormula facts = foldl (\fm -> \(idx, fact) -> fm .&&. (Ato (Action (LIT (Var (Free (LVar (show idx) LSortNode 0))) ) fact )))  ltrue (zip [0..]  (map freeFact facts))

-- Transforms different kind of facts into the desired form
freesToFresh :: [LVar] -> [LNFact]
freesToFresh vars = map (freshFact . lvarToLnterm) vars

premisesToOut :: [LNFact] -> [LNFact]
premisesToOut prems =  (map outFact . concat . map factTerms) prems

concsToKU :: [LNFact] -> [LNFact]
concsToKU concs = (map kuFact . concat . map factTerms) concs

-- Convenience functions for converting vars/terms
freeLNTerm :: LVar -> BVar LVar
freeLNTerm v = Free v

freeTerm :: LNTerm -> Term (Lit Name (BVar LVar))
freeTerm term =  fmap (fmap freeLNTerm) term

freeFact :: LNFact ->  Fact (Term (Lit Name (BVar LVar)))
freeFact fact = fmap freeTerm fact

lvarToLnterm :: LVar -> LNTerm
lvarToLnterm v =  LIT $ Var $ v

lntermToKUFact :: LNTerm -> LNFact
lntermToKUFact term = kuFact term
