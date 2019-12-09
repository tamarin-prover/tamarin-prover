{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Compute translation-specific restrictions
module Sapic.Accountability (
      generateAccountabilityLemmas
   ,  generateAccountabilityRestrictions
) where

import           Control.Monad.Catch
import           Control.Monad.Fresh
import qualified Extension.Data.Label   as L
import           Theory



------------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------------

-- | Create a lemma from a formula with quantifier. Copies accLemma's name
-- (plus suffix) and attributes.
toLemma :: AccLemmaGeneral c -> TraceQuantifier -> (String, LNFormula) -> Lemma ProofSkeleton
toLemma accLemma quantifier (suffix,formula)  = 
        skeletonLemma (L.get aName accLemma ++ suffix) (L.get aAttributes accLemma) quantifier formula (unproven ())

-- | Quantify the given variables
quantifyVars :: ((String, LSort) -> LVar -> LNFormula -> LNFormula) -> [LVar] -> LNFormula -> LNFormula
quantifyVars quan vars fm = foldr (\s -> hinted quan s) fm vars

-- | Quantify all free variables
quantifyFrees :: ((String, LSort) -> LVar -> LNFormula -> LNFormula) -> LNFormula -> LNFormula
quantifyFrees quan fm = quantifyVars quan (frees fm) fm

protoFactFormula :: String -> [VTerm Name (BVar LVar)] -> VTerm Name (BVar LVar) -> LNFormula
protoFactFormula name terms at = Ato $ Action at $ protoFact Linear name terms

tempTerm :: String -> VTerm Name (BVar LVar)
tempTerm name = varTerm $ Free $ LVar name LSortNode 0

msgTerm :: String -> VTerm Name (BVar LVar)
msgTerm name = varTerm $ Free $ LVar name LSortMsg  0

tempVar :: String -> LVar
tempVar name = LVar name LSortNode 0

msgVar :: String -> LVar
msgVar name = LVar name LSortMsg  0

freesSubsetCorrupt :: [LVar] -> LNFormula
freesSubsetCorrupt vars = foldl1 (.&&.) corrupted
    where
        corrupted = map corrupt vars
        corrupt var = quantifyVars exists [tempVar "i"] $ protoFactFormula "Corrupt" [varTerm $ Free $ traceId, varTerm $ Free var] (tempTerm "i")

corruptSubsetFrees :: [LVar] -> LNFormula
corruptSubsetFrees vars = quantifyVars forall [msgVar "a", tempVar "i"] $ 
                            (protoFactFormula "Corrupt" [varTerm $ Free $ traceId, msgTerm "a"] (tempTerm "i") .==>. isElem (msgVar "a") vars)


isElem :: LVar -> [LVar] -> LNFormula
isElem v vars = foldr1 (.||.) (map (eq v) vars)
    where
        eq x y = Ato $ EqE (varTerm $ Free x) (varTerm $ Free y)

strictSubsetOf :: [LVar] -> [LVar] -> LNFormula
strictSubsetOf left right = subset left right .&&. strict left right
    where
        subset xs ys = foldr1 (.&&.) (map (\x -> foldr1 (.||.) (map (\y -> eq x y) ys)) xs)
        strict xs ys = foldr1 (.||.) (map (\x -> foldr1 (.&&.) (map (\y -> Not $ eq y x) ys)) xs)
        eq x y = Ato $ EqE (varTerm $ Free x) (varTerm $ Free y)

ntuple :: [LVar] -> VTerm Name (BVar LVar)
ntuple vars = foldr1 (\a b -> fAppPair (a, b)) (map (varTerm . Free) vars)

varsEq :: [LVar] -> [LVar] -> LNFormula
varsEq l r = Ato $ EqE (ntuple l) (ntuple r)

traceId :: LVar
traceId = LVar "tid" LSortMsg  0

isTraceId :: LVar -> Bool
isTraceId (LVar name LSortMsg  _) = name == "tid"
isTraceId _ = False

freesNoTraceId :: LNFormula -> [LVar]
freesNoTraceId = filter (not . isTraceId) . frees

freeTraceIds :: LNFormula -> [LVar]
freeTraceIds = filter isTraceId . frees

sameInst :: LNFormula -> LNFormula -> LNFormula
sameInst t1 t2 = varsEq (freesNoTraceId t1) (freesNoTraceId t2)

newTrace :: MonadFresh m => LNFormula -> m LNFormula
newTrace fm = renameIgnoring (freesNoTraceId fm) fm

newInst :: MonadFresh m => LNFormula -> m LNFormula
newInst fm = renameIgnoring (freeTraceIds fm) fm

quantifyIds :: ((String, LSort) -> LVar -> LNFormula -> LNFormula) -> LNFormula -> LNFormula
quantifyIds quan fm = quantifyVars quan (freeTraceIds fm) fm

quantifyNonIds :: ((String, LSort) -> LVar -> LNFormula -> LNFormula) -> LNFormula -> LNFormula
quantifyNonIds quan fm = quantifyVars quan (freesNoTraceId fm) fm

singleInst :: MonadFresh m => LNFormula -> m LNFormula
singleInst t1 = do
    t2 <- newInst t1
    return $ t1 .&&. quantifyVars forall (freesNoTraceId t2) (t2 .==>. sameInst t1 t2)

noOther :: [LNFormula] -> LNFormula
noOther fms = foldr1 (.&&.) (map (Not . quantifyNonIds exists) fms)

andIf :: Bool -> Formula a s v -> Formula a s v -> Formula a s v
andIf p a b = if p then a .&&. b else b



------------------------------------------------------------------------------
-- Verification Conditions
------------------------------------------------------------------------------

sufficiency :: MonadFresh m => [CaseTest] -> CaseTest -> m (Lemma ProofSkeleton)
sufficiency caseTests caseTest = do
    t1 <- newTrace tau
    t2 <- singleInst tau
    t3 <- newTrace (t2 .&&. andIf (not $ null taus) (noOther taus) (corruptSubsetFrees (freesNoTraceId t1)))

    let formula = quantifyFrees forall $ t1 .==>. quantifyIds exists t3

    return $ skeletonLemma name [] AllTraces formula (unproven ())
    where
        name = L.get cName caseTest ++ "_sufficiency"
        tau = L.get cFormula caseTest
        taus = map (L.get cFormula) (filter (\c -> L.get cName caseTest /= L.get cName c) caseTests)


verifiability :: MonadFresh m => AccLemma -> m (Lemma ProofSkeleton)
verifiability accLemma = return $ toLemma accLemma AllTraces (suffix, formula)
    where
        suffix = "_verif"
        taus = map (L.get cFormula) (L.get aCaseTests accLemma)
        lhs = foldl1 (.&&.) $ map (Not . quantifyNonIds exists) taus
        phi = L.get aFormula accLemma
        formula = quantifyIds forall $ lhs .<=>. phi

minimality :: MonadFresh m => [CaseTest] -> CaseTest -> m (Lemma ProofSkeleton)
minimality caseTests caseTest = do
    t1 <- newInst tau
    tts <- mapM newInst taus

    let rhs = map (\t -> Not (quantifyVars exists (freesNoTraceId t) $ t .&&. strictSubsetOf (freesNoTraceId t) (freesNoTraceId t1))) tts
    let formula = simplifyFormula $ quantifyFrees forall $ t1 .==>. foldl1 (.&&.) rhs

    return $ skeletonLemma name [] AllTraces formula (unproven ())
    where
        name = L.get cName caseTest ++ "_minimality"
        tau = L.get cFormula caseTest
        taus = map (L.get cFormula) (filter (\c -> L.get cName caseTest /= L.get cName c) caseTests)

uniqueness :: MonadFresh m => CaseTest -> m (Lemma ProofSkeleton)
uniqueness caseTest = return $ skeletonLemma name [] AllTraces formula (unproven ())
    where
        name = L.get cName caseTest ++ "_uniqueness"
        tau = L.get cFormula caseTest
        formula = pnf $ quantifyFrees forall (tau .==>. (freesSubsetCorrupt $ freesNoTraceId tau))

terminating :: MonadFresh m => [CaseTest] -> CaseTest -> m (Lemma ProofSkeleton)
terminating caseTests caseTest = do
    t1 <- newTrace tau
    t2 <- singleInst tau
    t3 <- newTrace (andIf (not $ null taus) (noOther taus) t2)

    let formula = pnf $ quantifyFrees forall $ t1 .==>. quantifyIds exists t3
    
    return $ skeletonLemma name [] AllTraces formula (unproven ())
    where
        name = L.get cName caseTest ++ "_rel_terminating"
        tau = L.get cFormula caseTest
        taus = map (L.get cFormula) (filter (\c -> L.get cName caseTest /= L.get cName c) caseTests)


test :: MonadFresh m => CaseTest -> m (Lemma ProofSkeleton)
test caseTest = do
    t1 <- newTrace tau

    let formula = prenex $ quantifyFrees forall $ t1 .==>. t1
    
    return $ skeletonLemma name [] AllTraces formula (unproven ())
    where
        name = L.get cName caseTest ++ "_test"
        tau = L.get cFormula caseTest

------------------------------------------------------------------------------
-- Restrictions
------------------------------------------------------------------------------

relationTerminatingRes :: MonadFresh m => CaseTest -> m Restriction
relationTerminatingRes caseTest = do
    t1 <- newTrace tau
    t2 <- newInst t1
    t3 <- (singleInst >=> newTrace) t1
    t4 <- (singleInst >=> newTrace) t2
    let formula = t1 .&&. t2 .&&. (Not $ sameInst t1 t2) .==>. quantifyIds exists (t3 .&&. t4)
    return $ Restriction name $ quantifyFrees forall formula
    where
        name = L.get cName caseTest ++ "_rel_term"
        tau = L.get cFormula caseTest



------------------------------------------------------------------------------
-- Generation
------------------------------------------------------------------------------
            
casesLemmas :: MonadFresh m => AccLemma -> m [Lemma ProofSkeleton]
casesLemmas accLemma = do
        s <- mapM (sufficiency caseTests) caseTests
        v <- verifiability accLemma
        m <- mapM (minimality caseTests) caseTests
        u <- mapM uniqueness caseTests
        t <- mapM (terminating caseTests) caseTests
        tt <- mapM test caseTests

        return $ s ++ [v] ++ m ++ u ++ t ++ tt
    where
        caseTests = L.get aCaseTests accLemma

casesRestrictions :: MonadFresh m => AccLemma -> m [Restriction]
casesRestrictions accLemma = 
        mapM relationTerminatingRes caseTests
    where
        caseTests = L.get aCaseTests accLemma

generateAccountabilityLemmas :: (Monad m, MonadThrow m) => AccLemma -> m [Lemma ProofSkeleton]
generateAccountabilityLemmas accLemma = evalFreshT (casesLemmas accLemma) 0

generateAccountabilityRestrictions :: (Monad m, MonadThrow m) => AccLemma -> m [Restriction]
generateAccountabilityRestrictions accLemma = evalFreshT (casesRestrictions accLemma) 0