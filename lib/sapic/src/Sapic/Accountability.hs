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
toLemma :: AccLemmaGeneral c -> TraceQuantifier -> String -> LNFormula -> Lemma ProofSkeleton
toLemma accLemma quantifier suffix formula = 
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
        corrupt var = quantifyVars exists [tempVar "i"] $ protoFactFormula "Corrupt" [varTerm $ Free var] (tempTerm "i")

corruptSubsetFrees :: [LVar] -> LNFormula
corruptSubsetFrees vars = quantifyVars forall [msgVar "a", tempVar "i"] $ 
                            (protoFactFormula "Corrupt" [msgTerm "a"] (tempTerm "i") .==>. isElem (msgVar "a") vars)

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

noOther :: [LNFormula] -> LNFormula
noOther fms = foldr1 (.&&.) (map (Not . quantifyFrees exists) fms)

andIf :: Bool -> Formula a s v -> Formula a s v -> Formula a s v
andIf p a b = if p then a .&&. b else b

-- | TODO: Why do we need the second rename?
singleMatch :: MonadFresh m => LNFormula -> m LNFormula
singleMatch t = do
    t1 <- rename t
    t2 <- rename t
    return $ t1 .&&. quantifyVars forall (frees t2) (t2 .==>. varsEq (frees t2) (frees t1))



------------------------------------------------------------------------------
-- Verification Conditions
------------------------------------------------------------------------------

-- type VerificationCondition = LNFormula -> [LNFormula] -> LNFormula -> (String, TraceQuantifier, LNFormula)
-- 
-- sufficiency tau taus phi
-- 
-- generateLemmas :: MonadFresh m => AccLemma -> VerificationCondition -> m [Lemma ProofSkeleton]
-- generateLemmas accLemma sufficiency 
-- generateLemmas accLemma minimality 
-- 
-- toSmth "_suff" ExistsTrace formula

sufficiency :: MonadFresh m => [CaseTest] -> CaseTest -> m (Lemma ProofSkeleton)
sufficiency caseTests caseTest = do
    t1 <- singleMatch tau

    let formula = quantifyFrees exists (t1 .&&. andIf (not $ null taus) (noOther taus) (corruptSubsetFrees (frees t1)))

    return $ skeletonLemma name [] ExistsTrace  formula (unproven ())
    where
        name = L.get cName caseTest ++ "_suff"
        tau = L.get cFormula caseTest
        taus = map (L.get cFormula) (filter (\c -> L.get cName caseTest /= L.get cName c) caseTests)

verifiability :: MonadFresh m => AccLemma -> m (Lemma ProofSkeleton)
verifiability accLemma = return $ toLemma accLemma AllTraces suffix formula
    where
        suffix = "_verif"
        taus = map (L.get cFormula) (L.get aCaseTests accLemma)
        lhs = foldl1 (.&&.) $ map (Not . quantifyFrees exists) taus
        phi = L.get aFormula accLemma
        formula = quantifyFrees forall $ lhs .<=>. phi

minimality :: MonadFresh m => [CaseTest] -> CaseTest -> m (Lemma ProofSkeleton)
minimality caseTests caseTest = do
    t1 <- rename tau
    tts <- mapM rename taus

    let rhs = map (\t -> Not (quantifyVars exists (frees t) $ t .&&. strictSubsetOf (frees t) (frees t1))) tts
    let formula = quantifyFrees forall $ t1 .==>. foldl1 (.&&.) rhs

    return $ skeletonLemma name [] AllTraces formula (unproven ())
    where
        name = L.get cName caseTest ++ "_min"
        tau = L.get cFormula caseTest
        taus = map (L.get cFormula) (filter (\c -> L.get cName caseTest /= L.get cName c) caseTests)

uniqueness :: MonadFresh m => CaseTest -> m (Lemma ProofSkeleton)
uniqueness caseTest = return $ skeletonLemma name [] AllTraces formula (unproven ())
    where
        name = L.get cName caseTest ++ "_uniq"
        tau = L.get cFormula caseTest
        formula = quantifyFrees forall (tau .==>. (freesSubsetCorrupt $ frees tau))

-- | :TODO: : Avoid duplicates
injective :: MonadFresh m => CaseTest -> m (Lemma ProofSkeleton)
injective caseTest = return $ skeletonLemma name [] AllTraces  formula (unproven ())
    where
        name = L.get cName caseTest ++ "_inj"
        tau = L.get cFormula caseTest
        formula = quantifyFrees forall (tau .==>. foldr1 (.&&.) [ Not $ varsEq [x] [y] | x <- frees tau, y <- (frees tau), x /= y ])

terminating :: MonadFresh m => [CaseTest] -> CaseTest -> m (Lemma ProofSkeleton)
terminating caseTests caseTest = do
    t1 <- singleMatch tau

    let formula = quantifyFrees exists $ andIf (not $ null taus) t1 (noOther taus)

    return $ skeletonLemma name [] ExistsTrace  formula (unproven ())
    where
        name = L.get cName caseTest ++ "_rel_ter"
        tau = L.get cFormula caseTest
        taus = map (L.get cFormula) (filter (\c -> L.get cName caseTest /= L.get cName c) caseTests)



------------------------------------------------------------------------------
-- Generation
------------------------------------------------------------------------------
            
casesLemmas :: MonadFresh m => AccLemma -> m [Lemma ProofSkeleton]
casesLemmas accLemma = do
        s <- mapM (sufficiency caseTests) caseTests
        v <- verifiability accLemma
        m <- mapM (minimality caseTests) caseTests
        u <- mapM uniqueness caseTests
        i <- mapM injective caseTests
        t <- mapM (terminating caseTests) caseTests

        return $ s ++ [v] ++ m ++ u ++ i ++ t
    where
        caseTests = L.get aCaseTests accLemma

generateAccountabilityLemmas :: (Monad m, MonadThrow m) => AccLemma -> m [Lemma ProofSkeleton]
generateAccountabilityLemmas accLemma = evalFreshT (casesLemmas accLemma) 0