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
strictSubsetOf lhs rhs = subset lhs rhs .&&. strict lhs rhs
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

-- | FIXME: Why do we need the second rename?
singleMatch :: MonadFresh m => LNFormula -> m LNFormula
singleMatch t = do
    t1 <- rename t
    t2 <- rename t
    return $ t1 .&&. quantifyVars forall (frees t2) (t2 .==>. varsEq (frees t2) (frees t1))

caseTestFormulasExcept :: AccLemma -> CaseTest -> [LNFormula]
caseTestFormulasExcept accLemma caseTest = map (L.get cFormula) (filter (\c -> L.get cName caseTest /= L.get cName c) (L.get aCaseTests accLemma))



------------------------------------------------------------------------------
-- Verification Conditions
------------------------------------------------------------------------------

sufficiency :: MonadFresh m => AccLemma -> CaseTest -> m (Lemma ProofSkeleton)
sufficiency accLemma caseTest = do
    t1 <- singleMatch tau

    let formula = quantifyFrees exists (t1 .&&. andIf (not $ null taus) (noOther taus) (corruptSubsetFrees (frees t1)))

    return $ toLemma accLemma ExistsTrace name (toIntermediate formula)
    where
        name = "_" ++ L.get cName caseTest ++ "_suff"
        tau = L.get cFormula caseTest
        taus = caseTestFormulasExcept accLemma caseTest

verifiability :: MonadFresh m => AccLemma -> m (Lemma ProofSkeleton)
verifiability accLemma = return $ toLemma accLemma AllTraces name (toIntermediate formula)
    where
        name = "_verif"
        taus = map (L.get cFormula) (L.get aCaseTests accLemma)
        lhs = foldl (.&&.) (TF True) $ map (Not . quantifyFrees exists) taus
        phi = L.get aFormula accLemma
        formula = quantifyFrees forall $ lhs .<=>. phi

minimality :: MonadFresh m => AccLemma -> CaseTest -> m (Lemma ProofSkeleton)
minimality accLemma caseTest = do
    t1 <- rename tau
    tts <- mapM rename taus

    let rhs = map (\t -> Not (quantifyVars exists (frees t) $ t .&&. strictSubsetOf (frees t) (frees t1))) tts
    let formula = quantifyFrees forall $ t1 .==>. foldl (.&&.) (TF True) rhs

    return $ toLemma accLemma AllTraces name (toIntermediate formula)
    where
        name = "_" ++ L.get cName caseTest ++ "_min"
        tau = L.get cFormula caseTest
        taus = map (L.get cFormula) (L.get aCaseTests accLemma)

uniqueness :: MonadFresh m => AccLemma -> CaseTest -> m (Lemma ProofSkeleton)
uniqueness accLemma caseTest = return $ toLemma accLemma AllTraces name (toIntermediate formula)
    where
        name = "_" ++ L.get cName caseTest ++ "_uniq"
        tau = L.get cFormula caseTest
        formula = quantifyFrees forall (tau .==>. (freesSubsetCorrupt $ frees tau))

-- | :TODO: : Avoid duplicates
injective :: MonadFresh m => AccLemma -> CaseTest -> m (Lemma ProofSkeleton)
injective accLemma caseTest = return $ toLemma accLemma AllTraces name (toIntermediate formula)
    where
        name = "_" ++ L.get cName caseTest ++ "_inj"
        tau = L.get cFormula caseTest
        formula = quantifyFrees forall (tau .==>. foldr1 (.&&.) [ Not $ varsEq [x] [y] | x <- frees tau, y <- (frees tau), x /= y ])

terminating :: MonadFresh m => AccLemma -> CaseTest -> m (Lemma ProofSkeleton)
terminating accLemma caseTest = do
    t1 <- singleMatch tau

    let formula = quantifyFrees exists $ andIf (not $ null taus) (noOther taus) t1

    return $ toLemma accLemma ExistsTrace name (toIntermediate formula)
    where
        name = "_" ++ L.get cName caseTest ++ "_rel_ter" 
        tau = L.get cFormula caseTest
        taus = caseTestFormulasExcept accLemma caseTest



------------------------------------------------------------------------------
-- Generation
------------------------------------------------------------------------------
            
casesLemmas :: MonadFresh m => AccLemma -> m [Lemma ProofSkeleton]
casesLemmas accLemma = do
        s <- mapM (sufficiency accLemma) caseTests
        v <- verifiability accLemma
        m <- mapM (minimality  accLemma) caseTests
        u <- mapM (uniqueness  accLemma) caseTests
        i <- mapM (injective   accLemma) caseTests
        t <- mapM (terminating accLemma) caseTests

        return $ s ++ [v] ++ m ++ u ++ i ++ t
    where
        caseTests = L.get aCaseTests accLemma

generateAccountabilityLemmas :: (Monad m, MonadThrow m) => AccLemma -> m [Lemma ProofSkeleton]
generateAccountabilityLemmas accLemma = evalFreshT (casesLemmas accLemma) 0



------------------------------------------------------------------------------
-- Intermediate transformation
------------------------------------------------------------------------------

toIntermediate :: (Ord c, Ord v, Eq s) => Formula s c v -> Formula s c v
toIntermediate = simplifyFormula . mergeQuantifiers

pullQuantifiers :: (Ord c, Ord v, Eq s) => [Quantifier] -> Formula s c v -> Formula s c v
pullQuantifiers quans fm = case fm of
    Conn And (Qua All x p) (Qua All x' q)   | x == x' -> pull_2 All (.&&.) x p q
    Conn Or  (Qua Ex  x p) (Qua Ex  x' q)   | x == x' -> pull_2 Ex  (.||.) x p q
    Conn And (Qua qua x p) (Qua qua' x' q)  | qua == qua' -> Qua qua x (pull_r qua (.&&.) x' p q)
    Conn Or  (Qua qua  x p) (Qua qua' x' q) | qua == qua' -> Qua qua x (pull_r qua (.||.) x' p q)

    Conn And (Qua qua x p) q             | qua `elem` quans -> pull_l qua (.&&.) x p q
    Conn And p             (Qua qua x q) | qua `elem` quans -> pull_r qua (.&&.) x p q
    Conn Or  (Qua qua x p) q             | qua `elem` quans -> pull_l qua (.||.) x p q
    Conn Or  p             (Qua qua x q) | qua `elem` quans -> pull_r qua (.||.) x p q

    Conn Imp (Qua Ex x p) q  | All `elem` quans -> pull_l All (.==>.) x p q
    Conn Imp (Qua All x p) q | Ex  `elem` quans -> pull_l Ex  (.==>.) x p q

    _ -> fm
  where
    pull_l qua op x p q = Qua qua x (pullQuantifiers quans (p `op` shiftFreeIndices 1 q))
    pull_r qua op x p q = Qua qua x (pullQuantifiers quans (shiftFreeIndices 1 p `op` q))
    pull_2 qua op x p q = Qua qua x (pullQuantifiers quans (p `op` q))

mergeQuantifiers :: (Ord c, Ord v, Eq s) => Formula s c v -> Formula s c v
mergeQuantifiers = mergeQuantifiers1 [All, Ex]
  where
    mergeQuantifiers1 quans fm = case fm of
      Not p        -> Not (mergeQuantifiers1 quans p)
      Qua qua x p  -> Qua qua x (mergeQuantifiers1 [qua] p)
      Conn And p q -> pullQuantifiers quans $ mergeQuantifiers1 quans p .&&.  mergeQuantifiers1 quans q
      Conn Or  p q -> pullQuantifiers quans $ mergeQuantifiers1 quans p .||.  mergeQuantifiers1 quans q
      Conn Imp p q -> pullQuantifiers quans $ mergeQuantifiers1 quans p .==>. mergeQuantifiers1 quans q
      Conn Iff p q -> pullQuantifiers quans $ mergeQuantifiers1 quans p .==>. mergeQuantifiers1 quans q .&&. 
                                              mergeQuantifiers1 quans q .==>. mergeQuantifiers1 quans p
      _            -> fm