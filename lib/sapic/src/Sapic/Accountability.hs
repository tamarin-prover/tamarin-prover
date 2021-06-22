{-# LANGUAGE FlexibleContexts #-}
-- Copyright   : (c) 2019-2021 Robert Künnemann & Kevin Morio
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Compute translation-specific restrictions
module Sapic.Accountability (
        generateAccountabilityLemmas
      , thyReportRP
) where

import           Control.Monad.Catch
import           Control.Monad.Fresh
import           Data.Maybe
import qualified Extension.Data.Label   as L
import           Theory
import           Theory.Tools.Wellformedness (formulaTerms)
import           Debug.Trace

------------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------------

-- | Create a lemma from a formula with quantifier. Copies accLemma's name
-- (plus suffix) and attributes.
toLemma :: AccLemma -> TraceQuantifier -> String -> SyntacticLNFormula -> ProtoLemma SyntacticLNFormula ProofSkeleton
toLemma accLemma quantifier suffix formula =
        skeletonLemma (L.get aName accLemma ++ suffix) (L.get aAttributes accLemma) quantifier formula (unproven ())

-- | Quantify the given variables
quantifyVars :: ((String, LSort) -> LVar -> SyntacticLNFormula -> SyntacticLNFormula) -> [LVar] -> SyntacticLNFormula -> SyntacticLNFormula
quantifyVars quan vars fm = foldr (\s -> hinted quan s) fm vars

-- | Quantify all free variables
quantifyFrees :: ((String, LSort) -> LVar -> SyntacticLNFormula -> SyntacticLNFormula) -> SyntacticLNFormula -> SyntacticLNFormula
quantifyFrees quan fm = quantifyVars quan (frees fm) fm

protoFactFormula :: String -> [VTerm Name (BVar LVar)] -> VTerm Name (BVar LVar) -> SyntacticLNFormula
protoFactFormula name terms at = Ato $ Action at $ protoFact Linear name terms

tempTerm :: String -> VTerm Name (BVar LVar)
tempTerm name = varTerm $ Free $ LVar name LSortNode 0

msgTerm :: String -> VTerm Name (BVar LVar)
msgTerm name = varTerm $ Free $ LVar name LSortMsg  0

tempVar :: String -> LVar
tempVar name = LVar name LSortNode 0

msgVar :: String -> LVar
msgVar name = LVar name LSortMsg  0

freesSubsetCorrupt :: [LVar] -> SyntacticLNFormula
freesSubsetCorrupt vars = foldl1 (.&&.) corrupted
    where
        corrupted = map corrupt vars
        corrupt var = quantifyVars exists [tempVar "i"] $ protoFactFormula "Corrupted" [varTerm $ Free var] (tempTerm "i")

corruptSubsetFrees :: [LVar] -> SyntacticLNFormula
corruptSubsetFrees vars = quantifyVars forall [msgVar "a", tempVar "i"] $
                            (protoFactFormula "Corrupted" [msgTerm "a"] (tempTerm "i") .==>. isElem (msgVar "a") vars)

isElem :: LVar -> [LVar] -> SyntacticLNFormula
isElem v vars = foldr1 (.||.) (map (eq v) vars)
    where
        eq x y = Ato $ EqE (varTerm $ Free x) (varTerm $ Free y)

strictSubsetOf :: [LVar] -> [LVar] -> SyntacticLNFormula
strictSubsetOf lhs rhs = subset lhs rhs .&&. strict lhs rhs
    where
        subset xs ys = foldr1 (.&&.) (map (\x -> foldr1 (.||.) (map (\y -> eq x y) ys)) xs)
        strict xs ys = foldr1 (.||.) (map (\y -> foldr1 (.&&.) (map (\x -> Not $ eq y x) xs)) ys)
        eq x y = Ato $ EqE (varTerm $ Free x) (varTerm $ Free y)

ntuple :: [LVar] -> VTerm Name (BVar LVar)
ntuple vars = foldr1 (\a b -> fAppPair (a, b)) (map (varTerm . Free) vars)

varsEq :: [LVar] -> [LVar] -> SyntacticLNFormula
varsEq l r = Ato $ EqE (ntuple l) (ntuple r)

noOther :: [SyntacticLNFormula] -> SyntacticLNFormula
noOther fms = foldr1 (.&&.) (map (Not . quantifyFrees exists) fms)

andIf :: Bool -> SyntacticLNFormula -> SyntacticLNFormula -> SyntacticLNFormula
andIf p a b = if p then a .&&. b else a

-- | FIXME: Why do we need the second rename?
singleMatch :: MonadFresh m => SyntacticLNFormula -> m SyntacticLNFormula
singleMatch t = do
    t1 <- rename t
    t2 <- rename t
    return $ t1 .&&. quantifyVars forall (frees t2) (t2 .==>. varsEq (frees t2) (frees t1))

caseTestFormulasExcept :: AccLemma -> CaseTest -> [SyntacticLNFormula]
caseTestFormulasExcept accLemma caseTest = map (L.get cFormula) (filter (\c -> L.get cName caseTest /= L.get cName c) (L.get aCaseTests accLemma))

foldConn :: (SyntacticLNFormula -> SyntacticLNFormula -> SyntacticLNFormula) -> [SyntacticLNFormula] -> SyntacticLNFormula
foldConn _ [fm] = fm
foldConn op fms = foldl1 op fms



------------------------------------------------------------------------------
-- Verification Conditions
------------------------------------------------------------------------------

sufficiency :: MonadFresh m => AccLemma -> CaseTest -> m (ProtoLemma SyntacticLNFormula ProofSkeleton)
sufficiency accLemma caseTest = do
    t1 <- singleMatch tau

    let formula = quantifyFrees exists (t1 .&&. andIf (not $ null taus) (corruptSubsetFrees (frees t1)) (noOther taus))

    return $ toLemma accLemma ExistsTrace name (toIntermediate formula)
    where
        name = "_" ++ L.get cName caseTest ++ "_suff"
        tau = L.get cFormula caseTest
        taus = caseTestFormulasExcept accLemma caseTest

verifiabilityEmpty :: MonadFresh m => AccLemma -> m (ProtoLemma SyntacticLNFormula ProofSkeleton)
verifiabilityEmpty accLemma = return $ toLemma accLemma AllTraces name formula
    where
        name = "_verif_empty"
        taus = map (L.get cFormula) (L.get aCaseTests accLemma)
        lhs = Not $ foldConn (.||.) $ map (quantifyFrees exists) taus
        phi = L.get aFormula accLemma
        formula = quantifyFrees forall $ lhs .==>. phi

verifiabilityNonEmpty :: MonadFresh m => AccLemma -> CaseTest -> m (ProtoLemma SyntacticLNFormula ProofSkeleton)
verifiabilityNonEmpty accLemma caseTest = return $ toLemma accLemma AllTraces name (toIntermediate formula)
    where
        name = "_" ++ L.get cName caseTest ++ "_verif_nonempty"
        tau = L.get cFormula caseTest
        phi = L.get aFormula accLemma
        formula = quantifyFrees forall $ tau .==>. Not phi

minimality :: MonadFresh m => AccLemma -> CaseTest -> m (ProtoLemma SyntacticLNFormula ProofSkeleton)
minimality accLemma caseTest = do
    t1 <- rename tau
    tts <- mapM rename taus

    let rhs = map (\t -> Not (quantifyVars exists (frees t) $ t .&&. strictSubsetOf (frees t) (frees t1))) tts
    let formula = quantifyFrees forall $ t1 .==>. foldConn (.&&.) rhs

    return $ toLemma accLemma AllTraces name (toIntermediate formula)
    where
        name = "_" ++ L.get cName caseTest ++ "_min"
        tau = L.get cFormula caseTest
        taus = map (L.get cFormula) (L.get aCaseTests accLemma)

uniqueness :: MonadFresh m => AccLemma -> CaseTest -> m (ProtoLemma SyntacticLNFormula ProofSkeleton)
uniqueness accLemma caseTest = return $ toLemma accLemma AllTraces name (toIntermediate formula)
    where
        name = "_" ++ L.get cName caseTest ++ "_uniq"
        tau = L.get cFormula caseTest
        formula = quantifyFrees forall (tau .==>. freesSubsetCorrupt (frees tau))

-- | :TODO: : Avoid duplicates
injective :: MonadFresh m => AccLemma -> CaseTest -> m (ProtoLemma SyntacticLNFormula ProofSkeleton)
injective accLemma caseTest = return $ toLemma accLemma AllTraces name (toIntermediate formula)
    where
        name = "_" ++ L.get cName caseTest ++ "_inj"
        tau = L.get cFormula caseTest
        formula = quantifyFrees forall (tau .==>. foldl (.&&.) (TF True) [ Not $ varsEq [x] [y] | x <- frees tau, y <- frees tau, x /= y ])

singlematched :: MonadFresh m => AccLemma -> CaseTest -> m (ProtoLemma SyntacticLNFormula ProofSkeleton)
singlematched accLemma caseTest = do
    t1 <- singleMatch tau

    let formula = quantifyFrees exists $ andIf (not $ null taus) t1 (noOther taus)

    return $ toLemma accLemma ExistsTrace name (toIntermediate formula)
    where
        name = "_" ++ L.get cName caseTest ++ "_single"
        tau = L.get cFormula caseTest
        taus = caseTestFormulasExcept accLemma caseTest



------------------------------------------------------------------------------
-- Generation
------------------------------------------------------------------------------

casesLemmas :: MonadFresh m => AccLemma -> m [ProtoLemma SyntacticLNFormula ProofSkeleton]
casesLemmas accLemma = do
        s <- mapM (sufficiency accLemma) caseTests
        ve <- verifiabilityEmpty accLemma
        vne <- mapM (verifiabilityNonEmpty accLemma) caseTests
        m <- mapM (minimality  accLemma) caseTests
        u <- mapM (uniqueness  accLemma) caseTests
        i <- mapM (injective   accLemma) caseTests
        t <- mapM (singlematched accLemma) caseTests

        return $ s ++ [ve] ++ vne ++ m ++ u ++ i ++ t
    where
        caseTests = L.get aCaseTests accLemma

generateAccountabilityLemmas :: (Monad m, MonadThrow m) => AccLemma -> m [ProtoLemma SyntacticLNFormula ProofSkeleton]
generateAccountabilityLemmas accLemma = evalFreshT (casesLemmas accLemma) 0



------------------------------------------------------------------------------
-- Intermediate transformation
------------------------------------------------------------------------------

toIntermediate :: (Functor syn, Ord c, Ord v, Eq s) => ProtoFormula syn s c v -> ProtoFormula syn s c v
toIntermediate = simplifyFormula . mergeQuantifiers

pullQuantifiers :: (Functor syn, Ord c, Ord v, Eq s) => [Quantifier] -> ProtoFormula syn s c v -> ProtoFormula syn s c v
pullQuantifiers quans fm = case fm of
    Conn And (Qua All x p) (Qua All x' q)   | x == x' -> pull_2 All (.&&.) x p q
    Conn Or  (Qua Ex  x p) (Qua Ex  x' q)   | x == x' -> pull_2 Ex  (.||.) x p q
    -- Conn And (Qua qua x p) (Qua qua' x' q)  | qua == qua' -> Qua qua x (Qua qua' x' (p .&&. q))
    -- Conn Or  (Qua qua  x p) (Qua qua' x' q) | qua == qua' -> Qua qua x (Qua qua' x' (p .||. q))

    Conn And (Qua qua x p) q             | qua `elem` quans -> pull_l qua (.&&.) x p q
    Conn And p             (Qua qua x q) | qua `elem` quans -> pull_r qua (.&&.) x p q
    Conn Or  (Qua qua x p) q             | qua `elem` quans -> pull_l qua (.||.) x p q
    Conn Or  p             (Qua qua x q) | qua `elem` quans -> pull_r qua (.||.) x p q

    Conn Imp (Qua Ex x p) q  | All `elem` quans -> pull_l All (.==>.) x p q
    -- Are there any examples where this makes sense? (All a) => b --> Ex (a => b)
    -- Conn Imp (Qua All x p) q | Ex  `elem` quans -> pull_l Ex  (.==>.) x p q

    _ -> fm
  where
    pull_l qua op x p q = Qua qua x (pullQuantifiers quans (p `op` shiftFreeIndices 1 q))
    pull_r qua op x p q = Qua qua x (pullQuantifiers quans (shiftFreeIndices 1 p `op` q))
    pull_2 qua op x p q = Qua qua x (pullQuantifiers quans (p `op` q))

mergeQuantifiers :: (Functor syn, Ord c, Ord v, Eq s) => ProtoFormula syn s c v -> ProtoFormula syn s c v
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



------------------------------------------------------------------------------
-- Syntactic criterion for RP (BR)
------------------------------------------------------------------------------

-- | Check that the party identities are not public variables.
checkPartyIDPubVar :: OpenTheory -> Bool
checkPartyIDPubVar thy = any (not . isPubConst) $ filter (\x -> x `elem` caseTestsActionWithFrees (theoryCaseTests thy)) (rulesLNTerms thy)
    where
        caseTestsActionWithFrees caseTests = concatMap factTerms (concatMap getActionsInFormula (caseTestsLNFormulasWithFrees caseTests))
        caseTestsLNFormulasWithFrees caseTests = mapMaybe toLNFormula (filter hasFrees $ map (L.get cFormula) caseTests)
        hasFrees fm = not $ null $ frees fm


-- | Filter a formula and get all the action atoms from it. Then extract the Fact part from them.
getActionsInFormula :: Formula (String, LSort) Name LVar-> [LNFact]
getActionsInFormula fm = case fm of
    Ato pa -> (case pa of
        Action _ _ -> (case bvarToLVar pa of
            Action _ f1 -> [f1]
            _           -> [])
        _ -> [])
    TF _           -> []
    Not f          -> getActionsInFormula f
    Conn _ pf1 pf2 -> getActionsInFormula pf1 ++ getActionsInFormula pf2
    Qua _ _ pf     -> getActionsInFormula pf

-- | Get the list of LNTerms (in the premises, actions and conclusions) in the rules of a theory.
rulesLNTerms :: Theory sig c OpenProtoRule p s -> [LNTerm]
rulesLNTerms thy = concatMap factTerms (concat $ (rulesEPrems ++ rulesEActs ++ rulesEConcs ++ rulesACPrems ++ rulesACActs ++ rulesACConcs))
    where
        rulesE       = [ L.get oprRuleE ru | RuleItem ru <- L.get thyItems thy ]
        rulesEPrems  = map (L.get rPrems) rulesE
        rulesEActs   = map (L.get rActs) rulesE
        rulesEConcs  = map (L.get rConcs) rulesE
        rulesAC      = concat [ L.get oprRuleAC ru | RuleItem ru <- L.get thyItems thy ]
        rulesACPrems = map (L.get rPrems) rulesAC
        rulesACActs  = map (L.get rActs) rulesAC
        rulesACConcs = map (L.get rConcs) rulesAC

termContainsPubConst :: LNTerm -> Bool
termContainsPubConst = go
    where
        go c@(LIT _)   = isPubConst c
        go (FAPP  _ a) = any go a

-- | Check restriction formulas for public names.
-- checkRestrFormulasForPubConst :: Formula (String, LSort) Theory.Name LVar -> Bool
-- checkRestrFormulasForPubConst fm = any ((LSortPub ==) . sortOfName) (concatMap constsVTerm (formulaTerms fm))

-- | Get the formulas of the restrictions of a theory.
-- thyRestrFormulas :: Theory sig0 c0 r0 p0 s0 -> [LNFormula]
-- thyRestrFormulas thy = [ L.get rstrFormula restr | RestrictionItem restr <- L.get thyItems thy ]

-- | Check the restrictions of a theory for public names.
-- checkRestrsForPubConst :: Theory sig0 c0 r0 p0 s0 -> Bool
-- checkRestrsForPubConst thy = any checkRestrFormulasForPubConst (thyRestrFormulas thy)

-- | Check the rules of a theory for public names.
checkRulesForPubConst ::  Theory sig0 c0 OpenProtoRule p0 s0 -> Bool
checkRulesForPubConst thy = any termContainsPubConst $ rulesLNTerms thy

thyReportRP :: OpenTheory -> IO ()
thyReportRP thy =  do
    unless (null (theoryRestrictions thy)) $
        putStrLn "Warning: The model contains at least one restriction. RP needs to be checked manually.\n"

    when (checkRulesForPubConst thy) $
        putStrLn "Warning: The model contains public names. RP needs to be checked manually.\n"

    when (checkPartyIDPubVar thy) $
        putStrLn "Warning: At least one case test can be instantiated with non-public names. RP needs to be checked manually.\n"
