{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Rule (
    module Rule
    ,module Items.RuleItem
)where

import Items.RuleItem

import           Prelude                             hiding (id, (.))

import           Data.List

import qualified Data.Set                            as S

import           Control.Basics
import           Control.Category
import           Control.Monad.Reader

import qualified Extension.Data.Label                as L

import           Theory.Model
import           Theory.Proof
import           Theory.Tools.InjectiveFactInstances
import           Theory.Tools.RuleVariants
import           Theory.Tools.IntruderRules

import           Term.Positions
import           Term.Macro
import Theory.Constraint.Solver.Sources (IntegerParameters)


import Debug.Trace
import Text.PrettyPrint.Class
import Control.Monad.Bind (MonadFresh)


-- | Get an OpenProtoRule's name
getOpenProtoRuleName :: OpenProtoRule -> String
getOpenProtoRuleName (OpenProtoRule ruE _) = getRuleName ruE

-- | Add the diff label to an OpenProtoRule
addProtoDiffLabel :: OpenProtoRule -> String -> OpenProtoRule
addProtoDiffLabel (OpenProtoRule ruE ruAC) label = OpenProtoRule (addDiffLabel ruE label) (fmap ((flip addDiffLabel) label) ruAC)

equalOpenRuleUpToDiffAnnotation :: OpenProtoRule -> OpenProtoRule -> Bool
equalOpenRuleUpToDiffAnnotation (OpenProtoRule ruE1 ruAC1) (OpenProtoRule ruE2 ruAC2) =
  equalRuleUpToDiffAnnotationSym ruE1 ruE2 && length ruAC1 == length ruAC2 &&
  all (uncurry equalRuleUpToDiffAnnotationSym) (zip ruAC1 ruAC2)

-- Relation between open and closed rule sets
---------------------------------------------

-- | All intruder rules of a set of classified rules.
intruderRules :: ClassifiedRules -> [IntrRuleAC]
intruderRules rules = do
    Rule (IntrInfo i) ps cs as nvs <- joinAllRules rules
    return $ Rule i ps cs as nvs

-- | Open a rule cache. Variants and precomputed case distinctions are dropped.
openRuleCache :: ClosedRuleCache -> OpenRuleCache
openRuleCache = intruderRules . L.get crcRules

-- | Open a protocol rule; i.e., drop variants and proof annotations.
openProtoRule :: ClosedProtoRule -> OpenProtoRule
openProtoRule r = OpenProtoRule ruleE ruleAC
  where
    ruleE   = L.get cprRuleE r
    ruleAC' = L.get cprRuleAC r
    ruleAC  = if equalUpToTerms ruleAC' ruleE
               then []
               else [ruleAC']

-- | Unfold rule variants, i.e., return one ClosedProtoRule for each
-- variant
unfoldRuleVariants :: ClosedProtoRule -> [ClosedProtoRule]
unfoldRuleVariants (ClosedProtoRule ruE ruAC@(Rule ruACInfoOld ps cs as nvs))
   | isTrivialProtoVariantAC ruAC ruE = [ClosedProtoRule ruE ruAC]
   | otherwise = map toClosedProtoRule variants
        where
          ruACInfo i = ProtoRuleACInfo (rName i (L.get pracName ruACInfoOld)) rAttributes (Disj [emptySubstVFresh]) loopBreakers
          rAttributes = L.get pracAttributes ruACInfoOld
          loopBreakers = L.get pracLoopBreakers ruACInfoOld
          rName i oldName = case oldName of
            FreshRule -> FreshRule
            StandRule s -> StandRule $ s ++ "___VARIANT_" ++ show i

          toClosedProtoRule (i, (ps', cs', as', nvs'))
            = ClosedProtoRule ruE (Rule (ruACInfo i) ps' cs' as' nvs')
          variants = zip [1::Int ..] $ map (\x -> apply x (ps, cs, as, nvs)) $ substs (L.get pracVariants ruACInfoOld)
          substs (Disj s) = map (`freshToFreeAvoiding` ruAC) s

-- | Close a protocol rule; i.e., compute AC variant and source assertion
-- soundness sequent, if required.
closeProtoRule :: MaudeHandle -> [Macro] -> OpenProtoRule -> [ClosedProtoRule]
-- if there are no macros, we do not call applyMacroInRule to make sure that new vars are not overwritten (important for diff mode)
closeProtoRule hnd []     (OpenProtoRule ruE [])   = [ClosedProtoRule ruE (variantsProtoRule hnd ruE)]
closeProtoRule hnd macros (OpenProtoRule ruE [])   = [ClosedProtoRule ruE (variantsProtoRule hnd (applyMacroInRule macros ruE))]
closeProtoRule _   _      (OpenProtoRule ruE ruAC) = map (ClosedProtoRule ruE) ruAC


-- appSubst :: (MonadFresh m, Apply (Subst Name LVar) t) => LNSubstVFresh -> t -> m t
-- appSubst :: MonadFresh m => LNSubstVFresh -> (IntrRuleAC, IntrRuleAC) -> m (IntrRuleAC,IntrRuleAC)
-- appSubst x inst = do
--   subb <- freshToFree x
--   let instt = apply subb inst
--   --instt <- rename(apply subb inst)
--   return instt

appSubst :: MonadFresh m => [LNSubstVFresh] -> IntrRuleAC -> IntrRuleAC -> m [(IntrRuleAC,IntrRuleAC)]
appSubst [] _ _    = return []
appSubst (x:xs) inst0 inst1 = do
  sub <- freshToFree x
  let (instt0,instt1) = apply sub (inst0,inst1)
  rest <- appSubst xs inst0 inst1
  return ((instt0,instt1):rest)

derivationTest :: LNFact -> [LNFact] -> Bool
derivationTest fact terms = False
  where
    set = decompose terms

    decompose ((Fact KUFact annot [FAPP (NoEq (b,(n,Private,c))) p]):l) = map ([Fact KDFact annot [FAPP (NoEq (b,(n,Private,c))) p]] ++) (decompose l)
    decompose ((Fact KUFact annot [FAPP (AC (ACfct (b,(n,Private,c)))) p]):l) = map ([Fact KDFact annot [FAPP (AC (ACfct (b,(n,Private,c)))) p]] ++) (decompose l)
    decompose ((Fact KUFact annot [FAPP s p]):l) = map ([Fact KDFact annot [FAPP s p]] ++) (decompose l) ++ map (map (\x -> Fact KUFact annot [x]) p ++) (decompose l)
    decompose (f:l) = map ([f] ++) (decompose l)
    decompose [] = [[]]

checkChainReduction :: MaudeHandle -> IntrRuleAC -> Bool
checkChainReduction hnd r@(Rule (DestrRule _ _ _ _) ((Fact KDFact _ _):_) conc@[Fact KDFact _ _] _ _) =
 case runMaude $ unifyLNFactEqs [Equal (head conc) f1] of
    [] -> False
    subst -> trace ("\nsubst : " ++ show subst ++ "\nsigma instance : " ++ concatMap ppPair (auxMatcher subst r inst1)) searchMatcheraux (auxMatcher subst r inst1)-- searchMatcheraux subst
  where
    runMaude   = (`runReader` hnd)
    inst1 = r `renameAvoiding` r

    ppPair (x, y) = render (prettyIntrRuleAC x) ++ "\n" ++ render (prettyIntrRuleAC y)

    getPremsFactKD (Rule _ (fact:_) _ _ _) = fact
    getPremsFactTail (Rule _ ((Fact KDFact _ _):tls) _ _ _) = tls
    getConcFact (Rule _ _ [fact] _ _) = fact

    f1 = getPremsFactKD inst1

    auxMatcher :: [LNSubstVFresh] -> IntrRuleAC -> IntrRuleAC -> [(IntrRuleAC,IntrRuleAC)]
    auxMatcher subst ru0 ru1 = evalFreshAvoiding (appSubst subst ru0 ru1) (ru0, ru1)

    -- searchMatcheraux (s1:sq) = searchMatcher s1 && searchMatcheraux sq
    -- searchMatcheraux [] = True

    searchMatcheraux ((s1,h1):sq)  = searchMatcher s1 h1 && searchMatcheraux sq
    searchMatcheraux [] = True

    -- searchMatcher :: LNSubstVFresh -> Bool
    -- searchMatcher sub  =

    searchMatcher :: IntrRuleAC -> IntrRuleAC -> Bool
    searchMatcher instSigma inst1Sigma  =
      case doMatch (sigmaRHS1 `matchFact` rhs2 <> sigmaF `matchFact` f2) of
        [] -> trace ("\ninstance 2 : " ++ render ( prettyIntrRuleAC inst2)) False
        match -> trace ("\nmatch : " ++ show match) auxDeducible match
      where
        doMatch match = runReader (solveMatchLNTerm match) hnd

        --(instSigma, inst1Sigma) = evalFreshAvoiding (appSubst sub (r, inst1)) (r, inst1)

        inst2 = r `renameAvoiding` (inst1Sigma, instSigma)

        f2 = getPremsFactKD inst2
        rhs2 = getConcFact inst2

        sigmaRHS1 = getConcFact inst1Sigma
        sigmaF = getPremsFactKD instSigma

        auxDeducible (m1:mq) = checkDeducible m1 && auxDeducible mq
        auxDeducible [] = True

        checkDeducible :: Subst Name LVar -> Bool
        checkDeducible m = trace (show (aux prems)) aux prems || True

         where
          terms = getPremsFactTail instSigma ++ getPremsFactTail inst1Sigma
          termsT = foldMap getFactTerms terms
          inst2sigma2 = apply m inst2
          prems = getPremsFactTail inst2sigma2

          aux (fa@(Fact KUFact _ [f]):q) = (aux1 f || derivationTest fa terms) && aux q
          aux ((Fact KDFact _ _):_) = False
          aux []                    = True
          aux _                     = False

          aux1 f | f `elem` termsT    = True
          aux1 (FAPP (NoEq (_,(_,Private,_))) _) = False
          aux1 (FAPP (AC (ACfct (_,(_,Private,_)))) _) = False
          aux1 (FAPP _ p) = foldr (\x1 -> (&& aux1 x1)) True p
          aux1 _                     = False



checkChainReduction _ _ = False


-- | Close an intruder rule; i.e., compute maximum number of consecutive applications and variants
--   Should be parallelized like the variant computation for protocol rules (JD)
closeIntrRule :: MaudeHandle -> IntrRuleAC -> [IntrRuleAC]
closeIntrRule hnd r@(Rule (DestrRule name (-1) subterm constant) prems@((Fact KDFact _ [t]):_) concs@[Fact KDFact _ [rhs]] acts nvs) =
  trace ("Bool : " ++ show (checkChainReduction hnd r)) $ if subterm then [ru] else variantsIntruder hnd id False ru
    where
      ru = Rule (DestrRule name (if runMaude (unifiableLNTerms rhs t)
                              then (length (positions t)) - (if (isPrivateFunction t) then 1 else 2)
                              -- We do not need to count t itself, hence - 1.
                              -- If t is a private function symbol we need to permit one more rule
                              -- application as there is no associated constructor.
                              else 0) subterm constant) prems concs acts nvs
        where
           runMaude = (`runReader` hnd)
closeIntrRule hnd ir@(Rule (DestrRule _ _ False _) _ _ _ _) = variantsIntruder hnd id False ir
closeIntrRule _   ir                                        = [ir]


-- | Close a rule cache. Hower, note that the
-- requires case distinctions are not computed here.
closeRuleCache :: IntegerParameters  -- ^ Parameters for open chains and saturation limits
               -> [LNGuarded]        -- ^ Restrictions to use.
               -> [LNGuarded]        -- ^ Source lemmas to use.
               -> S.Set FactTag      -- ^ Fact tags forced to be injective
               -> SignatureWithMaude -- ^ Signature of theory.
               -> [ClosedProtoRule]  -- ^ Protocol rules with variants.
               -> OpenRuleCache      -- ^ Intruder rules modulo AC.
               -> Bool               -- ^ Verbose option
               -> Bool               -- ^ Diff or not
               -> Bool               -- ^ isSapic or not
               -> ClosedRuleCache    -- ^ Cached rules and case distinctions.
closeRuleCache parameters restrictions typAsms forcedInjFacts sig protoRules intrRules verbose isdiff isSapic = -- trace ("closeRuleCache: " ++ show classifiedRules) $
    ClosedRuleCache
        classifiedRules rawSources refinedSources injFactInstances
  where
    ctxt0 = ProofContext
        sig classifiedRules injFactInstances RawSource [] AvoidInduction Nothing Nothing
        (error "closeRuleCache: trace quantifier should not matter here")
        (error "closeRuleCache: lemma name should not matter here") [] verbose isdiff
        (all isSubtermRule {-- $ trace (show destr ++ " - " ++ show (map isSubtermRule destr))-} destr) (any isConstantRule destr)
        isSapic

    -- Maude handle
    hnd = L.get sigmMaudeHandle sig
    reducibles = reducibleFunSyms $ mhMaudeSig hnd

    forcedInjFacts' = S.map (\x -> (x, replicate (factTagArity x) [Unspecified])) forcedInjFacts
    -- inj fact instances
    injFactInstances = forcedInjFacts' `S.union`
        simpleInjectiveFactInstances reducibles (L.get cprRuleE <$> protoRules)

    -- precomputing the case distinctions: we make sure to only add safety
    -- restrictions. Otherwise, it wouldn't be sound to use the precomputed case
    -- distinctions for properties proven using induction.
    safetyRestrictions = filter isSafetyFormula restrictions
    rawSources         = precomputeSources parameters ctxt0 safetyRestrictions
    refinedSources     = refineWithSourceAsms parameters typAsms ctxt0 rawSources

    -- close intruder rules
    intrRulesAC = concat $ map (closeIntrRule hnd) intrRules

    -- classifying the rules
    rulesAC = (fmap IntrInfo                      <$> intrRulesAC) <|>
              ((fmap ProtoInfo . L.get cprRuleAC) <$> protoRules)

    anyOf ps = partition (\x -> any ($ x) ps)

    (nonProto, proto) = anyOf [isDestrRule, isConstrRule] rulesAC
    (constr, destr)   = anyOf [isConstrRule] nonProto

    -- and sort them into ClassifiedRules datastructure for later use in proofs
    classifiedRules = ClassifiedRules
      { _crConstruct  = constr
      , _crDestruct   = destr
      , _crProtocol   = proto
      }


-- | Returns true if the REFINED sources contain open chains.
containsPartialDeconstructions :: ClosedRuleCache    -- ^ Cached rules and case distinctions.
                     -> Bool               -- ^ Result
containsPartialDeconstructions (ClosedRuleCache _ _ cases _) =
      sum (map (sum . unsolvedChainConstraints) cases) /= 0

-- | Add an action to a closed Proto Rule.
--   Note that we only add the action to the variants modulo AC, not the initial rule.
addActionClosedProtoRule :: ClosedProtoRule -> LNFact -> ClosedProtoRule
addActionClosedProtoRule (ClosedProtoRule e ac) f
   = ClosedProtoRule e (addAction ac f)
