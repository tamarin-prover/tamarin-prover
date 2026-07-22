{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module CloseRule (
    closeRuleCache,
    closeTheoryWithMaude,
    proveTheory,
    mkSystem,
    applyNDCcheck,
    prettyNDCcheck
)where

import           Prelude                             hiding (id, (.))

import qualified Data.ByteString.Char8 as BC
import           Data.Function (on)
import           Data.List
import           Data.Maybe
import qualified Data.Set                            as S

import           Control.Basics
import           Control.Category
import           Control.Exception (evaluate)
import           Control.DeepSeq (force)
import           Control.Monad.Reader
import           Control.Monad.Bind (MonadFresh)
import qualified Control.Monad.State                 as MS
import           Control.Parallel.Strategies

import qualified Extension.Data.Label                as L
import           Extension.Data.Label                hiding (get)

import           Items.RuleItem

import           ClosedTheory
import           TheoryObject
import           OpenTheory
import           Theory.Model
import           Theory.Proof
import           Theory.Tools.InjectiveFactInstances
import           Theory.Tools.IntruderRules
import           Theory.Constraint.Solver.Sources (IntegerParameters)
import           Theory.Constraint.Solver.Sources     as Sources (IntegerParameters(..))
import           Theory.Tools.LoopBreakers

import           Utils.Misc

import           Text.PrettyPrint.Class

import           Debug.Trace
import           GHC.IO (unsafePerformIO)

-- | Close a theory given a maude signature. This signature must be valid for
-- the given theory.
closeTheoryWithMaude :: SignatureWithMaude -> OpenTranslatedTheory -> Bool -> Bool -> ClosedTheory
closeTheoryWithMaude sig thy0 autoSources showSaturation =
  if autoSources && containsPartialDeconstructions (cache items)
    then
        proveTheory (const True) checkProofM
      $ Theory (L.get thyName thy0) (L.get thyInFile thy0) h t sig (cache items') items' (L.get thyOptions thy0)  (L.get thyIsSapic thy0)
    else
        proveTheory (const True) checkProofM
      $ Theory (L.get thyName thy0) (L.get thyInFile thy0) h t sig (cache items) items (L.get thyOptions thy0) (L.get thyIsSapic thy0)
  where
    parameters = Sources.IntegerParameters (L.get (openChainsLimit . thyOptions) thy0) (L.get (saturationLimit . thyOptions) thy0) showSaturation
    h          = L.get thyHeuristic thy0
    t          = L.get thyTactic thy0
    forcedInjFacts = L.get forcedInjectiveFacts $ L.get thyOptions thy0
    cache its = closeRuleCache parameters restrictions (typAsms its) forcedInjFacts sig (rules its) (L.get thyCache thy0) (L.get (verboseOption . thyOptions) thy0) False (L.get thyIsSapic thy0)
    checkProofM = checkAndExtendProver (sorryProver Nothing)

    -- Maude / Signature handle
    hnd = L.get sigmMaudeHandle sig

    -- Close all theory items: in parallel (especially useful for variants)
    --
    -- NOTE that 'rdeepseq' is OK here, as the proof has not yet been checked
    -- and therefore no constraint systems will be unnecessarily cached.
    (items, _solveRel, _breakers) = (`runReader` hnd) $ addSolvingLoopBreakers $ unfoldClosedRules
       ((closeTheoryItem <$> L.get thyItems thy0) `using` parList rdeepseq)
    closeTheoryItem = foldTheoryItem
       (RuleItem . closeProtoRule hnd (theoryMacros thy0))
       (RestrictionItem . applyMacroInRestriction (theoryMacros thy0))
       (LemmaItem . fmap skeletonToIncrementalProof . applyMacroInLemma (theoryMacros thy0))
       TextItem
       ConfigBlockItem
       PredicateItem
       MacroItem
       TranslationItem

    unfoldClosedRules :: [TheoryItem [ClosedProtoRule] IncrementalProof s] -> [TheoryItem ClosedProtoRule IncrementalProof s]
    unfoldClosedRules        (RuleItem r:is) = map RuleItem r ++ unfoldClosedRules is
    unfoldClosedRules (RestrictionItem i:is) = RestrictionItem i:unfoldClosedRules is
    unfoldClosedRules       (LemmaItem i:is) = LemmaItem i:unfoldClosedRules is
    unfoldClosedRules        (TextItem i:is) = TextItem i:unfoldClosedRules is
    unfoldClosedRules (ConfigBlockItem i:is) = ConfigBlockItem i:unfoldClosedRules is
    unfoldClosedRules   (PredicateItem i:is) = PredicateItem i:unfoldClosedRules is
    unfoldClosedRules       (MacroItem i:is) = MacroItem i:unfoldClosedRules is
    unfoldClosedRules       (TranslationItem i:is) = TranslationItem i:unfoldClosedRules is
    unfoldClosedRules                     [] = []

    -- Name of the auto-generated lemma
    lemmaName = "AUTO_typing"

    itemsModAC = unfoldRules items

    unfoldRules (RuleItem r:is) = map RuleItem (unfoldRuleVariants r) ++ unfoldRules is
    unfoldRules          (i:is) = i:unfoldRules is
    unfoldRules              [] = []

    items' = addAutoSourcesLemma hnd lemmaName (cache itemsModAC) itemsModAC

    -- extract source restrictions and lemmas
    restrictions = do RestrictionItem rstr <- items
                      return $ formulaToGuarded_ $ L.get rstrFormula rstr
    typAsms its  = do LemmaItem lem <- its
                      guard (isSourceLemma lem)
                      return $ formulaToGuarded_ $ L.get lFormula lem

    -- extract protocol rules
    rules :: [TheoryItem ClosedProtoRule IncrementalProof s] -> [ClosedProtoRule]
    rules its = theoryRules (Theory errClose errClose errClose errClose errClose errClose its errClose False)
    errClose = error "closeTheory"

    addSolvingLoopBreakers = useAutoLoopBreakersAC
        (liftToItem $ enumPrems . L.get cprRuleAC)
        (liftToItem $ enumConcs . L.get cprRuleAC)
        (liftToItem $ getDisj . L.get (pracVariants . rInfo . cprRuleAC))
        addBreakers
      where
        liftToItem f (RuleItem ru) = f ru
        liftToItem _ _             = []

        addBreakers bs (RuleItem ru) =
            RuleItem (L.set (pracLoopBreakers . rInfo . cprRuleAC) bs ru)
        addBreakers _  item = item

-- Applying provers
-------------------

-- | Prove both the assertion soundness as well as all lemmas of the theory. If
-- the prover fails on a lemma, then its proof remains unchanged.
proveTheory :: (Lemma IncrementalProof -> Bool)   -- ^ Lemma selector.
            -> Prover
            -> ClosedTheory
            -> ClosedTheory
proveTheory selector prover thy =
    modify thyItems ((`MS.evalState` []) . mapM prove) thy
  where
    prove item = case item of
      LemmaItem l0 -> do l <- MS.gets (LemmaItem . proveLemma l0)
                         MS.modify (l :)
                         return l
      _            -> do return item

    proveLemma lem preItems
      | selector lem = modify lProof add lem
      | otherwise    = lem
      where
        ctxt    = getProofContext lem thy
        sys     = mkSystem ctxt (theoryRestrictions thy) preItems $ L.get lFormula lem
        add prf = fromMaybe prf $ runProver prover ctxt 0 sys prf


-- | Construct a constraint system for verifying the given formula.
mkSystem :: ProofContext -> [Restriction] -> [TheoryItem r p s]
         -> LNFormula -> System
mkSystem ctxt restrictions previousItems =
    -- Note that it is OK to add reusable lemmas directly to the system, as
    -- they do not change the considered set of traces. This is the key
    -- difference between lemmas and restrictions.
    addLemmasLocal
  . formulaToSystem (map (formulaToGuarded_ . L.get rstrFormula) restrictions)
                    (L.get pcSourceKind ctxt)
                    (L.get pcTraceQuantifier ctxt) False
  where
    addLemmasLocal sys =
        insertLemmas (gatherReusableLemmas $ L.get sSourceKind sys) sys

    gatherReusableLemmas kind = do
        LemmaItem lem <- previousItems
        guard $    lemmaSourceKind lem <= kind
                && ReuseLemma `elem` L.get lAttributes lem
                && AllTraces == L.get lTraceQuantifier lem
                && L.get lName lem `notElem` L.get pcHiddenLemmas ctxt
                && "ALL" `notElem` L.get pcHiddenLemmas ctxt
        return $ formulaToGuarded_ $ L.get lFormula lem

-- | Apply the given substitutions to the two given intruder rules and return all resulting rules. This is used for applying chain reduction rules.
appSubst :: MonadFresh m => [LNSubstVFresh] -> IntrRuleAC -> IntrRuleAC -> m [(IntrRuleAC,IntrRuleAC)]
appSubst [] _ _             = return []
appSubst (x:xs) inst0 inst1 = do
  sub <- freshToFree x
  let (instt0,instt1) = apply sub (inst0,inst1)
  rest <- appSubst xs inst0 inst1
  return ((instt0,instt1):rest)

-- Takes a list of facts and logically ands them into a formula that can be used for a lemma : see MessageDerivationChecks.hs for more details
landFormula :: [LNFact] -> ProtoFormula Unit2 (String,LSort) Name  LVar
landFormula facts = foldl (\ fm (idx, fact) -> fm .&&. Ato (Action (LIT (Var (Free (LVar (show (idx :: Integer)) LSortNode 0))) ) fact ))  ltrue (zip [0..]  (map (fmap (fmap (fmap Free))) facts))

-- | Naive deduction check: checks whether a fact is directly present in the given set of terms or can be derived from them by applying construction rules only.
--   This is used as a quick check before performing the more expensive deduction check.
dedNaive :: LNTerm -> [LNTerm] -> Bool
dedNaive fact terms = ded fact
  where
    ded f | f `elem` terms                      = True
    ded (FAPP (NoEq (_,(_,Private,_, _))) _)    = False
    ded (FAPP (AC (ACfct (_,(Private,_,_)))) _) = False
    ded (FAPP _ p)                              = foldr (\x1 -> (&& ded x1)) True p
    ded _                                       = False

-- | Checks whether given a Maude signature and intruder rules a certain fact can be derived from a given set of terms.
deductionCheck :: Integer -> Integer -> SignatureWithMaude -> OpenRuleCache -> LNFact -> [LNFact] -> Bool
deductionCheck ocLimit satLimit sig intrR fact terms =
    -- (if null setD then id else trace ndcTheoryTrace)
    (null setD || checkProofd tabProof1 || checkProofd tabProof2)
  where
    -- Dump the synthetic Tamarin theory/theories used for this NDC deduction
    -- check to the command line. We print the open (.spthy-renderable) theories,
    -- which show the generated Out0 source rule and the (not-yet-NDC-tagged)
    -- destructor rules.
    ndcTheoryTrace =
         "\n===== [NDC check] synthetic theory used for the deduction check =====\n"
      ++ "----- with restrictions OnlyOnce and OnlyOnceD -----\n"
      ++ tabTheory modifiedTheory1
      ++ "\n----- with restriction OnlyOnce only -----\n"
 --     ++ tabTheory modifiedTheory2
      ++ "\n===== [NDC check] end of synthetic theory =====\n"

    tInf (Fact _ _ [f]) = f
    tInListf = foldMap getFactTerms
    setD = filter (not . (dedNaive (tInf fact) . tInListf)) (decompose terms)

    decompose ((Fact KUFact annot [FAPP (NoEq (b,(n,Private,c,ndc))) p]):l) = map ([Fact KDFact annot [FAPP (NoEq (b,(n,Private,c,ndc))) p]] ++) (decompose l)
    decompose ((Fact KUFact annot [FAPP (AC (ACfct (b,(Private,c,ndc)))) p]):l) = map ([Fact KDFact annot [FAPP (AC (ACfct (b,(Private,c,ndc)))) p]] ++) (decompose l)
    decompose ((Fact KUFact annot [FAPP s p]):l) = map ([Fact KDFact annot [FAPP s p]] ++) (decompose l) ++ [x1 ++ y | x1 <- decompose (map (\x -> Fact KUFact annot [x]) p), y <- decompose l]
    decompose (f:l) = map ([f] ++) (decompose l)
    decompose [] = [[]]

    emptyThy = Theory "checkDeduction" "checkDeduction" [] [] (toSignaturePure sig) intrR [] (Option False False False False False False False False False False S.empty [] ocLimit satLimit) False

    tabProof1 = concatMap checkProofStatuses provenTheory1
    provenTheory1 = map (proveTheory (const True) defaultProver) closedTheory1
    closedTheory1 = map (\t -> closeTheoryWithMaude sig t False False) modifiedTheory1 -- no AutoSources
    modifiedTheory1 = map (\s -> (addRules (newRules s) . addLemmas (newLemmas s) . addRestrictions [newRestriction0,newRestriction2]) emptyThy) setD

    tabProof2 = concatMap checkProofStatuses provenTheory2
    provenTheory2 = map (proveTheory (const True) defaultProver) closedTheory2
    closedTheory2 = map (\t -> closeTheoryWithMaude sig t False False) modifiedTheory2 -- no AutoSources
    modifiedTheory2 = map (\s -> (addRules (newRules s) . addLemmas (newLemmas s) . addRestrictions [newRestriction0]) emptyThy) setD
 
    tabTheory (th1:thq) = render (prettyTheory prettySignaturePure prettyOpenRuleCache{-WithLimitAndNDC-} prettyOpenProtoRule prettyProof prettyTranslationElement th1) ++ " \n\n " ++ tabTheory thq
    tabTheory [] = ""

    newRules s = [OpenProtoRule (Rule (ProtoRuleEInfo (StandRule "Out0") (RuleAttributes Nothing Nothing False False Nothing) []) (pre s) (co s) (a s) []) []]
    varD s = frees $ concatMap factTerms s
    varFresh s = map msgToFreshVars (varD s)
    pre = freesToFresh . varFresh
    co = map (outFact . msgToFreshTerms) . concatMap factTerms
    a s = [protoFact Linear "Generated_0" (map (msgToFreshTerms . lvarToLnterm) (varD s)),factOnlyOnce]
    aLemma s = [protoFact Linear "Generated_0" (map lvarToLnterm (varD s))]

    newLemmas s = [Lemma "Deduction" "Deduction" False AllTraces f (Just f) [] (unproven ())]
      where
        f = Not (existFormula $ landFormula $ aLemma s ++ [kLogFact (head (factTerms fact))]) -- FIXME : the head could be a problem
    
    newRestriction0 :: Restriction
    newRestriction0 = Restriction "OnlyOnce" f (Just f)
      where
        f = forAllFormula (factAnd "i" .&&. factAnd "j" .==>. factEq "i" "j")
    factAnd x = Ato (Action (LIT (Var (Free (LVar x LSortNode 0)))) factOnlyOnce)
    factEq x y = Ato (EqE (LIT (Var (Free (LVar x LSortNode 0)))) (LIT (Var (Free (LVar y LSortNode 0)))))
    factOnlyOnce = protoFact Linear "OnlyOnce" []

    factAndD x = Ato (Action (LIT (Var (Free (LVar x LSortNode 0)))) factOnlyOnceD)
    factOnlyOnceD = protoFact Linear "OnlyOnceD" []

    newRestriction2 :: Restriction
    newRestriction2 = Restriction "OnlyOnceD" f (Just f)
     where
      f = forAllFormula (factAndD "i" .&&. factAndD "j" .&&. factAndD "k" .==>. factEq "i" "j" .||. factEq "i" "k" .||. factEq "j" "k" )

    defaultProver = replaceSorryProver $ runAutoProver (AutoProver Nothing Nothing Nothing CutDFS False)

    checkProofd (TraceFound:q) = checkProofd q
    checkProofd [] = True
    checkProofd _ = False

    msgToFreshVars :: LVar -> LVar
    msgToFreshVars (LVar name LSortMsg idx) = LVar name LSortFresh idx
    msgToFreshVars v@(LVar _ _ _) = v

    msgToFreshTerms :: LNTerm -> LNTerm
    msgToFreshTerms t = case viewTerm t of
      Lit (Var (LVar name LSortMsg idx)) -> varTerm (LVar name LSortFresh idx)
      Lit _                              -> t
      FApp f as                          -> termViewToTerm $ FApp f (map msgToFreshTerms as)

-- | Check if the chain of the two given intruder rules can be reduced. This is done by checking if the conclusion of one rule can be unified with a 
--   premise of the other rule and then checking if the resulting terms can be derived from the premises of both rules without chaining.
--   If the two rules cannot be chained, then Nothing is returned. If they can be chained, then Just True is returned if the chain can be reduced and
--   Just False is returned if the chain cannot be reduced.
ndcCheck :: Integer -> Integer -> SignatureWithMaude -> OpenRuleCache -> IntrRuleAC -> IntrRuleAC -> Maybe Bool
ndcCheck ocLimit satLimit sig intrR r@(Rule (DestrRule _ i _ _ _) ((Fact KDFact _ _):_) conc@[Fact KDFact _ _] _ _) r1@(Rule (DestrRule _ j _ _ _) ((Fact KDFact _ _):_) [Fact KDFact _ _] _ _)
  | i /= 1 && j /= 1 =
  case runMaude $ unifyLNFactEqs [Equal (head conc) (getDeconstrRuleKDPrem freshInst1)] of
    []    -> Nothing
    subst -> Just (checkDeduction (applySubsts subst r freshInst1))
  where
    hnd        = L.get sigmMaudeHandle sig
    runMaude   = (`runReader` hnd)
    freshInst1 = r1 `renameAvoiding` r
    -- ppPair (x, y) = render (prettyIntrRuleAC x) ++ " \n " ++ render (prettyIntrRuleAC y)

    -- Apply the given substitutions to the two given intruder rules and return all resulting rules.
    applySubsts :: [LNSubstVFresh] -> IntrRuleAC -> IntrRuleAC -> [(IntrRuleAC,IntrRuleAC)]
    applySubsts s ru0 ru1 = evalFreshAvoiding (appSubst s ru0 ru1) (ru0, ru1)

    -- Apply the deduction check to all pairs of rules resulting from applying the unifying substitutions to the two given intruder rules.
    checkDeduction ((s1,h1):sq) = chainedRulesDeductionTest ocLimit satLimit sig intrR s1 h1 && checkDeduction sq
    checkDeduction []           = True
ndcCheck _ _ _ _ _ _ = Nothing

-- Check if the conclusion of the second rule can be derived from the premises of both rules without chaining.
chainedRulesDeductionTest :: Integer -> Integer -> SignatureWithMaude -> OpenRuleCache -> IntrRuleAC -> IntrRuleAC -> Bool
chainedRulesDeductionTest ocLimit satLimit sig intrR instSigma inst1Sigma = aux factToDeduce
  where
    facts = getDeconstrRulePremsTail instSigma ++ getDeconstrRulePremsTail inst1Sigma ++ [getDeconstrRuleKDPrem instSigma]
    terms = foldMap getFactTerms facts
    factToDeduce = getConcFact inst1Sigma

    factOnlyOnce = protoFact Linear "OnlyOnceD" []

    -- intruder rules but with all deconstruction rules for the given AC symbol limited to one application for deduction checks
    intrRmodified = map boundToOne intrR

    boundToOne rule@(Rule (DestrRule name i subterm constant funs) premis concs acts nvs)
        | getDestrRuleFunction rule == getDestrRuleFunction instSigma   = Rule (DestrRule name i subterm constant (mapHead (setNDC IsNDC) funs)) premis concs (acts ++ [factOnlyOnce]) nvs -- for the rule instance we want to check, we add the factOnlyOnce to the actions to ensure that it is only applied once
    boundToOne rule@(Rule (DestrRule name _ _ _ _) _ _ _ _)
        | any (`BC.isSuffixOf` name) builtInDestrRuleInclPair = rule -- do not touch built-in deconstruction rules
    boundToOne (Rule (DestrRule name 0 subterm constant funs) premis concs acts nvs)
                                                      = Rule (DestrRule name 1 subterm constant funs) premis concs acts nvs -- bound the rule to one application other rules
    boundToOne rr                                     = rr

    aux fa@(Fact KDFact _ [f]) = dedNaive f terms || deductionCheck ocLimit satLimit sig intrRmodified fa facts
    aux _                      = error "No Deconstruction Chain Check: This case should not happen, please report it on the github page" 

-- | Apply no deconstruction chain check to a list of intruder rules. The first argument states
--   whether the rules belong to the diff-mode intruder rules, whose NDC property is recorded
--   separately in the signature.
applyNDCcheck :: Bool -> Integer -> Integer -> SignatureWithMaude -> OpenRuleCache -> [[IntrRuleAC]] -> (SignatureWithMaude, OpenRuleCache)
applyNDCcheck forDiff ocLimit satLimit sig intrR (t1:tq)  =
    if checkChainReductionIter ruleTuples == (True, False)
      then trace ("Function " ++ showFunSymName f ++ " has the NDC property" ++ modeSuffix ++ ".") (setNDCinSig' sig' f, map setNDCToTrue t1 ++ intrR')
      else trace ("Function " ++ showFunSymName f ++ " does not have the NDC property" ++ modeSuffix ++ ".") (sig', t1 ++ intrR')
  where
    f = fromJust (getDestrRuleFunction $ head t1)
    (sig', intrR') = applyNDCcheck forDiff ocLimit satLimit sig intrR tq
    modeSuffix = if forDiff then " in diff mode" else ""
    setNDCinSig' s fs = joinNDCinSigWMaude s fs (if forDiff then IsNDCDiff else IsNDC)
    ruleTuples = [(x,y) | x <- t1, y <- t1]
    checkChainReductionIter = foldr g (True, True)
      where
        g (x,y) (resSoFar, allNotChainable) = 
          case ndcCheck ocLimit satLimit sig intrR x y of
            Just result -> (resSoFar && result, False)
            Nothing -> (resSoFar, allNotChainable)

    setNDCToTrue (Rule (DestrRule name i subterm constant funs) prems concs acts nvs) = Rule (DestrRule name i subterm constant (mapHead (addNDC (if forDiff then IsNDCDiff else IsNDC)) funs)) prems concs acts nvs
    setNDCToTrue r = r
applyNDCcheck _ _ _ sig _ [] = (sig, [])

-- | Pretty print the result of chain reduction checks. The first argument states whether the
--   rules belong to the diff-mode intruder rules.
prettyNDCcheck :: Bool -> Integer -> Integer -> SignatureWithMaude -> String -> OpenRuleCache -> (SignatureWithMaude, OpenRuleCache)
prettyNDCcheck forDiff ocLimit satLimit sig name initRules = unsafePerformIO $ do
  let (builtInOrConstrOrNDC, nonBuiltInDestr) = partition (\x -> isBuiltInIntruderRule x || isConstrRule x || isJust (if forDiff then isNDCDiffRule x else isNDCRule x)) initRules
  -- for the no deconstruction check we group deconstruction rules of the same function together based on the rule function, as the NDC property is a property of the function and not of the individual rules. We then apply the NDC check to each group of rules separately, as the NDC property is a property of the function and not of the individual rules. This also allows us to parallelize the NDC check for different functions.
  let t' = groupBy ((==) `on` getDestrRuleFunction) $ sortOn getDestrRuleFunction nonBuiltInDestr
  let (subtermRules, t) = partition (all isSubtermRule) t' -- we only check the NDC property for deconstruction rules that are not subterm rules
  traceM ("[Theory " ++ name ++ "] No Deconstruction Chain checks " ++ (if forDiff then "for diff mode " else "") ++ "started")
  (sig', rules) <- evaluate . force $ applyNDCcheck forDiff ocLimit satLimit sig initRules t
  -- traceM ("Result : " ++ render (prettyOpenRuleCacheWithLimitAndNDC $ rules ++ builtInOrConstrOrNDC))
  traceM ("[Theory " ++ name ++ "] No Deconstruction Chain checks ended")
  return (sig', rules ++ builtInOrConstrOrNDC ++ concat subtermRules) -- we add the built-in rules back to the intruder rules, as they are not modified by the NDC check

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
closeRuleCache parameters restrictions typAsms forcedInjFacts sig protoRules intrRules verbose isdiff isSapic =
   ClosedRuleCache
        classifiedRules rawSources refinedSources injFactInstances
  where
    ctxt0 = ProofContext
        sig classifiedRules injFactInstances RawSource [] AvoidInduction Nothing Nothing
        (error "closeRuleCache: trace quantifier should not matter here")
        (error "closeRuleCache: lemma name should not matter here") [] verbose isdiff
        (all isSubtermRule destr) (any isConstantRule destr)
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

    -- classifying the rules
    rulesAC = (fmap IntrInfo                    <$> intrRules) <|>
              (fmap ProtoInfo . L.get cprRuleAC <$> protoRules)

    anyOf ps = partition (\x -> any ($ x) ps)

    (nonProto, proto) = anyOf [isDestrRule, isConstrRule] rulesAC
    (constr, destr)   = anyOf [isConstrRule] nonProto

    -- and sort them into ClassifiedRules datastructure for later use in proofs
    classifiedRules = ClassifiedRules
      { _crConstruct  = constr
      , _crDestruct   = destr
      , _crProtocol   = proto
      }
