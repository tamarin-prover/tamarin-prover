{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module CloseRule (
    closeRuleCache,
    closeTheoryWithMaude,
    proveTheory,
    mkSystem
)where

import Items.RuleItem

import           Prelude                             hiding (id, (.))

import           Data.List

import qualified Data.Set                            as S

import           Control.Basics
import           Control.Category
import           Control.Monad.Reader
import           Control.Monad.Bind (MonadFresh)

import qualified Extension.Data.Label                as L

import           ClosedTheory
import           TheoryObject
import           OpenTheory
import           Theory.Model
import           Theory.Proof
import           Theory.Tools.InjectiveFactInstances
import           Theory.Tools.IntruderRules

import           Term.Positions

import           Theory.Constraint.Solver.Sources (IntegerParameters)

import Debug.Trace
import Text.PrettyPrint.Class

import Data.Function (on)

import           Theory.Constraint.Solver.Sources     as Sources (IntegerParameters(..))

import qualified Control.Monad.State                 as MS
import           Control.Parallel.Strategies
import           Theory.Tools.LoopBreakers
import           Data.Maybe
import           Extension.Data.Label                hiding (get)


-- | Close a theory given a maude signature. This signature must be valid for
-- the given theory.
closeTheoryWithMaude :: SignatureWithMaude -> OpenTranslatedTheory -> Bool -> Bool -> ClosedTheory
closeTheoryWithMaude sig thy0 autoSources showSaturation =
  if autoSources && containsPartialDeconstructions (cache items)
    then
        proveTheory (const True) checkProof
      $ Theory (L.get thyName thy0) h t sig (cache items') items' (L.get thyOptions thy0)  (L.get thyIsSapic thy0)
    else
        proveTheory (const True) checkProof
      $ Theory (L.get thyName thy0) h t sig (cache items) items (L.get thyOptions thy0) (L.get thyIsSapic thy0)
  where
    parameters = Sources.IntegerParameters (L.get (openChainsLimit.thyOptions) thy0) (L.get (saturationLimit.thyOptions) thy0) showSaturation
    h          = L.get thyHeuristic thy0
    t          = L.get thyTactic thy0
    forcedInjFacts = L.get forcedInjectiveFacts $ L.get thyOptions thy0
    cache its = closeRuleCache parameters restrictions (typAsms its) forcedInjFacts sig (rules its) (L.get thyCache thy0) (L.get (verboseOption.thyOptions) thy0) False (L.get thyIsSapic thy0)
    checkProof = checkAndExtendProver (sorryProver Nothing)

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
       RestrictionItem
       (LemmaItem . fmap skeletonToIncrementalProof)
       TextItem
       PredicateItem
       MacroItem
       TranslationItem

    unfoldClosedRules :: [TheoryItem [ClosedProtoRule] IncrementalProof s] -> [TheoryItem ClosedProtoRule IncrementalProof s]
    unfoldClosedRules        (RuleItem r:is) = map RuleItem r ++ unfoldClosedRules is
    unfoldClosedRules (RestrictionItem i:is) = RestrictionItem i:unfoldClosedRules is
    unfoldClosedRules       (LemmaItem i:is) = LemmaItem i:unfoldClosedRules is
    unfoldClosedRules        (TextItem i:is) = TextItem i:unfoldClosedRules is
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
    rules its = theoryRules (Theory errClose errClose errClose errClose errClose its errClose False)
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
                && (L.get lName lem) `notElem` (L.get pcHiddenLemmas ctxt)
                && "ALL" `notElem` (L.get pcHiddenLemmas ctxt)
        return $ formulaToGuarded_ $ L.get lFormula lem


appSubst :: MonadFresh m => [LNSubstVFresh] -> IntrRuleAC -> IntrRuleAC -> m [(IntrRuleAC,IntrRuleAC)]
appSubst [] _ _    = return []
appSubst (x:xs) inst0 inst1 = do
  sub <- freshToFree x
  let (instt0,instt1) = apply sub (inst0,inst1)
  rest <- appSubst xs inst0 inst1
  return ((instt0,instt1):rest)

-- Takes a list of facts and logically ands them into a formula that can be used for a lemma : see MessageDerivationChecks.hs for more details
landFormula :: [LNFact] -> ProtoFormula Unit2 (String,LSort) Name  LVar
landFormula facts = foldl (\ fm (idx, fact) -> fm .&&. Ato (Action (LIT (Var (Free (LVar (show (idx :: Integer)) LSortNode 0))) ) fact ))  ltrue (zip [0..]  (map (fmap (fmap (fmap Free))) facts))

derivationTest :: SignatureWithMaude -> OpenRuleCache -> LNFact -> [LNFact] -> Bool
derivationTest sig intrR fact terms = trace ("\ntabProof : " ++ show tabProof) (checkProof tabProof)
  where
    setD = decompose terms

    decompose ((Fact KUFact annot [FAPP (NoEq (b,(n,Private,c))) p]):l) = map ([Fact KDFact annot [FAPP (NoEq (b,(n,Private,c))) p]] ++) (decompose l)
    decompose ((Fact KUFact annot [FAPP (AC (ACfct (b,(n,Private,c)))) p]):l) = map ([Fact KDFact annot [FAPP (AC (ACfct (b,(n,Private,c)))) p]] ++) (decompose l)
    decompose ((Fact KUFact annot [FAPP s p]):l) = map ([Fact KDFact annot [FAPP s p]] ++) (decompose l) ++ [x1 ++ y | x1 <- decompose (map (\x -> Fact KUFact annot [x]) p), y <- decompose l]-- ++ map (\x -> x ++ decompose l) (decompose (map (\x -> Fact KUFact annot [x]) p))
    -- problème s'il y a des doublons ?
    decompose (f:l) = map ([f] ++) (decompose l)
    decompose [] = [[]]

    emptyThy = Theory "checkReduction" [] [] (toSignaturePure sig) intrR [] defaultOption False

    tabProof = concatMap (\_ -> [TraceFound]) provenTheory
    --tabProof = concatMap checkProofStatuses provenTheory
    provenTheory = closedTheory 
    --provenTheory = map (proveTheory (const True) defaultProver) closedTheory
    closedTheory = trace ("\ntheory : \n" ++ tabTheory modifiedTheory) map (\t -> closeTheoryWithMaude sig t False False) modifiedTheory -- no AutoSources
    modifiedTheory = zipWith (\s t -> (addRules (newRules s) . addLemmas (newLemmas s)) t) setD (repeat emptyThy)

    tabTheory (th1:thq) = render (prettyTheory prettySignaturePure prettyOpenRuleCacheWithLimit prettyOpenProtoRule prettyProof prettyTranslationElement th1) ++ " \n\n " ++ tabTheory thq
    tabTheory [] = ""

    -- trace ("\nterms for deduction : " ++ show s1 ++ "\nfact : " ++ show fact)

    newRules s = [OpenProtoRule (Rule (ProtoRuleEInfo (StandRule "0") [] []) (pre s) (co s) (a s) []) []]
    varD s = frees $ concatMap factTerms s
    varFresh s = map msgToFreshVars (varD s)
    pre = freesToFresh . varFresh
    co = map (outFact . msgToFreshTerms) . concatMap factTerms
    a s = [protoFact Linear "Generated_0" (map (msgToFreshTerms . lvarToLnterm) (varD s))]
    alemma s = [protoFact Linear "Generated_0" (map lvarToLnterm (varD s))]

    newLemmas s = [Lemma "Derivation" AllTraces (Not (existFormula $ landFormula $ alemma s ++ [kLogFact (head (factTerms fact))])) [] (unproven ())] -- TODO : faire sans le head
    

    defaultProver = replaceSorryProver $ runAutoProver (AutoProver Nothing Nothing Nothing CutDFS)

    checkProof (TraceFound:q) = checkProof q
    checkProof [] = True
    checkProof _ = False

    msgToFreshVars :: LVar -> LVar
    msgToFreshVars (LVar name LSortMsg idx) = LVar name LSortFresh idx
    msgToFreshVars v@(LVar _ _ _) = v

    msgToFreshTerms :: LNTerm -> LNTerm
    msgToFreshTerms t = case viewTerm t of
      Lit (Var (LVar name LSortMsg idx)) -> varTerm (LVar name LSortFresh idx)
      Lit _                              -> t
      FApp f as                          -> termViewToTerm $ FApp f (map msgToFreshTerms as)

checkChainReduction :: SignatureWithMaude -> OpenRuleCache -> IntrRuleAC -> IntrRuleAC -> [IntrRuleAC] -> Bool
checkChainReduction sig intrR r@(Rule (DestrRule _ i _ _) ((Fact KDFact _ _):_) conc@[Fact KDFact _ _] _ _) r1@(Rule (DestrRule _ j _ _) ((Fact KDFact _ _):_) [Fact KDFact _ _] _ _) allR | (i /= 1 && j /=1) =
 case runMaude $ unifyLNFactEqs [Equal (head conc) f1] of
    [] -> False
    subst -> trace ("\nsubst : " ++ show subst) searchMatcheraux (auxMatcherFilter (auxMatcher subst r inst1))
    -- trace ("\nsigma instance : " ++ concatMap ppPair (auxMatcher subst r inst1) ++ "\n\nsigma instance filtered : " ++ concatMap ppPair (auxMatcherFilter (auxMatcher subst r inst1)))
  where
    hnd = L.get sigmMaudeHandle sig
    runMaude   = (`runReader` hnd)
    inst1 = r1 `renameAvoiding` r

    -- ppPair (x, y) = render (prettyIntrRuleAC x) ++ " \n " ++ render (prettyIntrRuleAC y)

    getPremsFactKD (Rule _ (fact:_) _ _ _) = fact
    getPremsFactTail (Rule _ ((Fact KDFact _ _):tls) _ _ _) = tls
    getConcFact (Rule _ _ [fact] _ _) = fact

    f1 = getPremsFactKD inst1

    auxMatcher :: [LNSubstVFresh] -> IntrRuleAC -> IntrRuleAC -> [(IntrRuleAC,IntrRuleAC)]
    auxMatcher s ru0 ru1 = evalFreshAvoiding (appSubst s ru0 ru1) (ru0, ru1)

    auxMatcherFilter = filter nullIntersect
    nullIntersect (i0,i1) = (frees (getPremsFactKD i0) `intersect` frees (getConcFact i1)) /= []

    searchMatcheraux ((s1,h1):sq)  = foldr (\ru -> (|| searchMatcher s1 h1 ru)) False allR && searchMatcheraux sq
    searchMatcheraux [] = True

    searchMatcher :: IntrRuleAC -> IntrRuleAC -> IntrRuleAC -> Bool
    searchMatcher instSigma inst1Sigma inst2init =
      case doMatch (sigmaRHS1 `matchFact` rhs2 <> sigmaF `matchFact` f2) of
        [] -> False
        match -> trace ("\nmatch : " ++ show match) auxDeducible match
      where
        doMatch match = runReader (solveMatchLNTerm match) hnd

        inst2 = inst2init `renameAvoiding` (inst1Sigma, instSigma)

        f2 = getPremsFactKD inst2
        rhs2 = getConcFact inst2

        sigmaRHS1 = getConcFact inst1Sigma
        sigmaF = getPremsFactKD instSigma

        auxDeducible (m1:mq) = checkDeducible m1 && auxDeducible mq
        auxDeducible [] = True

        checkDeducible :: Subst Name LVar -> Bool
        checkDeducible m = aux prems -- trace ("\ndeduce : " ++ show (aux prems))

         where
          terms = getPremsFactTail instSigma ++ getPremsFactTail inst1Sigma
          termsT = foldMap getFactTerms terms
          inst2sigma2 = apply m inst2
          prems = getPremsFactTail inst2sigma2

          intrRmodified = map boundToOne intrR
          boundToOne rule@(Rule (DestrRule name _ subterm constant) premis concs acts nvs) | getRuleName rule == getRuleName r = Rule (DestrRule name 1 subterm constant) premis concs acts nvs
          boundToOne rr = rr

          aux (fa@(Fact KUFact _ [f]):q) = (aux1 f || derivationTest sig intrRmodified fa terms) && aux q
          aux ((Fact KDFact _ _):_) = False
          aux []                    = True
          aux _                     = False

          aux1 f | f `elem` termsT    = True
          aux1 (FAPP (NoEq (_,(_,Private,_))) _) = False
          aux1 (FAPP (AC (ACfct (_,(_,Private,_)))) _) = False
          aux1 (FAPP _ p) = foldr (\x1 -> (&& aux1 x1)) True p
          aux1 _                     = False



checkChainReduction _ _ _ _ _ = False


applyChainReduction :: SignatureWithMaude -> OpenRuleCache -> [[IntrRuleAC]] -> [IntrRuleAC]
applyChainReduction sig intrR (t1:tq) = (if checkChainReductionIter tupleRule then set1ru t1 else t1) ++ applyChainReduction sig intrR tq
  where
    tupleRule = [(x,y) | x <- t1, y <- t1]
    checkChainReductionIter = foldr (\(x,y) -> (&& checkChainReduction sig intrR x y t1)) True

    set1ru = map change

    change (Rule (DestrRule name _ subterm constant) prems concs acts nvs) = Rule (DestrRule name 1 subterm constant) prems concs acts nvs
    change r = r
applyChainReduction _ _ [] = []

-- | Close an intruder rule; i.e., compute maximum number of consecutive applications and variants
--   Should be parallelized like the variant computation for protocol rules (JD)
closeIntrRule :: MaudeHandle -> IntrRuleAC -> [IntrRuleAC]
closeIntrRule hnd (Rule (DestrRule name (-1) subterm constant) prems@((Fact KDFact _ [t]):_) concs@[Fact KDFact _ [rhs]] acts nvs) =
  if subterm then [ru] else variantsIntruder hnd id False ru
    where
      ru = Rule (DestrRule name (if containsOnlyNoEq rhs && containsOnlyNoEq t && runMaude (unifiableLNTerms rhs t)
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

    tabT = groupBy ((==) `on` getRuleName) $ sortOn getRuleName intrRulesAC

    intrRulesACred = applyChainReduction sig intrRulesAC tabT

    -- classifying the rules
    rulesAC = (fmap IntrInfo                      <$> intrRulesACred) <|>
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
