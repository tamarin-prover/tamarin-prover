{-# LANGUAGE FlexibleContexts #-}


module ClosedTheory (
    module ClosedTheory
) where

import           Prelude                             hiding (id, (.))

import           Data.Maybe
import qualified Data.Set                            as S

import           Control.Basics
import           Control.Category
import           Control.Monad.Reader
import qualified Control.Monad.State                 as MS
import           Control.Parallel.Strategies

import           Extension.Data.Label                hiding (get)
import qualified Extension.Data.Label                as L
-- import qualified Data.Label.Total


import           Theory.Model
import           Theory.Proof
import           Theory.Text.Pretty
import           Theory.Tools.AbstractInterpretation
import           Theory.Tools.LoopBreakers


import Lemmas
import Theories
import Rule
import OpenTheory
import Safe


-- | Closed theories can be proven. Invariants:
--     1. Lemma names are unique
--     2. All proof steps with annotated sequents are sound with respect to the
--        closed rule set of the theory.
--     3. Maude is running under the given handle.
type ClosedTheory =
    Theory SignatureWithMaude ClosedRuleCache ClosedProtoRule IncrementalProof ()

-- | Closed Diff theories can be proven. Invariants:
--     1. Lemma names are unique
--     2. All proof steps with annotated sequents are sound with respect to the
--        closed rule set of the theory.
--     3. Maude is running under the given handle.
type ClosedDiffTheory =
    DiffTheory SignatureWithMaude ClosedRuleCache DiffProtoRule ClosedProtoRule IncrementalDiffProof IncrementalProof

-- | Either Therories can be Either a normal or a diff theory

type EitherClosedTheory = Either ClosedTheory ClosedDiffTheory
------------------------------------------------------------------------------
-- Closed theory querying / construction / modification
------------------------------------------------------------------------------

-- querying
-----------

-- | All lemmas.
getLemmas :: ClosedTheory -> [Lemma IncrementalProof]
getLemmas = theoryLemmas

-- | All diff lemmas.
getDiffLemmas :: ClosedDiffTheory -> [DiffLemma IncrementalDiffProof]
getDiffLemmas = diffTheoryDiffLemmas

-- | All side lemmas.
getEitherLemmas :: ClosedDiffTheory -> [(Side, Lemma IncrementalProof)]
getEitherLemmas = diffTheoryLemmas

-- | The variants of the intruder rules.
getIntrVariants :: ClosedTheory -> [IntrRuleAC]
getIntrVariants = intruderRules . L.get (crcRules . thyCache)

-- | The variants of the intruder rules.
getIntrVariantsDiff :: Side -> ClosedDiffTheory -> [IntrRuleAC]
getIntrVariantsDiff s
  | s == LHS  = intruderRules . L.get (crcRules . diffThyCacheLeft)
  | s == RHS  = intruderRules . L.get (crcRules . diffThyCacheRight)
  | otherwise = error $ "The Side MUST always be LHS or RHS."

-- | All protocol rules modulo E.
getProtoRuleEs :: ClosedTheory -> [ProtoRuleE]
-- we remove duplicates if they exist due to variant unfolding
getProtoRuleEs = S.toList . S.fromList . map ((L.get oprRuleE) . openProtoRule) . theoryRules

-- | All protocol rules modulo E.
getProtoRuleEsDiff :: Side -> ClosedDiffTheory -> [ProtoRuleE]
-- we remove duplicates if they exist due to variant unfolding
getProtoRuleEsDiff s = S.toList . S.fromList . map ((L.get oprRuleE) . openProtoRule) . diffTheorySideRules s

-- | Get the proof context for a lemma of the closed theory.
getProofContext :: Lemma a -> ClosedTheory -> ProofContext
getProofContext l thy = ProofContext
    ( L.get thySignature                       thy)
    ( L.get (crcRules . thyCache)              thy)
    ( L.get (crcInjectiveFactInsts . thyCache) thy)
    kind
    ( L.get (cases . thyCache)                 thy)
    inductionHint
    specifiedHeuristic
    (toSystemTraceQuantifier $ L.get lTraceQuantifier l)
    (L.get lName l)
    ([ h | HideLemma h <- L.get lAttributes l])
    False
    (all isSubtermRule  $ filter isDestrRule $ intruderRules $ L.get (crcRules . thyCache) thy)
    (any isConstantRule $ filter isDestrRule $ intruderRules $ L.get (crcRules . thyCache) thy)
  where
    kind    = lemmaSourceKind l
    cases   = case kind of RawSource     -> crcRawSources
                           RefinedSource -> crcRefinedSources
    inductionHint
      | any (`elem` [SourceLemma, InvariantLemma]) (L.get lAttributes l) = UseInduction
      | otherwise                                                        = AvoidInduction

    -- Heuristic specified for the lemma > globally specified heuristic > default heuristic
    specifiedHeuristic = case lattr of
        Just lh -> Just lh
        Nothing  -> case L.get thyHeuristic thy of
                    [] -> Nothing
                    gh -> Just (Heuristic gh)
      where
        lattr = (headMay [Heuristic gr
                    | LemmaHeuristic gr <- L.get lAttributes l])

-- | Get the proof context for a lemma of the closed theory.
getProofContextDiff :: Side -> Lemma a -> ClosedDiffTheory -> ProofContext
getProofContextDiff s l thy = case s of
  LHS -> ProofContext
            ( L.get diffThySignature                           thy)
            ( L.get (crcRules . diffThyCacheLeft)              thy)
            ( L.get (crcInjectiveFactInsts . diffThyCacheLeft) thy)
            kind
            ( L.get (cases . diffThyCacheLeft)                 thy)
            inductionHint
            specifiedHeuristic
            (toSystemTraceQuantifier $ L.get lTraceQuantifier l)
            (L.get lName l)
            ([ h | HideLemma h <- L.get lAttributes l])
            False
            (all isSubtermRule  $ filter isDestrRule $ intruderRules $ L.get (crcRules . diffThyCacheLeft) thy)
            (any isConstantRule $ filter isDestrRule $ intruderRules $ L.get (crcRules . diffThyCacheLeft) thy)
  RHS -> ProofContext
            ( L.get diffThySignature                    thy)
            ( L.get (crcRules . diffThyCacheRight)           thy)
            ( L.get (crcInjectiveFactInsts . diffThyCacheRight) thy)
            kind
            ( L.get (cases . diffThyCacheRight)              thy)
            inductionHint
            specifiedHeuristic
            (toSystemTraceQuantifier $ L.get lTraceQuantifier l)
            (L.get lName l)
            ([ h | HideLemma h <- L.get lAttributes l])
            False
            (all isSubtermRule  $ filter isDestrRule $ intruderRules $ L.get (crcRules . diffThyCacheRight) thy)
            (any isConstantRule $ filter isDestrRule $ intruderRules $ L.get (crcRules . diffThyCacheRight) thy)
  where
    kind    = lemmaSourceKind l
    cases   = case kind of RawSource     -> crcRawSources
                           RefinedSource -> crcRefinedSources
    inductionHint
      | any (`elem` [SourceLemma, InvariantLemma]) (L.get lAttributes l) = UseInduction
      | otherwise                                                        = AvoidInduction
    -- Heuristic specified for the lemma > globally specified heuristic > default heuristic
    specifiedHeuristic = case lattr of
        Just lh -> Just lh
        Nothing  -> case L.get diffThyHeuristic thy of
                    [] -> Nothing
                    gh -> Just (Heuristic gh)
      where
        lattr = (headMay [Heuristic gr
                    | LemmaHeuristic gr <- L.get lAttributes l])

-- | Get the proof context for a diff lemma of the closed theory.
getDiffProofContext :: DiffLemma a -> ClosedDiffTheory -> DiffProofContext
getDiffProofContext l thy = DiffProofContext (proofContext LHS) (proofContext RHS)
    (map (L.get dprRule) $ diffTheoryDiffRules thy) (L.get (crConstruct . crcRules . diffThyDiffCacheLeft) thy)
    (L.get (crDestruct . crcRules . diffThyDiffCacheLeft) thy)
    ((LHS, restrictionsLeft):[(RHS, restrictionsRight)]) gatherReusableLemmas
  where
    items = L.get diffThyItems thy
    restrictionsLeft  = do EitherRestrictionItem (LHS, rstr) <- items
                           return $ formulaToGuarded_ $ L.get rstrFormula rstr
    restrictionsRight = do EitherRestrictionItem (RHS, rstr) <- items
                           return $ formulaToGuarded_ $ L.get rstrFormula rstr
    gatherReusableLemmas = do
        EitherLemmaItem (s, lem) <- items
        guard $    lemmaSourceKind lem <= RefinedSource
                && ReuseDiffLemma `elem` L.get lAttributes lem
                && AllTraces == L.get lTraceQuantifier lem
        return $ (s, formulaToGuarded_ $ L.get lFormula lem)
    proofContext s   = case s of
        LHS -> ProofContext
            ( L.get diffThySignature                    thy)
            ( L.get (crcRules . diffThyDiffCacheLeft)           thy)
            ( L.get (crcInjectiveFactInsts . diffThyDiffCacheLeft) thy)
            RefinedSource
            ( L.get (crcRefinedSources . diffThyDiffCacheLeft)              thy)
            AvoidInduction
            specifiedHeuristic
            ExistsNoTrace
            ( L.get lDiffName l )
            ([ h | HideLemma h <- L.get lDiffAttributes l])
            True
            (all isSubtermRule  $ filter isDestrRule $ intruderRules $ L.get (crcRules . diffThyCacheLeft) thy)
            (any isConstantRule $ filter isDestrRule $ intruderRules $ L.get (crcRules . diffThyCacheLeft) thy)
        RHS -> ProofContext
            ( L.get diffThySignature                    thy)
            ( L.get (crcRules . diffThyDiffCacheRight)           thy)
            ( L.get (crcInjectiveFactInsts . diffThyDiffCacheRight) thy)
            RefinedSource
            ( L.get (crcRefinedSources . diffThyDiffCacheRight)              thy)
            AvoidInduction
            specifiedHeuristic
            ExistsNoTrace
            ( L.get lDiffName l )
            ([ h | HideLemma h <- L.get lDiffAttributes l])
            True
            (all isSubtermRule  $ filter isDestrRule $ intruderRules $ L.get (crcRules . diffThyCacheRight) thy)
            (any isConstantRule $ filter isDestrRule $ intruderRules $ L.get (crcRules . diffThyCacheRight) thy)

    specifiedHeuristic = case lattr of
        Just lh -> Just lh
        Nothing  -> case L.get diffThyHeuristic thy of
                    [] -> Nothing
                    gh -> Just (Heuristic gh)
      where
        lattr = (headMay [Heuristic gr
                    | LemmaHeuristic gr <- L.get lDiffAttributes l])

-- | The facts with injective instances in this theory
getInjectiveFactInsts :: ClosedTheory -> S.Set FactTag
getInjectiveFactInsts = L.get (crcInjectiveFactInsts . thyCache)

-- | The facts with injective instances in this theory
getDiffInjectiveFactInsts :: Side -> Bool -> ClosedDiffTheory -> S.Set FactTag
getDiffInjectiveFactInsts s isdiff = case (s, isdiff) of
           (LHS, False) -> L.get (crcInjectiveFactInsts . diffThyCacheLeft)
           (RHS, False) -> L.get (crcInjectiveFactInsts . diffThyCacheRight)
           (LHS, True)  -> L.get (crcInjectiveFactInsts . diffThyDiffCacheLeft)
           (RHS, True)  -> L.get (crcInjectiveFactInsts . diffThyDiffCacheRight)

-- | The classified set of rules modulo AC in this theory.
getClassifiedRules :: ClosedTheory -> ClassifiedRules
getClassifiedRules = L.get (crcRules . thyCache)

-- | The classified set of rules modulo AC in this theory.
getDiffClassifiedRules :: Side -> Bool -> ClosedDiffTheory -> ClassifiedRules
getDiffClassifiedRules s isdiff = case (s, isdiff) of
           (LHS, False) -> L.get (crcRules . diffThyCacheLeft)
           (RHS, False) -> L.get (crcRules . diffThyCacheRight)
           (LHS, True)  -> L.get (crcRules . diffThyDiffCacheLeft)
           (RHS, True)  -> L.get (crcRules . diffThyDiffCacheRight)

-- | The precomputed case distinctions.
getSource :: SourceKind -> ClosedTheory -> [Source]
getSource RawSource     = L.get (crcRawSources . thyCache)
getSource RefinedSource = L.get (crcRefinedSources .   thyCache)

-- | The precomputed case distinctions.
getDiffSource :: Side -> Bool -> SourceKind -> ClosedDiffTheory -> [Source]
getDiffSource LHS False RawSource     = L.get (crcRawSources .     diffThyCacheLeft)
getDiffSource RHS False RawSource     = L.get (crcRawSources .     diffThyCacheRight)
getDiffSource LHS False RefinedSource = L.get (crcRefinedSources . diffThyCacheLeft)
getDiffSource RHS False RefinedSource = L.get (crcRefinedSources . diffThyCacheRight)
getDiffSource LHS True  RawSource     = L.get (crcRawSources .     diffThyDiffCacheLeft)
getDiffSource RHS True  RawSource     = L.get (crcRawSources .     diffThyDiffCacheRight)
getDiffSource LHS True  RefinedSource = L.get (crcRefinedSources . diffThyDiffCacheLeft)
getDiffSource RHS True  RefinedSource = L.get (crcRefinedSources . diffThyDiffCacheRight)

-- construction
---------------

-- | Close a protocol rule; i.e., compute AC variant and source assertion
-- soundness sequent, if required.
closeEitherProtoRule :: MaudeHandle -> (Side, OpenProtoRule) -> (Side, [ClosedProtoRule])
closeEitherProtoRule hnd (s, ruE) = (s, closeProtoRule hnd ruE)

-- -- | Convert a lemma to the corresponding guarded formula.
-- lemmaToGuarded :: Lemma p -> Maybe LNGuarded
-- lemmaToGuarded lem =

-- | Close a theory by closing its associated rule set and checking the proof
-- skeletons and caching AC variants as well as precomputed case distinctions.
--
-- This function initializes the relation to the Maude process with the
-- correct signature. This is the right place to do that because in a closed
-- theory the signature may not change any longer.
closeTheory :: FilePath         -- ^ Path to the Maude executable.
            -> OpenTranslatedTheory
            -> Bool             -- ^ Try to auto-generate sources lemmas
            -> IO ClosedTheory
closeTheory maudePath thy0 autosources = do
    sig <- toSignatureWithMaude maudePath $ L.get thySignature thy0
    return $ closeTheoryWithMaude sig thy0 autosources

-- | Close a theory by closing its associated rule set and checking the proof
-- skeletons and caching AC variants as well as precomputed case distinctions.
--
-- This function initializes the relation to the Maude process with the
-- correct signature. This is the right place to do that because in a closed
-- theory the signature may not change any longer.
closeDiffTheory :: FilePath         -- ^ Path to the Maude executable.
            -> OpenDiffTheory
            -> Bool
            -> IO ClosedDiffTheory
closeDiffTheory maudePath thy0 autoSources = do
    sig <- toSignatureWithMaude maudePath $ L.get diffThySignature thy0
    return $ closeDiffTheoryWithMaude sig thy0 autoSources

-- | Close a diff theory given a maude signature. This signature must be valid for
-- the given theory.
closeDiffTheoryWithMaude :: SignatureWithMaude -> OpenDiffTheory -> Bool -> ClosedDiffTheory
closeDiffTheoryWithMaude sig thy0 autoSources =
  if autoSources && (containsPartialDeconstructions (cacheLeft items) || containsPartialDeconstructions (cacheRight items))
    then
      proveDiffTheory (const True) (const True) checkProof checkDiffProof
        (DiffTheory (L.get diffThyName thy0) h sig (cacheLeft items') (cacheRight items') (diffCacheLeft items') (diffCacheRight items') items')
    else
      proveDiffTheory (const True) (const True) checkProof checkDiffProof
        (DiffTheory (L.get diffThyName thy0) h sig (cacheLeft items) (cacheRight items) (diffCacheLeft items) (diffCacheRight items) items)
  where
    h              = L.get diffThyHeuristic thy0
    diffCacheLeft  its = closeRuleCache restrictionsLeft  (typAsms its) sig (leftClosedRules its)  (L.get diffThyDiffCacheLeft  thy0) True
    diffCacheRight its = closeRuleCache restrictionsRight (typAsms its) sig (rightClosedRules its) (L.get diffThyDiffCacheRight thy0) True
    cacheLeft  its = closeRuleCache restrictionsLeft  (typAsms its) sig (leftClosedRules its)  (L.get diffThyCacheLeft  thy0) False
    cacheRight its = closeRuleCache restrictionsRight (typAsms its) sig (rightClosedRules its) (L.get diffThyCacheRight thy0) False

    checkProof = checkAndExtendProver (sorryProver Nothing)
    checkDiffProof = checkAndExtendDiffProver (sorryDiffProver Nothing)
    diffRules  = diffTheoryDiffRules thy0
    leftOpenRules  = map (addProtoRuleLabel . getLeftProtoRule)  diffRules
    rightOpenRules = map (addProtoRuleLabel . getRightProtoRule) diffRules

    -- Maude / Signature handle
    hnd = L.get sigmMaudeHandle sig

    theoryItems = L.get diffThyItems thy0 ++ map (\x -> EitherRuleItem (LHS, x)) leftOpenRules ++ map (\x -> EitherRuleItem (RHS, x)) rightOpenRules
    -- Close all theory items: in parallel (especially useful for variants)
    --
    -- NOTE that 'rdeepseq' is OK here, as the proof has not yet been checked
    -- and therefore no constraint systems will be unnecessarily cached.
    (items, _solveRel, _breakers) = (`runReader` hnd) $ addSolvingLoopBreakers $ unfoldClosedRules
       ((closeDiffTheoryItem <$> theoryItems) `using` parList rdeepseq)

    closeDiffTheoryItem :: DiffTheoryItem DiffProtoRule OpenProtoRule DiffProofSkeleton ProofSkeleton -> DiffTheoryItem DiffProtoRule [ClosedProtoRule] IncrementalDiffProof IncrementalProof
    closeDiffTheoryItem = foldDiffTheoryItem
      DiffRuleItem
      (EitherRuleItem . closeEitherProtoRule hnd)
      (DiffLemmaItem . fmap skeletonToIncrementalDiffProof)
      (\(s, l) -> EitherLemmaItem (s, fmap skeletonToIncrementalProof l))
      EitherRestrictionItem
      DiffTextItem

    unfoldClosedRules :: [DiffTheoryItem DiffProtoRule [ClosedProtoRule] IncrementalDiffProof IncrementalProof] -> [DiffTheoryItem DiffProtoRule ClosedProtoRule IncrementalDiffProof IncrementalProof]
    unfoldClosedRules    (EitherRuleItem (s,r):is) = map (\x -> EitherRuleItem (s,x)) r ++ unfoldClosedRules is
    unfoldClosedRules          (DiffRuleItem i:is) = DiffRuleItem i:unfoldClosedRules is
    unfoldClosedRules         (DiffLemmaItem i:is) = DiffLemmaItem i:unfoldClosedRules is
    unfoldClosedRules       (EitherLemmaItem i:is) = EitherLemmaItem i:unfoldClosedRules is
    unfoldClosedRules (EitherRestrictionItem i:is) = EitherRestrictionItem i:unfoldClosedRules is
    unfoldClosedRules          (DiffTextItem i:is) = DiffTextItem i:unfoldClosedRules is
    unfoldClosedRules                           [] = []

    -- Name of the auto-generated lemma
    lemmaName = "AUTO_typing"

    itemsModAC = unfoldRules items

    unfoldRules (EitherRuleItem (s,r):is) = map (\x -> EitherRuleItem (s,x)) (unfoldRuleVariants r) ++ unfoldRules is
    unfoldRules                    (i:is) = i:unfoldRules is
    unfoldRules                        [] = []

    items' = addAutoSourcesLemmaDiff hnd lemmaName (cacheLeft itemsModAC) (cacheRight itemsModAC) itemsModAC

    -- extract source restrictions and lemmas
    restrictionsLeft  = do EitherRestrictionItem (LHS, rstr) <- items
                           return $ formulaToGuarded_ $ L.get rstrFormula rstr
    restrictionsRight = do EitherRestrictionItem (RHS, rstr) <- items
                           return $ formulaToGuarded_ $ L.get rstrFormula rstr
    typAsms its = do EitherLemmaItem (_, lem) <- its
                     guard (isSourceLemma lem)
                     return $ formulaToGuarded_ $ L.get lFormula lem

    -- extract protocol rules
    leftClosedRules  :: [DiffTheoryItem DiffProtoRule ClosedProtoRule IncrementalDiffProof s] -> [ClosedProtoRule]
    leftClosedRules its = leftTheoryRules  (DiffTheory errClose errClose errClose errClose errClose errClose errClose its)
    rightClosedRules :: [DiffTheoryItem DiffProtoRule ClosedProtoRule IncrementalDiffProof s] -> [ClosedProtoRule]
    rightClosedRules its = rightTheoryRules (DiffTheory errClose errClose errClose errClose errClose errClose errClose its)
    errClose  = error "closeDiffTheory"

    addSolvingLoopBreakers = useAutoLoopBreakersAC
        (liftToItem $ enumPrems . L.get cprRuleAC)
        (liftToItem $ enumConcs . L.get cprRuleAC)
        (liftToItem $ getDisj . L.get (pracVariants . rInfo . cprRuleAC))
        addBreakers
      where
        liftToItem f (EitherRuleItem (_, ru)) = f ru
        liftToItem _ _                        = []

        addBreakers bs (EitherRuleItem (s, ru)) =
            EitherRuleItem (s, L.set (pracLoopBreakers . rInfo . cprRuleAC) bs ru)
        addBreakers _  item              = item



-- | Close a theory given a maude signature. This signature must be valid for
-- the given theory.
closeTheoryWithMaude :: SignatureWithMaude -> OpenTranslatedTheory -> Bool -> ClosedTheory
closeTheoryWithMaude sig thy0 autoSources =
  if autoSources && containsPartialDeconstructions (cache items)
    then
        proveTheory (const True) checkProof
      $ Theory (L.get thyName thy0) h sig (cache items') items' (L.get thyOptions thy0)
    else
        proveTheory (const True) checkProof
      $ Theory (L.get thyName thy0) h sig (cache items) items (L.get thyOptions thy0)
  where
    h          = L.get thyHeuristic thy0
    cache its  = closeRuleCache restrictions (typAsms its) sig (rules its) (L.get thyCache thy0) False
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
       (RuleItem . closeProtoRule hnd)
       RestrictionItem
       (LemmaItem . fmap skeletonToIncrementalProof)
       TextItem
       PredicateItem
       SapicItem

    unfoldClosedRules :: [TheoryItem [ClosedProtoRule] IncrementalProof s] -> [TheoryItem ClosedProtoRule IncrementalProof s]
    unfoldClosedRules        (RuleItem r:is) = map RuleItem r ++ unfoldClosedRules is
    unfoldClosedRules (RestrictionItem i:is) = RestrictionItem i:unfoldClosedRules is
    unfoldClosedRules       (LemmaItem i:is) = LemmaItem i:unfoldClosedRules is
    unfoldClosedRules        (TextItem i:is) = TextItem i:unfoldClosedRules is
    unfoldClosedRules   (PredicateItem i:is) = PredicateItem i:unfoldClosedRules is
    unfoldClosedRules       (SapicItem i:is) = SapicItem i:unfoldClosedRules is
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
    rules its = theoryRules (Theory errClose errClose errClose errClose its errClose)
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






-- Partial evaluation / abstract interpretation
-----------------------------------------------

-- | Apply partial evaluation.
applyPartialEvaluation :: EvaluationStyle -> Bool -> ClosedTheory -> ClosedTheory
applyPartialEvaluation evalStyle autosources thy0 =
    closeTheoryWithMaude sig
      (removeSapicItems (L.modify thyItems replaceProtoRules (openTheory thy0)))
      autosources
  where
    sig          = L.get thySignature thy0
    ruEs         = getProtoRuleEs thy0
    (st', ruEs') = (`runReader` L.get sigmMaudeHandle sig) $
                   partialEvaluation evalStyle ruEs

    replaceProtoRules [] = []
    replaceProtoRules (item:items)
      | isRuleItem item  =
          [ TextItem ("text", render ppAbsState)
       -- Here we loose imported variants!
          ] ++ map (\x -> RuleItem (OpenProtoRule x [])) ruEs' ++ filter (not . isRuleItem) items
      | otherwise        = item : replaceProtoRules items

    ppAbsState =
      (text $ " the abstract state after partial evaluation"
              ++ " contains " ++ show (S.size st') ++ " facts:") $--$
      (numbered' $ map prettyLNFact $ S.toList st') $--$
      (text $ "This abstract state results in " ++ show (length ruEs') ++
              " refined multiset rewriting rules.\n" ++
              "Note that the original number of multiset rewriting rules was "
              ++ show (length ruEs) ++ ".\n\n")

-- | Apply partial evaluation.
applyPartialEvaluationDiff :: EvaluationStyle -> Bool -> ClosedDiffTheory -> ClosedDiffTheory
applyPartialEvaluationDiff evalStyle autoSources thy0 =
    closeDiffTheoryWithMaude sig
      (L.modify diffThyItems replaceProtoRules (openDiffTheory thy0)) autoSources
  where
    sig            = L.get diffThySignature thy0
    ruEs s         = getProtoRuleEsDiff s thy0
    (stL', ruEsL') = (`runReader` L.get sigmMaudeHandle sig) $
                     partialEvaluation evalStyle (ruEs LHS)
    (stR', ruEsR') = (`runReader` L.get sigmMaudeHandle sig) $
                     partialEvaluation evalStyle (ruEs RHS)

    replaceProtoRules [] = []
    replaceProtoRules (item:items)
      | isEitherRuleItem item  =
          [ DiffTextItem ("text", render ppAbsState)
       -- Here we loose imported variants!
          ] ++ map (\x -> EitherRuleItem (LHS, (OpenProtoRule x []))) ruEsL' ++ map (\x -> EitherRuleItem (RHS, (OpenProtoRule x []))) ruEsR' ++ filter (not . isEitherRuleItem) items
      | otherwise        = item : replaceProtoRules items

    isEitherRuleItem (EitherRuleItem _) = True
    isEitherRuleItem _                  = False

    ppAbsState =
      (text $ " the abstract state after partial evaluation"
              ++ " contains " ++ show (S.size stL') ++ " left facts:") $--$
      (numbered' $ map prettyLNFact $ S.toList stL') $--$
      (text $ "This abstract state results in " ++ show (length ruEsL') ++
              " left refined multiset rewriting rules.\n" ++
              "Note that the original number of multiset rewriting rules was "
              ++ show (length (ruEs LHS)) ++ ".\n\n") $--$
      (text $ " the abstract state after partial evaluation"
              ++ " contains " ++ show (S.size stR') ++ " right facts:") $--$
      (numbered' $ map prettyLNFact $ S.toList stR') $--$
      (text $ "This abstract state results in " ++ show (length ruEsR') ++
              " right refined multiset rewriting rules.\n" ++
              "Note that the original number of multiset rewriting rules was "
              ++ show (length (ruEs RHS)) ++ ".\n\n")


-- | Open a theory by dropping the closed world assumption and values whose
-- soundness depends on it.
openTheory :: ClosedTheory -> OpenTheory
openTheory  (Theory n h sig c items opts) = openTranslatedTheory(
    Theory n h (toSignaturePure sig) (openRuleCache c)
    -- We merge duplicate rules if they were split into variants
      (mergeOpenProtoRules $ map (mapTheoryItem openProtoRule incrementalToSkeletonProof) items)
      opts)

-- | Open a theory by dropping the closed world assumption and values whose
-- soundness depends on it.
openDiffTheory :: ClosedDiffTheory -> OpenDiffTheory
openDiffTheory  (DiffTheory n h sig c1 c2 c3 c4 items) =
    -- We merge duplicate rules if they were split into variants
    DiffTheory n h (toSignaturePure sig) (openRuleCache c1) (openRuleCache c2) (openRuleCache c3) (openRuleCache c4)
      (mergeOpenProtoRulesDiff $ map (mapDiffTheoryItem id (\(x, y) -> (x, (openProtoRule y))) (\(DiffLemma s a p) -> (DiffLemma s a (incrementalToSkeletonDiffProof p))) (\(x, Lemma a b c d e) -> (x, Lemma a b c d (incrementalToSkeletonProof e)))) items)





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

-- | Prove both the assertion soundness as well as all lemmas of the theory. If
-- the prover fails on a lemma, then its proof remains unchanged.
proveDiffTheory :: (Lemma IncrementalProof -> Bool)       -- ^ Lemma selector.
            -> (DiffLemma IncrementalDiffProof -> Bool)   -- ^ DiffLemma selector.
            -> Prover
            -> DiffProver
            -> ClosedDiffTheory
            -> ClosedDiffTheory
proveDiffTheory selector diffselector prover diffprover thy =
    modify diffThyItems ((`MS.evalState` []) . mapM prove) thy
  where
    prove item = case item of
      EitherLemmaItem (s, l0) -> do l <- MS.gets (\x -> EitherLemmaItem (s, (proveLemma s l0 x)))
                                    MS.modify (l :)
                                    return l
      DiffLemmaItem l0        -> do l' <- MS.gets (\x -> DiffLemmaItem (proveDiffLemma l0 x))
                                    MS.modify (l' :)
                                    return l'
      _                       -> do return item

    proveLemma s lem preItems
      | selector lem = modify lProof add lem
      | otherwise    = lem
      where
        ctxt    = getProofContextDiff s lem thy
        sys     = mkSystemDiff s ctxt (diffTheoryRestrictions thy) preItems $ L.get lFormula lem
        add prf = fromMaybe prf $ runProver prover ctxt 0 sys prf

    proveDiffLemma lem preItems
      | diffselector lem = modify lDiffProof add lem
      | otherwise        = lem
      where
        ctxt    = getDiffProofContext lem thy
        sys     = mkDiffSystem ctxt (diffTheoryRestrictions thy) preItems
        add prf = fromMaybe prf $ runDiffProver diffprover ctxt 0 sys prf

-- | Construct a constraint system for verifying the given formula.
mkSystem :: ProofContext -> [Restriction] -> [TheoryItem r p s]
         -> LNFormula -> System
mkSystem ctxt restrictions previousItems =
    -- Note that it is OK to add reusable lemmas directly to the system, as
    -- they do not change the considered set of traces. This is the key
    -- difference between lemmas and restrictions.
    addLemmas
  . formulaToSystem (map (formulaToGuarded_ . L.get rstrFormula) restrictions)
                    (L.get pcSourceKind ctxt)
                    (L.get pcTraceQuantifier ctxt) False
  where
    addLemmas sys =
        insertLemmas (gatherReusableLemmas $ L.get sSourceKind sys) sys

    gatherReusableLemmas kind = do
        LemmaItem lem <- previousItems
        guard $    lemmaSourceKind lem <= kind
                && ReuseLemma `elem` L.get lAttributes lem
                && AllTraces == L.get lTraceQuantifier lem
                && (L.get lName lem) `notElem` (L.get pcHiddenLemmas ctxt)
                && "ALL" `notElem` (L.get pcHiddenLemmas ctxt)
        return $ formulaToGuarded_ $ L.get lFormula lem

-- | Construct a constraint system for verifying the given formula.
mkSystemDiff :: Side -> ProofContext -> [(Side, Restriction)] -> [DiffTheoryItem r r2 p p2]
         -> LNFormula -> System
mkSystemDiff s ctxt restrictions previousItems =
    -- Note that it is OK to add reusable lemmas directly to the system, as
    -- they do not change the considered set of traces. This is the key
    -- difference between lemmas and restrictions.
    addLemmas
  . formulaToSystem (map (formulaToGuarded_ . L.get rstrFormula) restrictions')
                    (L.get pcSourceKind ctxt)
                    (L.get pcTraceQuantifier ctxt) False
  where
    restrictions' = foldr (\(s', a) l -> if s == s' then l ++ [a] else l) [] restrictions
    addLemmas sys =
        insertLemmas (gatherReusableLemmas $ L.get sSourceKind sys) sys

    gatherReusableLemmas kind = do
        EitherLemmaItem (s'', lem) <- previousItems
        guard $    lemmaSourceKind lem <= kind && s==s''
                && ReuseLemma `elem` L.get lAttributes lem
                && AllTraces == L.get lTraceQuantifier lem
        return $ formulaToGuarded_ $ L.get lFormula lem

-- | Construct a diff constraint system.
mkDiffSystem :: DiffProofContext -> [(Side, Restriction)] -> [DiffTheoryItem r r2 p p2]
        -> DiffSystem
mkDiffSystem _ _ _ = emptyDiffSystem
