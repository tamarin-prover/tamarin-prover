{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}

module Prover (
    module Prover
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
import           Lemma
import           ClosedTheory
import           TheoryObject
import           OpenTheory

import           Theory.Constraint.Solver.Sources     as Sources (IntegerParameters(..))


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
      proveDiffTheory (const True) checkProof checkDiffProof
        (DiffTheory (L.get diffThyName thy0) h sig (cacheLeft items') (cacheRight items') (diffCacheLeft items') (diffCacheRight items') items' (L.get diffThyOptions thy0))
    else
      proveDiffTheory (const True) checkProof checkDiffProof
        (DiffTheory (L.get diffThyName thy0) h sig (cacheLeft items) (cacheRight items) (diffCacheLeft items) (diffCacheRight items) items (L.get diffThyOptions thy0))

  where
    parameters = Sources.IntegerParameters (L.get (openChainsLimit.diffThyOptions) thy0) (L.get (saturationLimit.diffThyOptions) thy0)
    h              = L.get diffThyHeuristic thy0
    diffCacheLeft  its = closeRuleCache parameters restrictionsLeft  (typAsms its) S.empty sig (leftClosedRules its)  (L.get diffThyDiffCacheLeft  thy0) True
    diffCacheRight its = closeRuleCache parameters restrictionsRight (typAsms its) S.empty sig (rightClosedRules its) (L.get diffThyDiffCacheRight thy0) True
    cacheLeft  its = closeRuleCache parameters restrictionsLeft  (typAsms its) S.empty sig (leftClosedRules its)  (L.get diffThyCacheLeft  thy0) False
    cacheRight its = closeRuleCache parameters restrictionsRight (typAsms its) S.empty sig (rightClosedRules its) (L.get diffThyCacheRight thy0) False

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
    leftClosedRules its = leftTheoryRules  (DiffTheory errClose errClose errClose errClose errClose errClose errClose its errClose)
    rightClosedRules :: [DiffTheoryItem DiffProtoRule ClosedProtoRule IncrementalDiffProof s] -> [ClosedProtoRule]
    rightClosedRules its = rightTheoryRules (DiffTheory errClose errClose errClose errClose errClose errClose errClose its errClose)
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
    parameters = Sources.IntegerParameters (L.get (openChainsLimit.thyOptions) thy0) (L.get (saturationLimit.thyOptions) thy0)
    h          = L.get thyHeuristic thy0
    forcedInjFacts = L.get forcedInjectiveFacts $ L.get thyOptions thy0
    cache its = closeRuleCache parameters restrictions (typAsms its) forcedInjFacts sig (rules its) (L.get thyCache thy0) False
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
       TranslationItem

    unfoldClosedRules :: [TheoryItem [ClosedProtoRule] IncrementalProof s] -> [TheoryItem ClosedProtoRule IncrementalProof s]
    unfoldClosedRules        (RuleItem r:is) = map RuleItem r ++ unfoldClosedRules is
    unfoldClosedRules (RestrictionItem i:is) = RestrictionItem i:unfoldClosedRules is
    unfoldClosedRules       (LemmaItem i:is) = LemmaItem i:unfoldClosedRules is
    unfoldClosedRules        (TextItem i:is) = TextItem i:unfoldClosedRules is
    unfoldClosedRules   (PredicateItem i:is) = PredicateItem i:unfoldClosedRules is
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
proveDiffTheory :: (forall l. (HasLemmaName l, HasLemmaAttributes l) => l -> Bool)       -- ^ Lemma selector.
                   -> Prover
                   -> DiffProver
                   -> ClosedDiffTheory
                   -> ClosedDiffTheory
proveDiffTheory selector prover diffprover thy =
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
      | selector lem = modify lDiffProof add lem
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


-- Partial evaluation / abstract interpretation
-----------------------------------------------

-- | Apply partial evaluation.
applyPartialEvaluation :: EvaluationStyle -> Bool -> ClosedTheory -> ClosedTheory
applyPartialEvaluation evalStyle autosources thy0 =
    closeTheoryWithMaude sig
      (removeTranslationItems (L.modify thyItems replaceProtoRules (openTheory thy0)))
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
          ] ++ map (\x -> EitherRuleItem (LHS, OpenProtoRule x [])) ruEsL' ++ map (\x -> EitherRuleItem (RHS, OpenProtoRule x [])) ruEsR' ++ filter (not . isEitherRuleItem) items
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
openDiffTheory  (DiffTheory n h sig c1 c2 c3 c4 items opts) =
    -- We merge duplicate rules if they were split into variants
    DiffTheory n h (toSignaturePure sig) (openRuleCache c1) (openRuleCache c2) (openRuleCache c3) (openRuleCache c4)
      (mergeOpenProtoRulesDiff $ map (mapDiffTheoryItem id (\(x, y) -> (x, (openProtoRule y))) (\(DiffLemma s a p) -> (DiffLemma s a (incrementalToSkeletonDiffProof p))) (\(x, Lemma a b c d e) -> (x, Lemma a b c d (incrementalToSkeletonProof e)))) items)
      opts

------------------------------------------------------------------------------
-- References to lemmas
------------------------------------------------------------------------------

-- | Lemmas are referenced by their name.
type LemmaRef = String

-- | Resolve a path in a theory.
lookupLemmaProof :: LemmaRef -> ClosedTheory -> Maybe IncrementalProof
lookupLemmaProof name thy = L.get lProof <$> lookupLemma name thy


-- | Resolve a path in a diff theory.
lookupLemmaProofDiff :: Side -> LemmaRef -> ClosedDiffTheory -> Maybe IncrementalProof
lookupLemmaProofDiff s name thy = L.get lProof <$> lookupLemmaDiff s name thy


-- | Resolve a path in a diff theory.
lookupDiffLemmaProof :: LemmaRef -> ClosedDiffTheory -> Maybe IncrementalDiffProof
lookupDiffLemmaProof name thy = L.get lDiffProof <$> lookupDiffLemma name thy


-- | Modify the proof at the given lemma ref, if there is one. Fails if the
-- path is not present or if the prover fails.
modifyLemmaProof :: Prover -> LemmaRef -> ClosedTheory -> Maybe ClosedTheory
modifyLemmaProof prover name thy =
    modA thyItems changeItems thy
  where
    findLemma (LemmaItem lem) = name == L.get lName lem
    findLemma _               = False

    change preItems (LemmaItem lem) = do
         let ctxt = getProofContext lem thy
             sys  = mkSystem ctxt (theoryRestrictions thy) preItems $ L.get lFormula lem
         lem' <- modA lProof (runProver prover ctxt 0 sys) lem
         return $ LemmaItem lem'
    change _ _ = error "LemmaProof: change: impossible"

    changeItems items = case break findLemma items of
        (pre, i:post) -> do
             i' <- change pre i
             return $ pre ++ i':post
        (_, []) -> Nothing


-- | Modify the proof at the given lemma ref, if there is one. Fails if the
-- path is not present or if the prover fails.
modifyLemmaProofDiff :: Side -> Prover -> LemmaRef -> ClosedDiffTheory -> Maybe ClosedDiffTheory
modifyLemmaProofDiff s prover name thy =
    modA diffThyItems (changeItems s) thy
  where
    findLemma s'' (EitherLemmaItem (s''', lem)) = (name == L.get lName lem) && (s''' == s'')
    findLemma _ _                               = False

    change s'' preItems (EitherLemmaItem (s''', lem)) = if s''==s'''
        then
          do
            let ctxt = getProofContextDiff s'' lem thy
                sys  = mkSystemDiff s'' ctxt (diffTheoryRestrictions thy) preItems $ L.get lFormula lem
            lem' <- modA lProof (runProver prover ctxt 0 sys) lem
            return $ EitherLemmaItem (s''', lem')
        else
          error "LemmaProof: change: impossible"
    change _ _ _ = error "LemmaProof: change: impossible"

    changeItems s' items = case break (findLemma s') items of
        (pre, i:post) -> do
             i' <- change s' pre i
             return $ pre ++ i':post
        (_, []) -> Nothing


-- | Modify the proof at the given diff lemma ref, if there is one. Fails if the
-- path is not present or if the prover fails.
modifyDiffLemmaProof :: DiffProver -> LemmaRef -> ClosedDiffTheory -> Maybe ClosedDiffTheory
modifyDiffLemmaProof prover name thy = -- error $ show $ -- name ++ show thy
     modA diffThyItems changeItems thy
  where
    findLemma (DiffLemmaItem lem) = (name == L.get lDiffName lem)
    findLemma  _                  = False

    change preItems (DiffLemmaItem lem) =
          do
            -- I don't get why we need this here, but anyway the empty system does not seem to be a problem.
            let ctxt = getDiffProofContext lem thy
                sys  = mkDiffSystem ctxt (diffTheoryRestrictions thy) preItems
            lem' <- modA lDiffProof (runDiffProver prover ctxt 0 sys) lem
            return $ DiffLemmaItem lem'
    change _ _ = error "DiffLemmaProof: change: impossible"

    changeItems items = case break findLemma items of
        (pre, i:post) -> do
             i' <- change pre i
             return $ pre ++ i':post
        (_, []) -> Nothing
