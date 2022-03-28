{-# LANGUAGE FlexibleContexts #-}


module ClosedTheory (
    module ClosedTheory
) where

import           Prelude                             hiding (id, (.))

import qualified Data.Set                            as S

import           Control.Basics
import           Control.Category

import qualified Extension.Data.Label                as L
-- import qualified Data.Label.Total


import           Theory.Model
import           Theory.Proof


import Lemma
import TheoryObject
import Rule
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
