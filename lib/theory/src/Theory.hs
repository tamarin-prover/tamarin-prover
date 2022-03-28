{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- FIXME: for functions prove
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE PatternGuards        #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>, Alexander Dax <alexander@dax.saarland>
-- Portability : GHC only
--
-- Theory datatype and transformations on it.
module Theory (
  -- * Formulas
    expandFormula

  -- * Restrictions
  , expandRestriction


  -- * Processes
  , ProcessDef(..)
  , SapicElement(..)
  -- Datastructure added to Theory Items
  , addProcess
  , findProcess
  , addProcessDef
  , lookupProcessDef
  , pName
  , pBody

  -- * Options
  , transAllowPatternMatchinginLookup
  , transProgress
  , transReliable
  , transReport
  , thyOptions
  , setOption

  -- * Predicates
  , Predicate(..)
  , pFact
  , addPredicate

  -- * Lemmas
  , LemmaAttribute(..)
  , TraceQuantifier(..)
  , Lemma
  , SyntacticLemma
  , ProtoLemma(..)
  , lName
  , DiffLemma
  , lDiffName
  , lDiffAttributes
  , lDiffProof
  , lTraceQuantifier
  , lFormula
  , lAttributes
  , lProof
  , unprovenLemma
  , skeletonLemma
  , skeletonDiffLemma
  , isLeftLemma
  , isRightLemma
--   , isBothLemma
  , addLeftLemma
  , addRightLemma
  , expandLemma

  -- * Theories
  , Theory(..)
  , DiffTheory(..)
  , TheoryItem(..)
  , DiffTheoryItem(..)
  , thyName
  , thySignature
  , thyCache
  , thyItems
  , diffThyName
  , diffThySignature
  , diffThyCacheLeft
  , diffThyCacheRight
  , diffThyDiffCacheLeft
  , diffThyDiffCacheRight
  , diffThyItems
  , diffTheoryLemmas
  , diffTheorySideLemmas
  , diffTheoryDiffRules
  , diffTheoryDiffLemmas
  , theoryRules
  , theoryLemmas
  , theoryRestrictions
  , theoryProcesses
  , diffTheoryRestrictions
  , diffTheorySideRestrictions
  , addRestriction
  , addLemma
  , addRestrictionDiff
  , addLemmaDiff
  , addDiffLemma
  , addHeuristic
  , addDiffHeuristic
  , removeLemma
  , removeLemmaDiff
  , removeDiffLemma
  , lookupLemma
  , lookupDiffLemma
  , lookupLemmaDiff
  , addComment
  , addDiffComment
  , addStringComment
  , addFormalComment
  , addFormalCommentDiff
  , filterSide
  , addDefaultDiffLemma
  , addProtoRuleLabel
  , addIntrRuleLabels

  -- ** Open theories
  , OpenTheory
  , OpenTheoryItem
  , OpenTranslatedTheory
  , OpenDiffTheory
  , removeSapicItems
--  , EitherTheory
  , EitherOpenTheory
  , EitherClosedTheory
  , defaultOpenTheory
  , defaultOpenDiffTheory
  , addProtoRule
  , addProtoDiffRule
  , addOpenProtoRule
  , addOpenProtoDiffRule
  , applyPartialEvaluation
  , applyPartialEvaluationDiff
  , addIntrRuleACsAfterTranslate
  , addIntrRuleACs
  , addIntrRuleACsDiffBoth
  , addIntrRuleACsDiffBothDiff
  , addIntrRuleACsDiffAll
  , normalizeTheory

  -- ** Closed theories
  , ClosedTheory
  , ClosedDiffTheory
  , ClosedRuleCache(..) -- FIXME: this is only exported for the Binary instances
  , closeTheory
  , closeTheoryWithMaude
  , closeDiffTheory
  , closeDiffTheoryWithMaude
  , openTheory
  , openTranslatedTheory
  , openDiffTheory

  , ClosedProtoRule(..)
  , OpenProtoRule(..)
  , oprRuleE
  , oprRuleAC
  , cprRuleE
  , cprRuleAC
  , DiffProtoRule(..)
  , dprRule
  , dprLeftRight
  , unfoldRuleVariants

  , getLemmas
  , getEitherLemmas
  , getDiffLemmas
  , getIntrVariants
  , getIntrVariantsDiff
  , getProtoRuleEs
  , getProtoRuleEsDiff
  , getProofContext
  , getProofContextDiff
  , getDiffProofContext
  , getClassifiedRules
  , getDiffClassifiedRules
  , getInjectiveFactInsts
  , getDiffInjectiveFactInsts

  , getSource
  , getDiffSource

  -- ** Proving
  , ProofSkeleton
  , DiffProofSkeleton
  , proveTheory
  , proveDiffTheory

  -- ** Lemma references
  , lookupLemmaProof
  , modifyLemmaProof
  , lookupLemmaProofDiff
  , modifyLemmaProofDiff
  , lookupDiffLemmaProof
  , modifyDiffLemmaProof

  -- * Pretty printing
  , prettyTheory
  , prettyFormalComment
  , prettyLemmaName
  , prettyRestriction
  , prettyLemma
  , prettyDiffLemmaName
  , prettyClosedTheory
  , prettyClosedDiffTheory
  , prettyOpenTheory
  , prettyOpenTranslatedTheory
  , prettyOpenDiffTheory

  , prettyOpenProtoRule
  , prettyDiffRule

  , prettyClosedSummary
  , prettyClosedDiffSummary

  , prettyIntruderVariants
  , prettyTraceQuantifier

  , prettyProcess
  , prettyProcessDef
  , module Theories

  -- * Convenience exports
  , module Theory.Model
  , module Theory.Proof

  ) where

-- import           Debug.Trace

import           Prelude                             hiding (id, (.))

import           GHC.Generics                        (Generic)

-- import           Data.Typeable
import           Data.Binary
import           Data.List
import           Data.Maybe
import           Data.Either
import           Data.Monoid                         (Sum(..))
import qualified Data.Set                            as S

import           Control.Basics
import           Control.Category
import           Control.DeepSeq
import           Control.Monad.Reader
import qualified Control.Monad.State                 as MS
import           Control.Parallel.Strategies

import           Extension.Data.Label                hiding (get)
import qualified Extension.Data.Label                as L
import qualified Data.Label.Point
import qualified Data.Label.Poly
-- import qualified Data.Label.Total

import           Safe                                (headMay, atMay)

import           Theory.Model
import           Theory.Sapic
import           Theory.Sapic.Print
import           Theory.Proof
import           Theory.Text.Pretty
import           Theory.Tools.AbstractInterpretation
import           Theory.Tools.InjectiveFactInstances
import           Theory.Tools.LoopBreakers
import           Theory.Tools.RuleVariants
import           Theory.Tools.IntruderRules

import           Term.Positions

import           Utils.Misc

import           Theories

------------------------------------------------------------------------------
-- Specific proof types
------------------------------------------------------------------------------

-- | Proof skeletons are used to represent proofs in open theories.
type ProofSkeleton    = Proof ()

-- | Convert a proof skeleton to an incremental proof without any sequent
-- annotations.
skeletonToIncrementalProof :: ProofSkeleton -> IncrementalProof
skeletonToIncrementalProof = fmap (fmap (const Nothing))

-- | Convert an incremental proof to a proof skeleton by dropping all
-- annotations.
incrementalToSkeletonProof :: IncrementalProof -> ProofSkeleton
incrementalToSkeletonProof = fmap (fmap (const ()))

-- | Proof skeletons are used to represent proofs in open theories.
type DiffProofSkeleton    = DiffProof ()

-- | Convert a proof skeleton to an incremental proof without any sequent
-- annotations.
skeletonToIncrementalDiffProof :: DiffProofSkeleton -> IncrementalDiffProof
skeletonToIncrementalDiffProof = fmap (fmap (const Nothing))

-- | Convert an incremental proof to a proof skeleton by dropping all
-- annotations.
incrementalToSkeletonDiffProof :: IncrementalDiffProof -> DiffProofSkeleton
incrementalToSkeletonDiffProof = fmap (fmap (const ()))

------------------------------------------------------------------------------
-- Commented sets of rewriting rules
------------------------------------------------------------------------------

-- | A protocol rewriting rule modulo E together with its possible assertion
-- soundness proof.
-- Optionally, the variant(s) modulo AC can be present if they were loaded
-- or contain additional actions.
data OpenProtoRule = OpenProtoRule
       { _oprRuleE  :: ProtoRuleE             -- original rule modulo E
       , _oprRuleAC :: [ProtoRuleAC]          -- variant(s) modulo AC
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A diff protocol rewriting rule modulo E
-- Optionally, the left and right rules can be present if they were loaded
-- or contain additional actions.
data DiffProtoRule = DiffProtoRule
       { _dprRule       :: ProtoRuleE         -- original rule with diff
       , _dprLeftRight  :: Maybe (OpenProtoRule, OpenProtoRule)
                                              -- left and right instances
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A closed proto rule lists its original rule modulo E, the corresponding
-- variant(s) modulo AC, and if required the assertion soundness proof.
-- When using auto-sources, all non-trivial variants of a ClosedProtoRule are
-- split up into multiple ClosedProtoRules. Auto-sources also only adds
-- actions only to closed rules. Opening such rules keeps the AC rules s.t.
-- they can be exported.
data ClosedProtoRule = ClosedProtoRule
       { _cprRuleE         :: ProtoRuleE      -- original rule modulo E
       , _cprRuleAC        :: ProtoRuleAC     -- variant(s) modulo AC
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

type OpenRuleCache = [IntrRuleAC]

data ClosedRuleCache = ClosedRuleCache
       { _crcRules               :: ClassifiedRules
       , _crcRawSources          :: [Source]
       , _crcRefinedSources      :: [Source]
       , _crcInjectiveFactInsts  :: S.Set FactTag
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

$(mkLabels [''OpenProtoRule, ''DiffProtoRule, ''ClosedProtoRule, ''ClosedRuleCache])

instance HasRuleName OpenProtoRule where
    ruleName = ruleName . L.get oprRuleE

instance HasRuleName DiffProtoRule where
    ruleName = ruleName . L.get dprRule

instance HasRuleName ClosedProtoRule where
    ruleName = ruleName . L.get cprRuleAC

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
closeProtoRule :: MaudeHandle -> OpenProtoRule -> [ClosedProtoRule]
closeProtoRule hnd (OpenProtoRule ruE [])   = [ClosedProtoRule ruE (variantsProtoRule hnd ruE)]
closeProtoRule _   (OpenProtoRule ruE ruAC) = map (ClosedProtoRule ruE) ruAC

-- | Close an intruder rule; i.e., compute maximum number of consecutive applications and variants
--   Should be parallelized like the variant computation for protocol rules (JD)
closeIntrRule :: MaudeHandle -> IntrRuleAC -> [IntrRuleAC]
closeIntrRule hnd (Rule (DestrRule name (-1) subterm constant) prems@((Fact KDFact _ [t]):_) concs@[Fact KDFact _ [rhs]] acts nvs) =
  if subterm then [ru] else variantsIntruder hnd id False ru
    where
      ru = (Rule (DestrRule name (if runMaude (unifiableLNTerms rhs t)
                              then (length (positions t)) - (if (isPrivateFunction t) then 1 else 2)
                              -- We do not need to count t itself, hence - 1.
                              -- If t is a private function symbol we need to permit one more rule
                              -- application as there is no associated constructor.
                              else 0) subterm constant) prems concs acts nvs)
        where
           runMaude = (`runReader` hnd)
closeIntrRule hnd ir@(Rule (DestrRule _ _ False _) _ _ _ _) = variantsIntruder hnd id False ir
closeIntrRule _   ir                                        = [ir]


-- | Close a rule cache. Hower, note that the
-- requires case distinctions are not computed here.
closeRuleCache :: [LNGuarded]        -- ^ Restrictions to use.
               -> [LNGuarded]        -- ^ Source lemmas to use.
               -> SignatureWithMaude -- ^ Signature of theory.
               -> [ClosedProtoRule]  -- ^ Protocol rules with variants.
               -> OpenRuleCache      -- ^ Intruder rules modulo AC.
               -> Bool               -- ^ Diff or not
               -> ClosedRuleCache    -- ^ Cached rules and case distinctions.
closeRuleCache restrictions typAsms sig protoRules intrRules isdiff = -- trace ("closeRuleCache: " ++ show classifiedRules) $
    ClosedRuleCache
        classifiedRules rawSources refinedSources injFactInstances
  where
    ctxt0 = ProofContext
        sig classifiedRules injFactInstances RawSource [] AvoidInduction Nothing
        (error "closeRuleCache: trace quantifier should not matter here")
        (error "closeRuleCache: lemma name should not matter here") [] isdiff
        (all isSubtermRule {-- $ trace (show destr ++ " - " ++ show (map isSubtermRule destr))-} destr) (any isConstantRule destr)

    -- inj fact instances
    injFactInstances =
        simpleInjectiveFactInstances $ L.get cprRuleE <$> protoRules

    -- precomputing the case distinctions: we make sure to only add safety
    -- restrictions. Otherwise, it wouldn't be sound to use the precomputed case
    -- distinctions for properties proven using induction.
    safetyRestrictions = filter isSafetyFormula restrictions
    rawSources         = precomputeSources ctxt0 safetyRestrictions
    refinedSources     = refineWithSourceAsms typAsms ctxt0 rawSources

    -- Maude handle
    hnd = L.get sigmMaudeHandle sig

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










-- Lemma construction/modification
----------------------------------

-- | Create a new unproven lemma from a formula modulo E.
unprovenLemma :: String -> [LemmaAttribute] -> TraceQuantifier -> LNFormula
              -> Lemma ProofSkeleton
unprovenLemma name atts qua fm = Lemma name qua fm atts (unproven ())

skeletonLemma :: String -> [LemmaAttribute] -> TraceQuantifier -> f -> p -> ProtoLemma f p
skeletonLemma name atts qua fm = Lemma name qua fm atts

-- | Create a new unproven diff lemma.
unprovenDiffLemma :: String -> [LemmaAttribute]
              -> DiffLemma DiffProofSkeleton
unprovenDiffLemma name atts = DiffLemma name atts (diffUnproven ())

skeletonDiffLemma :: String -> [LemmaAttribute] -> DiffProofSkeleton -> DiffLemma DiffProofSkeleton
skeletonDiffLemma name atts = DiffLemma name atts



-- | Open theories can be extended. Invariants:
--   1. Lemma names are unique.
type OpenTheory =
    Theory SignaturePure [IntrRuleAC] OpenProtoRule ProofSkeleton SapicElement

type OpenTheoryItem = TheoryItem OpenProtoRule ProofSkeleton SapicElement


-- | Open theories can be extended. Invariants:
--   1. Lemma names are unique.
--   2. All SapicItems are translated
type OpenTranslatedTheory =
    Theory SignaturePure [IntrRuleAC] OpenProtoRule ProofSkeleton ()

-- | Open diff theories can be extended. Invariants:
--   1. Lemma names are unique.
type OpenDiffTheory =
    DiffTheory SignaturePure [IntrRuleAC] DiffProtoRule OpenProtoRule DiffProofSkeleton ProofSkeleton

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

-- type EitherTheory = Either Theory  DiffTheory
type EitherOpenTheory = Either OpenTheory OpenDiffTheory
type EitherClosedTheory = Either ClosedTheory ClosedDiffTheory


-- remove Sapic items and convert other items to identical item but with unit type for sapic elements
removeSapicItems :: OpenTheory -> OpenTranslatedTheory
removeSapicItems thy =
  Theory {_thyName=(L.get thyName thy)
          ,_thyHeuristic=(L.get thyHeuristic thy)
          ,_thySignature=(L.get thySignature thy)
          ,_thyCache=(L.get thyCache thy)
          ,_thyItems = newThyItems
          ,_thyOptions =(L.get thyOptions thy)}
    where
      newThyItems = map removeSapicElement (filter isNoSapicItem (L.get thyItems thy))
      removeSapicElement :: TheoryItem r p SapicElement -> TheoryItem r p ()
      removeSapicElement (SapicItem _) = SapicItem ()
      removeSapicElement (RuleItem r) = RuleItem r
      removeSapicElement (LemmaItem l) = LemmaItem l
      removeSapicElement (RestrictionItem rl) = RestrictionItem rl
      removeSapicElement (TextItem t) = TextItem t
      removeSapicElement (PredicateItem predi) = PredicateItem predi
      isNoSapicItem (SapicItem _) = False
      isNoSapicItem _             = True


--open translated theory again
openTranslatedTheory :: OpenTranslatedTheory -> OpenTheory
openTranslatedTheory thy =
  Theory {_thyName=(L.get thyName thy)
          ,_thyHeuristic=(L.get thyHeuristic thy)
          ,_thySignature=(L.get thySignature thy)
          ,_thyCache=(L.get thyCache thy)
          ,_thyItems = newThyItems
          ,_thyOptions =(L.get thyOptions thy)}
    where
      newThyItems = mapMaybe addSapicElement (L.get thyItems thy)
      addSapicElement :: TheoryItem r p () -> Maybe (TheoryItem r p s)
      addSapicElement (RuleItem r) = Just $ RuleItem r
      addSapicElement (LemmaItem l) = Just $ LemmaItem l
      addSapicElement (RestrictionItem rl) = Just $ RestrictionItem rl
      addSapicElement (TextItem t) = Just $ TextItem t
      addSapicElement (PredicateItem predi) = Just $ PredicateItem predi
      addSapicElement (SapicItem _) = Nothing

-- | Add an auto-generated sources lemma if possible
addAutoSourcesLemmaDiff :: MaudeHandle
                        -> String
                        -> ClosedRuleCache
                        -> ClosedRuleCache
                        -> [DiffTheoryItem DiffProtoRule ClosedProtoRule IncrementalDiffProof IncrementalProof]
                        -> [DiffTheoryItem DiffProtoRule ClosedProtoRule IncrementalDiffProof IncrementalProof]
addAutoSourcesLemmaDiff hnd lemmaName crcLeft crcRight items =
    diffPart ++ lhsPart ++ rhsPart
  where
    -- We split items into three. DiffRules, DiffLemmas, and DiffTextItems are
    -- kept as is. We apply addAutoSourcesLemma on each side (rules, lemmas and
    -- restrictions), and recompose everything.
    diffPart = mapMaybe f items
      where
        f (DiffRuleItem r)  = Just (DiffRuleItem r)
        f (DiffLemmaItem l) = Just (DiffLemmaItem l)
        f (DiffTextItem t)  = Just (DiffTextItem t)
        f _                 = Nothing

    lhsPart = if containsPartialDeconstructions crcLeft
        then mapMaybe (toSide LHS) $
                addAutoSourcesLemma hnd (lemmaName ++ "_LHS") crcLeft $
                  mapMaybe (filterItemSide LHS) items
        else mapMaybe (toSide LHS) $
                  mapMaybe (filterItemSide LHS) items
    rhsPart = if containsPartialDeconstructions crcRight
        then mapMaybe (toSide RHS) $
                addAutoSourcesLemma hnd (lemmaName ++ "_RHS") crcRight $
                  mapMaybe (filterItemSide RHS) items
        else mapMaybe (toSide RHS) $
                  mapMaybe (filterItemSide RHS) items

    filterItemSide s (EitherRuleItem (s', r))        | s == s' = Just (RuleItem r)
    filterItemSide s (EitherLemmaItem (s', l))       | s == s' = Just (LemmaItem l)
    filterItemSide s (EitherRestrictionItem (s', r)) | s == s' = Just (RestrictionItem r)
    filterItemSide _ _                                         = Nothing

    toSide s (RuleItem r)        = Just $ EitherRuleItem (s, r)
    toSide LHS (LemmaItem l)     = Just $ EitherLemmaItem (LHS, addLeftLemma  l)
    toSide RHS (LemmaItem l)     = Just $ EitherLemmaItem (RHS, addRightLemma l)
    toSide s (RestrictionItem r) = Just $ EitherRestrictionItem (s, r)
    toSide _ (TextItem t)        = Just $ DiffTextItem t
    -- FIXME: We currently ignore predicates and sapic stuff as they should not
    --        be generated by addAutoSourcesLemma
    toSide _ (PredicateItem _)   = Nothing
    toSide _ (SapicItem _)       = Nothing

-- | Add an auto-generated sources lemma if possible
addAutoSourcesLemma :: MaudeHandle
                    -> String
                    -> ClosedRuleCache
                    -> [TheoryItem ClosedProtoRule IncrementalProof s]
                    -> [TheoryItem ClosedProtoRule IncrementalProof s]
addAutoSourcesLemma hnd lemmaName (ClosedRuleCache _ raw _ _) items =
  -- We only add the lemma if there is no lemma of the same name
  case find lemma items of
    Nothing  -> items'++[LemmaItem l]
    (Just _) -> items'
  where
    runMaude   = (`runReader` hnd)

    -- searching for the lemma
    lemma (LemmaItem (Lemma name _ _ _ _)) | name == lemmaName = True
    lemma _                                                    = False

    -- build the lemma
    l = fmap skeletonToIncrementalProof $ unprovenLemma lemmaName [SourceLemma] AllTraces formula

    -- extract all rules from theory items
    rules = mapMaybe itemToRule items

    -- compute all encrypted subterms that are output by protocol rules
    allOutConcs :: [(ClosedProtoRule, LNTerm)]
    allOutConcs = do
        ru                                <- rules
        (_, protoOrOutFactView -> Just t) <- enumConcs $ L.get cprRuleAC ru
        unifyProtC                        <- concatMap allProtSubterms t
        return (ru, unifyProtC)

    -- compute all fact that are conclusions in protocol rules (not OutFact)
    allOutConcsNotProt :: [(ClosedProtoRule, LNFact)]
    allOutConcsNotProt = do
        ru              <- rules
        (_, unifyFactC) <- enumConcs $ L.get cprRuleAC ru
        -- we ignore cases where the fact is OutFact
        guard (getFactTag unifyFactC /= OutFact)
        return (ru, unifyFactC)

    -- We use the raw sources here to generate one lemma to rule them all...
    (items', formula, _) = foldl computeFormula (items, ltrue, []) chains

    -- Generate a list of all cases that contain open chains
    chains = concatMap (multiply unsolvedChains . duplicate) $
                   concatMap (map snd . getDisj . L.get cdCases) raw

    -- Given a list of theory items, a formula, a source with an open chain,
    -- return an updated list of theory items and an update formula for the sources lemma.
    computeFormula :: ([TheoryItem ClosedProtoRule IncrementalProof s], LNFormula, [(RuleInfo ProtoRuleName IntrRuleACInfo, ExtendedPosition)])
                   -> ((NodeConc, NodePrem), System)
                   -> ([TheoryItem ClosedProtoRule IncrementalProof s], LNFormula, [(RuleInfo ProtoRuleName IntrRuleACInfo, ExtendedPosition)])
    computeFormula (its, form, done) ((conc,_), source) = (its', form', done')
      where
        -- The new items are the old ones but with added labels
        its'  = addLabels inputsAndOutputs its
        -- The new formula is the old one AND the new formula
        form' = addFormula inputsAndOutputs form
        -- The new list of treated cases
        done' = addCases inputsAndOutputs done

        -- Variable causing the open chain
        v     = head $ getFactTerms $ nodeConcFact conc source

        -- Compute all rules that contain v, and the position of v inside the input term
        inputRules :: [(ClosedProtoRule, Either LNTerm LNFact, ExtendedPosition)]
        inputRules = concat $ mapMaybe g $ allPrems source
          where
            g (nodeid, pid, tidx, term) = do
              position <- findPos v term
              ruleSys  <- nodeRuleSafe nodeid source
              rule     <- find ((ruleName ruleSys ==).ruleName) rules
              premise  <- lookupPrem pid $ L.get cprRuleAC rule
              t'       <- protoOrInFactView premise
              t        <- atMay t' tidx
              return (terms position rule t ++ facts position rule t premise)
                where
                  terms position rule t = do
                    -- iterate over all positions found
                    pos     <- position
                    return (rule, Left t, (pid, tidx, pos))
                  facts position rule t premise = do
                        -- we only consider protocol facts and unprotected terms
                    guard $ isProtoFact premise && (isPair t || isAC t || isMsgVar t)
                        -- we only consider facts which are not already solved in the source
                        && ((nodeid, pid) `elem` map fst (unsolvedPremises source))
                    -- iterate over all positions found
                    pos     <- position
                    return (rule, Right premise, (pid, tidx, pos))

        -- a list of all input subterms to unify : Left for protected subterm and Right for non protected subterm
        premiseTermU :: [(ClosedProtoRule, Either (LNTerm, LNTerm) LNFact, ExtendedPosition)]
        premiseTermU = mapMaybe f inputRules
          where
            -- cases for protected subterms : we consider the deepest protected subterm
            f (x, Left y, (pidx, tidx, z)) = do
              v'        <- y `atPosMay` z
              protTerm' <- deepestProtSubterm y z
              -- We do not consider the case where the computed deepest
              -- protected subterm is the variable in question, as this
              -- against the definition (a variable is not a function).
              -- Moreover, this case
              -- 1. often leads to false lemmas as we do not unify with all
              --    conclusion facts, in particular not with fresh facts
              -- 2. blows up the lemma as a variable unifies with all outputs
              -- 3. typically only happens if a value is stored in a state fact,
              --    which is handled by the other case
              protTerm  <- if protTerm' == v'
                then Nothing
                else Just protTerm'
              return (x, Left (protTerm, v'), (pidx, tidx, z))
            -- cases for non-protected subterms : we consider the Fact
            f (x, Right fact, (pidx, tidx, z)) =
              return (x, Right fact, (pidx, tidx, z))

        -- compute matching outputs
        -- returns a list of inputs together with their list of matching outputs
        inputsAndOutputs :: [(ClosedProtoRule, Either (LNTerm, LNTerm, [(ClosedProtoRule, LNTerm)]) (LNFact, [(ClosedProtoRule, LNFact)]), ExtendedPosition)]
        inputsAndOutputs = do
            -- iterate over all inputs
            (rin, unify, pos) <- filterFacts premiseTermU
            -- find matching conclusions
            let matches = matchingConclusions rin unify
            return (rin, matches, pos)
          where
            -- we ignore fact cases which are covered by the protected subterms
            filterFacts cases = mapMaybe f cases
              where
                f c@(r, Left  _, p) = do
                  guard $ notElem (ruleName r, p) done
                  return c
                f c@(r, Right _, p) = do
                  guard $ notElem (ruleName r, p) done
                         && null subtermCasePositions
                  return c
                -- check if there are protected subterms for this variable
                subtermCasePositions = filter (isLeft . snd3) cases

            matchingConclusions rin (Left (unify, vin)) = Left (unify, vin, do
              (rout, tout) <- allOutConcs
              -- generate fresh instance of conclusion, avoiding the premise variables
              let fout = tout `renameAvoiding` unify
              -- we ignore outputs of the same rule
              guard ((ruleName . L.get cprRuleE) rin /= (ruleName . L.get cprRuleE) rout)
              -- check whether input and output are unifiable
              guard (runMaude $ unifiableLNTerms unify fout)
              return (rout, tout))
            matchingConclusions rin (Right unify) = Right (unify, do
              (rout, fout) <- allOutConcsNotProt
              -- we ignore outputs of the same rule
              guard ((ruleName . L.get cprRuleE) rin /= (ruleName . L.get cprRuleE) rout)
              -- we ignore cases where the output fact and the input fact have different name
              guard (factTagName (getFactTag unify) == factTagName (getFactTag fout))
              -- check whether input and output are unifiable
              let unifout = fout `renameAvoiding` unify
              guard (runMaude $ unifiableLNFacts unify unifout)
              return (rout, fout))

        -- construct action facts for the rule annotations and formula
        inputFactTerm pos ru terms var = Fact {factTag = ProtoFact Linear
              ("AUTO_IN_TERM_" ++ printPosition pos ++ "_" ++ getRuleName (L.get cprRuleAC ru)) (1 + length terms),
              factAnnotations = S.empty, factTerms = terms ++[var]}
        inputFactFact pos ru terms = Fact {factTag = ProtoFact Linear
              ("AUTO_IN_FACT_" ++ printFactPosition pos ++ "_" ++ getRuleName (L.get cprRuleAC ru)) (length terms),
              factAnnotations = S.empty, factTerms = terms}
        outputFactTerm pos ru terms = Fact {factTag = ProtoFact Linear
              ("AUTO_OUT_TERM_" ++ printPosition pos ++ "_" ++ getRuleName (L.get cprRuleAC ru)) (length terms),
              factAnnotations = S.empty, factTerms = terms}
        outputFactFact pos ru terms = Fact {factTag = ProtoFact Linear
              ("AUTO_OUT_FACT_" ++ printFactPosition pos ++ "_" ++ getRuleName (L.get cprRuleAC ru)) (length terms),
              factAnnotations = S.empty, factTerms = terms}

        -- add labels to rules for typing lemma
        addLabels :: [(ClosedProtoRule, Either (LNTerm, LNTerm, [(ClosedProtoRule, LNTerm)]) (LNFact, [(ClosedProtoRule, LNFact)]), ExtendedPosition)]
                  -> [TheoryItem ClosedProtoRule IncrementalProof s]
                  -> [TheoryItem ClosedProtoRule IncrementalProof s]
        addLabels matches = map update
          where
            update (RuleItem ru) = RuleItem $ foldr up ru $
                   filter ((ruleName ru ==). ruleName . fst3) acts
              where
                up (r, p, Left  (Left  (t, v'))) r' = addActionClosedProtoRule r' (inputFactTerm  p r [t] v')
                up (r, p, Left  (Right f))       r' = addActionClosedProtoRule r' (inputFactFact  p r (getFactTerms f))
                up (_, p, Right (r, Left  t))    r' = addActionClosedProtoRule r' (outputFactTerm p r [t])
                up (_, p, Right (r, Right f))    r' = addActionClosedProtoRule r' (outputFactFact p r (getFactTerms f))
            update item          = item

            acts = concatMap prepare matches
            -- Left Left means Input Term
            -- Left Right means Input Fact
            -- Right Left means Output Term
            -- Right Left means Output Fact
            prepare (r, Left  (t, v', tl), p) = (r, p, Left (Left  (t, v'))) : map (\(r', t') -> (r', p, Right (r, Left  t'))) tl
            prepare (r, Right (f, fl)    , p) = (r, p, Left (Right f))       : map (\(r', f') -> (r', p, Right (r, Right f'))) fl

        listOfM :: Int -> [String]
        listOfM n = zipWith (++) (replicate n "m") $ fmap show [1..n]

        -- add formula to lemma
        addFormula ::
             [(ClosedProtoRule, Either (LNTerm, LNTerm, [(ClosedProtoRule, LNTerm)]) (LNFact, [(ClosedProtoRule, LNFact)]), ExtendedPosition)]
          -> LNFormula
          -> LNFormula
        addFormula matches f = foldr addForm f matches
          where
            addForm ::
                 (ClosedProtoRule, Either (LNTerm, LNTerm, [(ClosedProtoRule, LNTerm)]) (LNFact, [(ClosedProtoRule, LNFact)]), ExtendedPosition)
              -> LNFormula
              -> LNFormula
            -- protected subterms: if there are no matching outputs, do add a formula with only KU
            addForm (ru, Left (_, _, []), p) f' = f' .&&. Qua All ("x", LSortMsg)
              (Qua All ("m", LSortMsg) (Qua All ("i", LSortNode)
              (Conn Imp (Ato (Action (varTerm (Bound 0))
              (inputFactTerm p ru [varTerm (Bound 1)] (varTerm (Bound 2)))))
              orKU)))
            -- protected subterms
            addForm (ru, Left _, p) f' = f' .&&. Qua All ("x", LSortMsg)
              (Qua All ("m", LSortMsg) (Qua All ("i", LSortNode)
              (Conn Imp (Ato (Action (varTerm (Bound 0))
              (inputFactTerm p ru [varTerm (Bound 1)] (varTerm (Bound 2)))))
              (toFactsTerm ru p orKU))))
            -- facts: even if there are no matching outputs, do add a formula with "false"
            addForm (ru, Right (m, []),     p) f' = f' .&&. formulaMultArity (factArity m)
              where formulaMultArity nb = foldr (\h -> Qua All (h,LSortMsg))
                           (Qua All ("i", LSortNode)
                           (Conn Imp (Ato (Action (varTerm (Bound 0))
                           (inputFactFact p ru (listVarTerm (toInteger $ factArity m) 1))))
                           lfalse)) (listOfM nb)
            -- facts
            addForm (ru, Right (m, outs:_), p) f' = f' .&&. formulaMultArity (factArity m)
              where formulaMultArity nb = foldr (\h -> Qua All (h,LSortMsg))
                           (Qua All ("i", LSortNode)
                           (Conn Imp (Ato (Action (varTerm (Bound 0))
                           (inputFactFact p ru (listVarTerm (toInteger $ factArity m) 1))))
                           (toFactsFact ru p (snd outs)))) (listOfM nb)
            orKU = Qua Ex ("j",LSortNode)
                   (Conn And (Ato (Action (varTerm (Bound 0))
                    Fact {factTag = KUFact, factAnnotations = S.empty,
                          factTerms = [varTerm (Bound 3)]} ))
                   (Ato (Less (varTerm (Bound 0)) (varTerm (Bound 1)))))
            toFactsTerm ru p f'' =
              Conn Or f''
              (Qua Ex ("j",LSortNode)
              (Conn And (Ato (Action (varTerm (Bound 0))
              (outputFactTerm p ru [varTerm (Bound 2)]) ))
              (Ato (Less (varTerm (Bound 0)) (varTerm (Bound 1))))))
            toFactsFact ru p outn =
              Qua Ex ("j",LSortNode)
              (Conn And (Ato (Action (varTerm (Bound 0))
              (outputFactFact p ru (listVarTerm (toInteger $ 1 + factArity outn) 2)) ))
              (Ato (Less (varTerm (Bound 0)) (varTerm (Bound 1)))))
            listVarTerm q s | q == s    = [varTerm (Bound q)]
            listVarTerm q s | otherwise = varTerm (Bound q) : listVarTerm (q-1) s

        -- add all cases (identified by rule name and input variable position) to the list of treated cases
        addCases matches d = d ++ map (\(r, _, p) -> (ruleName r, p)) matches

-- | Add a new process expression.  since expression (and not definitions)
-- could appear several times, checking for doubled occurrence isn't necessary

------------------------------------------------------------------------------
-- Open theory construction / modification
------------------------------------------------------------------------------
defaultOption :: Option
defaultOption = Option False False False False

-- | Default theory
defaultOpenTheory :: Bool -> OpenTheory
defaultOpenTheory flag = Theory "default" [] (emptySignaturePure flag) [] [] defaultOption

-- | Default diff theory
defaultOpenDiffTheory :: Bool -> OpenDiffTheory
defaultOpenDiffTheory flag = DiffTheory "default" [] (emptySignaturePure flag) [] [] [] [] []

-- Add the default Diff lemma to an Open Diff Theory
addDefaultDiffLemma:: OpenDiffTheory -> OpenDiffTheory
addDefaultDiffLemma thy = fromMaybe thy $ addDiffLemma (unprovenDiffLemma "Observational_equivalence" []) thy

-- Add the rule labels to an Open Diff Theory
addProtoRuleLabel :: OpenProtoRule -> OpenProtoRule
addProtoRuleLabel rule = addProtoDiffLabel rule ("DiffProto" ++ (getOpenProtoRuleName rule))

-- Get the left openProtoRules
getLeftProtoRule :: DiffProtoRule -> OpenProtoRule
getLeftProtoRule (DiffProtoRule ruE Nothing)       = OpenProtoRule (getLeftRule ruE) []
getLeftProtoRule (DiffProtoRule _   (Just (l, _))) = l

-- Get the rigth openProtoRules
getRightProtoRule :: DiffProtoRule -> OpenProtoRule
getRightProtoRule (DiffProtoRule ruE Nothing)       = OpenProtoRule (getRightRule ruE) []
getRightProtoRule (DiffProtoRule _   (Just (_, r))) = r

-- Add the rule labels to an Open Diff Theory
addIntrRuleLabels:: OpenDiffTheory -> OpenDiffTheory
addIntrRuleLabels thy =
    modify diffThyCacheLeft (map addRuleLabel) $ modify diffThyDiffCacheLeft (map addRuleLabel) $ modify diffThyDiffCacheRight (map addRuleLabel) $ modify diffThyCacheRight (map addRuleLabel) thy
  where
    addRuleLabel :: IntrRuleAC -> IntrRuleAC
    addRuleLabel rule = addDiffLabel rule ("DiffIntr" ++ (getRuleName rule))

-- | Returns true if there are OpenProtoRules containing manual variants
containsManualRuleVariants :: [TheoryItem OpenProtoRule p s] -> Bool
containsManualRuleVariants = foldl f False
  where
    f hasVariants (RuleItem (OpenProtoRule _ [])) = hasVariants
    f _           (RuleItem (OpenProtoRule _ _ )) = True
    f hasVariants _                               = hasVariants

-- | Merges variants of the same protocol rule modulo E
mergeOpenProtoRules :: [TheoryItem OpenProtoRule p s] -> [TheoryItem OpenProtoRule p s]
mergeOpenProtoRules = concatMap (foldr mergeRules []) . groupBy comp
  where
    comp (RuleItem (OpenProtoRule ruE _)) (RuleItem (OpenProtoRule ruE' _)) = ruE == ruE'
    comp (RuleItem _) _ = False
    comp _ (RuleItem _) = False
    comp _ _            = True

    mergeRules (RuleItem r)                          []                                              = [RuleItem r]
    mergeRules (RuleItem (OpenProtoRule ruE' ruAC')) [RuleItem (OpenProtoRule ruE ruAC)] | ruE==ruE' = [RuleItem (OpenProtoRule ruE (ruAC'++ruAC))]
    mergeRules (RuleItem _)                          _                                               = error "Error in mergeOpenProtoRules. Please report bug."
    mergeRules item                                  l                                               = item:l

-- | Returns true if there are DiffProtoRules containing manual instances or variants
containsManualRuleVariantsDiff :: [DiffTheoryItem DiffProtoRule r p p2] -> Bool
containsManualRuleVariantsDiff = foldl f False
  where
    f hasVariants (DiffRuleItem (DiffProtoRule _ Nothing )) = hasVariants
    f _           (DiffRuleItem (DiffProtoRule _ (Just _))) = True
    f hasVariants _                                         = hasVariants

-- | Merges variants of the same protocol rule modulo E
mergeOpenProtoRulesDiff :: [DiffTheoryItem r OpenProtoRule p p2] -> [DiffTheoryItem r OpenProtoRule p p2]
mergeOpenProtoRulesDiff = concatMap (foldr mergeRules []) . groupBy comp
  where
    comp (EitherRuleItem (s, OpenProtoRule ruE _)) (EitherRuleItem (s', OpenProtoRule ruE' _)) = ruE==ruE' && s==s'
    comp (EitherRuleItem _) _ = False
    comp _ (EitherRuleItem _) = False
    comp _ _                  = True

    mergeRules (EitherRuleItem r)                             [] = [EitherRuleItem r]
    mergeRules (EitherRuleItem (s, OpenProtoRule ruE' ruAC')) [EitherRuleItem (s', OpenProtoRule ruE ruAC)]
                                            | ruE==ruE' && s==s' = [EitherRuleItem (s, OpenProtoRule ruE (ruAC'++ruAC))]
    mergeRules (EitherRuleItem _)                             _  = error "Error in mergeOpenProtoRulesDiff. Please report bug."
    mergeRules item                                           l  = item:l

-- | Merges left and right instances with initial diff rule
mergeLeftRightRulesDiff :: (Show p, Show p2) => [DiffTheoryItem DiffProtoRule OpenProtoRule p p2] -> [DiffTheoryItem DiffProtoRule OpenProtoRule p p2]
mergeLeftRightRulesDiff rs = map clean $ concatMap (foldr mergeRules []) $ groupBy comp' $ sortBy comp rs
  where
    comp (EitherRuleItem (_, OpenProtoRule ruE _)) (EitherRuleItem (_, OpenProtoRule ruE' _)) = compare (ruleName ruE) (ruleName ruE')
    comp (EitherRuleItem (_, OpenProtoRule ruE _)) (DiffRuleItem (DiffProtoRule ruE' _))      = compare (ruleName ruE) (ruleName ruE')
    comp (DiffRuleItem (DiffProtoRule ruE _))      (EitherRuleItem (_, OpenProtoRule ruE' _)) = compare (ruleName ruE) (ruleName ruE')
    comp (DiffRuleItem (DiffProtoRule ruE _))      (DiffRuleItem (DiffProtoRule ruE' _))      = compare (ruleName ruE) (ruleName ruE')
    comp (EitherRuleItem _) _ = LT
    comp _ (EitherRuleItem _) = GT
    comp (DiffRuleItem _) _   = LT
    comp _ (DiffRuleItem _)   = GT
    comp _ _                  = EQ

    comp' a b = comp a b == EQ

    mergeRules (EitherRuleItem r)                                 [] = [EitherRuleItem r]
    mergeRules (DiffRuleItem r)                                   [] = [DiffRuleItem r]
    mergeRules (EitherRuleItem (s, ru@(OpenProtoRule ruE _)))     [EitherRuleItem (s', ru'@(OpenProtoRule ruE' _))]
                                            | ruleName ruE==ruleName ruE' && s==LHS && s'==RHS = [DiffRuleItem (DiffProtoRule ruE (Just (ru, ru')))]
    mergeRules (EitherRuleItem (s, ru@(OpenProtoRule ruE _)))     [EitherRuleItem (s', ru'@(OpenProtoRule ruE' _))]
                                            | ruleName ruE==ruleName ruE' && s==RHS && s'==LHS = [DiffRuleItem (DiffProtoRule ruE (Just (ru', ru)))]
    mergeRules (EitherRuleItem (_, ru@(OpenProtoRule ruE _)))     [DiffRuleItem (DiffProtoRule dru Nothing)]
                                            | ruleName ruE==ruleName dru = [DiffRuleItem (DiffProtoRule dru (Just (ru, ru)))]
    mergeRules (DiffRuleItem (DiffProtoRule dru Nothing))         [EitherRuleItem (_, ru@(OpenProtoRule ruE _))]
                                            | ruleName ruE==ruleName dru = [DiffRuleItem (DiffProtoRule dru (Just (ru, ru)))]
    mergeRules (EitherRuleItem (LHS, ru@(OpenProtoRule ruE _)))   [DiffRuleItem (DiffProtoRule dru (Just (_, ru')))]
                                            | ruleName ruE==ruleName dru = [DiffRuleItem (DiffProtoRule dru (Just (ru, ru')))]
    mergeRules (EitherRuleItem (RHS, ru@(OpenProtoRule ruE _)))   [DiffRuleItem (DiffProtoRule dru (Just (ru', _)))]
                                            | ruleName ruE==ruleName dru = [DiffRuleItem (DiffProtoRule dru (Just (ru', ru)))]
    mergeRules (DiffRuleItem (DiffProtoRule dru (Just (_, ru')))) [EitherRuleItem (LHS, ru@(OpenProtoRule ruE _))]
                                            | ruleName ruE==ruleName dru = [DiffRuleItem (DiffProtoRule dru (Just (ru, ru')))]
    mergeRules (DiffRuleItem (DiffProtoRule dru (Just (ru', _)))) [EitherRuleItem (RHS, ru@(OpenProtoRule ruE _))]
                                            | ruleName ruE==ruleName dru = [DiffRuleItem (DiffProtoRule dru (Just (ru', ru)))]
    mergeRules (DiffRuleItem (DiffProtoRule dru (Just (lr, rr)))) [DiffRuleItem (DiffProtoRule dru' Nothing)]
                                            | ruleName dru==ruleName dru' = [DiffRuleItem (DiffProtoRule dru (Just (lr, rr)))]
    mergeRules (DiffRuleItem (DiffProtoRule dru Nothing))         [DiffRuleItem (DiffProtoRule dru' (Just (lr, rr)))]
                                            | ruleName dru==ruleName dru' = [DiffRuleItem (DiffProtoRule dru (Just (lr, rr)))]
    mergeRules (DiffRuleItem (DiffProtoRule dru (Just (lr, rr)))) [DiffRuleItem (DiffProtoRule dru' (Just (lr', rr')))]
                                            | ruleName dru==ruleName dru' && equalOpenRuleUpToDiffAnnotation lr lr' && equalOpenRuleUpToDiffAnnotation rr rr' = [DiffRuleItem (DiffProtoRule dru (Just (lr, rr)))]
    mergeRules (EitherRuleItem _)                                 _  = error "Error in mergeLeftRightRulesDiff. Please report bug."
    mergeRules (DiffRuleItem _)                                   _  = error "Error in mergeLeftRightRulesDiff. Please report bug."
    mergeRules item                                               l  = item:l

    clean (DiffRuleItem (DiffProtoRule ruE (Just (OpenProtoRule ruEL [], OpenProtoRule ruER []))))
       | getLeftRule ruE `equalRuleUpToDiffAnnotation` ruEL
        && getRightRule ruE `equalRuleUpToDiffAnnotation` ruER = DiffRuleItem (DiffProtoRule ruE Nothing)
    clean i                                                    = i

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


-- | Find the open protocol rule with the given name.
lookupOpenProtoRule :: ProtoRuleName -> OpenTheory -> Maybe OpenProtoRule
lookupOpenProtoRule name =
    find ((name ==) . L.get (preName . rInfo . oprRuleE)) . theoryRules

-- | Find the open protocol rule with the given name.
lookupOpenDiffProtoDiffRule :: ProtoRuleName -> OpenDiffTheory -> Maybe DiffProtoRule
lookupOpenDiffProtoDiffRule name =
    find ((name ==) . L.get (preName . rInfo . dprRule)) . diffTheoryDiffRules

-- | Add new protocol rules. Fails, if a protocol rule with the same name
-- exists.
addOpenProtoRule :: OpenProtoRule -> OpenTheory -> Maybe OpenTheory
addOpenProtoRule ru@(OpenProtoRule ruE ruAC) thy = do
    guard nameNotUsedForDifferentRule
    guard allRuleNamesAreDifferent
    return $ modify thyItems (++ [RuleItem ru]) thy
  where
    nameNotUsedForDifferentRule =
        maybe True (ru ==) $ lookupOpenProtoRule (L.get (preName . rInfo . oprRuleE) ru) thy
    allRuleNamesAreDifferent = (S.size (S.fromList (ruleName ruE:map ruleName ruAC)))
        == ((length ruAC) + 1)

-- | Add a new protocol rules. Fails, if a protocol rule with the same name
-- exists.
addOpenProtoDiffRule :: DiffProtoRule -> OpenDiffTheory -> Maybe OpenDiffTheory
addOpenProtoDiffRule ru@(DiffProtoRule _ Nothing)  thy = do
    guard nameNotUsedForDifferentRule
    return $ modify diffThyItems (++ [DiffRuleItem ru]) thy
  where
    nameNotUsedForDifferentRule =
        maybe True (ru ==) $ lookupOpenDiffProtoDiffRule (L.get (preName . rInfo . dprRule) ru) thy
addOpenProtoDiffRule ru@(DiffProtoRule _ (Just (lr, rr))) thy = do
    guard nameNotUsedForDifferentRule
    guard $ allRuleNamesAreDifferent lr
    guard $ allRuleNamesAreDifferent rr
    guard leftAndRightHaveSameName
    return $ modify diffThyItems (++ [DiffRuleItem ru]) thy
  where
    nameNotUsedForDifferentRule =
        maybe True (ru ==) $ lookupOpenDiffProtoDiffRule (L.get (preName . rInfo . dprRule) ru) thy
    allRuleNamesAreDifferent (OpenProtoRule ruE ruAC) = (S.size (S.fromList (ruleName ruE:map ruleName ruAC)))
        == ((length ruAC) + 1)
    leftAndRightHaveSameName = ruleName ru == ruleName lr && ruleName lr == ruleName rr

-- | Add new protocol rules. Fails, if a protocol rule with the same name
-- exists. Ignore _restrict construct.
addProtoRule :: ProtoRuleE -> OpenTheory -> Maybe OpenTheory
addProtoRule ruE thy = do
    guard nameNotUsedForDifferentRule
    return $ modify thyItems (++ [RuleItem (OpenProtoRule ruE [])]) thy
  where
    nameNotUsedForDifferentRule =
        maybe True (ruE ==) $ fmap (L.get oprRuleE) $ lookupOpenProtoRule (L.get (preName . rInfo) ruE) thy

-- | Add a new protocol rules. Fails, if a protocol rule with the same name
-- exists.
addProtoDiffRule :: ProtoRuleE -> OpenDiffTheory -> Maybe OpenDiffTheory
addProtoDiffRule ruE thy = do
    guard nameNotUsedForDifferentRule
    return $ modify diffThyItems (++ [DiffRuleItem (DiffProtoRule ruE Nothing)]) thy
  where
    nameNotUsedForDifferentRule =
        maybe True (ruE ==) $ fmap (L.get dprRule) $ lookupOpenDiffProtoDiffRule (L.get (preName . rInfo) ruE) thy

-- | Add intruder proof rules after Translate.
addIntrRuleACsAfterTranslate :: [IntrRuleAC] -> OpenTranslatedTheory -> OpenTranslatedTheory
addIntrRuleACsAfterTranslate rs' = modify (thyCache) (\rs -> nub $ rs ++ rs')

-- | Add intruder proof rules.
addIntrRuleACs :: [IntrRuleAC] -> OpenTheory -> OpenTheory
addIntrRuleACs rs' = modify (thyCache) (\rs -> nub $ rs ++ rs')

-- | Add intruder proof rules for all diff and non-diff caches.
addIntrRuleACsDiffAll :: [IntrRuleAC] -> OpenDiffTheory -> OpenDiffTheory
addIntrRuleACsDiffAll rs' thy = addIntrRuleACsDiffBoth rs' (addIntrRuleACsDiffBothDiff rs' thy)

-- | Add intruder proof rules for both diff caches.
addIntrRuleACsDiffBothDiff :: [IntrRuleAC] -> OpenDiffTheory -> OpenDiffTheory
addIntrRuleACsDiffBothDiff rs' thy = addIntrRuleACsDiffRightDiff rs' (addIntrRuleACsDiffLeftDiff rs' thy)

-- | Add intruder proof rules for both caches.
addIntrRuleACsDiffBoth :: [IntrRuleAC] -> OpenDiffTheory -> OpenDiffTheory
addIntrRuleACsDiffBoth rs' thy = addIntrRuleACsDiffRight rs' (addIntrRuleACsDiffLeft rs' thy)

-- | Add intruder proof rules to left diff cache.
addIntrRuleACsDiffLeftDiff :: [IntrRuleAC] -> OpenDiffTheory -> OpenDiffTheory
addIntrRuleACsDiffLeftDiff rs' thy = modify (diffThyDiffCacheLeft) (\rs -> nub $ rs ++ rs') thy

-- | Add intruder proof rules to left cache.
addIntrRuleACsDiffLeft :: [IntrRuleAC] -> OpenDiffTheory -> OpenDiffTheory
addIntrRuleACsDiffLeft rs' thy = modify (diffThyCacheLeft) (\rs -> nub $ rs ++ rs') thy

-- | Add intruder proof rules to right diff cache.
addIntrRuleACsDiffRightDiff :: [IntrRuleAC] -> OpenDiffTheory -> OpenDiffTheory
addIntrRuleACsDiffRightDiff rs' thy = modify (diffThyDiffCacheRight) (\rs -> nub $ rs ++ rs') thy

-- | Add intruder proof rules to right cache.
addIntrRuleACsDiffRight :: [IntrRuleAC] -> OpenDiffTheory -> OpenDiffTheory
addIntrRuleACsDiffRight rs' thy = modify (diffThyCacheRight) (\rs -> nub $ rs ++ rs') thy

-- | Normalize the theory representation such that they remain semantically
-- equivalent. Use this function when you want to compare two theories (quite
-- strictly) for semantic equality; e.g., when testing the parser.
normalizeTheory :: OpenTheory -> OpenTheory
normalizeTheory =
    L.modify thyCache sort
  . L.modify thyItems (\items -> do
      item <- items
      return $ case item of
          LemmaItem lem ->
              LemmaItem $ L.modify lProof stripProofAnnotations $ lem
          RuleItem _    -> item
          TextItem _    -> item
          RestrictionItem _   -> item
          SapicItem _   -> item
          PredicateItem _   -> item
          )
  where
    stripProofAnnotations :: ProofSkeleton -> ProofSkeleton
    stripProofAnnotations = fmap stripProofStepAnnotations
    stripProofStepAnnotations (ProofStep method ()) =
        ProofStep (case method of
                     Sorry _         -> Sorry Nothing
                     Contradiction _ -> Contradiction Nothing
                     _               -> method)
                  ()


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


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Pretty print a side for parameters
prettySide :: HighlightDocument d => Side -> d
prettySide LHS = text "[left]"
prettySide RHS = text "[right]"

-- | Pretty print a formal comment
prettyFormalComment :: HighlightDocument d => String -> String -> d
prettyFormalComment "" body = multiComment_ [body]
prettyFormalComment header body = text $ header ++ "{*" ++ body ++ "*}"

-- | Pretty print a theory.
prettyTheoryWithSapic :: HighlightDocument d
             => (sig -> d) -> (c -> d) -> (r -> d) -> (p -> d) -> (SapicElement -> d)
             -> Theory sig c r p SapicElement -> d
prettyTheoryWithSapic ppSig ppCache ppRule ppPrf ppSap thy = vsep $
    [ kwTheoryHeader $ text $ L.get thyName thy
    , lineComment_ "Function signature and definition of the equational theory E"
    , ppSig $ L.get thySignature thy
    , if thyH == [] then text "" else text "heuristic: " <> text (prettyGoalRankings thyH)
    , ppCache $ L.get thyCache thy
    ] ++
    parMap rdeepseq ppItem (L.get thyItems thy) ++
    [ kwEnd ]
  where
    ppItem = foldTheoryItem
        ppRule prettyRestriction (prettyLemma ppPrf) (uncurry prettyFormalComment) prettyPredicate ppSap
    thyH = L.get thyHeuristic thy

--Pretty print a theory
prettyTheory :: HighlightDocument d
             => (sig -> d) -> (c -> d) -> (r -> d) -> (p -> d) -> (() -> d)
             -> Theory sig c r p () -> d
prettyTheory ppSig ppCache ppRule ppPrf ppSap thy = vsep $
    [ kwTheoryHeader $ text $ L.get thyName thy
    , lineComment_ "Function signature and definition of the equational theory E"
    , ppSig $ L.get thySignature thy
    , if thyH == [] then text "" else text "heuristic: " <> text (prettyGoalRankings thyH)
    , ppCache $ L.get thyCache thy
    ] ++
    parMap rdeepseq ppItem (L.get thyItems thy) ++
    [ kwEnd ]
  where
    ppItem = foldTheoryItem
        ppRule prettyRestriction (prettyLemma ppPrf) (uncurry prettyFormalComment) prettyPredicate ppSap
    thyH = L.get thyHeuristic thy

emptyString :: HighlightDocument d => () -> d
emptyString _ = text ("")

prettySapicElement :: HighlightDocument d => SapicElement -> d
prettySapicElement _ = text ("TODO prettyPrint SapicItems")

prettyPredicate :: HighlightDocument d => Predicate -> d
prettyPredicate p = kwPredicate <> colon <-> text (factstr ++ "<=>" ++ formulastr)
    where
        factstr = render $ prettyFact prettyLVar $ L.get pFact p
        formulastr = render $ prettyLNFormula $ L.get pFormula p

prettyProcess :: HighlightDocument d => Process -> d
prettyProcess p = text (prettySapic p)

prettyProcessDef :: HighlightDocument d => ProcessDef -> d
prettyProcessDef pDef = text ("let " ++ (L.get pName pDef) ++ " = " ++ (prettySapic (L.get pBody pDef)))

-- | Pretty print a diff theory.
prettyDiffTheory :: HighlightDocument d
                 => (sig -> d) -> (c -> d) -> ((Side, r2) -> d) -> (p -> d) -> (p2 -> d)
                 -> DiffTheory sig c DiffProtoRule r2 p p2 -> d
prettyDiffTheory ppSig ppCache ppRule ppDiffPrf ppPrf thy = vsep $
    [ kwTheoryHeader $ text $ L.get diffThyName thy
    , lineComment_ "Function signature and definition of the equational theory E"
    , ppSig $ L.get diffThySignature thy
    , if thyH == [] then text "" else text "heuristic: " <> text (prettyGoalRankings thyH)
    , ppCache $ L.get diffThyCacheLeft thy
    , ppCache $ L.get diffThyCacheRight thy
    , ppCache $ L.get diffThyDiffCacheLeft thy
    , ppCache $ L.get diffThyDiffCacheRight thy
    ] ++
    parMap rdeepseq ppItem (L.get diffThyItems thy) ++
    [ kwEnd ]
  where
    ppItem = foldDiffTheoryItem
        prettyDiffRule ppRule (prettyDiffLemma ppDiffPrf) (prettyEitherLemma ppPrf) prettyEitherRestriction (uncurry prettyFormalComment)
    thyH = L.get diffThyHeuristic thy

-- | Pretty print the lemma name together with its attributes.
prettyLemmaName :: HighlightDocument d => Lemma p -> d
prettyLemmaName l = case L.get lAttributes l of
      [] -> text (L.get lName l)
      as -> text (L.get lName l) <->
            (brackets $ fsep $ punctuate comma $ map prettyLemmaAttribute as)
  where
    prettyLemmaAttribute SourceLemma        = text "sources"
    prettyLemmaAttribute ReuseLemma         = text "reuse"
    prettyLemmaAttribute ReuseDiffLemma     = text "diff_reuse"
    prettyLemmaAttribute InvariantLemma     = text "use_induction"
    prettyLemmaAttribute (HideLemma s)      = text ("hide_lemma=" ++ s)
    prettyLemmaAttribute (LemmaHeuristic h) = text ("heuristic=" ++ (prettyGoalRankings h))
    prettyLemmaAttribute LHSLemma           = text "left"
    prettyLemmaAttribute RHSLemma           = text "right"
--     prettyLemmaAttribute BothLemma      = text "both"


-- | Pretty print the diff lemma name
prettyDiffLemmaName :: HighlightDocument d => DiffLemma p -> d
prettyDiffLemmaName l = text ((L.get lDiffName l))


-- | Pretty print a restriction.
prettyRestriction :: HighlightDocument d => Restriction -> d
prettyRestriction rstr =
    kwRestriction <-> text (L.get rstrName rstr) <> colon $-$
    (nest 2 $ doubleQuotes $ prettyLNFormula $ L.get rstrFormula rstr) $-$
    (nest 2 $ if safety then lineComment_ "safety formula" else emptyDoc)
  where
    safety = isSafetyFormula $ formulaToGuarded_ $ L.get rstrFormula rstr

-- | Pretty print an either restriction.
prettyEitherRestriction :: HighlightDocument d => (Side, Restriction) -> d
prettyEitherRestriction (s, rstr) =
    kwRestriction <-> text (L.get rstrName rstr) <-> prettySide s <> colon $-$
    (nest 2 $ doubleQuotes $ prettyLNFormula $ L.get rstrFormula rstr) $-$
    (nest 2 $ if safety then lineComment_ "safety formula" else emptyDoc)
  where
    safety = isSafetyFormula $ formulaToGuarded_ $ L.get rstrFormula rstr

    -- | Pretty print a lemma.
prettyLemma :: HighlightDocument d => (p -> d) -> Lemma p -> d
prettyLemma ppPrf lem =
    kwLemma <-> prettyLemmaName lem <> colon $-$
    (nest 2 $
      sep [ prettyTraceQuantifier $ L.get lTraceQuantifier lem
          , doubleQuotes $ prettyLNFormula $ L.get lFormula lem
          ]
    )
    $-$
    ppLNFormulaGuarded (L.get lFormula lem)
    $-$
    ppPrf (L.get lProof lem)
  where
    ppLNFormulaGuarded fm = case formulaToGuarded fm of
        Left err -> multiComment $
            text "conversion to guarded formula failed:" $$
            nest 2 err
        Right gf -> case toSystemTraceQuantifier $ L.get lTraceQuantifier lem of
          ExistsNoTrace -> multiComment
            ( text "guarded formula characterizing all counter-examples:" $-$
              doubleQuotes (prettyGuarded (gnot gf)) )
          ExistsSomeTrace -> multiComment
            ( text "guarded formula characterizing all satisfying traces:" $-$
              doubleQuotes (prettyGuarded gf) )

-- | Pretty print an Either lemma.
prettyEitherLemma :: HighlightDocument d => (p -> d) -> (Side, Lemma p) -> d
prettyEitherLemma ppPrf (_, lem) =
    kwLemma <-> prettyLemmaName lem <> colon $-$
    (nest 2 $
      sep [ prettyTraceQuantifier $ L.get lTraceQuantifier lem
          , doubleQuotes $ prettyLNFormula $ L.get lFormula lem
          ]
    )
    $-$
    ppLNFormulaGuarded (L.get lFormula lem)
    $-$
    ppPrf (L.get lProof lem)
  where
    ppLNFormulaGuarded fm = case formulaToGuarded fm of
        Left err -> multiComment $
            text "conversion to guarded formula failed:" $$
            nest 2 err
        Right gf -> case toSystemTraceQuantifier $ L.get lTraceQuantifier lem of
          ExistsNoTrace -> multiComment
            ( text "guarded formula characterizing all counter-examples:" $-$
              doubleQuotes (prettyGuarded (gnot gf)) )
          ExistsSomeTrace -> multiComment
            ( text "guarded formula characterizing all satisfying traces:" $-$
              doubleQuotes (prettyGuarded gf) )

-- | Pretty print a diff lemma.
prettyDiffLemma :: HighlightDocument d => (p -> d) -> DiffLemma p -> d
prettyDiffLemma ppPrf lem =
    kwDiffLemma <-> prettyDiffLemmaName lem <> colon
    $-$
    ppPrf (L.get lDiffProof lem)

-- | Pretty-print a non-empty bunch of intruder rules.
prettyIntruderVariants :: HighlightDocument d => [IntrRuleAC] -> d
prettyIntruderVariants vs = vcat . intersperse (text "") $ map prettyIntrRuleAC vs

{-
-- | Pretty-print the intruder variants section.
prettyIntrVariantsSection :: HighlightDocument d => [IntrRuleAC] -> d
prettyIntrVariantsSection rules =
    prettyFormalComment "section" " Finite Variants of the Intruder Rules " $--$
    nest 1 (prettyIntruderVariants rules)
-}

-- | Pretty print an open rule together with its assertion soundness proof.
prettyOpenProtoRule :: HighlightDocument d => OpenProtoRule -> d
prettyOpenProtoRule (OpenProtoRule ruE [])       = prettyProtoRuleE ruE
prettyOpenProtoRule (OpenProtoRule _   [ruAC])   = prettyProtoRuleACasE ruAC
prettyOpenProtoRule (OpenProtoRule ruE variants) = prettyProtoRuleE ruE $-$
    nest 1 (kwVariants $-$ nest 1 (ppList prettyProtoRuleAC variants))
  where
    ppList _  []     = emptyDoc
    ppList pp [x]    = pp x
    ppList pp (x:xr) = pp x $-$ comma $-$ ppList pp xr

-- | Pretty print an open rule together with its assertion soundness proof.
prettyOpenProtoRuleAsClosedRule :: HighlightDocument d => OpenProtoRule -> d
prettyOpenProtoRuleAsClosedRule (OpenProtoRule ruE [])
    = prettyProtoRuleE ruE $--$
    -- cannot show loop breakers here, as we do not have the information
    (nest 2 $ emptyDoc $-$
     multiComment_ ["has exactly the trivial AC variant"])
prettyOpenProtoRuleAsClosedRule (OpenProtoRule _ [ruAC@(Rule (ProtoRuleACInfo _ _ (Disj disj) _) _ _ _ _)])
    = prettyProtoRuleACasE ruAC $--$
    (nest 2 $ prettyLoopBreakers (L.get rInfo ruAC) $-$
     if length disj == 1 then
       multiComment_ ["has exactly the trivial AC variant"]
     else
       multiComment $ prettyProtoRuleAC ruAC
    )
prettyOpenProtoRuleAsClosedRule (OpenProtoRule ruE variants) = prettyProtoRuleE ruE $-$
    nest 1 (kwVariants $-$ nest 1 (ppList prettyProtoRuleAC variants))
  where
    ppList _  []     = emptyDoc
    ppList pp [x]    = pp x
    ppList pp (x:xr) = pp x $-$ comma $-$ ppList pp xr

-- | Pretty print a diff rule
prettyDiffRule :: HighlightDocument d => DiffProtoRule -> d
prettyDiffRule (DiffProtoRule ruE Nothing           ) = prettyProtoRuleE ruE
prettyDiffRule (DiffProtoRule ruE (Just (ruL,  ruR))) = prettyProtoRuleE ruE $-$
    nest 1
    (kwLeft  $-$ nest 1 (prettyOpenProtoRule ruL) $-$
     kwRight $-$ nest 1 (prettyOpenProtoRule ruR))

-- | Pretty print an either rule
prettyEitherRule :: HighlightDocument d => (Side, OpenProtoRule) -> d
prettyEitherRule (_, p) = prettyProtoRuleE $ L.get oprRuleE p

prettyIncrementalProof :: HighlightDocument d => IncrementalProof -> d
prettyIncrementalProof = prettyProofWith ppStep (const id)
  where
    ppStep step = sep
      [ prettyProofMethod (psMethod step)
      , if isNothing (psInfo step) then multiComment_ ["unannotated"]
                                   else emptyDoc
      ]

prettyIncrementalDiffProof :: HighlightDocument d => IncrementalDiffProof -> d
prettyIncrementalDiffProof = prettyDiffProofWith ppStep (const id)
  where
    ppStep step = sep
      [ prettyDiffProofMethod (dpsMethod step)
      , if isNothing (dpsInfo step) then multiComment_ ["unannotated"]
                                    else emptyDoc
      ]

-- | Pretty print an closed rule.
prettyClosedProtoRule :: HighlightDocument d => ClosedProtoRule -> d
prettyClosedProtoRule cru =
  if isTrivialProtoVariantAC ruAC ruE then
  -- We have a rule that only has one trivial variant, and without added annotations
  -- Hence showing the initial rule modulo E
    (prettyProtoRuleE ruE) $--$
    (nest 2 $ prettyLoopBreakers (L.get rInfo ruAC) $-$
     multiComment_ ["has exactly the trivial AC variant"])
  else
    if ruleName ruAC == ruleName ruE then
      if not (equalUpToTerms ruAC ruE) then
      -- Here we have a rule with added annotations,
      -- hence showing the annotated rule as if it was a rule mod E
      -- note that we can do that, as we unfolded variants
        (prettyProtoRuleACasE ruAC) $--$
        (nest 2 $ prettyLoopBreakers (L.get rInfo ruAC) $-$
         multiComment_ ["has exactly the trivial AC variant"])
      else
      -- Here we have a rule with one or multiple variants, but without other annotations
      -- Hence showing the rule mod E with commented variants
        (prettyProtoRuleE ruE) $--$
        (nest 2 $ prettyLoopBreakers (L.get rInfo ruAC) $-$
         (multiComment $ prettyProtoRuleAC ruAC))
    else
    -- Here we have a variant of a rule that has multiple variants.
    -- Hence showing only the variant as a rule modulo AC. This should not
    -- normally be used, as it breaks the ability to re-import.
      (prettyProtoRuleAC ruAC) $--$
      (nest 3 $ prettyLoopBreakers (L.get rInfo ruAC) $-$
          (multiComment_ ["variant of"]) $-$
          (multiComment $ prettyProtoRuleE ruE)
      )
 where
    ruAC      = L.get cprRuleAC cru
    ruE       = L.get cprRuleE cru

-- -- | Pretty print an closed rule.
-- prettyClosedEitherRule :: HighlightDocument d => (Side, ClosedProtoRule) -> d
-- prettyClosedEitherRule (s, cru) =
--     text ((show s) ++ ": ") <>
--     (prettyProtoRuleE ruE) $--$
--     (nest 2 $ prettyLoopBreakers (L.get rInfo ruAC) $-$ ppRuleAC)
--   where
--     ruAC = L.get cprRuleAC cru
--     ruE  = L.get cprRuleE cru
--     ppRuleAC
--       | isTrivialProtoVariantAC ruAC ruE = multiComment_ ["has exactly the trivial AC variant"]
--       | otherwise                        = multiComment $ prettyProtoRuleAC ruAC

-- | Pretty print an open theory.
prettyOpenTheory :: HighlightDocument d => OpenTheory -> d
prettyOpenTheory =
    prettyTheoryWithSapic prettySignaturePure
                 (const emptyDoc) prettyOpenProtoRule prettyProof prettySapicElement
                 -- prettyIntrVariantsSection prettyOpenProtoRule prettyProof

-- | Pretty print an open theory.
prettyOpenDiffTheory :: HighlightDocument d => OpenDiffTheory -> d
prettyOpenDiffTheory =
    prettyDiffTheory prettySignaturePure
                 (const emptyDoc) prettyEitherRule prettyDiffProof prettyProof
                 -- prettyIntrVariantsSection prettyOpenProtoRule prettyProof

-- | Pretty print a translated Open Theory
prettyOpenTranslatedTheory :: HighlightDocument d => OpenTranslatedTheory -> d
prettyOpenTranslatedTheory =
    prettyTheory prettySignaturePure
                 (const emptyDoc) prettyOpenProtoRule prettyProof emptyString


-- | Pretty print a closed theory.
prettyClosedTheory :: HighlightDocument d => ClosedTheory -> d
prettyClosedTheory thy = if containsManualRuleVariants mergedRules
    then
      prettyTheory prettySignatureWithMaude
                       ppInjectiveFactInsts
                       -- (prettyIntrVariantsSection . intruderRules . L.get crcRules)
                       prettyOpenProtoRuleAsClosedRule
                       prettyIncrementalProof
                       emptyString
                       thy'
    else
      prettyTheory prettySignatureWithMaude
               ppInjectiveFactInsts
               -- (prettyIntrVariantsSection . intruderRules . L.get crcRules)
               prettyClosedProtoRule
               prettyIncrementalProof
               emptyString
               thy
  where
    items = L.get thyItems thy
    mergedRules = mergeOpenProtoRules $ map (mapTheoryItem openProtoRule id) items
    thy' :: Theory SignatureWithMaude ClosedRuleCache OpenProtoRule IncrementalProof ()
    thy' = Theory {_thyName=(L.get thyName thy)
            ,_thyHeuristic=(L.get thyHeuristic thy)
            ,_thySignature=(L.get thySignature thy)
            ,_thyCache=(L.get thyCache thy)
            ,_thyItems = mergedRules
            ,_thyOptions =(L.get thyOptions thy)}
    ppInjectiveFactInsts crc =
        case S.toList $ L.get crcInjectiveFactInsts crc of
            []   -> emptyDoc
            tags -> multiComment $ sep
                      [ text "looping facts with injective instances:"
                      , nest 2 $ fsepList (text . showFactTagArity) tags ]

-- | Pretty print a closed diff theory.
prettyClosedDiffTheory :: HighlightDocument d => ClosedDiffTheory -> d
prettyClosedDiffTheory thy = if containsManualRuleVariantsDiff mergedRules
    then
      prettyDiffTheory prettySignatureWithMaude
                 ppInjectiveFactInsts
                 -- (prettyIntrVariantsSection . intruderRules . L.get crcRules)
                 (\_ -> emptyDoc) --prettyClosedEitherRule
                 prettyIncrementalDiffProof
                 prettyIncrementalProof
                 thy'
    else
        prettyDiffTheory prettySignatureWithMaude
                   ppInjectiveFactInsts
                   -- (prettyIntrVariantsSection . intruderRules . L.get crcRules)
                   (\_ -> emptyDoc) --prettyClosedEitherRule
                   prettyIncrementalDiffProof
                   prettyIncrementalProof
                   thy
  where
    items = L.get diffThyItems thy
    mergedRules = mergeLeftRightRulesDiff $ mergeOpenProtoRulesDiff $
       map (mapDiffTheoryItem id (\(x, y) -> (x, (openProtoRule y))) id id) items
    thy' :: DiffTheory SignatureWithMaude ClosedRuleCache DiffProtoRule OpenProtoRule IncrementalDiffProof IncrementalProof
    thy' = DiffTheory {_diffThyName=(L.get diffThyName thy)
            ,_diffThyHeuristic=(L.get diffThyHeuristic thy)
            ,_diffThySignature=(L.get diffThySignature thy)
            ,_diffThyCacheLeft=(L.get diffThyCacheLeft thy)
            ,_diffThyCacheRight=(L.get diffThyCacheRight thy)
            ,_diffThyDiffCacheLeft=(L.get diffThyDiffCacheLeft thy)
            ,_diffThyDiffCacheRight=(L.get diffThyDiffCacheRight thy)
            ,_diffThyItems = mergedRules}
    ppInjectiveFactInsts crc =
        case S.toList $ L.get crcInjectiveFactInsts crc of
            []   -> emptyDoc
            tags -> multiComment $ sep
                      [ text "looping facts with injective instances:"
                      , nest 2 $ fsepList (text . showFactTagArity) tags ]

prettyClosedSummary :: Document d => ClosedTheory -> d
prettyClosedSummary thy =
    vcat lemmaSummaries
  where
    lemmaSummaries = do
        LemmaItem lem  <- L.get thyItems thy
        -- Note that here we are relying on the invariant that all proof steps
        -- with a 'Just' annotation follow from the application of
        -- 'execProofMethod' to their parent and are valid in the sense that
        -- the application of 'execProofMethod' to their method and constraint
        -- system is guaranteed to succeed.
        --
        -- This is guaranteed initially by 'closeTheory' and is (must be)
        -- maintained by the provers being applied to the theory using
        -- 'modifyLemmaProof' or 'proveTheory'. Note that we could check the
        -- proof right before computing its status. This is however quite
        -- expensive, as it requires recomputing all intermediate constraint
        -- systems.
        --
        -- TODO: The whole consruction seems a bit hacky. Think of a more
        -- principled constrution with better correctness guarantees.
        let (status, Sum siz) = foldProof proofStepSummary $ L.get lProof lem
            quantifier = (toSystemTraceQuantifier $ L.get lTraceQuantifier lem)
            analysisType = parens $ prettyTraceQuantifier $ L.get lTraceQuantifier lem
        return $ text (L.get lName lem) <-> analysisType <> colon <->
                 text (showProofStatus quantifier status) <->
                 parens (integer siz <-> text "steps")

    proofStepSummary = proofStepStatus &&& const (Sum (1::Integer))

prettyClosedDiffSummary :: Document d => ClosedDiffTheory -> d
prettyClosedDiffSummary thy =
    (vcat lemmaSummaries) $$ (vcat diffLemmaSummaries)
  where
    lemmaSummaries = do
        EitherLemmaItem (s, lem)  <- L.get diffThyItems thy
        -- Note that here we are relying on the invariant that all proof steps
        -- with a 'Just' annotation follow from the application of
        -- 'execProofMethod' to their parent and are valid in the sense that
        -- the application of 'execProofMethod' to their method and constraint
        -- system is guaranteed to succeed.
        --
        -- This is guaranteed initially by 'closeTheory' and is (must be)
        -- maintained by the provers being applied to the theory using
        -- 'modifyLemmaProof' or 'proveTheory'. Note that we could check the
        -- proof right before computing its status. This is however quite
        -- expensive, as it requires recomputing all intermediate constraint
        -- systems.
        --
        -- TODO: The whole consruction seems a bit hacky. Think of a more
        -- principled constrution with better correctness guarantees.
        let (status, Sum siz) = foldProof proofStepSummary $ L.get lProof lem
            quantifier = (toSystemTraceQuantifier $ L.get lTraceQuantifier lem)
            analysisType = parens $ prettyTraceQuantifier $ L.get lTraceQuantifier lem
        return $ text (show s) <-> text ": " <-> text (L.get lName lem) <-> analysisType <> colon <->
                 text (showProofStatus quantifier status) <->
                 parens (integer siz <-> text "steps")

    diffLemmaSummaries = do
        DiffLemmaItem (lem)  <- L.get diffThyItems thy
        -- Note that here we are relying on the invariant that all proof steps
        -- with a 'Just' annotation follow from the application of
        -- 'execProofMethod' to their parent and are valid in the sense that
        -- the application of 'execProofMethod' to their method and constraint
        -- system is guaranteed to succeed.
        --
        -- This is guaranteed initially by 'closeTheory' and is (must be)
        -- maintained by the provers being applied to the theory using
        -- 'modifyLemmaProof' or 'proveTheory'. Note that we could check the
        -- proof right before computing its status. This is however quite
        -- expensive, as it requires recomputing all intermediate constraint
        -- systems.
        --
        -- TODO: The whole consruction seems a bit hacky. Think of a more
        -- principled constrution with better correctness guarantees.
        let (status, Sum siz) = foldDiffProof diffProofStepSummary $ L.get lDiffProof lem
        return $ text "DiffLemma: " <-> text (L.get lDiffName lem) <-> colon <->
                 text (showDiffProofStatus status) <->
                 parens (integer siz <-> text "steps")

    proofStepSummary = proofStepStatus &&& const (Sum (1::Integer))
    diffProofStepSummary = diffProofStepStatus &&& const (Sum (1::Integer))

-- | Pretty print a 'TraceQuantifier'.
prettyTraceQuantifier :: Document d => TraceQuantifier -> d
prettyTraceQuantifier ExistsTrace = text "exists-trace"
prettyTraceQuantifier AllTraces   = text "all-traces"

-- FIXME: Sort instances into the right files
