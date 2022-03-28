-- FIXME: for functions prove
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

  -- * Convenience exports
  , module Theory.Model
  , module Theory.Proof

  ) where

-- import           Debug.Trace

import           Prelude                             hiding (id, (.))


-- import           Data.Typeable
import           Data.List
import           Data.Maybe
import           Data.Monoid                         (Sum(..))
import qualified Data.Set                            as S

import           Control.Basics
import           Control.Category
import           Control.Parallel.Strategies

import qualified Extension.Data.Label                as L
-- import qualified Data.Label.Total


import           Theory.Model
import           Theory.Sapic
import           Theory.Sapic.Print
import           Theory.Proof
import           Theory.Text.Pretty



import           TheoryObject

import OpenTheory
import ClosedTheory
import Prover
--import Pretty


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
