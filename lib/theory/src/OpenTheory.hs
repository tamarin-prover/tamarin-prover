{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ViewPatterns #-}


module OpenTheory (
    module OpenTheory
    
    ) where

import GHC.Generics
import Control.DeepSeq
import Data.Binary

import           Prelude                             hiding (id, (.))

import           Data.List
import           Data.Maybe
import           Data.Either
import qualified Data.Set                            as S

import           Control.Basics
import           Control.Category
import           Control.Monad.Reader

import           Extension.Data.Label                hiding (get)
import qualified Extension.Data.Label                as L

import           Theory.Model
import           Theory.Proof
import           Theory.Tools.InjectiveFactInstances
import           Theory.Tools.RuleVariants
import           Theory.Tools.IntruderRules

import           Term.Positions

import           Utils.Misc
import Theories
import Safe

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
