{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ViewPatterns #-}

module OpenTheory
  ( module OpenTheory,
    module Theory.ProofSkeleton,
    module Rule,
    module Items.OpenTheoryItem,
  )
where

import Control.Basics
import Control.Category
import Control.Monad.Reader
import Control.Parallel.Strategies
import Data.Either
import Data.List
import Data.Maybe
import Data.Set qualified as S
import Extension.Data.Label hiding (get)
import Extension.Data.Label qualified as L
import Items.OpenTheoryItem
import Pretty
import Rule
import Safe
import Term.Positions
import Theory.Model
import Theory.Proof
import Theory.ProofSkeleton
import Theory.Text.Pretty
import TheoryObject
import Utils.Misc
import Prelude hiding (id, (.))

-- | map TranslationItems to () and keep other items as is
removeTranslationElement :: TheoryItem r p TranslationElement -> TheoryItem r p ()
removeTranslationElement (TranslationItem _) = TranslationItem ()
removeTranslationElement (RuleItem r) = RuleItem r
removeTranslationElement (LemmaItem l) = LemmaItem l
removeTranslationElement (RestrictionItem rl) = RestrictionItem rl
removeTranslationElement (TextItem t) = TextItem t
removeTranslationElement (ConfigBlockItem b) = ConfigBlockItem b
removeTranslationElement (PredicateItem predi) = PredicateItem predi
removeTranslationElement (MacroItem macro) = MacroItem macro

-- | remove TranslationItems from Theory and convert other items to identical item but with unit type for sapic elements
removeTranslationItems :: OpenTheory -> OpenTranslatedTheory
removeTranslationItems thy =
  thy {_thyItems = newThyItems}
  where
    newThyItems = map removeTranslationElement (L.get thyItems thy)

-- open translated theory again
openTranslatedTheory :: OpenTranslatedTheory -> OpenTheory
openTranslatedTheory thy =
  Theory
    { _thyName = (L.get thyName thy),
      _thyInFile = (L.get thyInFile thy),
      _thyHeuristic = (L.get thyHeuristic thy),
      _thyTactic = (L.get thyTactic thy),
      _thySignature = (L.get thySignature thy),
      _thyCache = (L.get thyCache thy),
      _thyItems = newThyItems,
      _thyOptions = (L.get thyOptions thy),
      _thyIsSapic = (L.get thyIsSapic thy)
    }
  where
    newThyItems = mapMaybe addTranslationElement (L.get thyItems thy)
    addTranslationElement :: TheoryItem r p () -> Maybe (TheoryItem r p s)
    addTranslationElement (RuleItem r) = Just $ RuleItem r
    addTranslationElement (LemmaItem l) = Just $ LemmaItem l
    addTranslationElement (RestrictionItem rl) = Just $ RestrictionItem rl
    addTranslationElement (TextItem t) = Just $ TextItem t
    addTranslationElement (ConfigBlockItem b) = Just $ ConfigBlockItem b
    addTranslationElement (PredicateItem predi) = Just $ PredicateItem predi
    addTranslationElement (MacroItem macro) = Just $ MacroItem macro
    addTranslationElement (TranslationItem _) = Nothing

-- | Add an auto-generated sources lemma if possible
addAutoSourcesLemmaDiff ::
  MaudeHandle ->
  String ->
  ClosedRuleCache ->
  ClosedRuleCache ->
  [DiffTheoryItem DiffProtoRule ClosedProtoRule IncrementalDiffProof IncrementalProof] ->
  [DiffTheoryItem DiffProtoRule ClosedProtoRule IncrementalDiffProof IncrementalProof]
addAutoSourcesLemmaDiff hnd lemmaName crcLeft crcRight items =
  diffPart ++ lhsPart ++ rhsPart
  where
    -- We split items into three. DiffRules, DiffLemmas, and DiffTextItems are
    -- kept as is. We apply addAutoSourcesLemma on each side (rules, lemmas and
    -- restrictions), and recompose everything.
    diffPart = mapMaybe f items
      where
        f (DiffRuleItem r) = Just (DiffRuleItem r)
        f (DiffLemmaItem l) = Just (DiffLemmaItem l)
        f (DiffTextItem t) = Just (DiffTextItem t)
        f (DiffConfigBlockItem b) = Just (DiffConfigBlockItem b)
        f _ = Nothing

    lhsPart =
      if containsPartialDeconstructions crcLeft
        then
          mapMaybe (toSide LHS) $
            addAutoSourcesLemma hnd (lemmaName ++ "_LHS") crcLeft $
              mapMaybe (filterItemSide LHS) items
        else
          mapMaybe (toSide LHS) $
            mapMaybe (filterItemSide LHS) items
    rhsPart =
      if containsPartialDeconstructions crcRight
        then
          mapMaybe (toSide RHS) $
            addAutoSourcesLemma hnd (lemmaName ++ "_RHS") crcRight $
              mapMaybe (filterItemSide RHS) items
        else
          mapMaybe (toSide RHS) $
            mapMaybe (filterItemSide RHS) items

    filterItemSide s (EitherRuleItem (s', r)) | s == s' = Just (RuleItem r)
    filterItemSide s (EitherLemmaItem (s', l)) | s == s' = Just (LemmaItem l)
    filterItemSide s (EitherRestrictionItem (s', r)) | s == s' = Just (RestrictionItem r)
    filterItemSide _ _ = Nothing

    toSide s (RuleItem r) = Just $ EitherRuleItem (s, r)
    toSide LHS (LemmaItem l) = Just $ EitherLemmaItem (LHS, addLeftLemma l)
    toSide RHS (LemmaItem l) = Just $ EitherLemmaItem (RHS, addRightLemma l)
    toSide s (RestrictionItem r) = Just $ EitherRestrictionItem (s, r)
    toSide _ (TextItem t) = Just $ DiffTextItem t
    toSide _ (MacroItem m) = Just $ DiffMacroItem m
    toSide _ (ConfigBlockItem b) = Just $ DiffConfigBlockItem b
    -- FIXME: We currently ignore predicates and sapic stuff as they should not
    --        be generated by addAutoSourcesLemma
    toSide _ (PredicateItem _) = Nothing
    toSide _ (TranslationItem _) = Nothing

-- | Add an auto-generated sources lemma if possible
addAutoSourcesLemma ::
  MaudeHandle ->
  String ->
  ClosedRuleCache ->
  [TheoryItem ClosedProtoRule IncrementalProof s] ->
  [TheoryItem ClosedProtoRule IncrementalProof s]
addAutoSourcesLemma hnd lemmaName (ClosedRuleCache _ raw _ _) items =
  -- We only add the lemma if there is no lemma of the same name
  case find lemma items of
    Nothing -> items' ++ [LemmaItem l]
    (Just _) -> items'
  where
    runMaude = (`runReader` hnd)

    -- searching for the lemma
    lemma (LemmaItem (Lemma name _ _ _ _ _ _)) | name == lemmaName = True
    lemma _ = False

    -- build the lemma
    l = fmap skeletonToIncrementalProof $ unprovenLemma lemmaName [SourceLemma] AllTraces formula

    -- extract all rules from theory items
    rules = mapMaybe itemToRule items

    -- compute all encrypted subterms that are output by protocol rules
    allOutConcs :: [(ClosedProtoRule, LNTerm)]
    allOutConcs = do
      ru <- rules
      (_, protoOrOutFactView -> Just t) <- enumConcs $ L.get cprRuleAC ru
      unifyProtC <- concatMap allProtSubterms t
      return (ru, unifyProtC)

    -- compute all fact that are conclusions in protocol rules (not OutFact)
    allOutConcsNotProt :: [(ClosedProtoRule, LNFact)]
    allOutConcsNotProt = do
      ru <- rules
      (_, unifyFactC) <- enumConcs $ L.get cprRuleAC ru
      -- we ignore cases where the fact is OutFact
      guard (getFactTag unifyFactC /= OutFact)
      return (ru, unifyFactC)

    -- We use the raw sources here to generate one lemma to rule them all...
    (items', formula, _) = foldl computeFormula (items, ltrue, []) chains

    -- Generate a list of all cases that contain open chains
    chains =
      concatMap (multiply unsolvedChains . duplicate) $
        concatMap (map snd . getDisj . L.get cdCases) raw

    -- Given a list of theory items, a formula, a source with an open chain,
    -- return an updated list of theory items and an update formula for the sources lemma.
    computeFormula ::
      ([TheoryItem ClosedProtoRule IncrementalProof s], LNFormula, [(RuleInfo ProtoRuleName IntrRuleACInfo, ExtendedPosition)]) ->
      ((NodeConc, NodePrem), System) ->
      ([TheoryItem ClosedProtoRule IncrementalProof s], LNFormula, [(RuleInfo ProtoRuleName IntrRuleACInfo, ExtendedPosition)])
    computeFormula (its, form, done) ((conc, _), source) = (its', form', done')
      where
        -- The new items are the old ones but with added labels
        its' = addLabels inputsAndOutputs its
        -- The new formula is the old one AND the new formula
        form' = addFormula inputsAndOutputs form
        -- The new list of treated cases
        done' = addCases inputsAndOutputs done

        -- Variable causing the open chain
        v = head $ getFactTerms $ nodeConcFact conc source

        -- Compute all rules that contain v, and the position of v inside the input term
        inputRules :: [(ClosedProtoRule, Either LNTerm LNFact, ExtendedPosition)]
        inputRules = concat $ mapMaybe g $ allPrems source
          where
            g (nodeid, pid, tidx, term) = do
              position <- findPos v term
              ruleSys <- nodeRuleSafe nodeid source
              rule <- find ((ruleName ruleSys ==) . ruleName) rules
              premise <- lookupPrem pid $ L.get cprRuleAC rule
              t' <- protoOrInFactView premise
              t <- atMay t' tidx
              return (terms position rule t ++ facts position rule t premise)
              where
                terms position rule t = do
                  -- iterate over all positions found
                  pos <- position
                  return (rule, Left t, (pid, tidx, pos))
                facts position rule t premise = do
                  -- we only consider protocol facts and unprotected terms
                  guard $
                    isProtoFact premise
                      && (isPair t || isAC t || isMsgVar t)
                      -- we only consider facts which are not already solved in the source
                      && ((nodeid, pid) `elem` map fst (unsolvedPremises source))
                  -- iterate over all positions found
                  pos <- position
                  return (rule, Right premise, (pid, tidx, pos))

        -- a list of all input subterms to unify : Left for protected subterm and Right for non protected subterm
        premiseTermU :: [(ClosedProtoRule, Either (LNTerm, LNTerm) LNFact, ExtendedPosition)]
        premiseTermU = mapMaybe f inputRules
          where
            -- cases for protected subterms : we consider the deepest protected subterm
            f (x, Left y, (pidx, tidx, z)) = do
              v' <- y `atPosMay` z
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
              protTerm <-
                if protTerm' == v'
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
                f c@(r, Left _, p) = do
                  guard $ notElem (ruleName r, p) done
                  return c
                f c@(r, Right _, p) = do
                  guard $
                    notElem (ruleName r, p) done
                      && null subtermCasePositions
                  return c
                -- check if there are protected subterms for this variable
                subtermCasePositions = filter (isLeft . snd3) cases

            matchingConclusions rin (Left (unify, vin)) =
              Left
                ( unify,
                  vin,
                  do
                    (rout, tout) <- allOutConcs
                    -- generate fresh instance of conclusion, avoiding the premise variables
                    let fout = tout `renameAvoiding` unify
                    -- we ignore outputs of the same rule
                    guard ((ruleName . L.get cprRuleE) rin /= (ruleName . L.get cprRuleE) rout)
                    -- check whether input and output are unifiable
                    guard (runMaude $ unifiableLNTerms unify fout)
                    return (rout, tout)
                )
            matchingConclusions rin (Right unify) =
              Right
                ( unify,
                  do
                    (rout, fout) <- allOutConcsNotProt
                    -- we ignore outputs of the same rule
                    guard ((ruleName . L.get cprRuleE) rin /= (ruleName . L.get cprRuleE) rout)
                    -- we ignore cases where the output fact and the input fact have different name
                    guard (factTagName (getFactTag unify) == factTagName (getFactTag fout))
                    -- check whether input and output are unifiable
                    let unifout = fout `renameAvoiding` unify
                    guard (runMaude $ unifiableLNFacts unify unifout)
                    return (rout, fout)
                )

        -- construct action facts for the rule annotations and formula
        inputFactTerm pos ru terms var =
          Fact
            { factTag =
                ProtoFact
                  Linear
                  ("AUTO_IN_TERM_" ++ printPosition pos ++ "_" ++ getRuleName (L.get cprRuleAC ru))
                  (1 + length terms),
              factAnnotations = S.empty,
              factTerms = terms ++ [var]
            }
        inputFactFact pos ru terms =
          Fact
            { factTag =
                ProtoFact
                  Linear
                  ("AUTO_IN_FACT_" ++ printFactPosition pos ++ "_" ++ getRuleName (L.get cprRuleAC ru))
                  (length terms),
              factAnnotations = S.empty,
              factTerms = terms
            }
        outputFactTerm pos ru terms =
          Fact
            { factTag =
                ProtoFact
                  Linear
                  ("AUTO_OUT_TERM_" ++ printPosition pos ++ "_" ++ getRuleName (L.get cprRuleAC ru))
                  (length terms),
              factAnnotations = S.empty,
              factTerms = terms
            }
        outputFactFact pos ru terms =
          Fact
            { factTag =
                ProtoFact
                  Linear
                  ("AUTO_OUT_FACT_" ++ printFactPosition pos ++ "_" ++ getRuleName (L.get cprRuleAC ru))
                  (length terms),
              factAnnotations = S.empty,
              factTerms = terms
            }

        -- add labels to rules for typing lemma
        addLabels ::
          [(ClosedProtoRule, Either (LNTerm, LNTerm, [(ClosedProtoRule, LNTerm)]) (LNFact, [(ClosedProtoRule, LNFact)]), ExtendedPosition)] ->
          [TheoryItem ClosedProtoRule IncrementalProof s] ->
          [TheoryItem ClosedProtoRule IncrementalProof s]
        addLabels matches = map update
          where
            update (RuleItem ru) =
              RuleItem $
                foldr up ru $
                  filter ((ruleName ru ==) . ruleName . fst3) acts
              where
                up (r, p, Left (Left (t, v'))) r' = addActionClosedProtoRule r' (inputFactTerm p r [t] v')
                up (r, p, Left (Right f)) r' = addActionClosedProtoRule r' (inputFactFact p r (getFactTerms f))
                up (_, p, Right (r, Left t)) r' = addActionClosedProtoRule r' (outputFactTerm p r [t])
                up (_, p, Right (r, Right f)) r' = addActionClosedProtoRule r' (outputFactFact p r (getFactTerms f))
            update item = item

            acts = concatMap prepare matches
            -- Left Left means Input Term
            -- Left Right means Input Fact
            -- Right Left means Output Term
            -- Right Left means Output Fact
            prepare (r, Left (t, v', tl), p) = (r, p, Left (Left (t, v'))) : map (\(r', t') -> (r', p, Right (r, Left t'))) tl
            prepare (r, Right (f, fl), p) = (r, p, Left (Right f)) : map (\(r', f') -> (r', p, Right (r, Right f'))) fl

        listOfM :: Int -> [String]
        listOfM n = zipWith (++) (replicate n "m") $ fmap show [1 .. n]

        -- add formula to lemma
        addFormula ::
          [(ClosedProtoRule, Either (LNTerm, LNTerm, [(ClosedProtoRule, LNTerm)]) (LNFact, [(ClosedProtoRule, LNFact)]), ExtendedPosition)] ->
          LNFormula ->
          LNFormula
        addFormula matches f = foldr addForm f matches
          where
            addForm ::
              (ClosedProtoRule, Either (LNTerm, LNTerm, [(ClosedProtoRule, LNTerm)]) (LNFact, [(ClosedProtoRule, LNFact)]), ExtendedPosition) ->
              LNFormula ->
              LNFormula
            -- protected subterms: if there are no matching outputs, do add a formula with only KU
            addForm (ru, Left (_, _, []), p) f' =
              f'
                .&&. Qua
                  All
                  ("x", LSortMsg)
                  ( Qua
                      All
                      ("m", LSortMsg)
                      ( Qua
                          All
                          ("i", LSortNode)
                          ( Conn
                              Imp
                              ( Ato
                                  ( Action
                                      (varTerm (Bound 0))
                                      (inputFactTerm p ru [varTerm (Bound 1)] (varTerm (Bound 2)))
                                  )
                              )
                              orKU
                          )
                      )
                  )
            -- protected subterms
            addForm (ru, Left _, p) f' =
              f'
                .&&. Qua
                  All
                  ("x", LSortMsg)
                  ( Qua
                      All
                      ("m", LSortMsg)
                      ( Qua
                          All
                          ("i", LSortNode)
                          ( Conn
                              Imp
                              ( Ato
                                  ( Action
                                      (varTerm (Bound 0))
                                      (inputFactTerm p ru [varTerm (Bound 1)] (varTerm (Bound 2)))
                                  )
                              )
                              (toFactsTerm ru p orKU)
                          )
                      )
                  )
            -- facts: even if there are no matching outputs, do add a formula with "false"
            addForm (ru, Right (m, []), p) f' = f' .&&. formulaMultArity (factArity m)
              where
                formulaMultArity nb =
                  foldr
                    (\h -> Qua All (h, LSortMsg))
                    ( Qua
                        All
                        ("i", LSortNode)
                        ( Conn
                            Imp
                            ( Ato
                                ( Action
                                    (varTerm (Bound 0))
                                    (inputFactFact p ru (listVarTerm (toInteger $ factArity m) 1))
                                )
                            )
                            lfalse
                        )
                    )
                    (listOfM nb)
            -- facts
            addForm (ru, Right (m, outs : _), p) f' = f' .&&. formulaMultArity (factArity m)
              where
                formulaMultArity nb =
                  foldr
                    (\h -> Qua All (h, LSortMsg))
                    ( Qua
                        All
                        ("i", LSortNode)
                        ( Conn
                            Imp
                            ( Ato
                                ( Action
                                    (varTerm (Bound 0))
                                    (inputFactFact p ru (listVarTerm (toInteger $ factArity m) 1))
                                )
                            )
                            (toFactsFact ru p (snd outs))
                        )
                    )
                    (listOfM nb)
            orKU =
              Qua
                Ex
                ("j", LSortNode)
                ( Conn
                    And
                    ( Ato
                        ( Action
                            (varTerm (Bound 0))
                            Fact
                              { factTag = KUFact,
                                factAnnotations = S.empty,
                                factTerms = [varTerm (Bound 3)]
                              }
                        )
                    )
                    (Ato (Less (varTerm (Bound 0)) (varTerm (Bound 1))))
                )
            toFactsTerm ru p f'' =
              Conn
                Or
                f''
                ( Qua
                    Ex
                    ("j", LSortNode)
                    ( Conn
                        And
                        ( Ato
                            ( Action
                                (varTerm (Bound 0))
                                (outputFactTerm p ru [varTerm (Bound 2)])
                            )
                        )
                        (Ato (Less (varTerm (Bound 0)) (varTerm (Bound 1))))
                    )
                )
            toFactsFact ru p outn =
              Qua
                Ex
                ("j", LSortNode)
                ( Conn
                    And
                    ( Ato
                        ( Action
                            (varTerm (Bound 0))
                            (outputFactFact p ru (listVarTerm (toInteger $ 1 + factArity outn) 2))
                        )
                    )
                    (Ato (Less (varTerm (Bound 0)) (varTerm (Bound 1))))
                )
            listVarTerm q s | q == s = [varTerm (Bound q)]
            listVarTerm q s | otherwise = varTerm (Bound q) : listVarTerm (q - 1) s

        -- add all cases (identified by rule name and input variable position) to the list of treated cases
        addCases matches d = d ++ map (\(r, _, p) -> (ruleName r, p)) matches

-- | Add a new process expression.  since expression (and not definitions)
-- could appear several times, checking for doubled occurrence isn't necessary

------------------------------------------------------------------------------
-- Open theory construction / modification
------------------------------------------------------------------------------
defaultOption :: Option
defaultOption = Option False False False False False False False False False S.empty [] 10 5

-- | Default theory
defaultOpenTheory :: Bool -> OpenTheory
defaultOpenTheory flag = Theory "default" "default" [] [] (emptySignaturePure flag) [] [] defaultOption False

-- | Default diff theory
defaultOpenDiffTheory :: Bool -> OpenDiffTheory
defaultOpenDiffTheory flag = DiffTheory "default" "default" [] [] (emptySignaturePure flag) [] [] [] [] [] defaultOption False

-- Add the default Diff lemma to an Open Diff Theory
addDefaultDiffLemma :: OpenDiffTheory -> OpenDiffTheory
addDefaultDiffLemma thy = fromMaybe thy $ addDiffLemma (unprovenDiffLemma "Observational_equivalence" []) thy

-- Add the rule labels to an Open Diff Theory
addProtoRuleLabel :: OpenProtoRule -> OpenProtoRule
addProtoRuleLabel rule = addProtoDiffLabel rule ("DiffProto" ++ (getOpenProtoRuleName rule))

-- Get the left openProtoRules
getLeftProtoRule :: DiffProtoRule -> OpenProtoRule
getLeftProtoRule (DiffProtoRule ruE Nothing) = OpenProtoRule (getLeftRule ruE) []
getLeftProtoRule (DiffProtoRule _ (Just (l, _))) = l

-- Get the rigth openProtoRules
getRightProtoRule :: DiffProtoRule -> OpenProtoRule
getRightProtoRule (DiffProtoRule ruE Nothing) = OpenProtoRule (getRightRule ruE) []
getRightProtoRule (DiffProtoRule _ (Just (_, r))) = r

-- Add the rule labels to an Open Diff Theory
addIntrRuleLabels :: OpenDiffTheory -> OpenDiffTheory
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
    f _ (RuleItem (OpenProtoRule _ _)) = True
    f hasVariants _ = hasVariants

-- | Merges variants of the same protocol rule modulo E
mergeOpenProtoRules :: [TheoryItem OpenProtoRule p s] -> [TheoryItem OpenProtoRule p s]
mergeOpenProtoRules = concatMap (foldr mergeRules []) . groupBy comp
  where
    comp (RuleItem (OpenProtoRule ruE _)) (RuleItem (OpenProtoRule ruE' _)) = ruE == ruE'
    comp (RuleItem _) _ = False
    comp _ (RuleItem _) = False
    comp _ _ = True

    mergeRules (RuleItem r) [] = [RuleItem r]
    mergeRules (RuleItem (OpenProtoRule ruE' ruAC')) [RuleItem (OpenProtoRule ruE ruAC)] | ruE == ruE' = [RuleItem (OpenProtoRule ruE (ruAC' ++ ruAC))]
    mergeRules (RuleItem _) _ = error "Error in mergeOpenProtoRules. Please report bug."
    mergeRules item l = item : l

-- | Returns true if there are DiffProtoRules containing manual instances or variants
containsManualRuleVariantsDiff :: [DiffTheoryItem DiffProtoRule r p p2] -> Bool
containsManualRuleVariantsDiff = foldl f False
  where
    f hasVariants (DiffRuleItem (DiffProtoRule _ Nothing)) = hasVariants
    f _ (DiffRuleItem (DiffProtoRule _ (Just _))) = True
    f hasVariants _ = hasVariants

-- | Merges variants of the same protocol rule modulo E
mergeOpenProtoRulesDiff :: [DiffTheoryItem r OpenProtoRule p p2] -> [DiffTheoryItem r OpenProtoRule p p2]
mergeOpenProtoRulesDiff = concatMap (foldr mergeRules []) . groupBy comp
  where
    comp (EitherRuleItem (s, OpenProtoRule ruE _)) (EitherRuleItem (s', OpenProtoRule ruE' _)) = ruE == ruE' && s == s'
    comp (EitherRuleItem _) _ = False
    comp _ (EitherRuleItem _) = False
    comp _ _ = True

    mergeRules (EitherRuleItem r) [] = [EitherRuleItem r]
    mergeRules (EitherRuleItem (s, OpenProtoRule ruE' ruAC')) [EitherRuleItem (s', OpenProtoRule ruE ruAC)]
      | ruE == ruE' && s == s' = [EitherRuleItem (s, OpenProtoRule ruE (ruAC' ++ ruAC))]
    mergeRules (EitherRuleItem _) _ = error "Error in mergeOpenProtoRulesDiff. Please report bug."
    mergeRules item l = item : l

-- | Merges left and right instances with initial diff rule
mergeLeftRightRulesDiff :: (Show p, Show p2) => [DiffTheoryItem DiffProtoRule OpenProtoRule p p2] -> [DiffTheoryItem DiffProtoRule OpenProtoRule p p2]
mergeLeftRightRulesDiff rs = map clean $ concatMap (foldr mergeRules []) $ groupBy comp' $ sortBy comp rs
  where
    comp (EitherRuleItem (_, OpenProtoRule ruE _)) (EitherRuleItem (_, OpenProtoRule ruE' _)) = compare (ruleName ruE) (ruleName ruE')
    comp (EitherRuleItem (_, OpenProtoRule ruE _)) (DiffRuleItem (DiffProtoRule ruE' _)) = compare (ruleName ruE) (ruleName ruE')
    comp (DiffRuleItem (DiffProtoRule ruE _)) (EitherRuleItem (_, OpenProtoRule ruE' _)) = compare (ruleName ruE) (ruleName ruE')
    comp (DiffRuleItem (DiffProtoRule ruE _)) (DiffRuleItem (DiffProtoRule ruE' _)) = compare (ruleName ruE) (ruleName ruE')
    comp (EitherRuleItem _) _ = LT
    comp _ (EitherRuleItem _) = GT
    comp (DiffRuleItem _) _ = LT
    comp _ (DiffRuleItem _) = GT
    comp _ _ = EQ

    comp' a b = comp a b == EQ

    mergeRules (EitherRuleItem r) [] = [EitherRuleItem r]
    mergeRules (DiffRuleItem r) [] = [DiffRuleItem r]
    mergeRules (EitherRuleItem (s, ru@(OpenProtoRule ruE _))) [EitherRuleItem (s', ru'@(OpenProtoRule ruE' _))]
      | ruleName ruE == ruleName ruE' && s == LHS && s' == RHS = [DiffRuleItem (DiffProtoRule ruE (Just (ru, ru')))]
    mergeRules (EitherRuleItem (s, ru@(OpenProtoRule ruE _))) [EitherRuleItem (s', ru'@(OpenProtoRule ruE' _))]
      | ruleName ruE == ruleName ruE' && s == RHS && s' == LHS = [DiffRuleItem (DiffProtoRule ruE (Just (ru', ru)))]
    mergeRules (EitherRuleItem (_, ru@(OpenProtoRule ruE _))) [DiffRuleItem (DiffProtoRule dru Nothing)]
      | ruleName ruE == ruleName dru = [DiffRuleItem (DiffProtoRule dru (Just (ru, ru)))]
    mergeRules (DiffRuleItem (DiffProtoRule dru Nothing)) [EitherRuleItem (_, ru@(OpenProtoRule ruE _))]
      | ruleName ruE == ruleName dru = [DiffRuleItem (DiffProtoRule dru (Just (ru, ru)))]
    mergeRules (EitherRuleItem (LHS, ru@(OpenProtoRule ruE _))) [DiffRuleItem (DiffProtoRule dru (Just (_, ru')))]
      | ruleName ruE == ruleName dru = [DiffRuleItem (DiffProtoRule dru (Just (ru, ru')))]
    mergeRules (EitherRuleItem (RHS, ru@(OpenProtoRule ruE _))) [DiffRuleItem (DiffProtoRule dru (Just (ru', _)))]
      | ruleName ruE == ruleName dru = [DiffRuleItem (DiffProtoRule dru (Just (ru', ru)))]
    mergeRules (DiffRuleItem (DiffProtoRule dru (Just (_, ru')))) [EitherRuleItem (LHS, ru@(OpenProtoRule ruE _))]
      | ruleName ruE == ruleName dru = [DiffRuleItem (DiffProtoRule dru (Just (ru, ru')))]
    mergeRules (DiffRuleItem (DiffProtoRule dru (Just (ru', _)))) [EitherRuleItem (RHS, ru@(OpenProtoRule ruE _))]
      | ruleName ruE == ruleName dru = [DiffRuleItem (DiffProtoRule dru (Just (ru', ru)))]
    mergeRules (DiffRuleItem (DiffProtoRule dru (Just (lr, rr)))) [DiffRuleItem (DiffProtoRule dru' Nothing)]
      | ruleName dru == ruleName dru' = [DiffRuleItem (DiffProtoRule dru (Just (lr, rr)))]
    mergeRules (DiffRuleItem (DiffProtoRule dru Nothing)) [DiffRuleItem (DiffProtoRule dru' (Just (lr, rr)))]
      | ruleName dru == ruleName dru' = [DiffRuleItem (DiffProtoRule dru (Just (lr, rr)))]
    mergeRules (DiffRuleItem (DiffProtoRule dru (Just (lr, rr)))) [DiffRuleItem (DiffProtoRule dru' (Just (lr', rr')))]
      | ruleName dru == ruleName dru' && equalOpenRuleUpToDiffAnnotation lr lr' && equalOpenRuleUpToDiffAnnotation rr rr' = [DiffRuleItem (DiffProtoRule dru (Just (lr, rr)))]
    mergeRules (EitherRuleItem _) _ = error "Error in mergeLeftRightRulesDiff. Please report bug."
    mergeRules (DiffRuleItem _) _ = error "Error in mergeLeftRightRulesDiff. Please report bug."
    mergeRules item l = item : l

    clean (DiffRuleItem (DiffProtoRule ruE (Just (OpenProtoRule ruEL [], OpenProtoRule ruER []))))
      | getLeftRule ruE `equalRuleUpToDiffAnnotation` ruEL
          && getRightRule ruE `equalRuleUpToDiffAnnotation` ruER =
          DiffRuleItem (DiffProtoRule ruE Nothing)
    clean i = i

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
    allRuleNamesAreDifferent =
      (S.size (S.fromList (ruleName ruE : map ruleName ruAC)))
        == ((length ruAC) + 1)

-- | Add a new protocol rules. Fails, if a protocol rule with the same name
-- exists.
addOpenProtoDiffRule :: DiffProtoRule -> OpenDiffTheory -> Maybe OpenDiffTheory
addOpenProtoDiffRule ru@(DiffProtoRule _ Nothing) thy = do
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
    allRuleNamesAreDifferent (OpenProtoRule ruE ruAC) =
      (S.size (S.fromList (ruleName ruE : map ruleName ruAC)))
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
    . L.modify
      thyItems
      ( \items -> do
          item <- items
          return $ case item of
            LemmaItem lem ->
              LemmaItem $ L.modify lProof stripProofAnnotations $ lem
            RuleItem _ -> item
            TextItem _ -> item
            ConfigBlockItem _ -> item
            RestrictionItem _ -> item
            TranslationItem _ -> item
            PredicateItem _ -> item
            MacroItem _ -> item
      )
  where
    stripProofAnnotations :: ProofSkeleton -> ProofSkeleton
    stripProofAnnotations = fmap stripProofStepAnnotations
    stripProofStepAnnotations (ProofStep method ()) =
      ProofStep
        ( case method of
            Sorry _ -> Sorry Nothing
            Finished (Contradictory _) -> Finished (Contradictory Nothing)
            _ -> method
        )
        ()

-- | Pretty print an open rule together with its assertion soundness proof.
prettyOpenProtoRule :: (HighlightDocument d) => OpenProtoRule -> d
prettyOpenProtoRule (OpenProtoRule ruE []) = prettyProtoRuleE ruE
prettyOpenProtoRule (OpenProtoRule _ [ruAC]) = prettyProtoRuleACasE ruAC
prettyOpenProtoRule (OpenProtoRule ruE variants) =
  prettyProtoRuleE ruE
    $-$ nest 1 (kwVariants $-$ nest 1 (ppList prettyProtoRuleAC variants))
  where
    ppList _ [] = emptyDoc
    ppList pp [x] = pp x
    ppList pp (x : xr) = pp x $-$ comma $-$ ppList pp xr

-- | Pretty print an open rule together with its assertion soundness proof.
prettyOpenProtoRuleAsClosedRule :: (HighlightDocument d) => OpenProtoRule -> d
prettyOpenProtoRuleAsClosedRule (OpenProtoRule ruE []) =
  prettyProtoRuleE ruE
    $--$
    -- cannot show loop breakers here, as we do not have the information
    ( nest 2 $
        emptyDoc
          $-$ multiComment_ ["has exactly the trivial AC variant"]
    )
prettyOpenProtoRuleAsClosedRule (OpenProtoRule _ [ruAC@(Rule (ProtoRuleACInfo _ _ (Disj disj) _) _ _ _ _)]) =
  prettyProtoRuleACasE ruAC
    $--$ ( nest 2 $
             prettyLoopBreakers (L.get rInfo ruAC)
               $-$ if length disj == 1
                 then multiComment_ ["has exactly the trivial AC variant"]
                 else multiComment $ prettyProtoRuleAC ruAC
         )
prettyOpenProtoRuleAsClosedRule (OpenProtoRule ruE variants) =
  prettyProtoRuleE ruE
    $-$ nest 1 (kwVariants $-$ nest 1 (ppList prettyProtoRuleAC variants))
  where
    ppList _ [] = emptyDoc
    ppList pp [x] = pp x
    ppList pp (x : xr) = pp x $-$ comma $-$ ppList pp xr

-- | Pretty print a diff rule
prettyDiffRule :: (HighlightDocument d) => DiffProtoRule -> d
prettyDiffRule (DiffProtoRule ruE Nothing) = prettyProtoRuleE ruE
prettyDiffRule (DiffProtoRule ruE (Just (ruL, ruR))) =
  prettyProtoRuleE ruE
    $-$ nest
      1
      ( kwLeft
          $-$ nest 1 (prettyOpenProtoRule ruL)
          $-$ kwRight
          $-$ nest 1 (prettyOpenProtoRule ruR)
      )

-- | Pretty print an either rule
prettyEitherRule :: (HighlightDocument d) => (Side, OpenProtoRule) -> d
prettyEitherRule (_, p) = prettyProtoRuleE $ L.get oprRuleE p

-- | Pretty print an open theory.
prettyOpenTheory :: (HighlightDocument d) => OpenTheory -> d
prettyOpenTheory thy =
  prettyTheory
    prettySignaturePure
    (const emptyDoc)
    prettyOpenProtoRule
    prettyProof
    prettyTranslationElement
    thy
  where
    -- prettyIntrVariantsSection prettyOpenProtoRule prettyProof

    funsyms = S.fromList $ map fst' $ theoryFunctionTypingInfos thy
    -- function symbols that are printed by sapic printer already
    fst' (a, _, _) = a

-- | Pretty print an open theory.
prettyOpenDiffTheory :: (HighlightDocument d) => OpenDiffTheory -> d
prettyOpenDiffTheory =
  prettyDiffTheory
    prettySignaturePure
    (const emptyDoc)
    prettyEitherRule
    prettyDiffProof
    prettyProof

-- prettyIntrVariantsSection prettyOpenProtoRule prettyProof

-- | Pretty print a translated Open Theory
prettyOpenTranslatedTheory :: (HighlightDocument d) => OpenTranslatedTheory -> d
prettyOpenTranslatedTheory =
  prettyTheory
    prettySignaturePure
    (const emptyDoc)
    prettyOpenProtoRule
    prettyProof
    emptyString

-- | Pretty print a diff theory.
prettyDiffTheory ::
  (HighlightDocument d) =>
  (sig -> d) ->
  (c -> d) ->
  ((Side, r2) -> d) ->
  (p -> d) ->
  (p2 -> d) ->
  DiffTheory sig c DiffProtoRule r2 p p2 ->
  d
prettyDiffTheory ppSig ppCache ppRule ppDiffPrf ppPrf thy =
  vsep $
    [ kwTheoryHeader $ text $ L.get diffThyName thy,
      lineComment_ "Function signature and definition of the equational theory E",
      ppSig $ L.get diffThySignature thy,
      if thyT == [] then text "" else vcat $ map prettyTactic thyT,
      if thyH == [] then text "" else text "heuristic: " <> text (prettyGoalRankings thyH),
      prettyMacros $ diffTheoryMacros thy,
      ppCache $ L.get diffThyCacheLeft thy,
      ppCache $ L.get diffThyCacheRight thy,
      ppCache $ L.get diffThyDiffCacheLeft thy,
      ppCache $ L.get diffThyDiffCacheRight thy
    ]
      ++ parMap rdeepseq ppItem (L.get diffThyItems thy)
      ++ [kwEnd]
  where
    ppItem =
      foldDiffTheoryItem
        prettyDiffRule
        ppRule
        (prettyDiffLemma ppDiffPrf)
        (prettyEitherLemma ppPrf)
        prettyEitherRestriction
        (const emptyDoc)
        (uncurry prettyFormalComment)
        prettyConfigBlock
    thyH = L.get diffThyHeuristic thy
    thyT = L.get diffThyTactic thy
