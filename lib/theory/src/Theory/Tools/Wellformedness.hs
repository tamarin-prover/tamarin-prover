{-# LANGUAGE ViewPatterns     #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections    #-}
-- |
-- Copyright   : (c) 2010-2012 Simon Meier & Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Wellformedness checks for intruder variants, protocol rules, and
-- properties.
--
-- The following checks are/should be performed
-- (FIXME: compare the list below to what is really implemented.)
--
--   [protocol rules]
--
--     1. no fresh names in rule. (protocol cond. 1)
--     ==> freshNamesReport
--
--     2. no Out or K facts in premises. (protocol cond. 2)
--     ==> factReports
--
--     3. no Fr, In, or K facts in conclusions. (protocol cond. 3)
--     ==> factReports
--
--     4. vars(rhs) subset of vars(lhs) u V_Pub
--     ==> multRestrictedReport
--
--     5. lhs does not contain reducible function symbols (*-restricted (a))
--     ==> multRestrictedReport
--
--     6. rhs does not contain * (*-restricted (b))
--     ==> multRestrictedReport
--
--     7. all facts are used with the same arity.
--
--     8. fr, in, and out, facts are used with arity 1.
--
--     9. fr facts are used with a variable of sort msg or sort fresh
--
--     10. fresh facts of the same rule contain different variables. [TODO]
--
--     11. no protocol fact uses a reserved name =>
--        [TODO] change parser to ensure this and pretty printer to show this.
--
--     12. (diff only) No rule uses a fact starting with 'DiffProto' or 'DiffIntr'
--
--     13. LSortNat is well typed
--
--   [security properties]
--
--     1. all facts occur with the same arity in the action of some
--        protocol rule.
--
--     2. no node variable is used in a message position and vice versa.
--
--
module Theory.Tools.Wellformedness (

  -- * Wellformedness checking
    WfErrorReport
  , checkWellformedness
  , checkWellformednessDiff

  , prettyWfErrorReport
  , underlineTopic

  , formulaFacts
  , formulaTerms
  ) where

import Rule

import           Prelude                     hiding (id, (.))

import           Control.Basics
import           Control.Category
import           Data.Char
import           Data.Generics.Uniplate.Data (universeBi)
import           Data.Label
import           Data.List                   (intersperse,(\\), intercalate, isPrefixOf)
import           Data.Maybe
-- import           Data.Monoid                 (mappend, mempty)
import qualified Data.Set                    as S
-- import           Data.Traversable            (traverse)

import           Control.Monad.Bind

import           Extension.Prelude
import           Term.LTerm

import           Term.Maude.Signature
import           Theory
import           Theory.Text.Pretty
import           Theory.Sapic
import           Theory.Tools.RuleVariants
import           Safe                        (lastMay)
import           Items.OptionItem            (lemmasToProve)
import           TheoryObject                (diffThyOptions, prettyVarList, theoryMacros, diffTheoryMacros)
import           Utils.Misc
import           Term.Macro

import Term.SubtermRule ( CtxtStRule, prettyCtxtStRule, filterNonSubtermCtxtRule)


------------------------------------------------------------------------------
-- Types for error reports
------------------------------------------------------------------------------

type Topic         = String
type WfError       = (Topic, Doc)
type WfErrorReport = [WfError]
type RuleAndFact   = (String, LNFact) -- String : name of rule where the fact is
                                      -- LNFact : the rule

prettyWfErrorReport :: WfErrorReport -> Doc
prettyWfErrorReport =
    vcat . intersperse (text "") . map ppTopic . groupOn fst
  where
    ppTopic []                 = error "prettyWfErrorReport: groupOn returned empty list"
    ppTopic errs@((topic,_):_) =
      text topic $-$
      (nest 2 . vcat . intersperse (text "") $ map snd errs)


------------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------------

-- | All protocol rules of a theory.
-- thyProtoRules :: OpenTranslatedTheory ->
thyProtoRules :: OpenTranslatedTheory -> [ProtoRuleE]
thyProtoRules thy = [ applyMacroInRule (theoryMacros thy) (get oprRuleE ru) | RuleItem ru <- get thyItems thy ]

-- | All protocol rules of a theory.
-- thyProtoRules :: OpenTranslatedTheory ->
diffThyProtoRules :: OpenDiffTheory -> [ProtoRuleE]
diffThyProtoRules thy = [ applyMacroInRule (diffTheoryMacros thy) (get dprRule ru) | DiffRuleItem ru <- get diffThyItems thy ]

-- | Lower-case a string.
lowerCase :: String -> String
lowerCase = map toLower

-- | Pretty-print a comma, separated list of 'LNTerms's.
prettyLNTermList :: Document d => [LNTerm] -> d
prettyLNTermList = fsep . punctuate comma . map prettyLNTerm

-- | Wrap strings at word boundaries.
wrappedText :: Document d => String -> d
wrappedText = fsep . map text . words

-- | Clashes
clashesOn :: (Ord b, Ord c)
          => (a -> b) -- ^ This projection
          -> (a -> c) -- ^ must determine this projection.
          -> [a] -> [[a]]
clashesOn f g xs = do
    grp <- groupOn f $ sortOn f xs
    guard (length (sortednubOn g grp) >= 2)
    return $ sortednubOn g grp

-- | Nice quoting.
quote :: String -> String
quote cs = '`' : cs ++ "'"

-- | add double underline to the topic
underlineTopic :: String -> String
underlineTopic topic = topic ++"\n" ++
                      (concat $ take (length topic) $ repeat "=")
                      ++"\n"

-- | To get the informations of a fact
factInfo :: Fact t -> (FactTag, Int, Multiplicity)
factInfo fa    = (factTag fa, factArity fa, factMultiplicity fa)

-- | To bind a list of premise facts with their most similar conclusion facts. The most similar fact
-- | has the minimual editing distance and the value of the distance must be
-- | between between 1 and 3. If no such fact exists, Nothing is returned.
mostSimilarName :: [RuleAndFact]->[RuleAndFact]
                  ->[(RuleAndFact, Maybe RuleAndFact)]
mostSimilarName lhs rhs =
    map (isSimilar . flip minimalEdFact rhs) $ removeSame lhs rhs
  where
    -- To remove all the facts in lhs and also in rhs
    removeSame :: [RuleAndFact] -> [RuleAndFact] ->[RuleAndFact]
    removeSame l r = filter (\x -> factInfo (snd x) `notElem` rhsFacts) l
      where
        rhsFacts = map (factInfo . snd) r

    -- to verify if the names of two facts are similar enough
    isSimilar :: (RuleAndFact, Maybe (RuleAndFact, Int))
                ->(RuleAndFact, Maybe RuleAndFact)
    isSimilar (rf, Nothing)                = (rf, Nothing)
    isSimilar (rf, Just (rfs, i)) | i <= 3 = (rf, Just rfs)
    isSimilar (rf, _)                      = (rf, Nothing)

    -- to get the fact in rhs which has the minimum editing distance
    -- with a given fact and the distance between the two facts
    minimalEdFact :: RuleAndFact->[RuleAndFact]->(RuleAndFact, Maybe (RuleAndFact, Int))
    minimalEdFact lFact rFacts      =  (lFact, listToMaybe $ sortOn snd $ edDistances lFact rFacts)

    -- Calculates the distance between a given fact and the facts of a list,
    -- also save each fact in the list and his editing distance to the given fact
    -- as a tuple
    edDistances :: RuleAndFact-> [RuleAndFact] -> [(RuleAndFact, Int)]
    edDistances s li = map (\x ->(,) x $ distance (snd s) x) li
      where
        distance factL factR  = editDistance (getName factL) (getName $ snd factR)
        getName fact          = factTagName $ getFactTag fact


-- Report a protocol fact occurs in an LHS but not in any RHS
factLhsOccurNoRhs' :: [ProtoRuleE] -> WfErrorReport
factLhsOccurNoRhs' ru =
  case factLhsNoRhs of
    []            -> []
    facts         -> return $ (,) (underlineTopic topic) $ numbered' $
                      map (nest 2 . showRuleAndFact ) facts
  where
    topic = "Facts occur in the left-hand-side but not in any right-hand-side "
    -- all the protocol facts in lhs but not in any rhs
    factLhsNoRhs = getFactLhsNoRhs (getFacts rPrems ru) (getFacts rConcs ru)

    -- get all the facts by their sides
    getFacts s = map (\x-> (,) (showRuleCaseName x)
                        $ filter isProtoFact $ get s x)

    -- for each fact on LHS, get his most similar fact in RHS
    getFactLhsNoRhs :: [(String,[LNFact])]->[(String,[LNFact])]
                      ->[(RuleAndFact,Maybe RuleAndFact)]
    getFactLhsNoRhs lfacts rfacts = mostSimilarName (regroup lfacts)
                                  (regroup rfacts)

    regroup :: [(String,[LNFact])] -> [RuleAndFact]
    regroup = foldr (\x acc -> zip (repeat $ fst x) (snd x)
                    ++ acc) []

    showRuleAndFact ((ruName,factL),Just (ruNameR,factR)) =
      text  ("in rule " ++ show ruName ++": "
              ++ showFactInfo (factInfo factL)
              ++ ". Perhaps you want to use the fact in rule "
              ++ show ruNameR ++": "
              ++ showFactInfo (factInfo factR)  )
    showRuleAndFact ((ruName,factL),Nothing) =
      text  ("in rule " ++ show ruName ++": "
              ++ showFactInfo (factInfo factL))
    showFactInfo (tag,arity,multi) =
              " factName "++quote (factTagName tag)
              ++ " arity: "++show arity
              ++ " multiplicity: "++show multi

------------------------------------------------------------------------------
-- Checks
------------------------------------------------------------------------------

--- | Check that the protocol rules are well-formed.
sortsClashCheck :: HasFrees t => String -> t -> WfErrorReport
sortsClashCheck info t = case clashesOn removeSort id $ frees t of
    [] -> []
    cs -> return
            ( topic++reason
            , text info $-$ nest 2 (numbered' $ map prettyVarList cs)
            )
  where
    topic = (underlineTopic "Variable with mismatching sorts or capitalization")++"\n"
    reason = "Possible reasons:\n"++
              "1. Identifiers are case sensitive, i.e.,"++
              "'x' and 'X' are considered to be different.\n"++
              "2. The same holds for sorts:, "++
              "i.e., '$x', 'x', and '~x' are considered to be different.\n"
    removeSort lv = (lowerCase (lvarName lv), lvarIdx lv)

-- | Report on sort clashes.
ruleSortsReport :: OpenTranslatedTheory -> WfErrorReport
ruleSortsReport thy = do
    ru <- thyProtoRules thy
    sortsClashCheck ("rule " ++ quote (showRuleCaseName ru) ++
                     ": ") ru


-- | bind quantified variables with substBound and return all terms from a formula
boundTerms :: [(Integer,LVar)] -> LNGuarded -> [BLTerm]
boundTerms l (substBound l -> GAto a) = atomTerms a
boundTerms l (GDisj disj)             = concatMap (boundTerms l) disj
boundTerms l (GConj conj)             = concatMap (boundTerms l) conj
boundTerms l (GGuarded _ ss _ gf)     = boundTerms extendedVarAssignment gf
  where
    extendedVarAssignment = zip [0..] [LVar name sort 0 | (name, sort) <- reverse ss] ++ l
boundTerms _ _                        = [] --cannot happen

-- | check nat-Sorting (i.e., below + is only nat)
nonWellSorted :: LNTerm -> [LNTerm]
nonWellSorted (viewTerm2 -> FNatPlus list) = concatMap notOnlyNat list
  where
    notOnlyNat :: LNTerm -> [LNTerm]
    notOnlyNat (viewTerm2 -> FNatPlus l) = concatMap notOnlyNat l
    notOnlyNat (viewTerm2 -> NatOne) = []
    notOnlyNat t | isNatVar t = []
    notOnlyNat t = [t]
nonWellSorted (viewTerm2 -> NatOne) = []
nonWellSorted (viewTerm -> Lit _) = []
nonWellSorted (viewTerm -> FApp _ ts) = concatMap nonWellSorted ts
-- TODO: nat let's are only nats (%x = h(n) is forbidden) (unimportant)

-- | safe version of bTermToLTerm if variables are not important
bTermToLTermStupid :: BLTerm -> LNTerm
bTermToLTermStupid = fmapTerm (fmap (foldBVar (LVar "boundVar" LSortMsg) id))

-- | typed version of formulaToGuarded
formulaToGuardedTyped :: LNFormula -> Either Doc LNGuarded
formulaToGuardedTyped = formulaToGuarded

-- | generate nat sort errors
natSortErrors :: [LNTerm] -> WfErrorReport
natSortErrors itemsTerms = [ (underlineTopic "Nat Sorts", prettyLNTerm err <> text " in term " <> prettyLNTerm t <> text " must be of sort nat") | t <- itemsTerms, err <- nonWellSorted t]

-- | check nat-Sorting (i.e., below + is only nat)
natWellSortedReport :: OpenTranslatedTheory -> WfErrorReport
natWellSortedReport thy = natSortErrors itemsTerms
  where
    itemsTerms = map bTermToLTermStupid (concat allRuleTerms ++ concatMap getItemTerms (get thyItems thy))

    getItemTerms :: TheoryItem OpenProtoRule ProofSkeleton () -> [BLTerm]
    -- getItemTerms (RuleItem (get oprRuleE -> r)) = map lTermToBTerm $ concatMap factTerms (get rPrems r ++ get rActs r ++ get rConcs r)
    -- FIXED: use thyProtoRules as below to ensure macros have been applied correctly
    getItemTerms (LemmaItem (formulaToGuardedTyped . get lFormula -> Right f)) = boundTerms [] f
    getItemTerms (RestrictionItem (formulaToGuardedTyped . get rstrFormula -> Right f)) = boundTerms [] f
    getItemTerms (PredicateItem (formulaToGuardedTyped . get pFormula -> Right p)) = boundTerms [] p
    getItemTerms _ = []

    allRuleTerms = map getRuleTerms $ thyProtoRules thy
    getRuleTerms r = map lTermToBTerm $ concatMap factTerms (get rPrems r ++ get rActs r ++ get rConcs r)

-- | check nat-Sorting (i.e., below + is only nat)
natWellSortedReportDiff :: OpenDiffTheory -> WfErrorReport
natWellSortedReportDiff thy = natSortErrors itemsTerms
  where
    itemsTerms = map bTermToLTermStupid (concat allRuleTerms ++ concatMap getItemTerms (get diffThyItems thy))

    getItemTerms :: DiffTheoryItem DiffProtoRule OpenProtoRule DiffProofSkeleton ProofSkeleton -> [BLTerm]
    -- getItemTerms (DiffRuleItem (get dprRule -> r)) = map lTermToBTerm $ concatMap factTerms (get rPrems r ++ get rActs r ++ get rConcs r)
    -- FIXED: use diffThyProtoRules as below to ensure macros have been applied correctly
    getItemTerms (EitherRuleItem (_, get oprRuleE -> r)) = map lTermToBTerm $ concatMap factTerms (get rPrems r ++ get rActs r ++ get rConcs r)
    getItemTerms (EitherLemmaItem (_, formulaToGuardedTyped . get lFormula -> Right f)) = boundTerms [] f
    getItemTerms (EitherRestrictionItem (_, formulaToGuardedTyped . get rstrFormula -> Right f)) = boundTerms [] f
    getItemTerms _ = []

    allRuleTerms = map getRuleTerms $ diffThyProtoRules thy
    getRuleTerms r = map lTermToBTerm $ concatMap factTerms (get rPrems r ++ get rActs r ++ get rConcs r)


--- | Check that the protocol rule variants are correct.
variantsCheck :: MaudeHandle -> [Macro] -> String -> OpenProtoRule -> WfErrorReport
variantsCheck _   _      _    (OpenProtoRule _ [])     = []
variantsCheck hnd macros info (OpenProtoRule ruE ruAC) =
  if sameVariantsUpToActions ruAC recomputedVariants then
    []
  else
    return $
            ( (underlineTopic "Variants")
            , text info $-$ (nest 2 $ (numbered' $ (map prettyProtoRuleAC ruAC)))
              $--$ text "Recomputed variants: " $--$
              (nest 2 $ (numbered' $ map prettyProtoRuleAC recomputedVariants))
            )
  where
    recomputedVariants = map (get cprRuleAC) $ unfoldRuleVariants $
      ClosedProtoRule ruE (variantsProtoRule hnd (applyMacroInRule macros ruE))
    sameVariantsUpToActions parsed computed = all (\x -> any (equalUpToAddedActions x) computed) parsed

-- | Report on missing or different variants.
ruleVariantsReport :: SignatureWithMaude -> OpenTranslatedTheory -> WfErrorReport
ruleVariantsReport sig thy = do
    ru <- [ ru | RuleItem ru <- get thyItems thy ]
    variantsCheck hnd (theoryMacros thy) ("Rule " ++ quote (showRuleCaseName (get oprRuleE ru)) ++
                     " cannot confirm manual variants:") ru
  where
    hnd = get sigmMaudeHandle sig

-- | Report on missing or different variants in case of diff rules.
ruleVariantsReportDiff :: SignatureWithMaude -> OpenDiffTheory -> WfErrorReport
ruleVariantsReportDiff sig thy = do
    lrRu <- [ get dprLeftRight ru | DiffRuleItem ru <- get diffThyItems thy ]
    case lrRu of
      Just (lr, rr) -> (variantsCheck hnd (diffTheoryMacros thy) ("Left rule " ++ quote (showRuleCaseName (get oprRuleE lr)) ++
                     " cannot confirm manual variants:") lr) ++
                      (variantsCheck hnd (diffTheoryMacros thy) ("Right rule " ++ quote (showRuleCaseName (get oprRuleE rr)) ++
                      " cannot confirm manual variants:") rr)
      Nothing -> []
  where
    hnd = get sigmMaudeHandle sig

-- | Report on inconsistent left/right rules. This does not check the variants (done by ruleVariantsReportDiff).
leftRightRuleReportDiff :: OpenDiffTheory -> WfErrorReport
leftRightRuleReportDiff thy = do
    ru <- [ ru | DiffRuleItem ru <- get diffThyItems thy ]
    case get dprLeftRight ru of
      Just ((OpenProtoRule lr _), _) | not (equalUpToAddedActions lr (getLeftRule (applyMacroInRule (diffTheoryMacros thy) (get dprRule ru)))) -> return $
              ( (underlineTopic "Left rule")
              , text "Inconsistent left rule" $-$ (nest 2 $ prettyProtoRuleE lr)
                $--$ text "w.r.t." $--$
                (nest 2 $ prettyProtoRuleE (get dprRule ru))
              )
      Just (_, (OpenProtoRule rr _)) | not (equalUpToAddedActions rr (getRightRule (applyMacroInRule (diffTheoryMacros thy) (get dprRule ru)))) -> return $
              ( (underlineTopic "Right rule")
              , text "Inconsistent right rule" $-$ (nest 2 $ prettyProtoRuleE rr)
                $--$ text "w.r.t." $--$
                (nest 2 $ prettyProtoRuleE (get dprRule ru))
              )
      Just (_, _) | otherwise -> []
      Nothing -> []

-- | Report on sort clashes.
ruleSortsReportDiff :: OpenDiffTheory -> WfErrorReport
ruleSortsReportDiff thy = do
    ru <- diffThyProtoRules thy
    sortsClashCheck ("rule " ++ quote (showRuleCaseName ru) ++
                     ":") ru

-- -- | Report on rule name clashes.
-- -- Unnecessary, is already checked during parsing!
-- ruleNameReportDiff :: OpenDiffTheory -> WfErrorReport
-- ruleNameReportDiff thy =
--   nameClashCheck ("clashing rule names:") (diffThyProtoRules thy)
--
--
-- --- | Check that the protocol rules are well-formed.
-- nameClashCheck :: String -> [(ProtoRuleE)] -> WfErrorReport
-- nameClashCheck info t = case clashes ruleName t of
--     [] -> []
--     cs -> return $
--             ( "names"
--             , text info $-$ (nest 2 $ numbered' $ map (text . getRuleNameDiff) cs)
--             )
--     where
--       ruleName r = map toLower $ getRuleNameDiff r
--       grp f xs = groupOn f $ sortOn f xs
--       clashes f xs = map head $ filter (\x -> length x >= 2) (grp f xs)

-- | Report on fresh names.
freshNamesReport' :: [ProtoRuleE] -> WfErrorReport
freshNamesReport' rules = do
    ru <- rules
    case filter ((LSortFresh ==) . sortOfName) $ universeBi ru of
      []    -> []
      names -> return $ (,) (underlineTopic "Fresh public constants") $ fsep $
          text ( "rule " ++ quote (showRuleCaseName ru) ++ ": " ++
                 "fresh public constants are not allowed:" )
        : punctuate comma (map (nest 2 . text . show) names)

-- | Report on fresh names.
freshNamesReport :: OpenTranslatedTheory -> WfErrorReport
freshNamesReport thy = freshNamesReport' $ thyProtoRules thy

-- | Report on fresh names.
freshNamesReportDiff :: OpenDiffTheory -> WfErrorReport
freshNamesReportDiff thy = freshNamesReport' $ diffThyProtoRules thy

-- | Report on capitalization of public names.
publicNamesReport' :: [ProtoRuleE] -> WfErrorReport
publicNamesReport' rules =
    case findClashes publicNames of
      []      -> []
      clashes -> return $ (,) (topic++notif) $ numbered' $
          map (nest 2 . fsep . punctuate comma . map ppRuleAndName. (groupOn fst)) clashes
  where
    topic       = underlineTopic "Public constants with mismatching capitalization" ++ "\n"
    notif       = "Identifiers are case-sensitive, "++
                  "mismatched capitalizations are considered as different, "++
                  "i.e., 'ID' is different from 'id'. "++
                  "Check the capitalization of your identifiers.\n"
    publicNames = do
        ru <- rules
        (,) (showRuleCaseName ru) <$>
            filter ((LSortPub ==) . sortOfName) (universeBi ru)
    findClashes   = clashesOn (map toLower . show . snd) (show . snd)
    ppRuleAndName ((ruName, pub):rest) =
        text $ "rule " ++ show ruName ++ ": "++" name " ++
         show (pub) ++ concatMap ((", " ++) . show . snd) rest
    ppRuleAndName [] = text "Error: empty clash"

publicNamesReport :: OpenTranslatedTheory -> WfErrorReport
publicNamesReport thy = publicNamesReport' $ thyProtoRules thy

-- | Report on capitalization of public names.
publicNamesReportDiff :: OpenDiffTheory -> WfErrorReport
publicNamesReportDiff thy = publicNamesReport' $ diffThyProtoRules thy

-- | Check whether a rule has unbound variables.
unboundCheck :: Document b => String -> Rule ProtoRuleEInfo -> [([Char], b)]
unboundCheck info ru
    | null unboundVars = []
    | otherwise        = return $
        ( underlineTopic "Unbound variables"
        , text info $-$ nest 2 (prettyVarList unboundVars) )
  where
    boundVars   = S.fromList $ frees (get rPrems ru)
    originatesFromLookup v = match v $ ruleProcess $ get preAttributes $ get rInfo ru
    match v (Just (ProcessComb (Lookup _ v') _ _ _))  = v == slvar v'
    match _ _ = False
    unboundVars = do
        v <- frees (get rConcs ru, get rActs ru, get rInfo ru)
        guard $ not (lvarSort v == LSortPub || v `S.member` boundVars || originatesFromLookup v)
        return v

-- | Report on sort clashes.
unboundReport :: OpenTranslatedTheory -> WfErrorReport
unboundReport thy = do
    ru <- thyProtoRules thy
    unboundCheck ("rule " ++ quote (showRuleCaseName ru) ++
                  " has unbound variables: "
                 ) ru

-- | Report on sort clashes.
unboundReportDiff :: OpenDiffTheory -> WfErrorReport
unboundReportDiff thy = do
    ru <- diffThyProtoRules thy
    unboundCheck ("rule " ++ quote (showRuleCaseName ru) ++
                  " has unbound variables: "
                 ) ru

-- Check for usage of all type facts with reserved names
reservedFactNameRules' :: [ProtoRuleE] -> WfErrorReport
reservedFactNameRules' rules = do
  ru <- rules
  let lfact = [fa| fa <- get rPrems ru
                  , factTag fa `elem` [KUFact,KDFact]
                  || isKLogFact fa]
      mfact = [fa | fa <- get rActs ru
                  , factTag fa `elem` [KUFact,KDFact,InFact,OutFact,FreshFact]
                  || isKLogFact fa]
      rfact = [fa | fa <- get rConcs ru
                  , factTag fa `elem` [KUFact, KDFact]
                  || isKLogFact fa]
      check _   []  = mzero
      check msg fas = return $ (,) (underlineTopic "Reserved names") $
            text ("Rule " ++ quote (showRuleCaseName ru))
            <-> text ("contains facts with reserved names"++msg) $-$
            nest 2 (fsep $ punctuate comma $ map prettyLNFact fas)

  msum [ check " on left-hand-side:"  lfact
        , check " on the middle:" mfact
        , check " on the right-hand-side:" rfact ]

-- Check for the usage of special facts at wrong positions
specialFactsUsage' :: [ProtoRuleE] -> WfErrorReport
specialFactsUsage' rules = do
    ru <- rules
    let lhsf = [ fa | fa <- get rPrems ru
                  , factTag fa == OutFact ]
        rhsf = [ fa | fa <- get rConcs ru
                  , factTag fa `elem` [FreshFact,InFact] ]
        check _   []  = mzero
        check msg fas = return $ (,) (underlineTopic "Special facts") $
            text ("rule " ++ quote (showRuleCaseName ru)) <-> text msg $-$
            nest 2 (fsep $ punctuate comma $ map prettyLNFact fas)

    msum [ check "uses disallowed facts on left-hand-side:"  lhsf
        , check "uses disallowed facts on right-hand-side:" rhsf ]


freshFactArguments' :: [ProtoRuleE] -> WfErrorReport
freshFactArguments' rules = do
    ru                        <- rules
    fa@(Fact FreshFact _ [m]) <- get rPrems ru
    guard (not (isMsgVar m || isFreshVar m))
    return $ (,) (underlineTopic "Fr facts must only use a fresh- or a msg-variable") $
        text ("rule " ++ quote (showRuleCaseName ru)) <->
        text "fact:" <-> prettyLNFact fa

-- | Report on facts usage. Skip checks on non-existant actions if `incompleteMSRs` is True.
factReports :: Bool -> OpenTranslatedTheory -> WfErrorReport
factReports incompleteMSRs thy =
    concat  [ reservedReport, reservedFactNameRules, freshFactArguments, specialFactsUsage
    , factUsage, factLhsOccurNoRhs]
    ++ concat [ inexistentActions ++ inexistentActionsRestrictions | incompleteMSRs ]
  where
    ruleFacts ru =
      ( "Rule " ++ quote (showRuleCaseName ru)
      , extFactInfo <$> concatMap (`get` ru) [rPrems, rActs, rConcs])

    -- NOTE: The check that the number of actual function arguments in a term
    -- agrees with the arity of the function as given by the signature is
    -- enforced by the parser and implicitly checked in 'factArity'.

    theoryFacts = -- sortednubOn (fst &&& (snd . snd)) $
          do ruleFacts <$> get thyCache thy
      <|> ((do
             ru <- thyProtoRules thy
             return $ ruleFacts $ ru)
          ++ (do
             RuleItem ru <- get thyItems thy
             ruAC <- get oprRuleAC ru
             return $ ruleFacts ruAC))
      <|> do LemmaItem l <- get thyItems thy
             return $ (,) ("Lemma " ++ quote (get lName l)) $ do
                 fa <- formulaFacts (get lFormula l)
                 return $ (text (show fa), factInfo fa)

    -- we must compute all important information up-front in order to
    -- mangle facts with terms with bound variables and such without them
    extFactInfo fa = (prettyLNFact fa, factInfo fa)

    --- Check for usage of protocol facts with reserved names
    reservedReport = do
        (origin, fas) <- theoryFacts
        case mapMaybe reservedFactName fas of
          []   -> []
          errs -> return $ (,) (underlineTopic "Reserved names") $ foldr1 ($--$) $
              wrappedText ("The " ++ origin ++
                           " contains facts with reserved names:")
            : map (nest 2) errs

    reservedFactName (ppFa, info@(ProtoFact _ name _, _,_))
      | map toLower name `elem` ["fr","ku","kd","out","in"] =
          return $ ppFa $-$ text ("show:" ++ show info)
    reservedFactName _ = Nothing

    -- Check for usage of all type facts with reserved names
    reservedFactNameRules = reservedFactNameRules' $ thyProtoRules thy

    freshFactArguments = freshFactArguments' $ thyProtoRules thy

    -- Check for the usage of special facts at wrong positions
    specialFactsUsage = specialFactsUsage' $ thyProtoRules thy

    -- Check for facts with equal name modulo capitalization, but different
    -- multiplicity or arity.
    factUsage = do
       clash <- clashesOn factIdentifier (snd . snd) theoryFacts'
       let (_, (_, (factName, _, _))) = head clash
           name =quote ( map toLower $ factTagName factName  )
       return $ (,) (topic++p1++p2) $ (text ("\nFact " ++ name ++ ":\n") $-$ ). numbered' $ do
           (origin, (ppFa, (tag, arity, multipl))) <- clash
           return $ text (origin ++
                          ", capitalization  " ++ show (factTagName tag) ++
                          ", " ++ show arity ++", " ++ show multipl)
                    $-$ nest 2 ppFa
      where
        topic = (underlineTopic "Fact usage") ++ "\n"
        p1    = "Possible reasons: \n"++
                "1. Fact names are case-sensitive, different capitalizations are "++
                  "considered as different facts, "++
                  "i.e., Fact() is different from FAct(). "++
                  "Check the capitalization of your fact names.\n"
        p2    = "2. Same fact is used with different arities, "++
                "i.e., Fact('A','B') is different from Fact('A'). "++
                "Check the arguments of your facts.\n "
        --showInfo (tag, k, multipl) = show $ (showFactTag tag, k, multipl)
        theoryFacts'   = [ (ru, fa) | (ru, fas) <- theoryFacts, fa <- fas ]
        factIdentifier (_, (_, (tag, _, _))) = map toLower $ factTagName tag


    -- Check that every fact referenced in a formula is present as an action
    -- of a protocol rule. We have to add the linear "K/1" fact, as the
    -- WF-check cannot rely on a loaded intruder theory.
    ruleActions = S.fromList $ map factInfo $
          kLogFact undefined
        : dedLogFact undefined
        : kuFact undefined
        : (do ru <- thyProtoRules thy; get rActs ru)
          ++ (do RuleItem ru <- get thyItems thy; racs <- get oprRuleAC ru; get rActs racs)

    -- Report a protocol fact occurs in an LHS but not in any RHS
    factLhsOccurNoRhs :: WfErrorReport
    factLhsOccurNoRhs = factLhsOccurNoRhs' $ thyProtoRules thy

    inexistentActions = do
        LemmaItem l <- get thyItems thy
        fa <- sortednub $ formulaFacts (get lFormula l)
        let info = factInfo fa
            name = get lName l
            (tag,ari,mul)=info
        if info `S.member` ruleActions
          then []
          else return $ (,) (underlineTopic "Inexistent lemma actions") $
                 text ("Lemma " ++ quote name ++ " references action ") $-$
                 nest 2 (text ("fact " ++ show (factTagName tag)++
                 " (arity "++ show ari++
                 ", "++show mul++") ")) $-$
                 text "but no rule has such an action."

    inexistentActionsRestrictions = do
        RestrictionItem l <- get thyItems thy
        fa <- sortednub $ formulaFacts (get rstrFormula l)
        let info = factInfo fa
            name = get rstrName l
            (tag,ari,mul)=info
        if info `S.member` ruleActions
          then []
          else return $ (,) (underlineTopic "Inexistent restriction actions") $
                 text ("Restriction " ++ quote name ++ " references action ") $-$
                 nest 2 (text ("fact " ++ show (factTagName tag)++
                 " (arity "++ show ari++
                 ", "++show mul++") ")) $-$
                 text "but no rule has such an action."


-- | Report on facts usage.
factReportsDiff :: OpenDiffTheory -> WfErrorReport
factReportsDiff thy = concat
    [ reservedReport,reservedFactNameRules, reservedPrefixReport, freshFactArguments, specialFactsUsage
    , factUsage, factLhsOccurNoRhs, inexistentActions, inexistentActionsRestrictions
    ]
  where
    ruleFacts ru =
      ( "Rule " ++ quote (showRuleCaseName ru)
      , extFactInfo <$> concatMap (`get` ru) [rPrems, rActs, rConcs])

    -- NOTE: The check that the number of actual function arguments in a term
    -- agrees with the arity of the function as given by the signature is
    -- enforced by the parser and implicitly checked in 'factArity'.

    theoryDiffRuleFacts = do
              ru <- diffThyProtoRules thy
              return $ ruleFacts ru

    theoryParsedRuleFacts = (do
              EitherRuleItem (_, ru) <- get diffThyItems thy
              return $ ruleFacts $ get oprRuleE ru)
              ++ (do
              EitherRuleItem (_, ru) <- get diffThyItems thy
              ruAC <- get oprRuleAC ru
              return $ ruleFacts ruAC)

    theoryFacts = -- sortednubOn (fst &&& (snd . snd)) $
          theoryDiffRuleFacts
      <|> theoryParsedRuleFacts
      <|> do EitherLemmaItem (s, l) <- get diffThyItems thy
             return $ (,) ("Lemma " ++ show s ++ " " ++ quote (get lName l)) $ do
                 fa <- formulaFacts (get lFormula l)
                 return (text (show fa), factInfo fa)

    -- we must compute all important information up-front in order to
    -- mangle facts with terms with bound variables and such without them
    extFactInfo fa = (prettyLNFact fa, factInfo fa)

    -- Check for usage of protocol facts with reserved names
    reservedReport = do
        (origin, fas) <- theoryFacts
        case mapMaybe reservedFactName fas of
          []   -> []
          errs -> return $ (,) (underlineTopic "Reserved names") $ foldr1 ($--$) $
              wrappedText ("The " ++ origin ++
                           " contains facts with reserved names:")
            : map (nest 2) errs

    reservedFactName (ppFa, info@(ProtoFact _ name _, _,_))
      | map toLower name `elem` ["fr","ku","kd","out","in"] =
          return $ ppFa $-$ text ("show:" ++ show info)
    reservedFactName _ = Nothing

    -- Check for usage of all type facts with reserved names
    reservedFactNameRules :: WfErrorReport
    reservedFactNameRules = reservedFactNameRules' $ diffThyProtoRules thy

    -- Check for usage of protocol facts in rules with reserved prefixes in names
    reservedPrefixReport = do
        (origin, fas) <- theoryDiffRuleFacts
        case mapMaybe reservedPrefixFactName fas of
          []   -> []
          errs -> return $ (,) (underlineTopic "Reserved prefixes") $ foldr1 ($--$) $
              wrappedText ("The " ++ origin ++
                           " contains facts with reserved prefixes ('DiffIntr', 'DiffProto') inside names:")
            : map (nest 2) errs

    reservedPrefixFactName (ppFa, info@(ProtoFact _ name _, _,_))
      | (take 8 (map toLower name) == "diffintr") || (take 9 (map toLower name) == "diffproto") =
          return $ ppFa $-$ text (show info)
    reservedPrefixFactName _ = Nothing

    freshFactArguments = freshFactArguments' $ diffThyProtoRules thy

    -- Check for the usage of special facts at wrong positions
    specialFactsUsage = specialFactsUsage' $ diffThyProtoRules thy

    -- Check for facts with equal name modulo capitalization, but different
    -- multiplicity or arity.
    factUsage = do
       clash <- clashesOn factIdentifier (snd . snd) theoryFacts'
       let (_, (_, (factName, _, _))) = head clash
           name =quote ( map toLower $ factTagName factName  )
       return $ (,) (topic++p1++p2) $ (text ("\nFact " ++ name ++ ":\n") $-$ ). numbered' $ do
           (origin, (ppFa, (tag, arity, multipl))) <- clash
           return $ text (origin ++
                          ", capitalization  " ++ show (factTagName tag) ++
                          ", " ++ show arity ++", " ++ show multipl)
                    $-$ nest 2 ppFa
      where
        topic = (underlineTopic "Fact usage" ) ++ "\n"
        p1    = "Possible reasons: \n"++
                "1. Fact names are case-sensitive, different capitalizations are "++
                  "considered as different facts, "++
                  "i.e., Fact() is different from FAct(). "++
                  "Check the capitalization of your fact names.\n"
        p2    = "2. Same fact is used with different arities, "++
                "i.e., Fact('A','B') is different from Fact('A'). "++
                "Check the arguments of your facts.\n "
        theoryFacts'   = [ (ru, fa) | (ru, fas) <- theoryFacts, fa <- fas ]
        factIdentifier (_, (_, (tag, _, _))) = map toLower $ factTagName tag


    -- Check that every fact referenced in a formula is present as an action
    -- of a protocol rule. In the diff case, we load the intruder theory before.
    ruleActions = S.fromList $ map factInfo $
          kLogFact undefined
        : dedLogFact undefined
        : kuFact undefined
        : (do ru <- diffThyProtoRules thy; Fact {factTag = ProtoFact Linear ("DiffProto" ++ getRuleName ru) 0, factAnnotations = S.empty, factTerms = []} : get rActs ru)
        ++ (do
          DiffRuleItem ruO <- get diffThyItems thy
          case get dprLeftRight ruO of
            Nothing -> []
            Just (OpenProtoRule lr lrAC, OpenProtoRule rr rrAC) -> get rActs lr ++ get rActs rr ++ concatMap (\x -> Fact {factTag = ProtoFact Linear ("DiffProto" ++ getRuleName x) 0, factAnnotations = S.empty, factTerms = []} : get rActs x) (lrAC ++ rrAC))
        ++ (do EitherRuleItem (_, ruO) <- get diffThyItems thy; let ru = get oprRuleE ruO in Fact {factTag = ProtoFact Linear ("DiffProto" ++ getRuleName ru) 0, factAnnotations = S.empty, factTerms = []} : get rActs ru)
        ++ (do EitherRuleItem (_, ruO) <- get diffThyItems thy; ru <- get oprRuleAC ruO; Fact {factTag = ProtoFact Linear ("DiffProto" ++ getRuleName ru) 0, factAnnotations = S.empty, factTerms = []} : get rActs ru)
        ++ (do ru <- get diffThyCacheRight thy; Fact {factTag = ProtoFact Linear ("DiffIntr" ++ getRuleName ru) 0, factAnnotations = S.empty, factTerms = []} : get rActs ru)
        ++ (do ru <- get diffThyDiffCacheRight thy; Fact {factTag = ProtoFact Linear ("DiffIntr" ++ getRuleName ru) 0, factAnnotations = S.empty, factTerms = []} : get rActs ru)
        ++ (do ru <- get diffThyCacheLeft thy; Fact {factTag = ProtoFact Linear ("DiffIntr" ++ getRuleName ru) 0, factAnnotations = S.empty, factTerms = []} : get rActs ru)
        ++ (do ru <- get diffThyDiffCacheLeft thy; Fact {factTag = ProtoFact Linear ("DiffIntr" ++ getRuleName ru) 0, factAnnotations = S.empty, factTerms = []} : get rActs ru)

    factLhsOccurNoRhs :: WfErrorReport
    factLhsOccurNoRhs = factLhsOccurNoRhs' $ diffThyProtoRules thy

    inexistentActions = do
        EitherLemmaItem (s, l) <- {-trace ("Caches: " ++ show ((get diffThyCacheRight thy) ++ (get diffThyDiffCacheRight thy) ++ (get diffThyCacheLeft thy) ++ (get diffThyDiffCacheLeft thy))) $-} get diffThyItems thy
        fa <- sortednub $ formulaFacts (get lFormula l)
        let info = factInfo fa
            name = get lName l
            (tag,ari,mul) = info
        if info `S.member` ruleActions
          then []
          else return $ (,) (underlineTopic "Inexistant lemma actions") $
                 text (show s ++ " lemma " ++ quote name ++ " references action ") $-$
                 nest 2 (text ("fact " ++ show (factTagName tag)++
                 " arity "++ show ari++
                 ", "++show mul++" ")) $-$
                 text "but no rule has such an action."

    inexistentActionsRestrictions = do
        EitherRestrictionItem (s, l) <- get diffThyItems thy
        fa <- sortednub $ formulaFacts (get rstrFormula l)
        let info = factInfo fa
            name = get rstrName l
            (tag,ari,mul) = info
        if info `S.member` ruleActions
          then []
          else return $ (,) (underlineTopic "Restriction actions") $
                 text (show s ++ "restriction " ++ quote name ++ " references action ") $-$
                 nest 2 (text ("fact " ++ show (factTagName tag)++
                 " (arity "++ show ari++
                 ", "++show mul++") ")) $-$
                 text "but no rule has such an action."

-- | Gather all facts referenced in a formula.
formulaFacts :: Formula s c v -> [Fact (VTerm c (BVar v))]
formulaFacts =
    foldFormula atomFacts
      (const mempty)
      id
      (const mappend) (const $ const id)
  where
    atomFacts (Action _ fa)   = [fa]
    atomFacts (Syntactic _)   = mempty --the 'facts' in a predicate atom are not real facts
    atomFacts (EqE _ _)       = mempty
    atomFacts (Subterm _ _)   = mempty
    atomFacts (Less _ _)      = mempty
    atomFacts (Last _)        = mempty

atomTerms :: ProtoAtom s t -> [t]
atomTerms (Action i fa)        = i : factTerms fa
atomTerms (Syntactic _)       = []
-- atomTerms (Syntactic (Pred p)) = factTerms p
atomTerms (EqE t s)            = [t, s]
atomTerms (Subterm i j)        = [i, j]
atomTerms (Less i j)           = [i, j]
atomTerms (Last i)             = [i]

-- | Gather all terms referenced in a formula.
formulaTerms :: Formula s c v -> [VTerm c (BVar v)]
formulaTerms =
    foldFormula atomTerms (const mempty) id (const mappend) (const $ const id)

-- TODO: Perhaps a lot of errors would be captured when making the signature
-- of facts, term, and atom constructors explicit.
lemmaAttributeReport :: OpenTranslatedTheory -> WfErrorReport
lemmaAttributeReport thy = do
    lem <- theoryLemmas thy
    guard $    get lTraceQuantifier lem == ExistsTrace
            && ReuseLemma `elem` get lAttributes lem
    return ( underlineTopic "Lemma annotations"
           , text "Lemma" <-> (text $ quote $ get lName lem) <> colon <->
             text "cannot reuse 'exists-trace' lemmas"
           )

-- TODO: Perhaps a lot of errors would be captured when making the signature
-- of facts, term, and atom constructors explicit.
lemmaAttributeReportDiff :: OpenDiffTheory -> WfErrorReport
lemmaAttributeReportDiff thy = do
    (s, lem) <- diffTheoryLemmas thy
    guard $    get lTraceQuantifier lem == ExistsTrace
            && ReuseLemma `elem` get lAttributes lem
    return ( underlineTopic "Lemma annotations"
           , text ("Lemma " ++ show s) <-> (text $ quote $ get lName lem) <> colon <->
             text "cannot reuse 'exists-trace' lemmas"
           )


-- check that only message and node variables are used
checkQuantifiers :: Document b => Show a => String -> ProtoFormula syn (a, LSort) c v -> [b]
checkQuantifiers header fm
  | null disallowed = []
  | otherwise       = return $ fsep $
      (text $ header ++ " uses quantifiers with wrong sort:") :
      (punctuate comma $ map (nest 2 . text . show) disallowed)
  where
    binders    = foldFormula (const mempty) (const mempty) id (const mappend)
                      (\_ binder rest -> binder : rest) fm
    disallowed = filter (not . (`elem` [LSortMsg, LSortNode, LSortNat]) . snd) binders

-- check that only bound variables and public names are used
checkTerms :: Document b => Show v => String -> MaudeSig -> Formula s Name v -> [b]
checkTerms header maudeSig fm
  | null offenders = []
  | otherwise      = return $
      (fsep $
        (text $ header ++ " uses terms of the wrong form:") :
        (punctuate comma $ map (nest 2 . text . quote . show) offenders)
      ) $--$
      wrappedText
        "The only allowed terms are public constants and bound node and message\
        \ variables. If you encounter free message variables, then you might\
        \ have forgotten a #-prefix. Sort prefixes can only be dropped where\
        \ this is unambiguous. Moreover, reducible function symbols are\
        \ disallowed."
  where
    irreducible = irreducibleFunSyms $ maudeSig

    offenders = filter (not . allowed) $ formulaTerms fm
    allowed (viewTerm -> Lit (Var (Bound _)))        = True
    allowed (viewTerm -> Lit (Con (Name PubName _))) = True
    -- we allow multiset union
    allowed (viewTerm2 -> FUnion args)               = all allowed args
    -- allowed (viewTerm2 -> FNatPlus args)             = all allowed args  -- line from Cedric Staub which seems to be unnecessary
    -- we allow irreducible function symbols
    allowed (viewTerm -> FApp o args) | o `S.member` irreducible = all allowed args
    allowed _                                                    = False

-- check that the formula can be converted to a guarded formula
checkGuarded :: HighlightDocument a => String -> LNFormula -> [a]
checkGuarded header fm = case formulaToGuarded fm of
    Left err -> return $
        text (header ++ " cannot be converted to a guarded formula:") $-$
        nest 2 err
    Right _  -> []

-- | Check for mistakes in lemmas.
--
-- TODO: Perhaps a lot of errors would be captured when making the signature
-- of facts, term, and atom constructors explicit.
formulaReports :: OpenTranslatedTheory -> WfErrorReport
formulaReports thy = do
    (header, fm) <- annFormulas
    msum [ ((,) (underlineTopic "Quantifier sorts")) <$> checkQuantifiers header fm
         , ((,) (underlineTopic "Formula terms"))    <$> checkTerms header (get (sigpMaudeSig . thySignature) thy) fm
         , ((,) (underlineTopic " Formula guardedness"))      <$> checkGuarded header fm
         ]
  where
    annFormulas = do LemmaItem l <- get thyItems thy
                     let header = "Lemma " ++ quote (get lName l)
                         fm     = get lFormula l
                     return (header, fm)
              <|> do RestrictionItem rstr <- get thyItems thy
                     let header = "Restriction " ++ quote (get rstrName rstr)
                         fm     = get rstrFormula rstr
                     return (header, fm)



-- | Check for mistakes in lemmas.
--
-- TODO: Perhaps a lot of errors would be captured when making the signature
-- of facts, term, and atom constructors explicit.
formulaReportsDiff :: OpenDiffTheory -> WfErrorReport
formulaReportsDiff thy = do
    (header, fm) <- annFormulas
    msum [ ((,) (underlineTopic "Quantifier sorts")) <$> checkQuantifiers header fm
         , ((,) (underlineTopic "Formula terms"))    <$> checkTerms header ( get (sigpMaudeSig . diffThySignature) thy) fm
         , ((,) (underlineTopic "Formula guardedness"))      <$> checkGuarded header fm
         ]
  where
    annFormulas = do EitherLemmaItem (s, l) <- get diffThyItems thy
                     let header = show s ++ " Lemma " ++ quote (get lName l)
                         fm     = get lFormula l
                     return (header, fm)
              <|> do EitherRestrictionItem (s, rstr) <- get diffThyItems thy
                     let header = show s ++ " Restriction " ++ quote (get rstrName rstr)
                         fm     = get rstrFormula rstr
                     return (header, fm)

-- | Check that all rules are multipliation restricted. Compared
-- to the definition in the paper we are slightly more lenient.
-- We also accept a rule that is an instance of a multiplication
-- restricted rule.
-- 1. Consistently abstract terms with outermost reducible function symbols
--    occuring in lhs with fresh variables in rule.
-- 2. check vars(rhs) subset of vars(lhs) u V_Pub for abstracted rule for abstracted variables.
-- 3. check that * does not occur in rhs of abstracted rule.
multRestrictedReport' :: FunSig -> [ProtoRuleE] -> WfErrorReport
multRestrictedReport' irreducible ru0 = do
    ru <- ru0
    (,) (underlineTopic "Multiplication restriction of rules") <$>
        case restrictedFailures ru of
          ([],[]) -> []
          (mults, unbounds) ->
              return $
                (text "The following rule is not multiplication restricted:")
                $-$ (nest 2 (prettyProtoRuleE ru))
                $-$ (text "")
                $-$ (text "After replacing reducible function symbols in lhs with variables:")
                $-$ (nest 2 $ prettyProtoRuleE (abstractRule ru))
                $-$ (text "")
                $-$ (if null mults then mempty
                     else nest 2 $ (text "Terms with multiplication: ") <-> (prettyLNTermList mults))
                $-$ (if null unbounds then mempty
                     else nest 2 $ (text "Variables that occur only in rhs: ") <-> (prettyVarList unbounds))
  where
    abstractRule ru@(Rule i lhs acts rhs nvs) =
        (`evalFreshAvoiding` ru) .  (`evalBindT` noBindings) $ do
        Rule i <$> mapM (traverse abstractTerm) lhs
               <*> mapM (traverse replaceAbstracted) acts
               <*> mapM (traverse replaceAbstracted) rhs
               <*> (traverse replaceAbstracted) nvs

    abstractTerm (viewTerm -> FApp o args) | o `S.member` irreducible =
        fApp o <$> mapM abstractTerm args
    abstractTerm (viewTerm -> Lit l) = return $ lit l
    abstractTerm t = varTerm <$> importBinding (`LVar` sortOfLNTerm t) t "x"

    replaceAbstracted t = do
        b <- lookupBinding t
        case b of
          Just v -> return $ varTerm v
          Nothing ->
              case viewTerm t of
                FApp o args ->
                    fApp o <$> mapM replaceAbstracted args
                Lit l       -> return $ lit l

    restrictedFailures ru = (mults, unbound ruAbstr \\ unbound ru)
      where
        ruAbstr = abstractRule ru

        mults = [ mt | Fact _ _ ts <- get rConcs ru, t <- ts, mt <- multTerms t ]

        multTerms t@(viewTerm -> FApp (AC Mult) _)  = [t]
        multTerms   (viewTerm -> FApp _         as) = concatMap multTerms as
        multTerms _                                 = []

    unbound ru = [v | v <- frees (get rConcs ru) \\ frees (get rPrems ru)
                 , lvarSort v /= LSortPub ]


-- | Check that all rules are multipliation restricted. Compared
-- to the definition in the paper we are slightly more lenient.
-- We also accept a rule that is an instance of a multiplication
-- restricted rule.
-- 1. Consistently abstract terms with outermost reducible function symbols
--    occuring in lhs with fresh variables in rule.
-- 2. check vars(rhs) subset of vars(lhs) u V_Pub for abstracted rule for abstracted variables.
-- 3. check that * does not occur in rhs of abstracted rule.
multRestrictedReport :: OpenTranslatedTheory -> WfErrorReport
multRestrictedReport thy = multRestrictedReport' irreducible (thyProtoRules thy)
  where
    irreducible = irreducibleFunSyms $ get (sigpMaudeSig . thySignature) thy


-- | Check that all rules are multipliation restricted. Compared
-- to the definition in the paper we are slightly more lenient.
-- We also accept a rule that is an instance of a multiplication
-- restricted rule.
-- 1. Consistently abstract terms with outermost reducible function symbols
--    occuring in lhs with fresh variables in rule.
-- 2. check vars(rhs) subset of vars(lhs) u V_Pub for abstracted rule for abstracted variables.
-- 3. check that * does not occur in rhs of abstracted rule.
multRestrictedReportDiff :: OpenDiffTheory -> WfErrorReport
multRestrictedReportDiff thy = multRestrictedReport' irreducible (diffThyProtoRules thy)
  where
    irreducible = irreducibleFunSyms $ get (sigpMaudeSig . diffThySignature) thy


-- | All 2-multicombinations of a list.
-- multicombine2 :: [a] -> [(a,a)]
-- multicombine2 xs0 = do (x,xs) <- zip xs0 $ tails xs0; (,) x <$> xs


--------------------
-- Check if lemmas from "--prove" / "--lemma" args are in the theory
--------------------

-- | A fold to check if the lemmas are proper
findNotProvedLemmas :: [String] -> [String] -> [String]
findNotProvedLemmas lemmaArgsNames lemmasInTheory = foldl (\acc x -> if not (argFilter x) then  x:acc else acc ) [] lemmaArgsNames
  where
      -- Check a lemma against a prefix* pattern or the name of a lemma
      lemmaChecker :: String -> String -> Bool
      lemmaChecker argLem lemFromThy
        | lastMay argLem == Just '*' = init argLem `isPrefixOf` lemFromThy
        | otherwise = argLem == lemFromThy

      -- A filter to check if a lemma (str) is in the list of lemmas from the theory
      argFilter :: String -> Bool
      argFilter str = any (lemmaChecker str) lemmasInTheory


-- | Check that all the lemmas in the arguments are lemmas of the theory and return an error if not
  -----------------------
checkIfLemmasInTheory :: Theory sig c r p s  -> WfErrorReport
checkIfLemmasInTheory thy
        | lemmaArgsNames == [[]] = []
        | null notProvedLemmas = []
        | otherwise =
            [(topic, vcat
            [ text $ "--> '" ++ intercalate "', '" notProvedLemmas ++ "'"  ++ " from arguments "
              ++ "do(es) not correspond to a specified lemma in the theory "
            -- , text $ "List of lemmas from the theory: " ++ show (map _lName (theoryLemmas thy))
            ])]

    where
      lemmaArgsNames = get (lemmasToProve . thyOptions) thy
      topic = underlineTopic "Check presence of the --prove/--lemma arguments in theory"
      lemmasInTheory = map _lName (theoryLemmas thy)
      notProvedLemmas = findNotProvedLemmas lemmaArgsNames lemmasInTheory


-- | Check that all the lemmas in the arguments are lemmas of the diffTheory and return an error if not
  -----------------------
checkIfLemmasInDiffTheory :: DiffTheory sig c r r2 p p2  -> WfErrorReport
checkIfLemmasInDiffTheory thy
        | lemmaArgsNames == [[]] = []
        | null notProvedLemmas = []
        | otherwise =
            [(topic, vcat
            [ text $ "--> '" ++ intercalate "', '"  notProvedLemmas ++ "'"  ++ " from arguments "
              ++ "do(es) not correspond to a specified lemma in the theory "
            -- , text $ "List of lemmas from the theory: " ++ show (map _lName (theoryLemmas thy))
            ])]

    where
      lemmaArgsNames = get (lemmasToProve . diffThyOptions) thy
      topic = underlineTopic "Check presence of the --prove/--lemma arguments in theory"
      lemmasInTheory = map (_lName . snd) (diffTheoryLemmas thy)
      notProvedLemmas = findNotProvedLemmas lemmaArgsNames lemmasInTheory


------------------------------------------------------------------------------
-- Theory
------------------------------------------------------------------------------

-- | All equations of an OpenTranslatedTheory.
thyEquations :: OpenTranslatedTheory -> [CtxtStRule]
thyEquations thy = S.toList $ stRules (sig thy)
  where
    sig = _sigMaudeInfo . _thySignature

-- | All equations of an OpenDiffTheory.
diffThyEquations :: OpenDiffTheory -> [CtxtStRule]
diffThyEquations thy = S.toList $ stRules (sig thy)
  where
    sig = _sigMaudeInfo . _diffThySignature

-- | Check if equations are marked as user-defined convergent in an OpenTranslatedTheory.
isUserMarkedConvergent :: OpenTranslatedTheory -> Bool
isUserMarkedConvergent thy = eqConvergent (sig thy)
  where
    sig = _sigMaudeInfo . _thySignature

-- | Check if equations are marked as user-defined convergent in an OpenTranslatedTheory.
isUserMarkedConvergentDiff :: OpenDiffTheory -> Bool
isUserMarkedConvergentDiff thy = eqConvergent (sig thy)
  where
    sig = _sigMaudeInfo . _diffThySignature

-- | Checks if all equations are subterm convergent.
checkEquationsSubtermConvergence :: OpenTranslatedTheory -> WfErrorReport
checkEquationsSubtermConvergence thy
  | null nonSubtermEquations = []
  | otherwise = [(topic, doc)]
  where
    equations = thyEquations thy
    nonSubtermEquations = filterNonSubtermCtxtRule equations
    topic = underlineTopic "Subterm Convergence Warning"
    doc = text "User-defined equations must be convergent and have the finite variant property. The following equations are not subterm convergent. If you are sure that the set of equations is nevertheless convergent and has the finite variant property, you can ignore this warning and continue \n"
          $-$ vcat (map prettyCtxtStRule nonSubtermEquations) $-$ text " \n For more information, please refer to the manual : https://tamarin-prover.com/manual/master/book/010_modeling-issues.html "

-- | Checks if all equations are subterm convergent in a DiffTheory.
checkDiffEquationsSubtermConvergence :: OpenDiffTheory -> WfErrorReport
checkDiffEquationsSubtermConvergence thy
  | null nonSubtermEquations = []
  | otherwise = [(topic, doc)]
  where
    equations = diffThyEquations thy
    nonSubtermEquations = filterNonSubtermCtxtRule equations
    topic = underlineTopic "Subterm Convergence Warning"
    doc = text "User-defined equations must be convergent and have the finite variant property. The following equations are not subterm convergent. If you are sure that the set of equations is nevertheless convergent and has the finite variant property, you can ignore this warning and continue \n"
          $-$ vcat (map prettyCtxtStRule nonSubtermEquations) $-$ text " \n For more information, please refer to the manual : https://tamarin-prover.com/manual/master/book/010_modeling-issues.html "


-- | Returns a list of errors, if there are any.
checkWellformednessDiff :: OpenDiffTheory -> SignatureWithMaude
                    -> WfErrorReport
checkWellformednessDiff thy sig = -- trace ("checkWellformednessDiff: " ++ show thy) $
  concatMap ($ thy)
    [ checkIfLemmasInDiffTheory
    , unboundReportDiff
    , freshNamesReportDiff
    , publicNamesReportDiff
    , ruleSortsReportDiff
    , factReportsDiff
    , ruleVariantsReportDiff sig
    , leftRightRuleReportDiff
--     , ruleNameReportDiff
    , formulaReportsDiff
    , lemmaAttributeReportDiff
    , multRestrictedReportDiff
    , natWellSortedReportDiff
    ] ++ (if not (isUserMarkedConvergentDiff thy) then checkDiffEquationsSubtermConvergence thy else [])

-- | Returns a list of errors, if there are any. `incompleteMSR`, if true, indicates
-- that the MSRs are incomplete (e.g., when we export to ProVerif) and that
-- checks that rely on that should not be performed.
checkWellformedness :: Bool -> OpenTranslatedTheory -> SignatureWithMaude -> WfErrorReport
checkWellformedness incompleteMSRs thy sig = concatMap ($ thy) (
    [ checkIfLemmasInTheory
    , unboundReport
    , freshNamesReport
    , publicNamesReport
    , ruleSortsReport
    , ruleVariantsReport sig
    , factReports incompleteMSRs
    , formulaReports
    , lemmaAttributeReport
    , multRestrictedReport
    , natWellSortedReport
    ]
    ++ -- additional checks
    [checkEquationsSubtermConvergence |  not (isUserMarkedConvergent thy) ]
    )
