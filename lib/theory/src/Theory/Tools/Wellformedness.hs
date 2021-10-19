{-# LANGUAGE ViewPatterns     #-}
{-# LANGUAGE FlexibleContexts #-}
-- |
-- Copyright   : (c) 2010-2012 Simon Meier & Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
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
  , noteWellformedness
  , checkWellformednessDiff
  , noteWellformednessDiff

  , prettyWfErrorReport
  ) where

-- import           Debug.Trace

import           Prelude                     hiding (id, (.))

import           Control.Basics
import           Control.Category
import           Data.Char
import           Data.Generics.Uniplate.Data (universeBi)
import           Data.Label
import           Data.List                   (intersperse,(\\))
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

------------------------------------------------------------------------------
-- Types for error reports
------------------------------------------------------------------------------

type Topic         = String
type WfError       = (Topic, Doc)
type WfErrorReport = [WfError]

prettyWfErrorReport :: WfErrorReport -> Doc
prettyWfErrorReport =
    vcat . intersperse (text "") . map ppTopic . groupOn fst
  where
    ppTopic []                 = error "prettyWfErrorReport: groupOn returned empty list"
    ppTopic errs@((topic,_):_) =
      text topic <> colon $-$
      (nest 2 . vcat . intersperse (text "") $ map snd errs)


------------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------------

-- | All protocol rules of a theory.
-- thyProtoRules :: OpenTranslatedTheory ->
thyProtoRules :: OpenTranslatedTheory -> [ProtoRuleE]
thyProtoRules thy = [ get oprRuleE ru | RuleItem ru <- get thyItems thy ]

-- | All protocol rules of a theory.
-- thyProtoRules :: OpenTranslatedTheory ->
diffThyProtoRules :: OpenDiffTheory -> [ProtoRuleE]
diffThyProtoRules thy = [ get dprRule ru | DiffRuleItem ru <- get diffThyItems thy ]

-- | Lower-case a string.
lowerCase :: String -> String
lowerCase = map toLower

-- | Pretty-print a comma, separated list of 'LVar's.
prettyVarList :: Document d => [LVar] -> d
prettyVarList = fsep . punctuate comma . map prettyLVar

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
    return grp

-- | Nice quoting.
quote :: String -> String
quote cs = '`' : cs ++ "'"

------------------------------------------------------------------------------
-- Checks
------------------------------------------------------------------------------

--- | Check that the protocol rules are well-formed.
sortsClashCheck :: HasFrees t => String -> t -> WfErrorReport
sortsClashCheck info t = case clashesOn removeSort id $ frees t of
    [] -> []
    cs -> return $
            ( "sorts"
            , text info $-$ (nest 2 $ numbered' $ map prettyVarList cs)
            )
  where
    removeSort lv = (lowerCase (lvarName lv), lvarIdx lv)

-- | Report on sort clashes.
ruleSortsReport :: OpenTranslatedTheory -> WfErrorReport
ruleSortsReport thy = do
    ru <- thyProtoRules thy
    sortsClashCheck ("rule " ++ quote (showRuleCaseName ru) ++
                     " clashing sorts, casings, or multiplicities:") ru

--- | Check that the protocol rule variants are correct.
variantsCheck :: MaudeHandle -> String -> OpenProtoRule -> WfErrorReport
variantsCheck _   _    (OpenProtoRule _ [])     = []
variantsCheck hnd info (OpenProtoRule ruE ruAC) =
  if sameVariantsUpToActions ruAC recomputedVariants then
    []
  else
    return $
            ( "variants"
            , text info $-$ (nest 2 $ (numbered' $ (map prettyProtoRuleAC ruAC)))
              $--$ text "Recomputed variants: " $--$
              (nest 2 $ (numbered' $ map prettyProtoRuleAC recomputedVariants))
            )
  where
    recomputedVariants = map (get cprRuleAC) $ unfoldRuleVariants $
      ClosedProtoRule ruE (variantsProtoRule hnd ruE)
    sameVariantsUpToActions parsed computed = all (\x -> any (equalUpToAddedActions x) computed) parsed

-- | Report on missing or different variants.
ruleVariantsReport :: SignatureWithMaude -> OpenTranslatedTheory -> WfErrorReport
ruleVariantsReport sig thy = do
    ru <- [ ru | RuleItem ru <- get thyItems thy ]
    variantsCheck hnd ("rule " ++ quote (showRuleCaseName (get oprRuleE ru)) ++
                     " cannot confirm manual variants:") ru
  where
    hnd = get sigmMaudeHandle sig

-- | Report on missing or different variants in case of diff rules.
ruleVariantsReportDiff :: SignatureWithMaude -> OpenDiffTheory -> WfErrorReport
ruleVariantsReportDiff sig thy = do
    lrRu <- [ get dprLeftRight ru | DiffRuleItem ru <- get diffThyItems thy ]
    case lrRu of
      Just (lr, rr) -> (variantsCheck hnd ("left rule " ++ quote (showRuleCaseName (get oprRuleE lr)) ++
                     " cannot confirm manual variants:") lr) ++
                      (variantsCheck hnd ("right rule " ++ quote (showRuleCaseName (get oprRuleE rr)) ++
                      " cannot confirm manual variants:") rr)
      Nothing -> []
  where
    hnd = get sigmMaudeHandle sig

-- | Report on inconsistent left/right rules. This does not check the variants (done by ruleVariantsReportDiff).
leftRightRuleReportDiff :: OpenDiffTheory -> WfErrorReport
leftRightRuleReportDiff thy = do
    ru <- [ ru | DiffRuleItem ru <- get diffThyItems thy ]
    case get dprLeftRight ru of
      Just ((OpenProtoRule lr _), _) | not (equalUpToAddedActions lr (getLeftRule (get dprRule ru))) -> return $
              ( "left rule"
              , text "Inconsistent left rule" $-$ (nest 2 $ prettyProtoRuleE lr)
                $--$ text "w.r.t." $--$
                (nest 2 $ prettyProtoRuleE (get dprRule ru))
              )
      Just (_, (OpenProtoRule rr _)) | not (equalUpToAddedActions rr (getRightRule (get dprRule ru))) -> return $
              ( "right rule"
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
                     " clashing sorts, casings, or multiplicities:") ru

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
freshNamesReport :: OpenTranslatedTheory -> WfErrorReport
freshNamesReport thy = do
    ru <- thyProtoRules thy
    case filter ((LSortFresh ==) . sortOfName) $ universeBi ru of
      []    -> []
      names -> return $ (,) "fresh names" $ fsep $
          text ( "rule " ++ quote (showRuleCaseName ru) ++ ": " ++
                 "fresh names are not allowed in rule:" )
        : punctuate comma (map (nest 2 . text . show) names)

-- | Report on fresh names.
freshNamesReportDiff :: OpenDiffTheory -> WfErrorReport
freshNamesReportDiff thy = do
    ru <- diffThyProtoRules thy
    case filter ((LSortFresh ==) . sortOfName) $ universeBi ru of
      []    -> []
      names -> return $ (,) "fresh names" $ fsep $
          text ( "rule " ++ quote (showRuleCaseName ru) ++ ": " ++
                 "fresh names are not allowed in rule:" )
        : punctuate comma (map (nest 2 . text . show) names)

-- | Report on capitalization of public names.
publicNamesReport :: OpenTranslatedTheory -> WfErrorReport
publicNamesReport thy =
    case findClashes publicNames of
      []      -> []
      clashes -> return $ (,) topic $ numbered' $
          map (nest 2 . fsep . punctuate comma . map ppRuleAndName) clashes
  where
    topic       = "public names with mismatching capitalization"
    publicNames = do
        ru <- thyProtoRules thy
        (,) (showRuleCaseName ru) <$>
            (filter ((LSortPub ==) . sortOfName) $ universeBi ru)
    findClashes   = clashesOn (map toLower . show . snd) (show . snd)
    ppRuleAndName (ruName, pub) =
        text $ "rule " ++ show ruName ++ " name " ++ show pub

-- | Report on capitalization of public names.
publicNamesReportDiff :: OpenDiffTheory -> WfErrorReport
publicNamesReportDiff thy =
    case findClashes publicNames of
      []      -> []
      clashes -> return $ (,) topic $ numbered' $
          map (nest 2 . fsep . punctuate comma . map ppRuleAndName) clashes
  where
    topic       = "public names with mismatching capitalization"
    publicNames = do
        ru <- diffThyProtoRules thy
        (,) (showRuleCaseName ru) <$>
            (filter ((LSortPub ==) . sortOfName) $ universeBi ru)
    findClashes   = clashesOn (map toLower . show . snd) (show . snd)
    ppRuleAndName (ruName, pub) =
        text $ "rule " ++ show ruName ++ " name " ++ show pub


-- | Check whether a rule has unbound variables.
unboundCheck :: Document b => String -> Rule ProtoRuleEInfo -> [([Char], b)]
unboundCheck info ru
    | null unboundVars = []
    | otherwise        = return $
        ( "unbound"
        , text info $-$ (nest 2 $ prettyVarList unboundVars) )
  where
    boundVars   = S.fromList $ frees (get rPrems ru)
    originatesFromLookup v = any (match v) $ get preAttributes $ get rInfo ru
    match v (Process (ProcessComb (Lookup _ v') _ _ _))  = v == v'
    match _ _ = False
    unboundVars = do
        v <- frees (get rConcs ru, get rActs ru, get rInfo ru)
        guard $ not (lvarSort v == LSortPub || v `S.member` boundVars || originatesFromLookup v)
        return v

-- | Report on sort clashes.
unboundReport :: OpenTranslatedTheory -> WfErrorReport
unboundReport thy = do
    RuleItem ru' <- get thyItems thy
    let ru = get oprRuleE ru'
    unboundCheck ("rule " ++ quote (showRuleCaseName ru) ++
                  " has unbound variables: "
                 ) ru

-- | Report on sort clashes.
unboundReportDiff :: OpenDiffTheory -> WfErrorReport
unboundReportDiff thy = do
    DiffRuleItem ru' <- get diffThyItems thy
    let ru = get dprRule ru'
    unboundCheck ("rule " ++ quote (showRuleCaseName ru) ++
                  " has unbound variables: "
                 ) ru

-- | Report on facts usage.
factReports :: OpenTranslatedTheory -> WfErrorReport
factReports thy = concat
    [ reservedReport, freshFactArguments, specialFactsUsage
    , factUsage, inexistentActions, inexistentActionsRestrictions
    ]
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
             RuleItem ru <- get thyItems thy
             return $ ruleFacts $ get oprRuleE ru)
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

    factInfo :: Fact t -> (FactTag, Int, Multiplicity)
    factInfo fa    = (factTag fa, factArity fa, factMultiplicity fa)

    --- Check for usage of protocol facts with reserved names
    reservedReport = do
        (origin, fas) <- theoryFacts
        case mapMaybe reservedFactName fas of
          []   -> []
          errs -> return $ (,) "Reserved names" $ foldr1 ($--$) $
              wrappedText ("The " ++ origin ++
                           " contains facts with reserved names:")
            : map (nest 2) errs

    reservedFactName (ppFa, info@(ProtoFact _ name _, _,_))
      | map toLower name `elem` ["fr","ku","kd","out","in"] =
          return $ ppFa $-$ text ("show:" ++ show info)
    reservedFactName _ = Nothing

    freshFactArguments = do
       ru                      <- thyProtoRules thy
       fa@(Fact FreshFact _ [m]) <- get rPrems ru
       guard (not (isMsgVar m || isFreshVar m))
       return $ (,) "Fr facts must only use a fresh- or a msg-variable" $
           text ("rule " ++ quote (showRuleCaseName ru)) <->
           text "fact:" <-> prettyLNFact fa

    -- Check for the usage of special facts at wrong positions
    specialFactsUsage = do
       ru <- thyProtoRules thy
       let lhsf = [ fa | fa <- get rPrems ru
                      , factTag fa `elem` [KUFact, KDFact, OutFact] ]
           rhsf = [ fa | fa <- get rConcs ru
                      , factTag fa `elem` [FreshFact, KUFact, KDFact, InFact] ]
           check _   []  = mzero
           check msg fas = return $ (,) "Special fact usage" $
               text ("rule " ++ quote (showRuleCaseName ru)) <-> text msg $-$
               (nest 2 $ fsep $ punctuate comma $ map prettyLNFact fas)

       msum [ check "uses disallowed facts on left-hand-side:"  lhsf
            , check "uses disallowed facts on right-hand-side:" rhsf ]

    -- Check for facts with equal name modulo capitalization, but different
    -- multiplicity or arity.
    factUsage = do
       clash <- clashesOn factIdentifier (snd . snd) theoryFacts'
       return $ (,) "Fact usage" $ numbered' $ do
           (origin, (ppFa, info@(tag, _, _))) <- clash
           return $ text (origin ++
                          ", fact " ++ show (map toLower $ factTagName tag) ++
                          ": " ++ showInfo info)
                    $-$ nest 2 ppFa
      where
        showInfo (tag, k, multipl) = show $ (showFactTag tag, k, multipl)
        theoryFacts'   = [ (ru, fa) | (ru, fas) <- theoryFacts, fa <- fas ]
        factIdentifier (_, (_, (tag, _, _))) = map toLower $ factTagName tag


    -- Check that every fact referenced in a formula is present as an action
    -- of a protocol rule. We have to add the linear "K/1" fact, as the
    -- WF-check cannot rely on a loaded intruder theory.
    ruleActions = S.fromList $ map factInfo $
          kLogFact undefined
        : dedLogFact undefined
        : kuFact undefined
        : (do RuleItem ru <- get thyItems thy; get rActs $ get oprRuleE ru)
          ++ (do RuleItem ru <- get thyItems thy; racs <- get oprRuleAC ru; get rActs racs)

    inexistentActions = do
        LemmaItem l <- get thyItems thy
        fa <- sortednub $ formulaFacts (get lFormula l)
        let info = factInfo fa
            name = get lName l
        if info `S.member` ruleActions
          then []
          else return $ (,) "Lemma actions" $
                 text ("lemma " ++ quote name ++ " references action ") $-$
                 nest 2 (text $ show info) $-$
                 text "but no rule has such an action."

    inexistentActionsRestrictions = do
        RestrictionItem l <- get thyItems thy
        fa <- sortednub $ formulaFacts (get rstrFormula l)
        let info = factInfo fa
            name = get rstrName l
        if info `S.member` ruleActions
          then []
          else return $ (,) "Restriction actions" $
                 text ("restriction " ++ quote name ++ " references action ") $-$
                 nest 2 (text $ show info) $-$
                 text "but no rule has such an action."


-- | Report on facts usage.
factReportsDiff :: OpenDiffTheory -> WfErrorReport
factReportsDiff thy = concat
    [ reservedReport, reservedPrefixReport, freshFactArguments, specialFactsUsage
    , factUsage, inexistentActions, inexistentActionsRestrictions
    ]
  where
    ruleFacts ru =
      ( "Rule " ++ quote (showRuleCaseName ru)
      , extFactInfo <$> concatMap (`get` ru) [rPrems, rActs, rConcs])

    -- NOTE: The check that the number of actual function arguments in a term
    -- agrees with the arity of the function as given by the signature is
    -- enforced by the parser and implicitly checked in 'factArity'.

    theoryDiffRuleFacts = (do
              DiffRuleItem ru <- get diffThyItems thy
              return $ ruleFacts $ get dprRule ru)

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

    factInfo :: Fact t -> (FactTag, Int, Multiplicity)
    factInfo fa    = (factTag fa, factArity fa, factMultiplicity fa)

    -- Check for usage of protocol facts with reserved names
    reservedReport = do
        (origin, fas) <- theoryFacts
        case mapMaybe reservedFactName fas of
          []   -> []
          errs -> return $ (,) "Reserved names" $ foldr1 ($--$) $
              wrappedText ("The " ++ origin ++
                           " contains facts with reserved names:")
            : map (nest 2) errs

    reservedFactName (ppFa, info@(ProtoFact _ name _, _,_))
      | map toLower name `elem` ["fr","ku","kd","out","in"] =
          return $ ppFa $-$ text ("show:" ++ show info)
    reservedFactName _ = Nothing

    -- Check for usage of protocol facts in rules with reserved prefixes in names
    reservedPrefixReport = do
        (origin, fas) <- theoryDiffRuleFacts
        case mapMaybe reservedPrefixFactName fas of
          []   -> []
          errs -> return $ (,) "Reserved names" $ foldr1 ($--$) $
              wrappedText ("The " ++ origin ++
                           " contains facts with reserved prefixes ('DiffIntr', 'DiffProto') inside names:")
            : map (nest 2) errs

    reservedPrefixFactName (ppFa, info@(ProtoFact _ name _, _,_))
      | (take 8 (map toLower name) == "diffintr") || (take 9 (map toLower name) == "diffproto") =
          return $ ppFa $-$ text (show info)
    reservedPrefixFactName _ = Nothing

    freshFactArguments = do
       ru                      <- diffThyProtoRules thy
       fa@(Fact FreshFact _ [m]) <- get rPrems ru
       guard (not (isMsgVar m || isFreshVar m))
       return $ (,) "Fr facts must only use a fresh- or a msg-variable" $
           text ("rule " ++ quote (showRuleCaseName ru)) <->
           text "fact:" <-> prettyLNFact fa

    -- Check for the usage of special facts at wrong positions
    specialFactsUsage = do
       ru <- diffThyProtoRules thy
       let lhsf = [ fa | fa <- get rPrems ru
                      , factTag fa `elem` [KUFact, KDFact, OutFact] ]
           rhsf = [ fa | fa <- get rConcs ru
                      , factTag fa `elem` [FreshFact, KUFact, KDFact, InFact] ]
           check _   []  = mzero
           check msg fas = return $ (,) "Special fact usage" $
               text ("rule " ++ quote (showRuleCaseName ru)) <-> text msg $-$
               (nest 2 $ fsep $ punctuate comma $ map prettyLNFact fas)

       msum [ check "uses disallowed facts on left-hand-side of rule:"  lhsf
            , check "uses disallowed facts on right-hand-side of rule:" rhsf ]

    -- Check for facts with equal name modulo capitalization, but different
    -- multiplicity or arity.
    factUsage = do
       clash <- clashesOn factIdentifier (snd . snd) theoryFacts'
       return $ (,) "Fact usage" $ numbered' $ do
           (origin, (ppFa, info@(tag, _, _))) <- clash
           return $ text (origin ++
                          ", fact " ++ show (map toLower $ factTagName tag) ++
                          ": " ++ showInfo info)
                    $-$ nest 2 ppFa
      where
        showInfo (tag, k, multipl) = show (showFactTag tag, k, multipl)
        theoryFacts'   = [ (ru, fa) | (ru, fas) <- theoryFacts, fa <- fas ]
        factIdentifier (_, (_, (tag, _, _))) = map toLower $ factTagName tag


    -- Check that every fact referenced in a formula is present as an action
    -- of a protocol rule. In the diff case, we load the intruder theory before.
    ruleActions = S.fromList $ map factInfo $
          kLogFact undefined
        : dedLogFact undefined
        : kuFact undefined
        : (do DiffRuleItem ruO <- get diffThyItems thy; let ru = get dprRule ruO in Fact {factTag = ProtoFact Linear ("DiffProto" ++ getRuleName ru) 0, factAnnotations = S.empty, factTerms = []} : get rActs ru)
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

    inexistentActions = do
        EitherLemmaItem (s, l) <- {-trace ("Caches: " ++ show ((get diffThyCacheRight thy) ++ (get diffThyDiffCacheRight thy) ++ (get diffThyCacheLeft thy) ++ (get diffThyDiffCacheLeft thy))) $-} get diffThyItems thy
        fa <- sortednub $ formulaFacts (get lFormula l)
        let info = factInfo fa
            name = get lName l
        if info `S.member` ruleActions
          then []
          else return $ (,) "Lemma actions" $
                 text (show s ++ " lemma " ++ quote name ++ " references action ") $-$
                 nest 2 (text $ show info) $-$
                 text "but no rule has such an action."

    inexistentActionsRestrictions = do
        EitherRestrictionItem (s, l) <- get diffThyItems thy
        fa <- sortednub $ formulaFacts (get rstrFormula l)
        let info = factInfo fa
            name = get rstrName l
        if info `S.member` ruleActions
          then []
          else return $ (,) "Restriction actions" $
                 text (show s ++ "restriction " ++ quote name ++ " references action ") $-$
                 nest 2 (text $ show info) $-$
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

-- | Gather all terms referenced in a formula.
formulaTerms :: Formula s c v -> [VTerm c (BVar v)]
formulaTerms =
    foldFormula atomTerms (const mempty) id (const mappend) (const $ const id)
  where
    atomTerms (Action i fa)        = i : factTerms fa
    atomTerms (Syntactic _)       = []
    -- atomTerms (Syntactic (Pred p)) = factTerms p
    atomTerms (EqE t s)            = [t, s]
    atomTerms (Subterm i j)        = [i, j]
    atomTerms (Less i j)           = [i, j]
    atomTerms (Last i)             = [i]

-- TODO: Perhaps a lot of errors would be captured when making the signature
-- of facts, term, and atom constructors explicit.
lemmaAttributeReport :: OpenTranslatedTheory -> WfErrorReport
lemmaAttributeReport thy = do
    lem <- theoryLemmas thy
    guard $    get lTraceQuantifier lem == ExistsTrace
            && ReuseLemma `elem` get lAttributes lem
    return ( "Attributes"
           , text "lemma" <-> (text $ quote $ get lName lem) <> colon <->
             text "cannot reuse 'exists-trace' lemmas"
           )

-- TODO: Perhaps a lot of errors would be captured when making the signature
-- of facts, term, and atom constructors explicit.
lemmaAttributeReportDiff :: OpenDiffTheory -> WfErrorReport
lemmaAttributeReportDiff thy = do
    (s, lem) <- diffTheoryLemmas thy
    guard $    get lTraceQuantifier lem == ExistsTrace
            && ReuseLemma `elem` get lAttributes lem
    return ( "Attributes"
           , text ("lemma " ++ show s) <-> (text $ quote $ get lName lem) <> colon <->
             text "cannot reuse 'exists-trace' lemmas"
           )

-- | Check for mistakes in lemmas.
--
-- TODO: Perhaps a lot of errors would be captured when making the signature
-- of facts, term, and atom constructors explicit.
formulaReports :: OpenTranslatedTheory -> WfErrorReport
formulaReports thy = do
    (header, fm) <- annFormulas
    msum [ ((,) "Quantifier sorts") <$> checkQuantifiers header fm
         , ((,) "Formula terms")    <$> checkTerms header fm
         , ((,) "Guardedness")      <$> checkGuarded header fm
         ]
  where
    annFormulas = do LemmaItem l <- get thyItems thy
                     let header = "lemma " ++ quote (get lName l)
                         fm     = get lFormula l
                     return (header, fm)
              <|> do RestrictionItem rstr <- get thyItems thy
                     let header = "restriction " ++ quote (get rstrName rstr)
                         fm     = get rstrFormula rstr
                     return (header, fm)

    -- check that only message and node variables are used
    checkQuantifiers header fm
      | null disallowed = []
      | otherwise       = return $ fsep $
          (text $ header ++ "uses quantifiers with wrong sort:") :
          (punctuate comma $ map (nest 2 . text . show) disallowed)
      where
        binders    = foldFormula (const mempty) (const mempty) id (const mappend)
                         (\_ binder rest -> binder : rest) fm
        disallowed = flip filter binders
          (\(_,s) -> not (s `elem` [LSortMsg, LSortNode, LSortNat] || isUserSort s))  --TODO-UNCERTAIN: what this change does

    -- check that only bound variables and public names are used
    checkTerms header fm
      | null offenders = []
      | otherwise      = return $
          (fsep $
            (text $ header ++ " uses terms of the wrong form:") :
            (punctuate comma $ map (nest 2 . text . quote . show) offenders)
          ) $--$
          wrappedText
            "The only allowed terms are public names and bound node and message\
            \ variables. If you encounter free message variables, then you might\
            \ have forgotten a #-prefix. Sort prefixes can only be dropped where\
            \ this is unambiguous. Moreover, reducible function symbols are\
            \ disallowed."
      where
        irreducible = irreducibleFunSyms $ get (sigpMaudeSig . thySignature) thy

        offenders = filter (not . allowed) $ formulaTerms fm
        allowed (viewTerm -> Lit (Var (Bound _)))        = True
        allowed (viewTerm -> Lit (Con (Name PubName _))) = True
        -- we allow multiset union
        allowed (viewTerm2 -> FUnion args)               = all allowed args
        allowed (viewTerm2 -> FUserAC _ _ args)          = all allowed args  --TODO-UNCERTAIN: what this line (and the below) do
        allowed (viewTerm2 -> FNatPlus args)             = all allowed args
        -- we allow irreducible function symbols
        allowed (viewTerm -> FApp o args) | o `S.member` irreducible = all allowed args
        allowed _                                                    = False

    -- check that the formula can be converted to a guarded formula
    checkGuarded header fm = case formulaToGuarded fm of
        Left err -> return $
            text (header ++ " cannot be converted to a guarded formula:") $-$
            nest 2 err
        Right _  -> []


-- | Check for mistakes in lemmas.
--
-- TODO: Perhaps a lot of errors would be captured when making the signature
-- of facts, term, and atom constructors explicit.
formulaReportsDiff :: OpenDiffTheory -> WfErrorReport
formulaReportsDiff thy = do
    (header, fm) <- annFormulas
    msum [ ((,) "Quantifier sorts") <$> checkQuantifiers header fm
         , ((,) "Formula terms")    <$> checkTerms header fm
         , ((,) "Guardedness")      <$> checkGuarded header fm
         ]
  where
    annFormulas = do EitherLemmaItem (s, l) <- get diffThyItems thy
                     let header = show s ++ " lemma " ++ quote (get lName l)
                         fm     = get lFormula l
                     return (header, fm)
              <|> do EitherRestrictionItem (s, rstr) <- get diffThyItems thy
                     let header = show s ++ " restriction " ++ quote (get rstrName rstr)
                         fm     = get rstrFormula rstr
                     return (header, fm)

    -- check that only message and node variables are used
    checkQuantifiers header fm
      | null disallowed = []
      | otherwise       = return $ fsep $
          (text $ header ++ "uses quantifiers with wrong sort:") :
          (punctuate comma $ map (nest 2 . text . show) disallowed)
      where
        binders    = foldFormula (const mempty) (const mempty) id (const mappend)
                         (\_ binder rest -> binder : rest) fm
        disallowed = filter (not . (`elem` [LSortMsg, LSortNode]) . snd) binders

    -- check that only bound variables and public names are used
    checkTerms header fm
      | null offenders = []
      | otherwise      = return $
          (fsep $
            (text $ header ++ " uses terms of the wrong form:") :
            (punctuate comma $ map (nest 2 . text . quote . show) offenders)
          ) $--$
          wrappedText
            "The only allowed terms are public names and bound node and message\
            \ variables. If you encounter free message variables, then you might\
            \ have forgotten a #-prefix. Sort prefixes can only be dropped where\
            \ this is unambiguous. Moreover, reducible function symbols are\
            \ disallowed."
      where
        irreducible = irreducibleFunSyms $ get (sigpMaudeSig . diffThySignature) thy

        offenders = filter (not . allowed) $ formulaTerms fm
        allowed (viewTerm -> Lit (Var (Bound _)))        = True
        allowed (viewTerm -> Lit (Con (Name PubName _))) = True
        -- we allow multiset union
        allowed (viewTerm2 -> FUnion args)                = all allowed args
        -- we allow irreducible function symbols
        allowed (viewTerm -> FApp o args) | o `S.member` irreducible = all allowed args
        allowed _                                                    = False

    -- check that the formula can be converted to a guarded formula
    checkGuarded header fm = case formulaToGuarded fm of
        Left err -> return $
            text (header ++ " cannot be converted to a guarded formula:") $-$
            nest 2 err
        Right _  -> []


-- | Check that all rules are multipliation restricted. Compared
-- to the definition in the paper we are slightly more lenient.
-- We also accept a rule that is an instance of a multiplication
-- restricted rule.
-- 1. Consistently abstract terms with outermost reducible function symbols
--    occuring in lhs with fresh variables in rule.
-- 2. check vars(rhs) subset of vars(lhs) u V_Pub for abstracted rule for abstracted variables.
-- 3. check that * does not occur in rhs of abstracted rule.
multRestrictedReport :: OpenTranslatedTheory -> WfErrorReport
multRestrictedReport thy = do
    ruO <- theoryRules thy
    let ru = get oprRuleE ruO
    (,) "Multiplication restriction of rules" <$>
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
multRestrictedReportDiff thy = do
    ruO <- diffTheoryDiffRules thy
    let ru = get dprRule ruO
    (,) "Multiplication restriction of rules" <$>
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


    irreducible = irreducibleFunSyms $ get (sigpMaudeSig . diffThySignature) thy


-- | All 2-multicombinations of a list.
-- multicombine2 :: [a] -> [(a,a)]
-- multicombine2 xs0 = do (x,xs) <- zip xs0 $ tails xs0; (,) x <$> xs


------------------------------------------------------------------------------
-- Theory
------------------------------------------------------------------------------

-- | Returns a list of errors, if there are any.
checkWellformednessDiff :: OpenDiffTheory -> SignatureWithMaude
                    -> WfErrorReport
checkWellformednessDiff thy sig = -- trace ("checkWellformednessDiff: " ++ show thy) $
  concatMap ($ thy)
    [ unboundReportDiff
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
    ]


-- | Returns a list of errors, if there are any.
checkWellformedness :: OpenTranslatedTheory -> SignatureWithMaude
                    -> WfErrorReport
checkWellformedness thy sig = concatMap ($ thy)
    [ unboundReport
    , freshNamesReport
    , publicNamesReport
    , ruleSortsReport
    , ruleVariantsReport sig
    , factReports
    , formulaReports
    , lemmaAttributeReport
    , multRestrictedReport
    ]

-- | Adds a note to the end of the theory, if it is not well-formed.
noteWellformedness :: WfErrorReport -> OpenTranslatedTheory -> Bool -> OpenTranslatedTheory
noteWellformedness report thy quitOnWarning =
    addComment wfErrorReport thy
  where
    wfErrorReport
      | null report = text "All well-formedness checks were successful."
      | otherwise   = if quitOnWarning
                      then error ("quit-on-warning mode selected - aborting on following wellformedness errors.\n"
                                 ++ (render (prettyWfErrorReport report)))
                      else vsep
          [ text "WARNING: the following wellformedness checks failed!"
          , prettyWfErrorReport report
          ]

-- | Adds a note to the end of the theory, if it is not well-formed.
noteWellformednessDiff :: WfErrorReport -> OpenDiffTheory -> Bool -> OpenDiffTheory
noteWellformednessDiff report thy quitOnWarning =
    addDiffComment wfErrorReport thy
  where
    wfErrorReport
      | null report = text "All well-formedness checks were successful."
      | otherwise   = if quitOnWarning
                      then error ("quit-on-warning mode selected - aborting on following wellformedness errors.\n"
                                 ++ (render (prettyWfErrorReport report)))
                      else vsep
          [ text "WARNING: the following wellformedness checks failed!"
          , prettyWfErrorReport report
          ]
