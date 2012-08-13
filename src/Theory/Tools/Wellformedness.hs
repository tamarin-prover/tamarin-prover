{-# LANGUAGE ViewPatterns #-}
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

  , prettyWfErrorReport
  ) where

import           Prelude                     hiding (id, (.))

import           Control.Basics
import           Control.Category
import           Data.Char
import           Data.Generics.Uniplate.Data (universeBi)
import           Data.Label
import           Data.List
import           Data.Maybe
import           Data.Monoid                 (mappend, mempty)
import qualified Data.Set                    as S
import           Data.Traversable            (traverse)

import           Control.Monad.Bind

import           Extension.Prelude
import           Term.LTerm
import           Term.Maude.Signature
import           Theory
import           Theory.Text.Pretty

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
-- thyProtoRules :: OpenTheory ->
thyProtoRules :: OpenTheory -> [ProtoRuleE]
thyProtoRules thy = [ ru | RuleItem ru <- get thyItems thy ]

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
ruleSortsReport :: OpenTheory -> WfErrorReport
ruleSortsReport thy = do
    ru <- thyProtoRules thy
    sortsClashCheck ("rule " ++ quote (showRuleCaseName ru) ++
                     " clashing sorts, casings, or multiplicities:") ru

-- | Report on fresh names.
freshNamesReport :: OpenTheory -> WfErrorReport
freshNamesReport thy = do
    ru <- thyProtoRules thy
    case filter ((LSortFresh ==) . sortOfName) $ universeBi ru of
      []    -> []
      names -> return $ (,) "fresh names" $ fsep $
          text ( "rule " ++ quote (showRuleCaseName ru) ++ ": " ++
                 "fresh names are not allowed in rule:" )
        : punctuate comma (map (nest 2 . text . show) names)

-- | Report on capitalization of public names.
publicNamesReport :: OpenTheory -> WfErrorReport
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

-- | Check whether a rule has unbound variables.
unboundCheck :: HasFrees i => String -> Rule i -> WfErrorReport
unboundCheck info ru
    | null unboundVars = []
    | otherwise        = return $
        ( "unbound"
        , text info $-$ (nest 2 $ prettyVarList unboundVars) )
  where
    boundVars   = S.fromList $ frees (get rPrems ru)
    unboundVars = do
        v <- frees (get rConcs ru, get rActs ru, get rInfo ru)
        guard $ not (lvarSort v == LSortPub || v `S.member` boundVars)
        return v

-- | Report on sort clashes.
unboundReport :: OpenTheory -> WfErrorReport
unboundReport thy = do
    RuleItem ru <- get thyItems thy
    unboundCheck ("rule " ++ quote (showRuleCaseName ru) ++
                  " has unbound variables: "
                 ) ru

-- | Report on facts usage.
factReports :: OpenTheory -> WfErrorReport
factReports thy = concat
    [ reservedReport, freshFactArguments, specialFactsUsage
    , factUsage, inexistentActions
    ]
  where
    ruleFacts ru =
      ( "rule " ++ quote (showRuleCaseName ru)
      , extFactInfo <$> concatMap (`get` ru) [rPrems, rActs, rConcs])

    -- NOTE: The check that the number of actual function arguments in a term
    -- agrees with the arity of the function as given by the signature is
    -- enforced by the parser and implicitly checked in 'factArity'.

    theoryFacts = -- sortednubOn (fst &&& (snd . snd)) $
          do ruleFacts <$> get thyCache thy
      <|> do RuleItem ru <- get thyItems thy
             return $ ruleFacts ru
      <|> do LemmaItem l <- get thyItems thy
             return $ (,) ("lemma " ++ quote (get lName l)) $ do
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
          errs -> return $ (,) "reseved names" $ foldr1 ($--$) $
              wrappedText ("The " ++ origin ++
                           " contains facts with reserved names:")
            : map (nest 2) errs

    reservedFactName (ppFa, info@(ProtoFact _ name _, _,_))
      | map toLower name `elem` ["fr","ku","kd","out","in"] =
          return $ ppFa $-$ text ("show:" ++ show info)
    reservedFactName _ = Nothing

    freshFactArguments = do
       ru                      <- thyProtoRules thy
       fa@(Fact FreshFact [m]) <- get rPrems ru
       guard (not (isMsgVar m || isFreshVar m))
       return $ (,) "Fr facts must only use a fresh- or a msg-variable" $
           text ("rule " ++ quote (showRuleCaseName ru)) <->
           text "fact:" <-> prettyLNFact fa

    -- Check for the usage of special facts at wrong positions
    specialFactsUsage = do
       ru <- thyProtoRules thy
       let lhs = [ fa | fa <- get rPrems ru
                      , factTag fa `elem` [KUFact, KDFact, OutFact] ]
           rhs = [ fa | fa <- get rConcs ru
                      , factTag fa `elem` [FreshFact, KUFact, KDFact, InFact] ]
           check _   []  = mzero
           check msg fas = return $ (,) "special fact usage" $
               text ("rule " ++ quote (showRuleCaseName ru)) <-> text msg $-$
               (nest 2 $ fsep $ punctuate comma $ map prettyLNFact fas)

       msum [ check "uses disallowed facts on left-hand-side:"  lhs
            , check "uses disallowed facts on right-hand-side:" rhs ]

    -- Check for facts with equal name modulo capitalization, but different
    -- multiplicity or arity.
    factUsage = do
       clash <- clashesOn factIdentifier (snd . snd) theoryFacts'
       return $ (,) "fact usage" $ numbered' $ do
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
        : (do RuleItem ru <- get thyItems thy; get rActs ru)

    inexistentActions = do
        LemmaItem l <- get thyItems thy
        fa <- sortednub $ formulaFacts (get lFormula l)
        let info = factInfo fa
            name = get lName l
        if info `S.member` ruleActions
          then []
          else return $ (,) "lemma actions" $
                 text ("lemma " ++ quote name ++ " references action ") $-$
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
    atomFacts (EqE _ _)       = mempty
    atomFacts (Less _ _)      = mempty
    atomFacts (Last _)        = mempty

-- | Gather all terms referenced in a formula.
formulaTerms :: Formula s c v -> [VTerm c (BVar v)]
formulaTerms =
    foldFormula atomTerms (const mempty) id (const mappend) (const $ const id)
  where
    atomTerms (Action i fa)   = i : factTerms fa
    atomTerms (EqE t s)       = [t, s]
    atomTerms (Less i j)      = [i, j]
    atomTerms (Last i)        = [i]

-- TODO: Perhaps a lot of errors would be captured when making the signature
-- of facts, term, and atom constructors explicit.
lemmaAttributeReport :: OpenTheory -> WfErrorReport
lemmaAttributeReport thy = do
    lem <- theoryLemmas thy
    guard $    get lTraceQuantifier lem == ExistsTrace
            && ReuseLemma `elem` get lAttributes lem
    return ( "attributes"
           , text "lemma" <-> (text $ quote $ get lName lem) <> colon <->
             text "cannot reuse 'exists-trace' lemmas"
           )

-- | Check for mistakes in lemmas.
--
-- TODO: Perhaps a lot of errors would be captured when making the signature
-- of facts, term, and atom constructors explicit.
formulaReports :: OpenTheory -> WfErrorReport
formulaReports thy = do
    (header, fm) <- annFormulas
    msum [ ((,) "quantifier sorts") <$> checkQuantifiers header fm
         , ((,) "formula terms")    <$> checkTerms header fm
         , ((,) "guardedness")      <$> checkGuarded header fm
         ]
  where
    annFormulas = do LemmaItem l <- get thyItems thy
                     let header = "lemma " ++ quote (get lName l)
                         fm     = get lFormula l
                     return (header, fm)
              <|> do AxiomItem ax <- get thyItems thy
                     let header = "axiom " ++ quote (get axName ax)
                         fm     = get axFormula ax
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
            \ this is unambiguous."
      where
        offenders = filter (not . allowed) $ formulaTerms fm
        allowed (viewTerm -> Lit (Var (Bound _)))        = True
        allowed (viewTerm -> Lit (Con (Name PubName _))) = True
        allowed _                                        = False

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
multRestrictedReport :: OpenTheory -> WfErrorReport
multRestrictedReport thy = do
    ru <- theoryRules thy
    (,) "multiplication restriction of rules" <$>
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
    abstractRule ru@(Rule i lhs acts rhs) =
        (`evalFreshAvoiding` ru) .  (`evalBindT` noBindings) $ do
        Rule i <$> mapM (traverse abstractTerm) lhs
               <*> mapM (traverse replaceAbstracted) acts
               <*> mapM (traverse replaceAbstracted) rhs

    abstractTerm (viewTerm -> FApp (NonAC o) args) | o `S.member` irreducible =
        fAppNonAC o <$> mapM abstractTerm args
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

        mults = [ mt | Fact _ ts <- get rConcs ru, t <- ts, mt <- multTerms t ]

        multTerms t@(viewTerm -> FApp (AC Mult) _)  = [t]
        multTerms   (viewTerm -> FApp _         as) = concatMap multTerms as
        multTerms _                                 = []

    unbound ru = [v | v <- frees (get rConcs ru) \\ frees (get rPrems ru)
                 , lvarSort v /= LSortPub ]


    irreducible = irreducibleFunctionSymbols $ get (sigpMaudeSig . thySignature) thy



-- | All 2-multicombinations of a list.
-- multicombine2 :: [a] -> [(a,a)]
-- multicombine2 xs0 = do (x,xs) <- zip xs0 $ tails xs0; (,) x <$> xs


------------------------------------------------------------------------------
-- Theory
------------------------------------------------------------------------------



-- | Returns a list of errors, if there are any.
checkWellformedness :: OpenTheory
                    -> WfErrorReport
checkWellformedness thy = concatMap ($ thy)
    [ unboundReport
    , freshNamesReport
    , publicNamesReport
    , ruleSortsReport
    , factReports
    , formulaReports
    , lemmaAttributeReport
    , multRestrictedReport
    ]

-- | Adds a note to the end of the theory, if it is not well-formed.
noteWellformedness :: WfErrorReport -> OpenTheory -> OpenTheory
noteWellformedness report thy =
    addComment wfErrorReport thy
  where
    wfErrorReport
      | null report = text "All well-formedness checks were successful."
      | otherwise   = vsep
          [ text "WARNING: the following wellformedness checks failed!"
          , prettyWfErrorReport report
          ]

