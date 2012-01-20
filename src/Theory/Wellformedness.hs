-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Wellformedness checks for intruder variants, protocol rules, and
-- properties.
--
-- The following checks should be performed (TODO: implement them):
--   
--   [protocol rules] 
--
--     1. all facts are used with the same arity.
--
--     2. fresh, pub, msg, snd, and knows facts are used with arity 1.
--
--     3. fresh and pub facts contain exactly a single variable.
--
--     5. fresh facts of the same rule contain different variables.
--
--     4. no fresh, pub, msg, and knows  facts in conclusions.
--
--     5. no send facts in premises.
--
--     6. no protocol fact uses a reserved name => change parser to ensure
--        this and pretty printer to show this.
--
--   [security properties]
--
--     1. all facts occur with the same arity in the action of some
--        protocol rule.
--
--     2. no node variable is used in a message position and vice versa.
--
--
module Theory.Wellformedness (

  -- * Wellformedness checking
    WfErrorReport
  , checkWellformedness
  , noteWellformedness

  , prettyWfErrorReport
  ) where

import           Prelude hiding (id, (.))

import           Data.Char
import           Data.Generics.Uniplate.Data (universeBi)
import           Data.List
import           Data.Label
import           Data.Maybe
import           Data.Monoid (mempty, mappend)
import qualified Data.Set      as S
import           Control.Basics
import           Control.Category

import           Extension.Prelude
import           Text.Isar
import           Theory

------------------------------------------------------------------------------
-- Types for error reports
------------------------------------------------------------------------------

type Topic         = String
type WfError       = (Topic, Doc)
type WfErrorReport = [WfError]

prettyWfErrorReport :: WfErrorReport -> Doc
prettyWfErrorReport []     = text "All well-formedness checks were successful."
prettyWfErrorReport report = foldr1 ($-$)
  [ text "Error: the following well-formedness checks failed!"
  , text ""
  , vcat . intersperse (text "") . map ppTopic $ groupOn fst report
  ]
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

-- | Pretty-print a comman, separated list of 'LVar's.
prettyVarList :: Document d => [LVar] -> d
prettyVarList = fsep . punctuate comma . map prettyLVar

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
    sortsClashCheck ("rule " ++ quote (showRuleCaseName ru) ++ " clashing sorts:") ru

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
    [reservedReport, specialFactsUsage, factUsage, inexistentActions]
  where
    ruleFacts ru = 
      ( "rule " ++ quote (showRuleCaseName ru)
      , extFactInfo <$> concatMap (`get` ru) [rPrems, rActs, rConcs])

    -- FIXME: Possibly the check that term arity agrees with fact-tag arity
    -- should be made here instead of just throwing an error, as implemented
    -- in 'factArity'.

    theoryFacts = -- sortednubOn (fst &&& (snd . snd)) $
          do ruleFacts <$> get thyCache thy
      <|> do RuleItem ru <- get thyItems thy
             return $ ruleFacts ru
      <|> do LemmaItem (Lemma name fmE _ _ _) <- get thyItems thy
             return $ (,) ("lemma " ++ quote name) $ do
                 fa <- formulaFacts fmE
                 return $ (text (show fa), factInfo fa)
      <|> do return $ (,) "unique_insts declaration" $ do
               tag <- S.toList $ get (sigpUniqueInsts . thySignature) thy 
               return $ ( text $ showFactTagArity tag
                        , (tag, factTagArity tag, factTagMultiplicity tag)
                        )

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
      | map toLower name `elem` ["fresh","knows","ku","kd","send"] =
          return $ ppFa $-$ text ("show:" ++ show info)
    reservedFactName _ = Nothing

    -- Check for the usage of special facts at wrong positions
    specialFactsUsage = do
       ru <- thyProtoRules thy
       let lhs = [ fa | fa <- get rPrems ru
                      , factTag fa `elem` [KUFact, KDFact, SendFact] ]
           rhs = [ fa | fa <- get rConcs ru
                      , factTag fa `elem` [FreshFact, KUFact, KDFact, KnowsFact] ]
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
                          ", fact " ++ show (map toLower $ showFactTag tag) ++
                          ": " ++ showInfo info)
                    $-$ nest 2 ppFa
      where
        showInfo (tag, k, mult) = show $ (showFactTag tag, k, mult)
        theoryFacts'   = [ (ru, fa) | (ru, fas) <- theoryFacts, fa <- fas ]
        factIdentifier (_, (_, (tag, _, _))) = map toLower $ showFactTag tag


    -- Check that every fact referenced in a formula is present as an action
    -- of a protocol rule.
    ruleActions = S.fromList $ do 
        RuleItem ru <- get thyItems thy
        factInfo <$> get rActs ru

    inexistentActions = do
        LemmaItem (Lemma name fmE _ _ _) <- get thyItems thy
        fa <- sortednub $ formulaFacts fmE
        let info = factInfo fa
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
    atomFacts (Provides _ fa) = [fa]
    atomFacts (Requires _ fa) = [fa]
    atomFacts (Action _ fa)   = [fa]
    atomFacts (EqE _ _)       = mempty
    atomFacts (Less _ _)      = mempty
    atomFacts (Last _)        = mempty
    atomFacts (DedBefore _ _) = mempty
    atomFacts (EdgeA _ _)     = mempty

-- | Gather all terms referenced in a formula.
formulaTerms :: Formula s c v -> [VTerm c (BVar v)]
formulaTerms = 
    foldFormula atomTerms (const mempty) id (const mappend) (const $ const id)
  where
    atomTerms (Provides i fa) = i : factTerms fa
    atomTerms (Requires i fa) = i : factTerms fa
    atomTerms (Action i fa)   = i : factTerms fa
    atomTerms (EqE t s)       = [t, s]
    atomTerms (Less i j)      = [i, j]
    atomTerms (Last i)        = [i]
    atomTerms (DedBefore t i) = [t, i]
    atomTerms (EdgeA x y)     = [fst x, fst y]


-- | Check for mistakes in lemmas.
--
-- TODO: Perhaps a lot of errors would be captured when making the signature
-- of facts, term, and atom constructors explicit.
formulaReports :: OpenTheory -> WfErrorReport
formulaReports thy = do
    LemmaItem (Lemma name fmE _ _ _) <- get thyItems thy
    let header = "lemma " ++ quote name 
    msum [ ((,) "quantifier sorts") <$> checkQuantifiers header fmE
         , ((,) "formula terms")    <$> checkTerms header fmE
         , ((,) "guardedness")      <$> checkGuarded header fmE 
         ]
  where
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
      | otherwise      = return $ fsep $
          (text $ header ++ "uses terms of the wrong form:") :
          (punctuate comma $ map (nest 2 . text . quote . show) offenders)
      where
        offenders = filter (not . allowed) $ formulaTerms fm
        allowed (Lit (Var (Bound _)))        = True
        allowed (Lit (Con (Name PubName _))) = True
        allowed _                            = False

    -- check that the formula can be converted to a guarded formula
    checkGuarded header fm = case fromFormulaNegate fm of
        Left err -> return $ 
            text (header ++ " cannot be converted to a guarded formula:") $-$
            nest 2 (text err)
        Right _  -> []

             

uniqueInstsReport :: OpenTheory -> WfErrorReport
uniqueInstsReport thy = do
    tag <- S.toList $ get (sigpUniqueInsts . thySignature) thy
    (,) "unique fact instances" <$> 
        if (Persistent == factTagMultiplicity tag)
          then return $ text $ showFactTagArity tag ++ " is persistent"
          else msum 
                [ checkAtMostOneConc tag
                , checkCopying tag
                ]
  where
    checkAtMostOneConc tag = do
        ru <- thyProtoRules thy
        let occs = length $ filter ((tag ==) . factTag) $ get rConcs ru
        guard (occs > 1)
        return $ wrappedText $
            "Failed to prove unique fact instances of " ++
            showFactTagArity tag ++ ", as it occurs " ++ show occs ++
            " times as a conclusion of rule '" ++ showRuleCaseName ru ++ "'."

    checkCopying _f = [] -- FIXME: Implement check.
    {-
        (ru1, ru2) <- 
      where
        rules = 
            filter (any (any ((f ==) . factSymbol) . get rPrems)) $
            thyProtoRules thy
    -}

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
    , uniqueInstsReport
    ]

-- | Adds a note to the end of the theory, if it is not well-formed.
noteWellformedness :: WfErrorReport -> OpenTheory -> OpenTheory
noteWellformedness report thy = addComment (prettyWfErrorReport report) thy

