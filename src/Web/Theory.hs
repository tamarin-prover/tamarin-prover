{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE QuasiQuotes   #-}
{-# LANGUAGE TupleSections #-}
-- FIXME: for functions prefixedShowDot
{-# LANGUAGE FlexibleContexts           #-}
{- |
Module      :  Web.Theory
Description :  Pretty-printing security protocol theories into HTML code.
Copyright   :  (c) 2011, 2012 Simon Meier & Cedric Staub
License     :  GPL-3

Stability   :  experimental
Portability :  non-portable
-}
module Web.Theory
  ( htmlThyPath
  , htmlDiffThyPath
--  , htmlThyDbgPath
  , imgThyPath
  , imgDiffThyPath
  , titleThyPath
  , titleDiffThyPath
  , theoryIndex
  , diffTheoryIndex
  , nextThyPath
  , nextDiffThyPath
  , prevThyPath
  , prevDiffThyPath
  , nextSmartThyPath
  , nextSmartDiffThyPath
  , prevSmartThyPath
  , prevSmartDiffThyPath
  , applyMethodAtPath
  , applyMethodAtPathDiff
  , applyDiffMethodAtPath
  , applyProverAtPath
  , applyDiffProverAtPath
  , applyProverAtPathDiff
  )
where


import           Debug.Trace                  (trace, traceM)

import           Data.Char                    (toUpper)
import           Data.List
import qualified Data.Map                     as M
import           Data.Maybe
-- import           Data.Monoid
import qualified Data.Set                     as S
import qualified Data.Text                    as T
import           Data.Time.Format             (formatTime)

import           Control.Basics
import           Control.Concurrent           (threadDelay)

import           System.Directory
import           System.FilePath
-- #if MIN_VERSION_time(1,5,0)
import           Data.Time.Format             (defaultTimeLocale)
-- #else
-- For GHC 7.10 comment line below and uncoment line 2 above
-- import           System.Locale                (defaultTimeLocale)
-- #endif

import           Extension.Data.Label

import           Text.Blaze.Html              (preEscapedToMarkup, toHtml)
import qualified Text.Dot                     as D
import           Text.Hamlet                  (Html, hamlet)
import           Text.PrettyPrint.Html
import           Utils.Misc                   (stringSHA256)

import           System.Exit
import           System.Process

import           Logic.Connectives
import           Theory
import           Theory.Text.Pretty
import           TheoryObject

import           Web.Settings
import           Web.Types
import Theory.Constraint.System (usesOracle)

------------------------------------------------------------------------------
-- Various other functions
------------------------------------------------------------------------------

applyMethodAtPath :: ClosedTheory -> String -> ProofPath
                  -> AutoProver            -- ^ How to extract/order the proof methods.
                  -> Int                   -- What proof method to use.
                  -> Maybe ClosedTheory
applyMethodAtPath thy lemmaName proofPath prover i = do
    lemma <- lookupLemma lemmaName thy
    subProof <- get lProof lemma `atPath` proofPath
    let ctxt  = getProofContext lemma thy
        sys   = psInfo (root subProof)
        heuristic = selectHeuristic prover ctxt
        ranking = useHeuristic heuristic (length proofPath)
        tactic = selectTactic prover ctxt
    methods <- map fst . rankProofMethods ranking tactic ctxt <$> sys
    method <- if length methods >= i then Just (methods !! (i-1)) else Nothing
    applyProverAtPath thy lemmaName proofPath (oneStepProver method)

applyMethodAtPathDiff :: ClosedDiffTheory -> Side -> String -> ProofPath
                      -> AutoProver             -- ^ How to extract/order the proof methods.
                      -> Int                   -- What proof method to use.
                      -> Maybe ClosedDiffTheory
applyMethodAtPathDiff thy s lemmaName proofPath prover i = do
    lemma <- lookupLemmaDiff s lemmaName thy
    subProof <- get lProof lemma `atPath` proofPath
    let ctxt  = getProofContextDiff s lemma thy
        sys   = psInfo (root subProof)
        heuristic = selectHeuristic prover ctxt
        ranking = useHeuristic heuristic (length proofPath)
        tactic = selectTactic prover ctxt
    methods <- (map fst . rankProofMethods ranking tactic ctxt) <$> sys
    method <- if length methods >= i then Just (methods !! (i-1)) else Nothing
    applyProverAtPathDiff thy s lemmaName proofPath
      (oneStepProver method                                       `mappend`
       replaceSorryProver (oneStepProver Simplify)                `mappend`
       replaceSorryProver (contradictionProver)                   `mappend`
       replaceSorryProver (oneStepProver (Finished Unfinishable)) `mappend`
       replaceSorryProver (oneStepProver (Finished Solved))
      )

applyDiffMethodAtPath :: ClosedDiffTheory -> String -> ProofPath
                      -> AutoProver             -- ^ How to extract/order the proof methods.
                      -> Int                   -- What proof method to use.
                      -> Maybe ClosedDiffTheory
applyDiffMethodAtPath thy lemmaName proofPath prover i = do
    lemma <- lookupDiffLemma lemmaName thy
    subProof <- get lDiffProof lemma `atPathDiff` proofPath
    let ctxt  = getDiffProofContext lemma thy
        sys   = dpsInfo (root subProof)
        heuristic = selectDiffHeuristic prover ctxt
        ranking = useHeuristic heuristic (length proofPath)
        tactic = selectDiffTactic prover ctxt
    methods <- (map fst . rankDiffProofMethods ranking tactic ctxt) <$> sys
    method <- if length methods >= i then Just (methods !! (i-1)) else Nothing
    applyDiffProverAtPath thy lemmaName proofPath
      (   oneStepDiffProver method                                 
       <> replaceDiffSorryProver (oneStepDiffProver (DiffBackwardSearchStep Simplify))
       <> replaceDiffSorryProver contradictionDiffProver
       <> replaceDiffSorryProver (oneStepDiffProver DiffMirrored)
       <> replaceDiffSorryProver (oneStepDiffProver DiffUnfinishable)
      )

applyProverAtPath :: ClosedTheory -> String -> ProofPath
                  -> Prover -> Maybe ClosedTheory
applyProverAtPath thy lemmaName proofPath prover =
    modifyLemmaProof (focus proofPath prover) lemmaName thy

applyProverAtPathDiff :: ClosedDiffTheory -> Side -> String -> ProofPath
                      -> Prover -> Maybe ClosedDiffTheory
applyProverAtPathDiff thy s lemmaName proofPath prover =
    modifyLemmaProofDiff s (focus proofPath prover) lemmaName thy

applyDiffProverAtPath :: ClosedDiffTheory -> String -> ProofPath
                      -> DiffProver -> Maybe ClosedDiffTheory
applyDiffProverAtPath thy lemmaName proofPath prover =
--     error (show thy ++ "<br> " ++ show lemmaName ++ "<br> " ++ show proofPath ++ "<br> "{- ++ show prover-})
    modifyDiffLemmaProof (focusDiff proofPath prover) lemmaName thy

------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Reference a dot graph for the given path.
refDotPath :: HtmlDocument d => RenderUrl -> TheoryIdx -> TheoryPath -> d
refDotPath renderUrl tidx path = closedTag "img" [("class", "graph"), ("src", imgPath), ("onclick", jsOpenSrcInNewTab)]
  where
    imgPath = T.unpack $ renderUrl (TheoryGraphR tidx path)
    jsOpenSrcInNewTab = "window.open(this.src, '_blank')"

-- | Reference a dot graph for the given diff path.
refDotDiffPath :: HtmlDocument d => RenderUrl -> TheoryIdx -> DiffTheoryPath -> Bool -> d
refDotDiffPath renderUrl tidx path mirror = withTag "a" [("href", imgPath), ("target", "_blank")] $ closedTag "img" [("class", "graph"), ("src", imgPath)]
  where
    imgPath = if mirror
              then T.unpack $ renderUrl (TheoryMirrorDiffR tidx path)
              else T.unpack $ renderUrl (TheoryGraphDiffR tidx path)

-- | Generate the dot file path for an intermediate dot output.
getDotPath :: String -> FilePath
getDotPath code = imageDir </> addExtension (stringSHA256 code) "dot"

-- | Generate the image file path for the final output.
getGraphPath :: OutputFormat -> String -> FilePath
getGraphPath ext code = imageDir </> addExtension (stringSHA256 code) (show ext)

-- | Create a link to a given theory path.
linkToPath :: HtmlDocument d
           => RenderUrl   -- ^ Url rendering function.
           -> Route WebUI -- ^ Route that should be linked.
           -> [String]    -- ^ Additional class
           -> d           -- ^ Document that carries the link.
           -> d
linkToPath renderUrl route cls = withTag "a" [("class", classes), ("href", linkPath)]
  where
    classes = unwords $ "internal-link" : cls
    linkPath = T.unpack $ renderUrl route

-- | Output some preformatted text.
preformatted :: HtmlDocument d => Maybe String -> d -> d
preformatted cl = withTag "div" [("class", classes cl)]
  where
    classes (Just cls) = "preformatted " ++ cls
    classes (Nothing) = "preformatted"

-- | Render a proof index relative to a theory path constructor.
proofIndex :: HtmlDocument d
           => String
           -> Int
           -> RenderUrl
           -> (ProofPath -> Route WebUI)         -- ^ Relative addressing function
           -> Proof (Maybe System, ProofStepColor) -- ^ The annotated incremental proof
           -> d
proofIndex l tidx renderUrl mkRoute =
    prettyProofWith ppStep ppCase . insertPaths
  where
    ppCase step = markStatus (fst $ psInfo step)

    ppStep step =
           case fst $ psInfo step of
               (Nothing, _)  -> superfluousStep
               (_, Unmarked) -> stepLink ["sorry-step"]
               (_, Green)    -> stepLink ["hl_good"]
               (_, Yellow)   -> invalidatedStep
               (_, Red)      -> stepLink ["hl_bad"]
        <> case psMethod step of
               Sorry _ -> emptyDoc
               _       -> removeStep
      where
        ppMethod = prettyProofMethod $ psMethod step
        stepLink cls = linkToPath renderUrl
            (mkRoute . snd . psInfo $ step)
            ("proof-step" : cls) ppMethod

        superfluousStep = withTag "span" [("class","hl_superfluous")] ppMethod

        invalidatedStep = if psMethod step == Invalidated 
                            then stepLink ["hl_medium"] <-> 
                                  (linkToPath renderUrl (TheoryVerifyR tidx $ TheoryProof l []) ["hl_medium"] $ text "verify it")
                            else stepLink ["hl_medium"]


        removeStep = linkToPath renderUrl (mkRoute . snd . psInfo $ step)
          ["remove-step"] emptyDoc

-- | Render a proof index relative to a theory path constructor.
diffProofIndex :: HtmlDocument d
           => RenderUrl
           -> (ProofPath -> Route WebUI)          -- ^ Relative addressing function
           -> DiffProof (Maybe DiffSystem, ProofStepColor) -- ^ The annotated incremental proof
           -> d
diffProofIndex renderUrl mkRoute =
    prettyDiffProofWith ppStep ppCase . insertPathsDiff
  where
    ppCase step = markStatusDiff (fst $ dpsInfo step)

    ppStep step =
           case fst $ dpsInfo step of
               (Nothing, _)  -> superfluousStep
               (_, Unmarked) -> stepLink ["sorry-step"]
               (_, Green)    -> stepLink ["hl_good"]
               (_, Yellow)   -> stepLink ["hl_medium"]
               (_, Red)      -> stepLink ["hl_bad"]
        <> case dpsMethod step of
               DiffSorry _ -> emptyDoc
               _           -> removeStep
      where
        ppMethod = prettyDiffProofMethod $ dpsMethod step
        stepLink cls = linkToPath renderUrl
            (mkRoute . snd . dpsInfo $ step)
            ("proof-step" : cls) ppMethod

        superfluousStep = withTag "span" [("class","hl_superfluous")] ppMethod

        removeStep = linkToPath renderUrl (mkRoute . snd . dpsInfo $ step)
          ["remove-step"] emptyDoc


-- | Render the indexing links for a single lemma
lemmaIndex :: HtmlDocument d
           => RenderUrl                   -- ^ The url rendering function
           -> TheoryIdx                   -- ^ The theory index
           -> Lemma IncrementalProof      -- ^ The lemma
           -> d
lemmaIndex renderUrl tidx l =
    ( markStatus (psInfo $ root annPrf) $
        (kwLemma <-> prettyLemmaName l <> colon)
        $-$
        nest 2 ( sep [ prettyTraceQuantifier $ get lTraceQuantifier l
                     , doubleQuotes $ prettyLNFormula $ get lFormula l
                     ] )

        $-$
        (linkToPath renderUrl lemmaEdit ["edit"] $ text "edit lemma") 
        <->
        text " or " 
        <->
        (linkToPath renderUrl lemmaDelete ["delete"] $ text "delete lemma")

    ) $-$
    proofIndex (get lName l) tidx renderUrl mkRoute annPrf
    $-$
    text ""
    $-$
    (linkToPath renderUrl lemmaAdd ["add"] $ text "add lemma")
  where

    lemmaEdit = TheoryPathMR tidx $ TheoryEdit $ get lName l
    lemmaDelete = TheoryPathMR tidx $ TheoryDelete $ get lName l
    lemmaAdd = TheoryPathMR tidx $ TheoryAdd $ get lName l

    annPrf = annotateLemmaProof l
    mkRoute proofPath = TheoryPathMR tidx (TheoryProof (get lName l) proofPath)

-- | Render the indexing links for a single lemma
lemmaIndexDiff :: HtmlDocument d
           => RenderUrl                   -- ^ The url rendering function
           -> TheoryIdx                   -- ^ The theory index
           -> Side
           -> Lemma IncrementalProof      -- ^ The lemma
           -> d
lemmaIndexDiff renderUrl tidx s l =
--     error (show annPrf)
    ( markStatus (psInfo $ root annPrf) $
        (kwLemma <-> prettyLemmaName l <> colon)
        $-$
        nest 2 ( sep [ prettyTraceQuantifier $ get lTraceQuantifier l
                     , doubleQuotes $ prettyLNFormula $ get lFormula l
                     ] )
    ) $-$
    proofIndex (get lName l) tidx renderUrl mkRoute annPrf
  where
    annPrf = annotateLemmaProof l
    mkRoute proofPath = TheoryPathDiffMR tidx (DiffTheoryProof s (get lName l) proofPath)

-- | Render the indexing links for a single diff lemma
diffLemmaIndex :: HtmlDocument d
           => RenderUrl                   -- ^ The url rendering function
           -> TheoryIdx                   -- ^ The theory index
           -> DiffLemma IncrementalDiffProof      -- ^ The lemma
           -> d
diffLemmaIndex renderUrl tidx l =
--     error (show annPrf)
    ( markStatusDiff (dpsInfo $ root annPrf) $
        (kwLemma <-> prettyDiffLemmaName l {-<> text (show annPrf)-} <> colon)
    ) $-$
    diffProofIndex renderUrl mkRoute annPrf
  where

    annPrf = annotateDiffLemmaProof l
    mkRoute proofPath = TheoryPathDiffMR tidx (DiffTheoryDiffProof (get lDiffName l) proofPath)


-- | Render the theory index.
theoryIndex :: HtmlDocument d => RenderUrl -> TheoryIdx -> ClosedTheory -> d
theoryIndex renderUrl tidx thy = foldr1 ($-$)
    [ kwTheoryHeader
        $ linkToPath renderUrl (TheoryPathMR tidx TheoryHelp) ["help"]
        $ text $ get thyName thy
    , text ""
    , messageLink
    , text ""
    , ruleLink
    , text ""
    , tacticLink
    , text ""
    , reqCasesLink "Raw sources" RawSource
    , text ""
    , reqCasesLink "Refined sources " RefinedSource
    , text ""
    , (linkToPath renderUrl (TheoryPathMR tidx $ TheoryAdd $ "<first>") ["add"] $ text "add lemma")
    , text ""
    , vcat $ intersperse (text "") lemmas
    , text ""
    , kwEnd
    ]
  where
    lemmaIndex' lemma = lemmaIndex renderUrl tidx lemma

    lemmas         = map lemmaIndex' (getLemmas thy)
    rules          = getClassifiedRules thy
    rulesInfo      = parens $ int $ length $ get crProtocol rules
    casesInfo kind =
        parens $ nCases <> comma <-> text chainInfo
      where
        cases   = getSource kind thy
        nChains = sum $ map (sum . unsolvedChainConstraints) cases
        nCases  = int (length cases) <-> text "cases"
        chainInfo | nChains == 0 = "deconstructions complete"
                  | otherwise    = show nChains ++ " partial deconstructions left"

    bold                = withTag "strong" [] . text
    overview n info p   = linkToPath renderUrl (TheoryPathMR tidx p) [] (bold n <-> info)
    messageLink         = overview "Message theory" (text "") TheoryMessage
    ruleLink            = overview ruleLinkMsg rulesInfo TheoryRules
    ruleLinkMsg         = "Multiset rewriting rules" ++
                          if null(theoryRestrictions thy) then "" else " and restrictions"
    tacticLink          = overview "Tactic(s)" (text "") TheoryTactic

    reqCasesLink name k = overview name (casesInfo k) (TheorySource k 0 0)

-- | Render the theory index.
diffTheoryIndex :: HtmlDocument d => RenderUrl -> TheoryIdx -> ClosedDiffTheory -> d
diffTheoryIndex renderUrl tidx thy = foldr1 ($-$)
    [ kwTheoryHeader
        $ linkToPath renderUrl (TheoryPathDiffMR tidx DiffTheoryHelp) ["help"]
        $ text $ get diffThyName thy
    , text ""
    , diffRules
    , text ""
    , messageLink LHS False
    , text ""
    , messageLink RHS False
    , text ""
    , messageLink LHS True
    , text ""
    , messageLink RHS True
    , text ""
    , ruleLink LHS False
    , text ""
    , ruleLink RHS False
    , text ""
    , ruleLink LHS True
    , text ""
    , ruleLink RHS True
    , text ""
    , reqCasesLink LHS "LHS: Raw sources "            RawSource False
    , text ""
    , reqCasesLink RHS "RHS: Raw sources "            RawSource False
    , text ""
    , reqCasesLink LHS "LHS: Raw sources [Diff] "     RawSource True
    , text ""
    , reqCasesLink RHS "RHS: Raw sources [Diff] "     RawSource True
    , text ""
    , reqCasesLink LHS "LHS: Refined sources "        RefinedSource   False
    , text ""
    , reqCasesLink RHS "RHS: Refined sources "        RefinedSource   False
    , text ""
    , reqCasesLink LHS "LHS: Refined sources [Diff] " RefinedSource   True
    , text ""
    , reqCasesLink RHS "RHS: Refined sources [Diff] " RefinedSource   True
    , text ""
    , bold "LHS: Lemmas"
    , text ""
    , vcat $ intersperse (text "") (lemmas LHS)
    , text ""
    , bold "RHS: Lemmas"
    , text ""
    , vcat $ intersperse (text "") (lemmas RHS)
    , text ""
    , bold "Diff-Lemmas"
    , text ""
    , vcat $ intersperse (text "") (diffLemmas)
    , text ""
    , kwEnd
    ]
  where
    lemmaIndex' s lemma = lemmaIndexDiff renderUrl tidx s lemma
    diffLemmaIndex' lemma = diffLemmaIndex renderUrl tidx lemma

    lemmas s           = map (lemmaIndex' s) (diffTheorySideLemmas s thy)
    diffLemmas         = map diffLemmaIndex' (getDiffLemmas thy)
    rules s isdiff     = getDiffClassifiedRules s isdiff thy
    rulesInfo s isdiff = parens $ int $ length $ get crProtocol (rules s isdiff)
    casesInfo s kind isdiff =
        parens $ nCases <> comma <-> text chainInfo
      where
        cases   = getDiffSource s isdiff kind thy
        nChains = sum $ map (sum . unsolvedChainConstraints) cases
        nCases  = int (length cases) <-> text "cases"
        chainInfo | nChains == 0 = "deconstructions complete"
                  | otherwise    = show nChains ++ " partial deconstructions left"

    bold                 = withTag "strong" [] . text
    overview n info p    = linkToPath renderUrl (TheoryPathDiffMR tidx p) [] (bold n <-> info)
    diffRules            = overview ("Diff Rules") (text "") (DiffTheoryDiffRules)
    messageLink s isdiff = overview (show s ++ ": Message theory" ++ if isdiff then " [Diff]" else "") (text "") (DiffTheoryMessage s isdiff)
    ruleLink s isdiff    = overview (ruleLinkMsg s isdiff) (rulesInfo s isdiff) (DiffTheoryRules s isdiff)
    ruleLinkMsg s isdiff = show s ++ ": Multiset rewriting rules " ++
                           (if null(diffTheorySideRestrictions s thy) then "" else " and restrictions") ++ (if isdiff then " [Diff]" else "")

    reqCasesLink s name k isdiff = overview name (casesInfo s k isdiff) (DiffTheorySource s k isdiff 0 0)


{-
-- | A snippet that explains a sequent using a rendered graph and the pretty
-- printed sequent.
sequentSnippet :: HtmlDocument d
               => System     -- ^ System to pretty print.
               -> TheoryPath  -- ^ The sequents path (NOT the path to its PNG)
               -> d
sequentSnippet se path = refDotPath path $-$ preformatted Nothing (prettySystem se)
-}

-- | A snippet that explains a sub-proof by displaying its proof state, the
-- open-goals, and the new cases.
subProofSnippet :: HtmlDocument d
                => RenderUrl
                -> RenderUrl                 -- ^ URL renderer that includes GET parameters for the image.
                -> TheoryIdx                 -- ^ The theory index.
                -> TheoryInfo                -- ^ The theory info of this index.
                -> String                    -- ^ The lemma.
                -> ProofPath                 -- ^ The proof path.
                -> ProofContext              -- ^ The proof context.
                -> IncrementalProof          -- ^ The sub-proof.
                -> d
subProofSnippet renderUrl renderImgUrl tidx ti lemma proofPath ctxt prf =
    case psInfo $ root prf of
      Nothing -> text $ "no annotated constraint system / " ++ nCases ++ " sub-case(s)"
      Just se -> vcat $
        prettyApplicableProofMethods se
        ++
        [ text ""
        , withTag "h3" [] (text "Constraint system")
        ] ++
        [ refDotPath renderImgUrl tidx (TheoryProof lemma proofPath)
        | nonEmptyGraph se ]
        ++
        [ preformatted (Just "sequent") (prettyNonGraphSystem se)
        , withTag "h3" [] (text $ nCases ++ " sub-case(s)")
        ] ++
        subCases
  where
    prettyApplicableProofMethods sys = case proofMethods sys of
        [] | finishedSubterms ctxt sys  -> [ withTag "h3" [] (text "Constraint System is Solved") ]
        []                              -> [ withTag "h3" [] (text "Constraint System is Unfinishable") ]
        pms ->
          [ withTag "h3" [] (text "Applicable Proof Methods:" <->
                             comment_ (goalRankingName ranking))
          , preformatted (Just "methods") (numbered' $ zipWith prettyPM [1..] pms)
          , autoProverLinks 'a' ""         emptyDoc      0
          , autoProverLinks 'b' "bounded-" boundDesc bound ] ++
          [ autoProverLinks 'o' "oracle-"  oracleDesc    0
          | usesOracle heuristic ] ++
          [ autoProverLinks 's' "all-"     allProve      0 ]
        where
          boundDesc = text $ " with proof-depth bound " ++ show bound
          bound     = fromMaybe 5 $ apBound $ tiAutoProver ti
          oracleDesc = text "until oracle returns nothing"
          allProve  = text " for all lemmas "
    autoProverLinks key "all-" nameSuffix bound = hsep
      [ text (key : ".")
      , linkToPath renderUrl
            (AutoProverAllR tidx CutDFS bound (TheoryProof lemma proofPath))
            ["autoprove-all"]
            (keyword_ "autoprove")
      , parens $
          text (toUpper key : ".") <->
          linkToPath renderUrl
              (AutoProverAllR tidx CutNothing bound (TheoryProof lemma proofPath))
              ["characterization-all"]
              (keyword_ "for all solutions")
      , nameSuffix
      ]
    autoProverLinks key "oracle-" nameSuffix bound = hsep
      [ text (key : ".")
      , linkToPath renderUrl
            (AutoProverR tidx CutDFS bound True (TheoryProof lemma proofPath))
            ["oracle-autoprove"]
            (keyword_ "autoprove")
      , nameSuffix ]
    autoProverLinks key classPrefix nameSuffix bound = hsep
      [ text (key : ".")
      , linkToPath renderUrl
            (AutoProverR tidx CutDFS bound False (TheoryProof lemma proofPath))
            [classPrefix ++ "autoprove"]
            (keyword_ "autoprove")
      , parens $
          text (toUpper key : ".") <->
          linkToPath renderUrl
              (AutoProverR tidx CutNothing bound False (TheoryProof lemma proofPath))
              [classPrefix ++ "characterization"]
              (keyword_ "for all solutions")
      , nameSuffix
      ]

    prettyPM i (m, (_cases, expl)) =
      linkToPath renderUrl
        (TheoryPathMR tidx (TheoryMethod lemma proofPath i))
        ["proof-method"] (prettyProofMethod m)
      <-> (if null expl then emptyDoc else lineComment_ expl)

    nCases                  = show $ M.size $ children prf
    depth                   = length proofPath
    heuristic               = selectHeuristic (tiAutoProver ti) ctxt
    ranking                 = useHeuristic heuristic depth
    tactic                 = selectTactic (tiAutoProver ti) ctxt
    proofMethods            = rankProofMethods ranking tactic ctxt
    subCases                = concatMap refSubCase $ M.toList $ children prf
    refSubCase (name, prf') =
        [ withTag "h4" [] (text "Case" <-> text name)
        , maybe (text "no proof state available")
                (const $ refDotPath renderUrl tidx $ TheoryProof lemma (proofPath ++ [name]))
                (psInfo $ root prf')
        ]

-- | A snippet that explains a sub-proof by displaying its proof state, the
-- open-goals, and the new cases.
subProofDiffSnippet :: HtmlDocument d
                    => RenderUrl
                    -> TheoryIdx                 -- ^ The theory index.
                    -> DiffTheoryInfo            -- ^ The diff theory info of this index.
                    -> Side                      -- ^ The side of the lemma.
                    -> String                    -- ^ The lemma.
                    -> ProofPath                 -- ^ The proof path.
                    -> ProofContext              -- ^ The proof context.
                    -> IncrementalProof          -- ^ The sub-proof.
                    -> d
subProofDiffSnippet renderUrl tidx ti s lemma proofPath ctxt prf =
    case psInfo $ root prf of
      Nothing -> text $ "no annotated constraint system / " ++ nCases ++ " sub-case(s)"
      Just se -> vcat $
        prettyApplicableProofMethods se
        ++
        [ text ""
        , withTag "h3" [] (text "Constraint system")
        ] ++
        [ refDotDiffPath renderUrl tidx (DiffTheoryProof s lemma proofPath) False
        | nonEmptyGraph se ]
        ++
        [ preformatted (Just "sequent") (prettyNonGraphSystem se)
        , withTag "h3" [] (text $ nCases ++ " sub-case(s)")
        ] ++
        subCases
  where
    prettyApplicableProofMethods sys = case proofMethods sys of
        [] | finishedSubterms ctxt sys  -> [ withTag "h3" [] (text "Constraint System is Solved") ]
        []                              -> [ withTag "h3" [] (text "Constraint System is Unfinishable") ]
        pms ->
          [ withTag "h3" [] (text "Applicable Proof Methods:" <->
                             comment_ (goalRankingName ranking))
          , preformatted (Just "methods") (numbered' $ map prettyPM $ zip [1..] pms)
          , autoProverLinks 'a' ""         emptyDoc      0
          , autoProverLinks 'b' "bounded-" boundDesc bound
          , autoProverLinks 's' "all-"     allProve      0
          ]
        where
          boundDesc = text $ " with proof-depth bound " ++ show bound
          bound     = fromMaybe 5 $ apBound $ dtiAutoProver ti
          allProve  = text " for all lemmas "

    autoProverLinks key "all-" nameSuffix bound = hsep
      [ text (key : ".")
      , linkToPath renderUrl
            (AutoProverAllDiffR tidx CutDFS bound)
            ["autoprove-all"]
            (keyword_ "autoprove")
      , parens $
          text (toUpper key : ".") <->
          linkToPath renderUrl
              (AutoProverAllDiffR tidx CutNothing bound)
              ["characterization-all"]
              (keyword_ "for all solutions")
      , nameSuffix
      ]
    autoProverLinks key classPrefix nameSuffix bound = hsep
      [ text (key : ".")
      , linkToPath renderUrl
            (AutoProverDiffR tidx CutDFS bound s (DiffTheoryProof s lemma proofPath))
            [classPrefix ++ "autoprove"]
            (keyword_ "autoprove")
      , parens $
          text (toUpper key : ".") <->
          linkToPath renderUrl
              (AutoProverDiffR tidx CutNothing bound s (DiffTheoryProof s lemma proofPath))
              [classPrefix ++ "characterization"]
              (keyword_ "for all solutions")
      , nameSuffix
      ]

    prettyPM (i, (m, (_cases, expl))) =
      linkToPath renderUrl
        (TheoryPathDiffMR tidx (DiffTheoryMethod s lemma proofPath i))
        ["proof-method"] (prettyProofMethod m)
      <-> (if null expl then emptyDoc else lineComment_ expl)

    nCases                  = show $ M.size $ children prf
    depth                   = length proofPath
    heuristic               = selectHeuristic (dtiAutoProver ti) ctxt
    ranking                 = useHeuristic heuristic depth
    tactic                 = selectTactic (dtiAutoProver ti) ctxt
    proofMethods            = rankProofMethods ranking tactic ctxt
    subCases                = concatMap refSubCase $ M.toList $ children prf
    refSubCase (name, prf') =
        [ withTag "h4" [] (text "Case" <-> text name)
        , maybe (text "no proof state available")
                (const $ refDotDiffPath renderUrl tidx (DiffTheoryProof s lemma (proofPath ++ [name])) False)
                (psInfo $ root prf')
        ]

-- | A snippet that explains a sub-proof by displaying its proof state, the
-- open-goals, and the new cases.
subDiffProofSnippet :: HtmlDocument d
                    => RenderUrl
                    -> TheoryIdx                 -- ^ The theory index.
                    -> DiffTheoryInfo            -- ^ The diff theory info of this index.
                    -> String                    -- ^ The diff lemma.
                    -> ProofPath                 -- ^ The proof path.
                    -> DiffProofContext          -- ^ The proof context.
                    -> IncrementalDiffProof      -- ^ The sub-proof.
                    -> d
subDiffProofSnippet renderUrl tidx ti lemma proofPath ctxt prf =
    case dpsInfo $ root prf of
      Nothing -> text $ "no annotated constraint system / " ++ nCases ++ " sub-case(s)"
      Just se -> vcat $
        prettyApplicableDiffProofMethods se
        ++
        [ text ""
        , withTag "h3" [] (text "Constraint system")
        ] ++
        [ refDotDiffPath renderUrl tidx (DiffTheoryDiffProof lemma proofPath) False
        | nonEmptyGraphDiff se ]
        ++
        mirrorSystem
        ++
        [ preformatted (Just "sequent") (prettyNonGraphSystemDiff ctxt se)
        , withTag "h3" [] (text $ nCases ++ " sub-case(s)")
        ] ++
        subCases
  where
    prettyApplicableDiffProofMethods sys = case (diffProofMethods sys, get dsSide sys, get dsSystem sys) of
        ([], Nothing, _)                                                                  -> [ withTag "h3" [] (text "Constraint System is Solved") ]
        ([], _, Nothing)                                                                  -> [ withTag "h3" [] (text "Constraint System is Solved") ]
        ([], Just side, Just sys') | finishedSubterms (eitherProofContext ctxt side) sys' -> [ withTag "h3" [] (text "Constraint System is Solved") ]
        ([], _, _)                                                                           -> [ withTag "h3" [] (text "Constraint System is Unfinishable") ]
        (pms, _, _) ->
          [ withTag "h3" [] (text "Applicable Proof Methods:" <->
                             comment_ (goalRankingName ranking))
          , preformatted (Just "methods") (numbered' $ zipWith prettyPM [1..] pms)
          , autoProverLinks 'a' ""         emptyDoc      0
          , autoProverLinks 'b' "bounded-" boundDesc bound
          , autoProverLinks 's' "all-"     allProve      0
          ]
        where
          boundDesc = text $ " with proof-depth bound " ++ show bound
          bound     = fromMaybe 5 $ apBound $ dtiAutoProver ti
          allProve  = text " for all lemmas "

    mirrorSystem =
        if dpsMethod (root prf) == DiffMirrored
           then [ text "", withTag "h3" [] (text "mirror:") ] ++
                [ refDotDiffPath renderUrl tidx (DiffTheoryDiffProof lemma proofPath) True ] ++
                [ text "" ]
        else if dpsMethod (root prf) == DiffAttack
           then [ text "", withTag "h3" [] (text "attack:") ] ++
                [ refDotDiffPath renderUrl tidx (DiffTheoryDiffProof lemma proofPath) True ] ++
                [ text "(If no attack graph is shown, the current graph has no mirrors. If one of the mirror graphs violates a restriction, this graph is shown.)" ] ++
                [ text "" ]
        else if dpsMethod (root prf) == DiffUnfinishable
           then [ text "", withTag "h3" [] (text "mirror:") ] ++
                [ refDotDiffPath renderUrl tidx (DiffTheoryDiffProof lemma proofPath) True ] ++
                [ text "The proof cannot be finished as there are reducible operators at the top of subterms in the subterm store." ] ++
                [ text "" ]
           else []

    autoProverLinks key "all-" nameSuffix bound = hsep
      [ text (key : ".")
      , linkToPath renderUrl
            (AutoProverAllDiffR tidx CutDFS bound)
            ["autoprove-all"]
            (keyword_ "autoprove")
      , parens $
          text (toUpper key : ".") <->
          linkToPath renderUrl
              (AutoProverAllDiffR tidx CutNothing bound)
              ["characterization-all"]
              (keyword_ "for all solutions")
      , nameSuffix ]
    autoProverLinks key classPrefix nameSuffix bound = hsep
      [ text (key : ".")
      , linkToPath renderUrl
            (AutoDiffProverR tidx CutDFS bound (DiffTheoryDiffProof lemma proofPath))
            [classPrefix ++ "autoprove"]
            (keyword_ "autoprove")
      , parens $
          text (toUpper key : ".") <->
          linkToPath renderUrl
              (AutoDiffProverR tidx CutNothing bound (DiffTheoryDiffProof lemma proofPath))
              [classPrefix ++ "characterization"]
              (keyword_ "for all solutions")
      , nameSuffix ]

    prettyPM i (m, (_cases, expl)) =
      linkToPath renderUrl
        (TheoryPathDiffMR tidx (DiffTheoryDiffMethod lemma proofPath i))
        ["proof-method"] (prettyDiffProofMethod m)
      <-> (if null expl then emptyDoc else lineComment_ expl)

    nCases                  = show $ M.size $ children prf
    depth                   = length proofPath
    heuristic               = selectDiffHeuristic (dtiAutoProver ti) ctxt
    ranking                 = useHeuristic heuristic depth
    tactic                 = selectDiffTactic (dtiAutoProver ti) ctxt
    diffProofMethods        = rankDiffProofMethods ranking tactic ctxt
    subCases                = concatMap refSubCase $ M.toList $ children prf
    refSubCase (name, prf') =
        [ withTag "h4" [] (text "Case" <-> text name)
        , maybe (text "no proof state available")
                (const $ refDotDiffPath renderUrl tidx (DiffTheoryDiffProof lemma (proofPath ++ [name])) False)
                (dpsInfo $ root prf')
        ]

-- | A Html document representing the requires case splitting theorem.
htmlSource :: HtmlDocument d
                    => RenderUrl -> TheoryIdx -> SourceKind -> (Int, Source) -> d
htmlSource renderUrl tidx kind (j, th) =
    if null cases
      then withTag "h2" [] ppHeader $-$ withTag "h3" [] (text "No cases.")
      else vcat $ withTag "h2" [] ppHeader : cases
  where
    cases    = concatMap ppCase $ zip [1..] $ getDisj $ get cdCases th
    wrapP    = withTag "p" [("class","monospace cases")]
    nCases   = int $ length $ getDisj $ get cdCases th
    ppPrem   = nest 2 $ doubleQuotes $ prettyGoal $ get cdGoal th
    ppHeader = hsep
      [ text "Sources of" <-> ppPrem
      , parens $ nCases <-> text "cases"
      ]
    ppCase (i, (names, se)) =
      [ withTag "h3" [] $ fsep [ text "Source", int i, text "of", nCases
                               , text " / named ", doubleQuotes (text name),
                                 if isPartial then text "(partial deconstructions)" else text "" ]
      , refDotPath renderUrl tidx (TheorySource kind j i)
      , withTag "p" [] $ ppPrem
      , wrapP $ prettyNonGraphSystem se
      ]
      where
        name = intercalate "_" names
        isPartial = not $ null $ unsolvedChains se

-- | A Html document representing the requires case splitting theorem.
htmlSourceDiff :: HtmlDocument d
                    => RenderUrl -> TheoryIdx -> Side -> SourceKind -> Bool -> (Int, Source) -> d
htmlSourceDiff renderUrl tidx s kind d (j, th) =
    if null cases
      then withTag "h2" [] ppHeader $-$ withTag "h3" [] (text "No cases.")
      else vcat $ withTag "h2" [] ppHeader : cases
  where
    cases    = concatMap ppCase $ zip [1..] $ getDisj $ get cdCases th
    wrapP    = withTag "p" [("class","monospace cases")]
    nCases   = int $ length $ getDisj $ get cdCases th
    ppPrem   = nest 2 $ doubleQuotes $ prettyGoal $ get cdGoal th
    ppHeader = hsep
      [ text "Sources of" <-> ppPrem
      , parens $ nCases <-> text "cases"
      ]
    ppCase (i, (names, se)) =
      [ withTag "h3" [] $ fsep [ text "Source", int i, text "of", nCases
                               , text " / named ", doubleQuotes (text name),
                                 if isPartial then text "(partial deconstructions)" else text "" ]
      , refDotDiffPath renderUrl tidx (DiffTheorySource s kind d j i) False
      , withTag "p" [] ppPrem
      , wrapP $ prettyNonGraphSystem se
      ]
      where
        name = intercalate "_" names
        isPartial = not $ null $ unsolvedChains se


-- | Build the Html document showing the source cases.
reqCasesSnippet :: HtmlDocument d => RenderUrl -> TheoryIdx -> SourceKind -> ClosedTheory -> d
reqCasesSnippet renderUrl tidx kind thy = vcat $
    htmlSource renderUrl tidx kind <$> zip [1..] (getSource kind thy)

-- | Build the Html document showing the source cases.
reqCasesDiffSnippet :: HtmlDocument d => RenderUrl -> TheoryIdx -> Side -> SourceKind -> Bool -> ClosedDiffTheory -> d
reqCasesDiffSnippet renderUrl tidx s kind isdiff thy = vcat $
    htmlSourceDiff renderUrl tidx s kind isdiff <$> zip [1..] (getDiffSource s isdiff kind thy)

-- | Build the Html document showing the rules of the theory.
rulesSnippet :: HtmlDocument d => ClosedTheory -> d
rulesSnippet thy = vcat
    [ if null(theoryMacros thy) then text empty
                                else ppWithHeader "Macros" $ 
        (prettyMacros $ theoryMacros thy)
    , ppWithHeader "Fact Symbols with Injective Instances" $
        (if null injFacts then text "None" else fsepList (text . showInjFact) injFacts)
    , ppWithHeader "Multiset Rewriting Rules" $
        (if null(theoryMacros thy) then text empty else text "(Shown with macros application)") <-> (vsep $ map prettyRuleAC msrRules)
    , ppWithHeader "Restrictions of the Set of Traces" $
        vsep $ map prettyRestriction $ theoryRestrictions thy
    ]
  where
    msrRules   = get crProtocol $ getClassifiedRules thy
    injFacts   = S.toList $ getInjectiveFactInsts thy
    showInjFact (tag, behaviours) = showFactTag tag ++ "(" ++ concat (intersperse "," ("id":positions)) ++ ")"
      where positions = [case bb of
                          [b] -> show b
                          _   -> "(" ++ concat (intersperse "," (map show bb)) ++ ")"
                        | bb <- behaviours ]
    ppWithHeader header body =
        caseEmptyDoc
            emptyDoc
            ( withTag "h2" []                            (text header) $$
              withTag "p"  [("class","monospace rules")] body             )
            body

-- | Build the Html document showing the message theory.
messageSnippet :: HtmlDocument d => ClosedTheory -> d
messageSnippet thy = vcat
    [ ppSection "Signature"            [prettySignatureWithMaude (get thySignature thy)]
    , ppSection "Construction Rules"   (ppRules crConstruct)
    , ppSection "Deconstruction Rules" (ppRules crDestruct)
    ]
  where
    ppRules l = map prettyRuleAC $ get l $ getClassifiedRules thy
    ppSection header s =
      withTag "h2" [] (text header) $$ withTag "p"
        [("class","monospace rules")]
        (vcat (intersperse (text "") $ s))

-- | Build the Html document showing the message theory.
tacticSnippet :: HtmlDocument d => ClosedTheory -> d
tacticSnippet thy = ppSection "Tactic(s)" (map prettyTactic $ get thyTactic thy)
  where
    ppSection header s =
      withTag "h2" [] (text header) $$ withTag "p"
        [("class","monospace rules")]
        (vcat (intersperse (text "") $ s))

-- | Build the Html document showing the diff rules of the diff theory.
rulesDiffSnippet :: HtmlDocument d => ClosedDiffTheory -> d
rulesDiffSnippet thy = vcat
    [ ppWithHeader "Multiset Rewriting Rules" $
        vsep $ map prettyDiffRule msrRules
    ]
  where
    msrRules   = diffTheoryDiffRules thy
    ppWithHeader header body =
        caseEmptyDoc
            emptyDoc
            ( withTag "h2" []                            (text header) $$
              withTag "p"  [("class","monospace rules")] body             )
            body

-- | Build the Html document showing the either rules of the diff theory.
rulesDiffSnippetSide :: HtmlDocument d => Side -> Bool -> ClosedDiffTheory -> d
rulesDiffSnippetSide s isdiff thy = vcat
    [ if null(diffTheoryMacros thy) then text empty
                                     else ppWithHeader "Macros" $
        (prettyMacros $ diffTheoryMacros thy)
    ,ppWithHeader "Fact Symbols with Injective Instances" $
        (if null injFacts then text "None" else fsepList (text . showInjFact) injFacts)
    , ppWithHeader "Multiset Rewriting Rules" $
        (if null(diffTheoryMacros thy) then text empty else text "(Shown with macros application)") <-> (vsep $ map prettyRuleAC msrRules)
    , ppWithHeader "Restrictions of the Set of Traces" $
        vsep $ map prettyRestriction $ diffTheorySideRestrictions s thy
    ]
  where
    msrRules = get crProtocol $ getDiffClassifiedRules s isdiff thy
    injFacts = S.toList $ getDiffInjectiveFactInsts s isdiff thy
    showInjFact (tag, behaviours) = showFactTag tag ++ "(" ++ concat (intersperse "," ("id":positions)) ++ ")"
      where positions = [case bb of
                          [b] -> show b
                          _   -> "(" ++ concat (intersperse "," (map show bb)) ++ ")"
                        | bb <- behaviours ]
    ppWithHeader header body =
        caseEmptyDoc
            emptyDoc
            ( withTag "h2" []                            (text header) $$
              withTag "p"  [("class","monospace rules")] body             )
            body


-- | Build the Html document showing the message theory.
messageDiffSnippet :: HtmlDocument d => Side -> Bool -> ClosedDiffTheory -> d
messageDiffSnippet s isdiff thy = vcat
    [ ppSection "Signature"            [prettySignatureWithMaude (get diffThySignature thy)]
    , ppSection "Construction Rules"   (ppRules crConstruct)
    , ppSection "Deconstruction Rules" (ppRules crDestruct)
    ]
  where
    ppRules l = map prettyRuleAC $ get l $ getDiffClassifiedRules s isdiff thy
    ppSection header t =
      withTag "h2" [] (text header) $$ withTag "p"
        [("class","monospace rules")]
        (vcat (intersperse (text "") $ t))

-- | Render the item in the given theory given by the supplied path.
htmlThyPath :: RenderUrl      -- ^ The function for rendering Urls.
            -> RenderUrl      -- ^ URL renderer that includes GET parameters for the image.
            -> TheoryInfo     -- ^ The info of the theory to render
            -> TheoryPath     -- ^ Path to render
            -> String         -- ^ the lemma's plaintext
            -> Html
htmlThyPath renderUrl renderImgUrl info path lPlaintext =   go path
  where
    thy  = tiTheory info
    tidx = tiIndex  info

    -- Rendering a HtmlDoc to Html
    pp :: HtmlDoc Doc -> Html
    pp d = case renderHtmlDoc d of
      [] -> toHtml "Trying to render document yielded empty string. This is a bug."
      cs -> preEscapedToMarkup cs

    go (TheoryMethod _ _ _)    = pp $ text "Cannot display theory method."

    go TheoryRules             = pp $ rulesSnippet thy
    go TheoryMessage           = pp $ messageSnippet thy
    go TheoryTactic            = pp $ tacticSnippet thy 
    go (TheorySource kind _ _) = pp $ reqCasesSnippet renderUrl tidx kind thy

    go (TheoryProof l p)       = pp $
        fromMaybe (text "No such lemma or proof path.") $ do
           lemma <- lookupLemma l thy
           subProofSnippet renderUrl renderImgUrl tidx info l p (getProofContext lemma thy)
             <$> resolveProofPath thy l p

    go (TheoryEdit name) = do
        let p = "../../edit/edit/"++name
        [hamlet|
             <form method="post" action=#{p}>
                <div contenteditable="true">
                    <label for="lemmaTextArea"> Edit Lemma #{name}
                    <textarea name="lemma-text" id="lemmaTextArea" rows=#{textHeight}>#{lPlaintext}
                <button type="submit">Submit
                <p>
                <h3> Introduction to Lemma Edit:
                <noscript>
                  <div class="warning">
                    Warning: JavaScript must be enabled for the
                    <span class="tamarin">Tamarin</span>
                    prover GUI to function properly.
                <p>
                  <ul .wrap-text>
                    <li>
                     Modifying the lemma in the box above and clicking the submit button will attempt to modify the lemma in the current theory.
                     <br>&zwnj;
                    <li>
                     Failures in parsing the lemma or verifying its well-formedness will result in an error, and the lemma will NOT be modified.
                     However, your changes will be kept on this page until you leave this right panel.
                     <br>&zwnj;
                    <li>
                     Editing a lemma will NOT modify the file it was loaded from, but clicking on the "append lemmas to file" button adds all modified lemmas as a comment at the end of the file on disk they were loaded from.
                     <br>&zwnj;
                    <li>
                     Clicking on the "Download" button will download the modified version of the theory (including the modified lemmas), but not modify the file on disk.
                     <br>&zwnj;
                    <li>
                     Modifying a reuse lemma will invalidate all subsequent proofs.
                     <br>&zwnj;
                    <li>
                     Modifying a sources lemma is not supported and will result in an error.
                  <style>
                     .wrap-text li {
                         white-space: normal;
                         word-wrap: break-word;
                     }
                  |] renderUrl
        where textHeight = 2 + (length $ filter (=='\n') lPlaintext)

    go (TheoryLemma _)         = pp $ text "this is a mistake"

    go (TheoryDelete name)        = do
        let p = "../../edit/delete/" ++ name
        [hamlet|
        <p> Do you want to delete lemma #{name}?
        <form method="post" action=#{p}>
            <button type="submit">Yes
          <p>
          <h3> Introduction to Lemma Delete:
          <noscript>
            <div class="warning">
              Warning: JavaScript must be enabled for the
              <span class="tamarin">Tamarin</span>
              prover GUI to function properly.
          <p>
            <ul .wrap-text>
              <li>
               Clicking on the button above will delete the lemma from the loaded theory.
               <br>&zwnj;
              <li>
               Deleting a lemma will NOT modify the file it was loaded from, but clicking on the "Download" button will download the modified version of the theory (so without the deleted lemmas).
               <br>&zwnj;
              <li>
               Deleting a reuse lemma will invalidate all subsequent proofs.
               <br>&zwnj;
              <li>
               Deleting a source lemma is not supported and will result in an error.
             <style>
                 .wrap-text li {
                     white-space: normal;
                     word-wrap: break-word;
                 }
             |] renderUrl

    go (TheoryAdd name)  = do
        let p = "../../edit/add/" ++ name
        [hamlet|
             <form method="post" action=#{p}>
                <div contenteditable="true">
                    <label for="lemmaTextArea">LemmaText
                    <textarea name="lemma-text" id="lemmaTextArea">#{lPlaintext}
                <button type="submit">Submit
              <p>
              <h3> Introduction to Adding Lemmas:
              <noscript>
                <div class="warning">
                  Warning: JavaScript must be enabled for the
                  <span class="tamarin">Tamarin</span>
                  prover GUI to function properly.
              <p>
                <ul .wrap-text>
                  <li>
                   Adds the lemma in the current position in the theory, but will throw an error if a lemma with the same name exists, the parsing fails, or the lemma isn't well-formed.
                   <br>&zwnj;
                  <li>
                   Adding a lemma will NOT modify the loaded source file, but clicking on the "Append lemmas to file" button appends all added lemmas as a comment at the end of the current theory file.
                   <br>&zwnj;
                  <li>
                   Clicking on the "Download" button will download the modified version of the theory (including the added lemmas).
                <style>
                    .wrap-text li {
                        white-space: normal;
                        word-wrap: break-word;
                    }
                |] renderUrl


    go TheoryHelp              = do
      [hamlet|
        $newline never
        <p>
          Theory: #{get thyName $ tiTheory info}
          \ (Loaded at #{formatTime defaultTimeLocale "%T" $ tiTime info}
          \ from #{show $ tiOrigin info})
          \ #{preEscapedToMarkup infoErrors}
        <div id="help">
          <h3>Quick introduction
          <noscript>
            <div class="warning">
              Warning: JavaScript must be enabled for the
              <span class="tamarin">Tamarin</span>
              prover GUI to function properly.
          <p>
            <em>Left pane: Proof scripts display.
            <ul>
              <li>
                When a theory is initially loaded, there will be a line at the
                \ end of each theorem stating #
                <tt>"by sorry // not yet proven"
                .  Click on #
                <tt>sorry
                \ to inspect the proof state.
              <li>
                Right-click to show further options, such as autoprove.
          <p>
            <em>Right pane: Visualization.
            <ul>
              <li>
                Visualization and information display relating to the
                \ currently selected item.

        <h3>Keyboard shortcuts
        <p>
          <table>
            <tr>
              <td>
                <span class="keys">j/k
              <td>
                Jump to the next/previous proof path within the currently
                \ focused lemma.
            <tr>
              <td>
                <span class="keys">J/K
              <td>
                Jump to the next/previous open constraint within the currently
                \ focused lemma, or to the next/previous lemma if there are no
                \ more #
                <tt>sorry
                \ steps in the proof of the current lemma.
            <tr>
              <td>
                <span class="keys">1-9
              <td>
                Apply the proof method with the given number as shown in the
                \ applicable proof method section in the main view.
            <tr>
              <td>
                <span class="keys">a/A
              <td>
                Apply the autoprove method to the focused proof step.
                \ <span class="keys">a</span>
                \ stops after finding a solution, and
                \ <span class="keys">A</span>
                \ searches for all solutions.
                \ Needs to have a #
                <tt>sorry
                \ selected to work.
            <tr>
              <td>
                <span class="keys">b/B
              <td>
                Apply a bounded-depth version of the autoprove method to the
                \ focused proof step.
                \ <span class="keys">b</span>
                \ stops after finding a solution, and
                \ <span class="keys">B</span>
                \ searches for all solutions.
                \ Needs to have a #
                <tt>sorry
                \ selected to work.
            <tr>
              <td>
                <span class="keys">s/S
              <td>
                Apply the autoprove method to all lemmas.
                \ <span class="keys">s</span>
                \ stops after finding a solution, and
                \ <span class="keys">S</span>
                \ searches for all solutions.
            <tr>
              <td>
                <span class="keys">?
              <td>
                Display this help message.
      |] renderUrl
         where
             infoErrors = tiErrorsHtml info

-- | Render the item in the given theory given by the supplied path.
htmlDiffThyPath :: RenderUrl    -- ^ The function for rendering Urls.
                -> DiffTheoryInfo   -- ^ The info of the theory to render
                -> DiffTheoryPath   -- ^ Path to render
                -> Html
htmlDiffThyPath renderUrl info path =
    go path
  where
    thy  = dtiTheory info
    tidx = dtiIndex  info

    -- Rendering a HtmlDoc to Html
    pp :: HtmlDoc Doc -> Html
    pp d = case renderHtmlDoc d of
      [] -> toHtml "Trying to render document yielded empty string. This is a bug."
      cs -> preEscapedToMarkup cs

    go (DiffTheoryMethod _ _ _ _)      = pp $ text "Cannot display theory method."
    go (DiffTheoryDiffMethod _ _ _)    = pp $ text "Cannot display theory diff method."

    go (DiffTheoryDiffLemma _)         = pp $ text "Implement diff lemma pretty printing!"

    go (DiffTheoryDiffRules)           = pp $ rulesDiffSnippet thy
    go (DiffTheoryRules s d)           = pp $ rulesDiffSnippetSide s d thy
    go (DiffTheoryMessage s d)         = pp $ messageDiffSnippet s d thy
    go (DiffTheorySource s kind d _ _) = pp $ reqCasesDiffSnippet renderUrl tidx s kind d thy

    go (DiffTheoryProof s l p)         = pp $
        fromMaybe (text "No such lemma or proof path.") $ do
           lemma <- lookupLemmaDiff s l thy
           subProofDiffSnippet renderUrl tidx info s l p (getProofContextDiff s lemma thy)
             <$> resolveProofPathDiff thy s l p

    go (DiffTheoryDiffProof l p)       = pp $
        fromMaybe (text "No such lemma or proof path.") $ do
           lemma <- lookupDiffLemma l thy
           subDiffProofSnippet renderUrl tidx info l p (getDiffProofContext lemma thy)
             <$> resolveProofPathDiffLemma thy l p

    go (DiffTheoryLemma _ _)           = pp $ text "Implement lemma pretty printing!"

    go DiffTheoryHelp                  = [hamlet|
        $newline never
        <p>
          Theory: #{get diffThyName $ dtiTheory info}
          \ (Loaded at #{formatTime defaultTimeLocale "%T" $ dtiTime info}
          \ from #{show $ dtiOrigin info})
          \ #{preEscapedToMarkup infoErrors}
        <div id="help">
          <h3>Quick introduction
          <noscript>
            <div class="warning">
              Warning: JavaScript must be enabled for the
              <span class="tamarin">Tamarin</span>
              prover GUI to function properly.
          <p>
            <em>Left pane: Proof scripts display.
            <ul>
              <li>
                When a theory is initially loaded, there will be a line at the
                \ end of each theorem stating #
                <tt>"by sorry // not yet proven"
                .  Click on #
                <tt>sorry
                \ to inspect the proof state.
              <li>
                Right-click to show further options, such as autoprove.
          <p>
            <em>Right pane: Visualization.
            <ul>
              <li>
                Visualization and information display relating to the
                \ currently selected item.

        <h3>Keyboard shortcuts
        <p>
          <table>
            <tr>
              <td>
                <span class="keys">j/k
              <td>
                Jump to the next/previous proof path within the currently
                \ focused lemma.
            <tr>
              <td>
                <span class="keys">J/K
              <td>
                Jump to the next/previous open constraint within the currently
                \ focused lemma, or to the next/previous lemma if there are no
                \ more #
                <tt>sorry
                \ steps in the proof of the current lemma.
            <tr>
              <td>
                <span class="keys">1-9
              <td>
                Apply the proof method with the given number as shown in the
                \ applicable proof method section in the main view.
            <tr>
              <td>
                <span class="keys">a/A
              <td>
                Apply the autoprove method to the focused proof step.
                \ <span class="keys">a</span>
                \ stops after finding a solution, and
                \ <span class="keys">A</span>
                \ searches for all solutions.
                \ Needs to have a #
                <tt>sorry
                \ selected to work.
            <tr>
              <td>
                <span class="keys">b/B
              <td>
                Apply a bounded-depth version of the autoprove method to the
                \ focused proof step.
                \ <span class="keys">b</span>
                \ stops after finding a solution, and
                \ <span class="keys">B</span>
                \ searches for all solutions.
                \ Needs to have a #
                <tt>sorry
                \ selected to work.
            <tr>
              <td>
                <span class="keys">s/S
              <td>
                Apply the autoprove method to all lemmas.
                \ <span class="keys">s</span>
                \ stops after finding a solution, and
                \ <span class="keys">S</span>
                \ searches for all solutions.
            <tr>
              <td>
                <span class="keys">?
              <td>
                Display this help message.
      |] renderUrl
         where
             infoErrors = dtiErrorsHtml info

{-
-- | Render debug information for the item in the theory given by the path.
htmlThyDbgPath :: HtmlDocument d
               => ClosedTheory -- ^ The theory to render
               -> TheoryPath   -- ^ Path to render
               -> Maybe d
htmlThyDbgPath thy path = go path
  where
    go (TheoryProof l p) = do
      proof <- resolveProofPath thy l p
      prettySystem <$> psInfo (root proof)
    go _ = Nothing
-}

-- | Output either JSON or an image corresponding to the given theory path and return the generated file's path.
-- Returns Nothing if there was an error during the image generation.
imgThyPath :: ImageFormat                  -- ^ The preferred image output format. 
           -> OutputCommand                -- ^ Choice and command for rendering.
           -> FilePath                     -- ^ Tamarin's cache directory
           -> (System -> D.Dot ())         -- ^ Function to render a System to Graphviz dot format.
           -> (String -> System -> String) -- ^ Function to render a System to JSON.
           -> ClosedTheory                 -- ^ Theory from which to extract the 'System'.
           -> TheoryPath                   -- ^ Path of the 'System' in the theory.
           -> IO (Maybe FilePath)          -- ^ Path to the generated file.
imgThyPath imageFormat outputCommand cacheDir_ toDot toJSON thy thyPath = 
    case thyPathSystem thyPath of
      Nothing -> return Nothing
      Just (jsonLabel, system) -> do
        let code = case ocFormat outputCommand of
                     OutDot -> prefixedShowDot $ toDot system
                     OutJSON -> toJSON jsonLabel system 
        renderGraphCode code
  where
    thyPathSystem :: TheoryPath -> Maybe (String, System)
    thyPathSystem (TheorySource k i j)          = casesSystem k i j
    thyPathSystem (TheoryProof lemma proofPath) = proofPathSystem lemma proofPath
    thyPathSystem _                             = error "Unhandled theory path. This is a bug."

    -- | Get a string serialization for one case.
    casesSystem k i j = do
      let jsonLabel = "Theory: " ++ (get thyName thy) ++ " Case: " ++ show i ++ ":" ++ show j
          cases = map (getDisj . get cdCases) (getSource k thy)
      return (jsonLabel, snd $ cases !! (i-1) !! (j-1))

    -- | Get string serialization for proof path in lemma.
    proofPathSystem lemma proofPath = do
      let jsonLabel = "Theory: " ++ (get thyName thy) ++ " Lemma: " ++ lemma 
      subProof <- resolveProofPath thy lemma proofPath
      sequent <- psInfo $ root subProof
      return (jsonLabel, sequent)

    -- | Prefix dot code with comment mentioning all protocol rule names
    prefixedShowDot dot = unlines
        [ "// protocol rules: "          ++ ruleList (getProtoRuleEs thy)
        , "// message deduction rules: " ++ ruleList (getIntrVariants thy)
        , D.showDot "G" dot
        ]
      where
        ruleList :: HasRuleName (Rule i) => [Rule i] -> String
        ruleList = concat . intersperse ", " . nub . map showRuleCaseName

    -- Render a piece of dot or JSON code
    renderGraphCode code = do
      let graphPath = cacheDir_ </> getGraphPath (ocFormat outputCommand) code
          imgPath = addExtension graphPath $ show imageFormat

          -- A busy wait loop with a maximal number of iterations
          renderedOrRendering :: Int -> IO Bool
          renderedOrRendering n = do
              graphExists <- doesFileExist graphPath
              imgExists <- doesFileExist imgPath
              if (n > 0 && graphExists && not imgExists)
                  then do
                    threadDelay (10 * 1000) -- wait 10 ms
                    renderedOrRendering (n - 1)
                  else return imgExists

      -- Ensure that the output directory exists.
      createDirectoryIfMissing True (takeDirectory graphPath)

      imgGenerated <- firstSuccess
        [ -- There might be some other thread that rendered or is rendering
          -- this dot file. We wait at most 50 iterations (0.5 sec timout)
          -- for this other thread to render the image. Afterwards, we give
          -- it a try by ourselves.
          renderedOrRendering 50,
          -- create dot-file and render to image
          do
            writeFile graphPath code
            -- select the correct command to generate img
            case ocFormat outputCommand of
              OutDot  -> dotToImg "dot" graphPath imgPath
              OutJSON -> jsonToImg graphPath imgPath,
          -- sometimes 'dot' fails => use 'fdp' as a backup tool
          case ocFormat outputCommand of
            OutDot -> dotToImg "fdp" graphPath imgPath
            _      -> return False
        ]
      if imgGenerated
        then return $ Just imgPath
        else trace ("WARNING: failed to convert:\n  '" ++ graphPath ++ "'")
                   (return Nothing)

    -- render img file from json file
    jsonToImg jsonFile imgFile = do
      (ecode,_out,err) <- readProcessWithExitCode (ocGraphCommand outputCommand) [imgFile, jsonFile] ""
      case ecode of
        ExitSuccess   -> return True
        ExitFailure i -> do
          putStrLn $ "jsonToImg: "++ ocGraphCommand outputCommand ++" failed with code "
                      ++show i++" for file "++jsonFile++":\n"++err
          return False

    -- render img file from dot file
    dotToImg dotMode dotFile imgFile = do
      (ecode,_out,err) <- readProcessWithExitCode (ocGraphCommand outputCommand)
                              [ "-T"++show imageFormat, "-K"++dotMode, "-o",imgFile, dotFile]
                              ""
      case ecode of
        ExitSuccess   -> return True
        ExitFailure i -> do
          putStrLn $ "dotToImg: "++ ocGraphCommand outputCommand ++" failed with code "
                      ++show i++" for file "++dotFile++":\n"++err
          return False

    firstSuccess []     = return False
    firstSuccess (m:ms) = do
      s <- m
      if s then return True else firstSuccess ms

-- | Render the image corresponding to the given theory path.
-- Returns Nothing if there was an error during image generation.
imgDiffThyPath :: ImageFormat
           -> FilePath               -- ^ 'dot' command
           -> FilePath               -- ^ Tamarin's cache directory
           -> (System -> D.Dot ())
           -> ClosedDiffTheory
           -> DiffTheoryPath
           -> Bool
           -> IO (Maybe FilePath)            -- ^ True if we want the mirror graph
imgDiffThyPath imgFormat dotCommand cacheDir_ compact thy path mirror = go path
  where
    go (DiffTheorySource s k d i j) = renderDotCode (casesDotCode s k i j d)
    go (DiffTheoryProof s l p)      = renderDotCode (proofPathDotCode s l p)
    go (DiffTheoryDiffProof l p)    = renderDotCode (proofPathDotCodeDiff l p mirror)
    go _                            = error "Unhandled theory path. This is a bug."

    -- Prefix dot code with comment mentioning all protocol rule names
    prefixedShowDot dot = unlines
        [ "// protocol rules: "          ++ ruleList (getProtoRuleEsDiff LHS thy) -- FIXME RS: the rule names are the same on LHS and RHS, so we just pick LHS; should pass the current Side through to make this clean
        , "// message deduction rules: " ++ ruleList (getIntrVariantsDiff LHS thy) -- FIXME RS: the intruder rule names are the same on LHS and RHS; should pass the current Side through to make this clean
--        , "// message deduction rules: " ++ ruleList ((intruderRules . get (_crcRules . diffThyCacheLeft)) thy) -- FIXME RS: again, we arbitrarily pick the LHS version of the cache, should be the same on both sides
--intruderRules . L.get (crcRules . diffThyCacheLeft)
        , D.showDot "G" dot
        ]
      where
        ruleList :: HasRuleName (Rule i) => [Rule i] -> String
        ruleList = concat . intersperse ", " . nub . map showRuleCaseName

    -- Get dot code for required cases
    casesDotCode s k i j isdiff = prefixedShowDot $
        compact $ snd $ cases !! (i-1) !! (j-1)
      where
        cases = map (getDisj . get cdCases) (getDiffSource s isdiff k thy)

    -- Get dot code for proof path in lemma
    proofPathDotCode s lemma proofPath =
      D.showDot "G" $ fromMaybe (return ()) $ do
        subProof <- resolveProofPathDiff thy s lemma proofPath
        sequent <- psInfo $ root subProof
        return $ compact sequent

    -- Get dot code for proof path in lemma
    proofPathDotCodeDiff lemma proofPath mir =
      D.showDot "G" $ fromMaybe (return ()) $ do
        subProof <- resolveProofPathDiffLemma thy lemma proofPath
        diffSequent <- dpsInfo $ root subProof
        if mir
          then do
            lem <- lookupDiffLemma lemma thy
            let ctxt = getDiffProofContext lem thy
            side <- get dsSide diffSequent
            let isSolved s sys' = (rankProofMethods GoalNrRanking [defaultTactic] (eitherProofContext ctxt s) sys') == [] -- checks if the system is solved
            nsequent <- get dsSystem diffSequent
            -- Here we can potentially get Nothing if there is no mirror DG
            let sequentList = snd $ getMirrorDGandEvaluateRestrictions ctxt diffSequent (isSolved side nsequent)
            if null sequentList then Nothing else return $ compact $ head sequentList
          else do
            sequent <- get dsSystem diffSequent
            return $ compact sequent

    -- Render a piece of dot code
    renderDotCode code = do
      let dotPath = cacheDir_ </> getDotPath code
          imgPath = addExtension dotPath (show imgFormat)

          -- A busy wait loop with a maximal number of iterations
          renderedOrRendering :: Int -> IO Bool
          renderedOrRendering n = do
              dotExists <- doesFileExist dotPath
              imgExists <- doesFileExist imgPath
              if (n > 0 && dotExists && not imgExists)
                  then do threadDelay (10 * 1000) -- wait 10 ms
                          renderedOrRendering (n - 1)
                  else return imgExists

      -- Ensure that the output directory exists.
      createDirectoryIfMissing True (takeDirectory dotPath)

      imgGenerated <- firstSuccess
          [ -- There might be some other thread that rendered or is rendering
            -- this dot file. We wait at most 50 iterations (0.5 sec timout)
            -- for this other thread to render the image. Afterwards, we give
            -- it a try by ourselves.
            renderedOrRendering 50
            -- create dot-file and render to image
          , do writeFile dotPath code
               dotToImg "dot" dotPath imgPath
            -- sometimes 'dot' fails => use 'fdp' as a backup tool
          , dotToImg "fdp" dotPath imgPath
          ]
      if imgGenerated
        then return $ Just imgPath
        else trace ("WARNING: failed to convert:\n  '" ++ dotPath ++ "'")
                   (return Nothing)

    dotToImg dotMode dotFile imgFile = do
      (ecode,_out,err) <- readProcessWithExitCode dotCommand
                              [ "-T"++show imgFormat, "-K"++dotMode, "-o",imgFile, dotFile]
                              ""
      case ecode of
        ExitSuccess   -> return True
        ExitFailure i -> do
          putStrLn $ "dotToImg: "++dotCommand++" failed with code "
                      ++show i++" for file "++dotFile++":\n"++err
          return False

    firstSuccess []     = return False
    firstSuccess (m:ms) = do
      s <- m
      if s then return True else firstSuccess ms


-- | Get title to display for a given proof path.
titleThyPath :: ClosedTheory -> TheoryPath -> String
titleThyPath thy path = go path
  where
    go TheoryHelp                       = "Theory: " ++ get thyName thy
    go TheoryRules                      = "Multiset rewriting rules and restrictions"
    go TheoryMessage                    = "Message theory"
    go TheoryTactic                     = "Tactics"
    go (TheorySource RawSource _ _)     = "Raw sources"
    go (TheorySource RefinedSource _ _) = "Refined sources"
    go (TheoryEdit l)                   = "Edit Lemma: " ++ l
    go (TheoryAdd _)                    = "Add new Lemma"
    go (TheoryDelete l)                 = "Delete " ++ l
    go (TheoryLemma l)                  = "Lemma: " ++ l
    go (TheoryProof l [])               = "Lemma: " ++ l
    go (TheoryProof l p)
      | null (last p)       = "Method: " ++ methodName l p
      | otherwise           = "Case: " ++ last p
    go (TheoryMethod _ _ _) = "Method Path: This title should not be shown. Please file a bug"

    methodName l p =
      case resolveProofPath thy l p of
        Nothing -> "None"
        Just proof -> renderHtmlDoc $ prettyProofMethod $ psMethod $ root proof

-- | Get title to display for a given proof path.
titleDiffThyPath :: ClosedDiffTheory -> DiffTheoryPath -> String
titleDiffThyPath thy path = go path
  where
    go DiffTheoryHelp                           = "Theory: " ++ get diffThyName thy
    go (DiffTheoryRules s d)                    = "Multiset rewriting rules and restrictions [" ++ show s ++ "]" ++ if d then " [Diff]" else ""
    go DiffTheoryDiffRules                      = "Multiset rewriting rules and restrictions - unprocessed"
    go (DiffTheoryMessage s d)                  = "Message theory [" ++ show s ++ "]" ++ if d then " [Diff]" else ""
    go (DiffTheorySource s RawSource d _ _)     = "Raw sources [" ++ show s ++ "]" ++ if d then " [Diff]" else ""
    go (DiffTheorySource s RefinedSource d _ _) = "Refined sources [" ++ show s ++ "]" ++ if d then " [Diff]" else ""
    go (DiffTheoryLemma s l)                    = "Lemma: " ++ l ++ "[" ++ show s ++ "]"
    go (DiffTheoryDiffLemma l)                  = "DiffLemma: " ++ l
    go (DiffTheoryProof s l [])                 = "Lemma: " ++ l ++ "[" ++ show s ++ "]"
    go (DiffTheoryProof s l p)
      | null (last p)       = "Method: " ++ methodName s l p
      | otherwise           = "Case: " ++ last p
    go (DiffTheoryDiffProof l [])               = "Diff-Lemma: " ++ l
    go (DiffTheoryDiffProof l p)
      | null (last p)       = "Method: " ++ diffMethodName l p
      | otherwise           = "Case: " ++ last p
    go (DiffTheoryMethod _ _ _ _)     = "Method Path: This title should not be shown. Please file a bug"
    go (DiffTheoryDiffMethod _ _ _) = "DiffMethod Path: This title should not be shown. Please file a bug"

    methodName s l p =
      case resolveProofPathDiff thy s l p of
        Nothing -> "None"
        Just proof -> renderHtmlDoc $ prettyProofMethod $ psMethod $ root proof

    diffMethodName l p =
      case resolveProofPathDiffLemma thy l p of
        Nothing -> "None"
        Just proof -> renderHtmlDoc $ prettyDiffProofMethod $ dpsMethod $ root proof


-- | Resolve a proof path.
resolveProofPath :: ClosedTheory            -- ^ Theory to resolve in
                 -> String                  -- ^ Name of lemma
                 -> ProofPath               -- ^ Path to resolve
                 -> Maybe IncrementalProof
resolveProofPath thy lemmaName path = do
  lemma <- lookupLemma lemmaName thy
  get lProof lemma `atPath` path

-- | Resolve a diff proof path.
resolveProofPathDiff :: ClosedDiffTheory       -- ^ Theory to resolve in
                    -> Side                    -- ^ Side of lemma
                    -> String                  -- ^ Name of lemma
                    -> ProofPath               -- ^ Path to resolve
                    -> Maybe IncrementalProof
resolveProofPathDiff thy s lemmaName path = do
  lemma <- lookupLemmaDiff s lemmaName thy
  get lProof lemma `atPath` path

-- | Resolve a proof path for a diff lemma.
resolveProofPathDiffLemma :: ClosedDiffTheory       -- ^ Theory to resolve in
                    -> String                  -- ^ Name of lemma
                    -> ProofPath               -- ^ Path to resolve
                    -> Maybe IncrementalDiffProof
resolveProofPathDiffLemma thy lemmaName path = do
  lemma <- lookupDiffLemma lemmaName thy
  get lDiffProof lemma `atPathDiff` path


------------------------------------------------------------------------------
-- Moving to next/prev proof path
------------------------------------------------------------------------------

-- | Get 'next' theory path.
nextThyPath :: ClosedTheory -> TheoryPath -> TheoryPath
nextThyPath thy = go
  where
    go TheoryHelp                       = TheoryMessage
    go TheoryMessage                    = TheoryRules
    go TheoryRules                      = TheoryTactic
    go TheoryTactic                     = TheorySource RawSource 0 0
    go (TheorySource RawSource _ _)     = TheorySource RefinedSource 0 0
    go (TheorySource RefinedSource _ _) = fromMaybe TheoryHelp firstLemma
    go (TheoryLemma lemma)              = TheoryProof lemma []
    go (TheoryEdit _)                   = TheoryHelp 
    go (TheoryAdd _)                    = TheoryHelp
    go (TheoryDelete _)                 = TheoryHelp
    go (TheoryProof l p)
      | Just nextPath <- getNextPath l p = TheoryProof l nextPath
      | Just nextLemma <- getNextLemma l = TheoryProof nextLemma []
      | otherwise                        = TheoryProof l p
    go path@(TheoryMethod _ _ _)         = path

    lemmas = map (\l -> (get lName l, l)) $ getLemmas thy
    firstLemma = flip TheoryProof [] . fst <$> listToMaybe lemmas

    getNextPath lemmaName path = do
      lemma <- lookupLemma lemmaName thy
      let paths = map fst $ getProofPaths $ get lProof lemma
      getNextElement (== path) paths

    getNextLemma lemmaName = getNextElement (== lemmaName) (map fst lemmas)

-- | Get 'next' diff theory path.
nextDiffThyPath :: ClosedDiffTheory -> DiffTheoryPath -> DiffTheoryPath
nextDiffThyPath thy = go
  where
    go DiffTheoryHelp                                 = DiffTheoryDiffRules
    go DiffTheoryDiffRules                            = DiffTheoryMessage LHS False
    go (DiffTheoryMessage LHS False)                  = DiffTheoryMessage RHS False
    go (DiffTheoryMessage RHS False)                  = DiffTheoryMessage LHS True
    go (DiffTheoryMessage LHS True)                   = DiffTheoryMessage RHS True
    go (DiffTheoryMessage RHS True)                   = (DiffTheoryRules LHS False)
    go (DiffTheoryRules LHS False)                    = DiffTheoryRules RHS False
    go (DiffTheoryRules RHS False)                    = DiffTheoryRules LHS True
    go (DiffTheoryRules LHS True)                     = DiffTheoryRules RHS True
    go (DiffTheoryRules RHS True)                     = DiffTheorySource LHS RawSource False 0 0
    go (DiffTheorySource LHS RawSource False _ _)     = DiffTheorySource RHS RawSource False 0 0
    go (DiffTheorySource RHS RawSource False _ _)     = DiffTheorySource LHS RawSource True  0 0
    go (DiffTheorySource LHS RawSource True  _ _)     = DiffTheorySource RHS RawSource True  0 0
    go (DiffTheorySource RHS RawSource True  _ _)     = DiffTheorySource LHS RefinedSource False 0 0
    go (DiffTheorySource LHS RefinedSource False _ _) = DiffTheorySource RHS RefinedSource False 0 0
    go (DiffTheorySource RHS RefinedSource False _ _) = DiffTheorySource LHS RefinedSource True  0 0
    go (DiffTheorySource LHS RefinedSource True  _ _) = DiffTheorySource RHS RefinedSource True 0 0
    go (DiffTheorySource RHS RefinedSource True  _ _) = fromMaybe DiffTheoryHelp firstLemma
    go (DiffTheoryLemma s lemma)                      = DiffTheoryProof s lemma []
    go (DiffTheoryDiffLemma lemma)                    = DiffTheoryDiffProof lemma []
    go (DiffTheoryProof s l p)
      | Just nextPath <- getNextPath s l p = DiffTheoryProof s l nextPath
      | Just nextLemma <- getNextLemma s l = DiffTheoryProof s nextLemma []
      | s == LHS = case lemmas RHS of
                     []  -> firstDiffLemma
                     l':_ -> (DiffTheoryProof RHS (fst l') [])
      | s == RHS = firstDiffLemma
      | otherwise  = DiffTheoryProof s l p
    go (DiffTheoryDiffProof l p)
      | Just nextPath <- getNextDiffPath l p = DiffTheoryDiffProof l nextPath
      | Just nextDiffLemma <- getNextDiffLemma l = DiffTheoryDiffProof nextDiffLemma []
      | otherwise  = DiffTheoryDiffProof l p
    go path@(DiffTheoryMethod _ _ _ _)                = path
    go path@(DiffTheoryDiffMethod _ _ _)              = path

    firstDiffLemma = case getDiffLemmas thy of
                      []  -> DiffTheoryHelp
                      l:_ -> DiffTheoryDiffProof (get lDiffName l) []

    lemmas s = map (\l -> (get lName l, l)) $ diffTheorySideLemmas s thy
    diffLemmas = map (\l -> (get lDiffName l, l)) $ diffTheoryDiffLemmas thy
    firstLemma = case lemmas LHS of
                  []  -> case lemmas RHS of
                             []   -> Nothing
                             l:_ -> Just (DiffTheoryProof RHS (fst l) [])
                  l:_ -> Just (DiffTheoryProof LHS (fst l) [])

    getNextPath s lemmaName path = do
      lemma <- lookupLemmaDiff s lemmaName thy
      let paths = map fst $ getProofPaths $ get lProof lemma
      getNextElement (== path) paths

    getNextDiffPath lemmaName path = do
      lemma <- lookupDiffLemma lemmaName thy
      let paths = map fst $ getDiffProofPaths $ get lDiffProof lemma
      getNextElement (== path) paths

    getNextLemma s lemmaName = getNextElement (== lemmaName) (map fst (lemmas s))

    getNextDiffLemma lemmaName = getNextElement (== lemmaName) (map fst (diffLemmas))

-- | Get 'prev' theory path.
prevThyPath :: ClosedTheory -> TheoryPath -> TheoryPath
prevThyPath thy = go
  where
    go TheoryHelp                        = TheoryHelp
    go TheoryMessage                     = TheoryHelp
    go TheoryRules                       = TheoryMessage
    go TheoryTactic                      = TheoryRules
    go (TheorySource RawSource _ _)      = TheoryTactic
    go (TheorySource RefinedSource _ _)  = TheorySource RawSource 0 0
    go (TheoryEdit  _ )                  = TheoryHelp 
    go (TheoryAdd _)                     = TheoryHelp
    go (TheoryDelete _)                  = TheoryHelp
    go (TheoryLemma l)
      | Just prevLemma <- getPrevLemma l = TheoryProof prevLemma (lastPath prevLemma)
      | otherwise                        = TheorySource RefinedSource 0 0
    go (TheoryProof l p)
      | Just prevPath <- getPrevPath l p = TheoryProof l prevPath
      | Just prevLemma <- getPrevLemma l = TheoryProof prevLemma (lastPath prevLemma)
      | otherwise                        = TheorySource RefinedSource 0 0
    go path@(TheoryMethod _ _ _)         = path

    lemmas = map (\l -> (get lName l, l)) $ getLemmas thy

    getPrevPath lemmaName path = do
      lemma <- lookupLemma lemmaName thy
      let paths = map fst $ getProofPaths $ get lProof lemma
      getPrevElement (== path) paths

    lastPath lemmaName = last $ map fst $ getProofPaths $
      get lProof $ fromJust $ lookupLemma lemmaName thy

    getPrevLemma lemmaName = getPrevElement (== lemmaName) (map fst lemmas)

-- | Get 'prev' diff theory path.
prevDiffThyPath :: ClosedDiffTheory -> DiffTheoryPath -> DiffTheoryPath
prevDiffThyPath thy = go
  where
    go DiffTheoryHelp                                 = DiffTheoryHelp
    go DiffTheoryDiffRules                            = DiffTheoryHelp
    go (DiffTheoryMessage LHS False)                  = DiffTheoryDiffRules
    go (DiffTheoryMessage RHS False)                  = DiffTheoryMessage LHS False
    go (DiffTheoryMessage LHS True)                   = DiffTheoryMessage RHS False
    go (DiffTheoryMessage RHS True)                   = DiffTheoryMessage LHS True
    go (DiffTheoryRules LHS False)                    = DiffTheoryMessage RHS True
    go (DiffTheoryRules RHS False)                    = DiffTheoryRules LHS False
    go (DiffTheoryRules LHS True)                     = DiffTheoryRules RHS False
    go (DiffTheoryRules RHS True)                     = DiffTheoryRules LHS True
    go (DiffTheorySource LHS RawSource False _ _)     = DiffTheoryRules RHS True
    go (DiffTheorySource RHS RawSource False _ _)     = DiffTheorySource LHS RawSource False 0 0
    go (DiffTheorySource LHS RawSource True  _ _)     = DiffTheorySource RHS RawSource False 0 0
    go (DiffTheorySource RHS RawSource True  _ _)     = DiffTheorySource LHS RawSource True  0 0
    go (DiffTheorySource LHS RefinedSource False _ _) = DiffTheorySource RHS RawSource True  0 0
    go (DiffTheorySource RHS RefinedSource False _ _) = DiffTheorySource LHS RefinedSource   False 0 0
    go (DiffTheorySource LHS RefinedSource True  _ _) = DiffTheorySource RHS RefinedSource   False 0 0
    go (DiffTheorySource RHS RefinedSource True  _ _) = DiffTheorySource LHS RefinedSource   True 0 0
    go (DiffTheoryLemma s l)
      | Just prevLemma <- getPrevLemma s l = DiffTheoryProof s prevLemma (lastPath s prevLemma)
      | otherwise                          = DiffTheorySource RHS RefinedSource True 0 0
    go (DiffTheoryDiffLemma l)
      | Just prevLemma <- getPrevDiffLemma l      = DiffTheoryDiffProof prevLemma (lastPathDiff prevLemma)
      | otherwise                                 = lastLemmaRHS
    go (DiffTheoryProof s l p)
      | Just prevPath <- getPrevPath s l p = DiffTheoryProof s l prevPath
      | Just prevLemma <- getPrevLemma s l = DiffTheoryProof s prevLemma (lastPath s prevLemma)
      | s == RHS                           = lastLemmaLHS
      | otherwise                          = DiffTheorySource RHS RefinedSource True 0 0
    go (DiffTheoryDiffProof l p)
      | Just prevPath <- getPrevDiffPath l p     = DiffTheoryDiffProof l prevPath
      | Just prevDiffLemma <- getPrevDiffLemma l = DiffTheoryDiffProof prevDiffLemma (lastPathDiff prevDiffLemma)
      | otherwise                                = lastLemmaRHS
    go path@(DiffTheoryMethod _ _ _ _)         = path
    go path@(DiffTheoryDiffMethod _ _ _)       = path

    lemmas s = map (\l -> (get lName l, l)) $ diffTheorySideLemmas s thy

    diffLemmas = map (\l -> (get lDiffName l, l)) $ diffTheoryDiffLemmas thy

    getPrevPath s lemmaName path = do
      lemma <- lookupLemmaDiff s lemmaName thy
      let paths = map fst $ getProofPaths $ get lProof lemma
      getPrevElement (== path) paths

    getPrevDiffPath lemmaName path = do
      lemma <- lookupDiffLemma lemmaName thy
      let paths = map fst $ getDiffProofPaths $ get lDiffProof lemma
      getPrevElement (== path) paths

    lastPath s lemmaName = last $ map fst $ getProofPaths $
      get lProof $ fromJust $ lookupLemmaDiff s lemmaName thy

    lastPathDiff lemmaName = last $ map fst $ getDiffProofPaths $
      get lDiffProof $ fromJust $ lookupDiffLemma lemmaName thy

    getPrevLemma s lemmaName = getPrevElement (== lemmaName) (map fst (lemmas s))

    getPrevDiffLemma lemmaName = getPrevElement (== lemmaName) (map fst (diffLemmas))

    lastLemmaLHS = case lemmas LHS of
                  [] -> DiffTheorySource RHS RefinedSource True 0 0
                  l  -> DiffTheoryProof LHS (fst (last l)) (lastPath LHS (fst (last l)))

    lastLemmaRHS = case lemmas RHS of
                  [] -> lastLemmaLHS
                  l  -> DiffTheoryProof RHS (fst (last l)) (lastPath RHS (fst (last l)))

-- | Interesting proof methods that are not skipped by next/prev-smart.
isInterestingMethod :: ProofMethod -> Bool
isInterestingMethod (Sorry _) = True
isInterestingMethod (Finished Solved) = True
isInterestingMethod (Finished Unfinishable) = True
isInterestingMethod _ = False

-- | Interesting diff proof methods that are not skipped by next/prev-smart.
isInterestingDiffMethod :: DiffProofMethod -> Bool
isInterestingDiffMethod (DiffSorry _) = True
isInterestingDiffMethod DiffAttack    = True
isInterestingDiffMethod _             = False

-- Get 'next' smart theory path.
nextSmartThyPath :: ClosedTheory -> TheoryPath -> TheoryPath
nextSmartThyPath thy = go
  where
    go TheoryHelp                         = TheoryMessage
    go TheoryMessage                      = TheoryRules
    go TheoryRules                        = TheoryTactic
    go TheoryTactic                       = TheorySource RawSource 0 0
    go (TheorySource RawSource _ _)       = TheorySource RefinedSource 0 0
    go (TheorySource RefinedSource   _ _) = fromMaybe TheoryHelp firstLemma
    go (TheoryEdit  _ )                   = TheoryHelp 
    go (TheoryAdd _ )                     = TheoryHelp
    go (TheoryDelete _)                   = TheoryHelp
    go (TheoryLemma lemma)                = TheoryProof lemma []
    go (TheoryProof l p)
      | Just nextPath <- getNextPath l p = TheoryProof l nextPath
      | Just nextLemma <- getNextLemma l = TheoryProof nextLemma []
      | otherwise                        = TheoryProof l p
    go path@(TheoryMethod _ _ _)         = path

    lemmas = map (\l -> (get lName l, l)) $ getLemmas thy
    firstLemma = flip TheoryProof [] . fst <$> listToMaybe lemmas

    getNextPath lemmaName path = do
      lemma <- lookupLemma lemmaName thy
      let paths = getProofPaths $ get lProof lemma
      case dropWhile ((/= path) . fst) paths of
        []        -> Nothing
        nextSteps -> listToMaybe . map fst . filter (isInterestingMethod . snd) $ tail nextSteps

    getNextLemma lemmaName = getNextElement (== lemmaName) (map fst lemmas)

-- Get 'next' smart theory path.
nextSmartDiffThyPath :: ClosedDiffTheory -> DiffTheoryPath -> DiffTheoryPath
nextSmartDiffThyPath thy = go
  where
    go DiffTheoryHelp                                 = DiffTheoryDiffRules
    go DiffTheoryDiffRules                            = DiffTheoryMessage LHS False
    go (DiffTheoryMessage LHS False)                  = DiffTheoryMessage RHS False
    go (DiffTheoryMessage RHS False)                  = DiffTheoryMessage LHS True
    go (DiffTheoryMessage LHS True)                   = DiffTheoryMessage RHS True
    go (DiffTheoryMessage RHS True)                   = (DiffTheoryRules LHS False)
    go (DiffTheoryRules LHS False)                    = DiffTheoryRules RHS False
    go (DiffTheoryRules RHS False)                    = DiffTheoryRules LHS True
    go (DiffTheoryRules LHS True)                     = DiffTheoryRules RHS True
    go (DiffTheoryRules RHS True)                     = DiffTheorySource LHS RawSource False 0 0
    go (DiffTheorySource LHS RawSource False _ _)     = DiffTheorySource RHS RawSource False 0 0
    go (DiffTheorySource RHS RawSource False _ _)     = DiffTheorySource LHS RawSource True  0 0
    go (DiffTheorySource LHS RawSource True  _ _)     = DiffTheorySource RHS RawSource True  0 0
    go (DiffTheorySource RHS RawSource True  _ _)     = DiffTheorySource LHS RefinedSource False 0 0
    go (DiffTheorySource LHS RefinedSource False _ _) = DiffTheorySource RHS RefinedSource False 0 0
    go (DiffTheorySource RHS RefinedSource False _ _) = DiffTheorySource LHS RefinedSource True  0 0
    go (DiffTheorySource LHS RefinedSource True  _ _) = DiffTheorySource RHS RefinedSource True 0 0
    go (DiffTheorySource RHS RefinedSource True  _ _) = fromMaybe DiffTheoryHelp firstLemma
    go (DiffTheoryLemma s lemma)                      = DiffTheoryProof s lemma []
    go (DiffTheoryDiffLemma lemma)                    = DiffTheoryDiffProof lemma []
    go (DiffTheoryProof s l p)
      | Just nextPath <- getNextPath s l p = DiffTheoryProof s l nextPath
      | Just nextLemma <- getNextLemma s l = DiffTheoryProof s nextLemma []
      | s == LHS = case lemmas RHS of
                     []   -> firstDiffLemma
                     l':_ -> (DiffTheoryProof RHS (fst l') [])
      | s == RHS = firstDiffLemma
      | otherwise                            = DiffTheoryProof s l p
    go (DiffTheoryDiffProof l p)
      | Just nextPath <- getNextDiffPath l p = DiffTheoryDiffProof l nextPath
      | Just nextLemma <- getNextDiffLemma l = DiffTheoryDiffProof nextLemma []
      | otherwise                            = DiffTheoryDiffProof l p
    go path@(DiffTheoryMethod _ _ _ _)       = path
    go path@(DiffTheoryDiffMethod _ _ _)     = path

    firstDiffLemma = case getDiffLemmas thy of
                      []  -> DiffTheoryHelp
                      l:_ -> DiffTheoryDiffProof (get lDiffName l) []

    lemmas s = map (\l -> (get lName l, l)) $ diffTheorySideLemmas s thy
    diffLemmas = map (\l -> (get lDiffName l, l)) $ diffTheoryDiffLemmas thy
    firstLemma = case lemmas LHS of
                  []  -> case lemmas RHS of
                            []  -> Nothing
                            l:_ -> Just (DiffTheoryProof RHS (fst l) [])
                  l:_ -> Just (DiffTheoryProof LHS (fst l) [])

    getNextPath s lemmaName path = do
      lemma <- lookupLemmaDiff s lemmaName thy
      let paths = getProofPaths $ get lProof lemma
      case dropWhile ((/= path) . fst) paths of
        []        -> Nothing
        nextSteps -> listToMaybe . map fst . filter (isInterestingMethod . snd) $ tail nextSteps

    getNextDiffPath lemmaName path = do
      lemma <- lookupDiffLemma lemmaName thy
      let paths = getDiffProofPaths $ get lDiffProof lemma
      case dropWhile ((/= path) . fst) paths of
        []        -> Nothing
        nextSteps -> listToMaybe . map fst . filter (isInterestingDiffMethod . snd) $ tail nextSteps

    getNextLemma s lemmaName = getNextElement (== lemmaName) (map fst (lemmas s))

    getNextDiffLemma lemmaName = getNextElement (== lemmaName) (map fst (diffLemmas))

-- Get 'prev' smart theory path.
prevSmartThyPath :: ClosedTheory -> TheoryPath -> TheoryPath
prevSmartThyPath thy = go
  where
    go TheoryHelp                          = TheoryHelp
    go TheoryMessage                       = TheoryHelp
    go TheoryRules                         = TheoryMessage
    go TheoryTactic                        = TheoryRules
    go (TheorySource RawSource _ _)        = TheoryTactic
    go (TheorySource RefinedSource   _ _)  = TheorySource RawSource 0 0
    go (TheoryEdit  _)                     = TheoryHelp 
    go (TheoryAdd _ )                      = TheoryHelp
    go (TheoryDelete _ )                   = TheoryHelp
    go (TheoryLemma l)
      | Just prevLemma <- getPrevLemma l   = TheoryProof prevLemma (lastPath prevLemma)
      | otherwise                          = TheorySource RefinedSource 0 0
    go (TheoryProof l p)
      | Just prevPath <- getPrevPath l p   = TheoryProof l prevPath
--      | Just firstPath <- getFirstPath l p = TheoryProof l firstPath
      | Just prevLemma <- getPrevLemma l   = TheoryProof prevLemma (lastPath prevLemma)
      | otherwise                          = TheorySource RefinedSource 0 0
    go path@(TheoryMethod _ _ _)           = path

    lemmas = map (\l -> (get lName l, l)) $ getLemmas thy

    {-
    getFirstPath lemmaName current = do
      lemma <- lookupLemma lemmaName thy
      let paths = map fst $ getProofPaths $ get lProof lemma
      if null paths || (head paths == current)
        then Nothing
        else Just $ head paths
    -}

    getPrevPath lemmaName path = do
      lemma <- lookupLemma lemmaName thy
      let paths = getProofPaths $ get lProof lemma
      case filter (isInterestingMethod . snd) . takeWhile ((/= path) . fst) $ paths of
        []        -> Nothing
        prevSteps -> Just . fst . last $ prevSteps

    lastPath lemmaName = last $ map fst $ getProofPaths $
      get lProof $ fromJust $ lookupLemma lemmaName thy

    getPrevLemma lemmaName = getPrevElement (== lemmaName) (map fst lemmas)

-- Get 'prev' smart diff theory path.
prevSmartDiffThyPath :: ClosedDiffTheory -> DiffTheoryPath -> DiffTheoryPath
prevSmartDiffThyPath thy = go
  where
    go DiffTheoryHelp                                 = DiffTheoryHelp
    go DiffTheoryDiffRules                            = DiffTheoryHelp
    go (DiffTheoryMessage LHS False)                  = DiffTheoryDiffRules
    go (DiffTheoryMessage RHS False)                  = DiffTheoryMessage LHS False
    go (DiffTheoryMessage LHS True)                   = DiffTheoryMessage RHS False
    go (DiffTheoryMessage RHS True)                   = DiffTheoryMessage LHS True
    go (DiffTheoryRules LHS False)                    = DiffTheoryMessage RHS True
    go (DiffTheoryRules RHS False)                    = DiffTheoryRules LHS False
    go (DiffTheoryRules LHS True)                     = DiffTheoryRules RHS False
    go (DiffTheoryRules RHS True)                     = DiffTheoryRules LHS True
    go (DiffTheorySource LHS RawSource False _ _)     = DiffTheoryRules RHS True
    go (DiffTheorySource RHS RawSource False _ _)     = DiffTheorySource LHS RawSource False 0 0
    go (DiffTheorySource LHS RawSource True  _ _)     = DiffTheorySource RHS RawSource False 0 0
    go (DiffTheorySource RHS RawSource True  _ _)     = DiffTheorySource LHS RawSource True  0 0
    go (DiffTheorySource LHS RefinedSource False _ _) = DiffTheorySource RHS RawSource True  0 0
    go (DiffTheorySource RHS RefinedSource False _ _) = DiffTheorySource LHS RefinedSource   False 0 0
    go (DiffTheorySource LHS RefinedSource True  _ _) = DiffTheorySource RHS RefinedSource   False 0 0
    go (DiffTheorySource RHS RefinedSource True  _ _) = DiffTheorySource LHS RefinedSource   True 0 0
    go (DiffTheoryLemma s l)
      | Just prevLemma <- getPrevLemma s l            = DiffTheoryProof s prevLemma (lastPath s prevLemma)
      | otherwise                                     = DiffTheorySource RHS RefinedSource True 0 0
    go (DiffTheoryDiffLemma l)
      | Just prevLemma <- getPrevDiffLemma l          = DiffTheoryDiffProof prevLemma (lastPathDiff prevLemma)
      | otherwise                                     = lastLemmaRHS
    go (DiffTheoryProof s l p)
      | Just prevPath <- getPrevPath s l p            = DiffTheoryProof s l prevPath
      | Just prevLemma <- getPrevLemma s l            = DiffTheoryProof s prevLemma (lastPath s prevLemma)
      | s == RHS                                      = lastLemmaLHS
      | otherwise                                     = DiffTheorySource RHS RefinedSource True 0 0
    go (DiffTheoryDiffProof l p)
      | Just prevPath <- getPrevPathDiff l p          = DiffTheoryDiffProof l prevPath
      | Just prevDiffLemma <- getPrevDiffLemma l      = DiffTheoryDiffProof prevDiffLemma (lastPathDiff prevDiffLemma)
      | otherwise                                     = lastLemmaRHS
    go path@(DiffTheoryMethod _ _ _ _)                = path
    go path@(DiffTheoryDiffMethod _ _ _)              = path

    lemmas s = map (\l -> (get lName l, l)) $ diffTheorySideLemmas s thy

    diffLemmas = map (\l -> (get lDiffName l, l)) $ diffTheoryDiffLemmas thy

    {-
    getFirstPath lemmaName current = do
      lemma <- lookupLemma lemmaName thy
      let paths = map fst $ getProofPaths $ get lProof lemma
      if null paths || (head paths == current)
        then Nothing
        else Just $ head paths
    -}

    getPrevPath s lemmaName path = do
      lemma <- lookupLemmaDiff s lemmaName thy
      let paths = getProofPaths $ get lProof lemma
      case filter (isInterestingMethod . snd) . takeWhile ((/= path) . fst) $ paths of
        []        -> Nothing
        prevSteps -> Just . fst . last $ prevSteps

    getPrevPathDiff lemmaName path = do
      lemma <- lookupDiffLemma lemmaName thy
      let paths = getDiffProofPaths $ get lDiffProof lemma
      case filter (isInterestingDiffMethod . snd) . takeWhile ((/= path) . fst) $ paths of
        []        -> Nothing
        prevSteps -> Just . fst . last $ prevSteps

    lastPath s lemmaName = last $ map fst $ getProofPaths $
      get lProof $ fromJust $ lookupLemmaDiff s lemmaName thy

    lastPathDiff lemmaName = last $ map fst $ getDiffProofPaths $
      get lDiffProof $ fromJust $ lookupDiffLemma lemmaName thy

    getPrevLemma s lemmaName = getPrevElement (== lemmaName) (map fst (lemmas s))

    getPrevDiffLemma lemmaName = getPrevElement (== lemmaName) (map fst (diffLemmas))

    lastLemmaLHS = case lemmas LHS of
      [] -> DiffTheorySource RHS RefinedSource True 0 0
      l  -> DiffTheoryProof LHS (fst (last l)) (lastPath LHS (fst (last l)))

    lastLemmaRHS = case lemmas RHS of
      [] -> lastLemmaLHS
      l  -> DiffTheoryProof RHS (fst (last l)) (lastPath RHS (fst (last l)))

-- | Extract proof paths out of a proof.
getProofPaths :: LTree CaseName (ProofStep a) -> [([String], ProofMethod)]
getProofPaths proof = ([], psMethod . root $ proof) : go proof
  where
    go = concatMap paths . M.toList . children
    paths (lbl, prf) = ([lbl], psMethod . root $ prf) : map (first (lbl:)) (go prf)

-- | Extract proof paths out of a proof.
getDiffProofPaths :: LTree CaseName (DiffProofStep a) -> [([String], DiffProofMethod)]
getDiffProofPaths proof = ([], dpsMethod . root $ proof) : go proof
  where
    go = concatMap paths . M.toList . children
    paths (lbl, prf) = ([lbl], dpsMethod . root $ prf) : map (first (lbl:)) (go prf)

-- | Get element _after_ the matching element in the list.
getNextElement :: (a -> Bool) -> [a] -> Maybe a
getNextElement _ [] = Nothing
getNextElement f (x:xs)
  | f x = listToMaybe xs
  | otherwise = getNextElement f xs

-- | Get element _before_ the matching element in the list.
getPrevElement :: (a -> Bool) -> [a] -> Maybe a
getPrevElement _ [] = Nothing
getPrevElement f (x:xs) = go x xs
  where
    go _ [] = Nothing
    go old (z:zs)
      | f z = Just old
      | otherwise = go z zs

-- | Translate a proof status returned by 'annotateLemmaProof' to a
-- corresponding CSS class.
markStatus :: HtmlDocument d => (Maybe System, ProofStepColor) -> d -> d
markStatus (Nothing, _       ) = withTag "span" [("class","hl_superfluous")]
markStatus (Just _,  Green   ) = withTag "span" [("class","hl_good")]
markStatus (Just _,  Red     ) = withTag "span" [("class","hl_bad")]
markStatus (Just _,  Yellow  ) = withTag "span" [("class","hl_medium")]
markStatus (Just _,  Unmarked) = id

-- | Translate a diff proof status returned by 'annotateLemmaProof' to a
-- corresponding CSS class.
markStatusDiff :: HtmlDocument d => (Maybe DiffSystem, ProofStepColor) -> d -> d
markStatusDiff (Nothing, _       ) = withTag "span" [("class","hl_superfluous")]
markStatusDiff (Just _,  Green   ) = withTag "span" [("class","hl_good")]
markStatusDiff (Just _,  Red     ) = withTag "span" [("class","hl_bad")]
markStatusDiff (Just _,  Yellow  ) = withTag "span" [("class","hl_medium")]
markStatusDiff (Just _,  Unmarked) = id


data ProofStepColor = Unmarked | Green | Red | Yellow

-- | Annotate a proof for pretty printing.
-- The boolean flag indicates that the given proof step's children
-- are (a) all annotated and (b) contain no sorry steps.
annotateLemmaProof :: Lemma IncrementalProof
                   -> Proof (Maybe System, ProofStepColor)
annotateLemmaProof lem =
--     error (show (get lProof lem) ++ " - " ++ show prf)
    mapProofInfo (second interpret) prf
  where
    prf = annotateProof annotate $ get lProof lem
    annotate step cs  =
        case get lProof lem of
           LNode (ProofStep  Invalidated _) _ -> (psInfo step, InvalidatedProof)
           _                                  -> ( psInfo step, mconcat $ proofStepStatus step : incomplete ++ map snd cs)
      where
        incomplete = if isNothing (psInfo step) then [IncompleteProof] else []

    interpret status = case (get lTraceQuantifier lem, status) of
      (_,                IncompleteProof)   -> Unmarked
      (_,                UndeterminedProof) -> Unmarked
      (_,                UnfinishableProof) -> Yellow
      (_,                InvalidatedProof)  -> Yellow
      (AllTraces,        TraceFound)        -> Red
      (AllTraces,        CompleteProof)     -> Green
      (ExistsTrace,      TraceFound)        -> Green
      (ExistsTrace,      CompleteProof)     -> Red

-- | Annotate a proof for pretty printing.
-- The boolean flag indicates that the given proof step's children
-- are (a) all annotated and (b) contain no sorry steps.
annotateDiffLemmaProof :: DiffLemma IncrementalDiffProof
                   -> DiffProof (Maybe DiffSystem, ProofStepColor)
annotateDiffLemmaProof lem =
    mapDiffProofInfo (second interpret) prf
  where
    prf = annotateDiffProof annotate $ get lDiffProof lem
    annotate step cs =
        ( dpsInfo step
        , mconcat $ diffProofStepStatus step : incomplete ++ map snd cs
        )
      where
        incomplete = if isNothing (dpsInfo step) then [IncompleteProof] else []

    interpret status = case status of
      IncompleteProof   -> Unmarked
      UndeterminedProof -> Unmarked
      UnfinishableProof -> Yellow
      InvalidatedProof -> Yellow
      TraceFound        -> Red
      CompleteProof     -> Green
