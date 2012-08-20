{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE QuasiQuotes   #-}
{-# LANGUAGE TupleSections #-}
{- |
Module      :  Web.Theory
Description :  Pretty-printing security protocol theories into HTML code.
Copyright   :  (c) 2011, 2012 Simon Meier & Cedric Staub
License     :  GPL-3

Maintainer  :  Simon Meier <iridcode@gmail.com>
Stability   :  experimental
Portability :  non-portable
-}
module Web.Theory
  ( htmlThyPath
--  , htmlThyDbgPath
  , imgThyPath
  , titleThyPath
  , theoryIndex
  , nextThyPath
  , prevThyPath
  , nextSmartThyPath
  , prevSmartThyPath
  , applyMethodAtPath
  , applyProverAtPath
  )
where

import           Data.Char                    (toUpper)
import           Data.List
import qualified Data.Map                     as M
import           Data.Maybe
import           Data.Monoid
import qualified Data.Set                     as S
import qualified Data.Text                    as T
import           Data.Time.Format             (formatTime)

import           Control.Basics
import           Control.Concurrent           (threadDelay)

import           System.Directory
import           System.FilePath
import           System.Locale                (defaultTimeLocale)

import           Extension.Data.Label

import           Text.Blaze.Html5             (preEscapedString, toHtml)
import qualified Text.Dot                     as D
import           Text.Hamlet                  (Html, hamlet)
import           Text.PrettyPrint.Html
import           Utils.Misc                   (stringSHA256)

import           System.Exit
import           System.Process

import           Logic.Connectives
import           Theory
import           Theory.Constraint.System.Dot (nonEmptyGraph)
import           Theory.Text.Pretty

import           Web.Settings
import           Web.Types


------------------------------------------------------------------------------
-- Various other functions
------------------------------------------------------------------------------

applyMethodAtPath :: ClosedTheory -> String -> ProofPath
                  -> Heuristic             -- ^ How to extract/order the proof methods.
                  -> Int                   -- What proof method to use.
                  -> Maybe ClosedTheory
applyMethodAtPath thy lemmaName proofPath heuristic i = do
    lemma <- lookupLemma lemmaName thy
    subProof <- get lProof lemma `atPath` proofPath
    let ctxt  = getProofContext lemma thy
        sys   = psInfo (root subProof)
        ranking = useHeuristic heuristic (length proofPath)
    methods <- (map fst . rankProofMethods ranking ctxt) <$> sys
    method <- if length methods >= i then Just (methods !! (i-1)) else Nothing
    applyProverAtPath thy lemmaName proofPath
      (oneStepProver method                        `mappend`
       replaceSorryProver (oneStepProver Simplify) `mappend`
       replaceSorryProver (contradictionProver)    `mappend`
       replaceSorryProver (oneStepProver Solved)
      )

applyProverAtPath :: ClosedTheory -> String -> ProofPath
                  -> Prover -> Maybe ClosedTheory
applyProverAtPath thy lemmaName proofPath prover =
    modifyLemmaProof (focus proofPath prover) lemmaName thy


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Reference a dot graph for the given path.
refDotPath :: HtmlDocument d => RenderUrl -> TheoryIdx -> TheoryPath -> d
refDotPath renderUrl tidx path = closedTag "img" [("class", "graph"), ("src", imgPath)]
  where imgPath = T.unpack $ renderUrl (TheoryGraphR tidx path)

getDotPath :: String -> FilePath
getDotPath code = imageDir </> addExtension (stringSHA256 code) "dot"

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
           => RenderUrl
           -> (ProofPath -> Route WebUI)         -- ^ Relative addressing function
           -> Proof (Maybe System, Maybe Bool) -- ^ The annotated incremental proof
           -> d
proofIndex renderUrl mkRoute =
    prettyProofWith ppStep ppCase . insertPaths
  where
    ppCase step = markStatus (fst $ psInfo step)

    ppStep step =
           case fst $ psInfo step of
               (Nothing, _)    -> superfluousStep
               (_, Nothing)    -> stepLink ["sorry-step"]
               (_, Just True)  -> stepLink ["hl_good"]
               (_, Just False) -> stepLink ["hl_bad"]
        <> case psMethod step of
               Sorry _ -> emptyDoc
               _       -> removeStep
      where
        ppMethod = prettyProofMethod $ psMethod step
        stepLink cls = linkToPath renderUrl
            (mkRoute . snd . psInfo $ step)
            ("proof-step" : cls) ppMethod

        superfluousStep = withTag "span" [("class","hl_superfluous")] ppMethod

        removeStep = linkToPath renderUrl (mkRoute . snd . psInfo $ step)
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
        -- FIXME: Reactivate theory editing.
        -- <->
        -- (linkToPath renderUrl lemmaRoute  ["edit-link"] editPng <->
        -- linkToPath renderUrl lemmaRoute ["delete-link"] deletePng)
        $-$
        nest 2 ( sep [ prettyTraceQuantifier $ get lTraceQuantifier l
                     , doubleQuotes $ prettyLNFormula $ get lFormula l
                     ] )
    ) $-$
    proofIndex renderUrl mkRoute annPrf
  where
    -- editPng = png "/static/img/edit.png"
    -- deletePng = png "/static/img/delete.png"
    -- png path = closedTag "img" [("class","icon"),("src",path)]
    -- lemmaRoute = TheoryPathMR tidx (TheoryLemma $ get lName l)

    annPrf = annotateLemmaProof l
    mkRoute proofPath = TheoryPathMR tidx (TheoryProof (get lName l) proofPath)

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
    , reqCasesLink "Untyped case distinctions" UntypedCaseDist
    , text ""
    , reqCasesLink "Typed case distinctions "  TypedCaseDist
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
        cases   = getCaseDistinction kind thy
        nChains = sum $ map (sum . unsolvedChainConstraints) cases
        nCases  = int (length cases) <-> text "cases"
        chainInfo | nChains == 0 = "all chains solved"
                  | otherwise    = show nChains ++ " chains left"

    bold                = withTag "strong" [] . text
    overview n info p   = linkToPath renderUrl (TheoryPathMR tidx p) [] (bold n <-> info)
    messageLink         = overview "Message theory" (text "") TheoryMessage
    ruleLink            = overview ruleLinkMsg rulesInfo TheoryRules
    ruleLinkMsg         = "Multiset rewriting rules" ++
                          if null(theoryAxioms thy) then "" else " and axioms"

    reqCasesLink name k = overview name (casesInfo k) (TheoryCaseDist k 0 0)


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
                -> TheoryIdx                 -- ^ The theory index.
                -> TheoryInfo                -- ^ The theory info of this index.
                -> String                    -- ^ The lemma.
                -> ProofPath                 -- ^ The proof path.
                -> ProofContext              -- ^ The proof context.
                -> IncrementalProof          -- ^ The sub-proof.
                -> d
subProofSnippet renderUrl tidx ti lemma proofPath ctxt prf =
    case psInfo $ root prf of
      Nothing -> text $ "no annotated constraint system / " ++ nCases ++ " sub-case(s)"
      Just se -> vcat $
        prettyApplicableProofMethods se
        ++
        [ text ""
        , withTag "h3" [] (text "Constraint system")
        ] ++
        [ refDotPath renderUrl tidx (TheoryProof lemma proofPath)
        | nonEmptyGraph se ]
        ++
        [ preformatted (Just "sequent") (prettyNonGraphSystem se)
        , withTag "h3" [] (text $ nCases ++ " sub-case(s)")
        ] ++
        subCases
  where
    prettyApplicableProofMethods sys = case proofMethods sys of
        []  -> [ withTag "h3" [] (text "Constraint System is Solved") ]
        pms ->
          [ withTag "h3" [] (text "Applicable Proof Methods:" <->
                             comment_ (goalRankingName ranking))
          , preformatted (Just "methods") (numbered' $ map prettyPM $ zip [1..] pms)
          , autoProverLinks 'a' ""         emptyDoc      0
          , autoProverLinks 'b' "bounded-" boundDesc bound
          ]
        where
          boundDesc = text $ " with proof-depth bound " ++ show bound
          bound     = fromMaybe 5 $ apBound $ tiAutoProver ti

    autoProverLinks key classPrefix nameSuffix bound = hsep
      [ text (key : ".")
      , linkToPath renderUrl
            (AutoProverR tidx CutDFS bound (TheoryProof lemma proofPath))
            [classPrefix ++ "autoprove"]
            (keyword_ $ "autoprove")
      , parens $
          text (toUpper key : ".") <->
          linkToPath renderUrl
              (AutoProverR tidx CutNothing bound (TheoryProof lemma proofPath))
              [classPrefix ++ "characterization"]
              (keyword_ "for all solutions")
      , nameSuffix
      ]

    prettyPM (i, (m, (_cases, expl))) =
      linkToPath renderUrl
        (TheoryPathMR tidx (TheoryMethod lemma proofPath i))
        ["proof-method"] (prettyProofMethod m)
      <-> (if null expl then emptyDoc else lineComment_ expl)

    nCases                  = show $ M.size $ children prf
    depth                   = length proofPath
    ranking                 = useHeuristic (apHeuristic $ tiAutoProver ti) depth
    proofMethods            = rankProofMethods ranking ctxt
    subCases                = concatMap refSubCase $ M.toList $ children prf
    refSubCase (name, prf') =
        [ withTag "h4" [] (text "Case" <-> text name)
        , maybe (text "no proof state available")
                (const $ refDotPath renderUrl tidx $ TheoryProof lemma (proofPath ++ [name]))
                (psInfo $ root prf')
        ]


-- | A Html document representing the requires case splitting theorem.
htmlCaseDistinction :: HtmlDocument d
                    => RenderUrl -> TheoryIdx -> CaseDistKind -> (Int, CaseDistinction) -> d
htmlCaseDistinction renderUrl tidx kind (j, th) =
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
                               , text " / named ", doubleQuotes (text name) ]
      , refDotPath renderUrl tidx (TheoryCaseDist kind j i)
      , withTag "p" [] $ ppPrem
      , wrapP $ prettyNonGraphSystem se
      ]
      where
        name = intercalate "_" names

-- | Build the Html document showing the source cases distinctions.
reqCasesSnippet :: HtmlDocument d => RenderUrl -> TheoryIdx -> CaseDistKind -> ClosedTheory -> d
reqCasesSnippet renderUrl tidx kind thy = vcat $
    htmlCaseDistinction renderUrl tidx kind <$> zip [1..] (getCaseDistinction kind thy)

-- | Build the Html document showing the rules of the theory.
rulesSnippet :: HtmlDocument d => ClosedTheory -> d
rulesSnippet thy = vcat
    [ ppWithHeader "Fact Symbols with Injective Instances" $
        fsepList (text . showFactTagArity) injFacts
    , ppWithHeader "Multiset Rewriting Rules" $
        vsep $ map prettyRuleAC msrRules
    , ppWithHeader "Axioms Restricting the Set of Traces" $
        vsep $ map prettyAxiom $ theoryAxioms thy
    ]
  where
    msrRules   = get crProtocol $ getClassifiedRules thy
    injFacts   = S.toList $ getInjectiveFactInsts thy
    ppWithHeader header body =
        caseEmptyDoc
            emptyDoc
            ( withTag "h2" []                            (text header) $$
              withTag "p"  [("class","monospace rules")] body             )
            body

-- | Build the Html document showing the message theory.
messageSnippet :: HtmlDocument d => ClosedTheory -> d
messageSnippet thy = vcat
    [ ppSection "Signature"           [prettySignatureWithMaude (get thySignature thy)]
    , ppSection "Construction Rules"  (ppRules crConstruct)
    , ppSection "Destruction Rules"   (ppRules crDestruct)
    ]
  where
    ppRules l = map prettyRuleAC $ get l $ getClassifiedRules thy
    ppSection header s =
      withTag "h2" [] (text header) $$ withTag "p"
        [("class","monospace rules")]
        (vcat (intersperse (text "") $ s))

-- | Render the item in the given theory given by the supplied path.
htmlThyPath :: RenderUrl    -- ^ The function for rendering Urls.
            -> TheoryInfo   -- ^ The info of the theory to render
            -> TheoryPath   -- ^ Path to render
            -> Html
htmlThyPath renderUrl info path =
    go path
  where
    thy  = tiTheory info
    tidx = tiIndex  info

    -- Rendering a HtmlDoc to Html
    pp :: HtmlDoc Doc -> Html
    pp d = case renderHtmlDoc d of
      [] -> toHtml "Trying to render document yielded empty string. This is a bug."
      cs -> preEscapedString cs

    go (TheoryMethod _ _ _)      = pp $ text "Cannot display theory method."

    go TheoryRules               = pp $ rulesSnippet thy
    go TheoryMessage             = pp $ messageSnippet thy
    go (TheoryCaseDist kind _ _) = pp $ reqCasesSnippet renderUrl tidx kind thy

    go (TheoryProof l p)         = pp $
        fromMaybe (text "No such lemma or proof path.") $ do
           lemma <- lookupLemma l thy
           subProofSnippet renderUrl tidx info l p (getProofContext lemma thy)
             <$> resolveProofPath thy l p

    go (TheoryLemma _)      = pp $ text "Implement lemma pretty printing!"

    go TheoryHelp           = [hamlet|
        <p>
          Theory: #{get thyName $ tiTheory info}
          \ (Loaded at #{formatTime defaultTimeLocale "%T" $ tiTime info}
          \ from #{show $ tiOrigin info})
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
                Jump to the next/previous open goal within the currently
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
            <tr>
              <td>
                <span class="keys">?
              <td>
                Display this help message.
      |] renderUrl



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

-- | Render the image corresponding to the given theory path.
imgThyPath :: ImageFormat
           -> FilePath               -- ^ 'dot' command
           -> FilePath               -- ^ Tamarin's cache directory
           -> (System -> D.Dot ())
           -> ClosedTheory
           -> TheoryPath
           -> IO FilePath
imgThyPath imgFormat dotCommand cacheDir_ compact thy path = go path
  where
    go (TheoryCaseDist k i j) = renderDotCode (casesDotCode k i j)
    go (TheoryProof l p)      = renderDotCode (proofPathDotCode l p)
    go _                      = error "Unhandled theory path. This is a bug."

    -- Get dot code for required cases
    casesDotCode k i j = D.showDot $
        compact $ snd $ cases !! (i-1) !! (j-1)
      where
        cases = map (getDisj . get cdCases) (getCaseDistinction k thy)

    -- Get dot code for proof path in lemma
    proofPathDotCode lemma proofPath =
      D.showDot $ fromMaybe (return ()) $ do
        subProof <- resolveProofPath thy lemma proofPath
        sequent <- psInfo $ root subProof
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
              if (n <= 0 || (dotExists && not imgExists))
                  then do threadDelay 100             -- wait 10 ms
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
        then return imgPath
        else return $ imageDir ++ "/img/delete.png"

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
    go TheoryHelp                           = "Theory: " ++ get thyName thy
    go TheoryRules                          = "Multiset rewriting rules and axioms"
    go TheoryMessage                        = "Message theory"
    go (TheoryCaseDist UntypedCaseDist _ _) = "Untyped case distinctions"
    go (TheoryCaseDist TypedCaseDist _ _)   = "Typed case distinctions"
    go (TheoryLemma l)                      = "Lemma: " ++ l
    go (TheoryProof l [])                   = "Lemma: " ++ l
    go (TheoryProof l p)
      | null (last p)       = "Method: " ++ methodName l p
      | otherwise           = "Case: " ++ last p
    go (TheoryMethod _ _ _) = "Method Path: This title should not be shown. Please file a bug"

    methodName l p =
      case resolveProofPath thy l p of
        Nothing -> "None"
        Just proof -> renderHtmlDoc $ prettyProofMethod $ psMethod $ root proof

-- | Resolve a proof path.
resolveProofPath :: ClosedTheory            -- ^ Theory to resolve in
                 -> String                  -- ^ Name of lemma
                 -> ProofPath               -- ^ Path to resolve
                 -> Maybe IncrementalProof
resolveProofPath thy lemmaName path = do
  lemma <- lookupLemma lemmaName thy
  get lProof lemma `atPath` path


------------------------------------------------------------------------------
-- Moving to next/prev proof path
------------------------------------------------------------------------------

-- | Get 'next' theory path.
nextThyPath :: ClosedTheory -> TheoryPath -> TheoryPath
nextThyPath thy = go
  where
    go TheoryHelp                           = TheoryMessage
    go TheoryMessage                        = TheoryRules
    go TheoryRules                          = TheoryCaseDist UntypedCaseDist 0 0
    go (TheoryCaseDist UntypedCaseDist _ _) = TheoryCaseDist TypedCaseDist 0 0
    go (TheoryCaseDist TypedCaseDist _ _)   = fromMaybe TheoryHelp firstLemma
    go (TheoryLemma lemma)                  = TheoryProof lemma []
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

-- | Get 'prev' theory path.
prevThyPath :: ClosedTheory -> TheoryPath -> TheoryPath
prevThyPath thy = go
  where
    go TheoryHelp                           = TheoryHelp
    go TheoryMessage                        = TheoryHelp
    go TheoryRules                          = TheoryMessage
    go (TheoryCaseDist UntypedCaseDist _ _) = TheoryRules
    go (TheoryCaseDist TypedCaseDist _ _)   = TheoryCaseDist UntypedCaseDist 0 0
    go (TheoryLemma l)
      | Just prevLemma <- getPrevLemma l = TheoryProof prevLemma (lastPath prevLemma)
      | otherwise                        = TheoryCaseDist TypedCaseDist 0 0
    go (TheoryProof l p)
      | Just prevPath <- getPrevPath l p = TheoryProof l prevPath
      | Just prevLemma <- getPrevLemma l = TheoryProof prevLemma (lastPath prevLemma)
      | otherwise                        = TheoryCaseDist TypedCaseDist 0 0
    go path@(TheoryMethod _ _ _)         = path

    lemmas = map (\l -> (get lName l, l)) $ getLemmas thy

    getPrevPath lemmaName path = do
      lemma <- lookupLemma lemmaName thy
      let paths = map fst $ getProofPaths $ get lProof lemma
      getPrevElement (== path) paths

    lastPath lemmaName = last $ map fst $ getProofPaths $
      get lProof $ fromJust $ lookupLemma lemmaName thy

    getPrevLemma lemmaName = getPrevElement (== lemmaName) (map fst lemmas)

-- | Interesting proof methods that are not skipped by next/prev-smart.
isInterestingMethod :: ProofMethod -> Bool
isInterestingMethod (Sorry _) = True
isInterestingMethod Solved    = True
isInterestingMethod _         = False

-- Get 'next' smart theory path.
nextSmartThyPath :: ClosedTheory -> TheoryPath -> TheoryPath
nextSmartThyPath thy = go
  where
    go TheoryHelp                           = TheoryMessage
    go TheoryMessage                        = TheoryRules
    go TheoryRules                          = TheoryCaseDist UntypedCaseDist 0 0
    go (TheoryCaseDist UntypedCaseDist _ _) = TheoryCaseDist TypedCaseDist 0 0
    go (TheoryCaseDist TypedCaseDist   _ _) = fromMaybe TheoryHelp firstLemma
    go (TheoryLemma lemma)                  = TheoryProof lemma []
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

-- Get 'prev' smart theory path.
prevSmartThyPath :: ClosedTheory -> TheoryPath -> TheoryPath
prevSmartThyPath thy = go
  where
    go TheoryHelp                           = TheoryHelp
    go TheoryMessage                        = TheoryHelp
    go TheoryRules                          = TheoryMessage
    go (TheoryCaseDist UntypedCaseDist _ _) = TheoryRules
    go (TheoryCaseDist TypedCaseDist   _ _) = TheoryCaseDist UntypedCaseDist 0 0
    go (TheoryLemma l)
      | Just prevLemma <- getPrevLemma l   = TheoryProof prevLemma (lastPath prevLemma)
      | otherwise                          = TheoryCaseDist TypedCaseDist 0 0
    go (TheoryProof l p)
      | Just prevPath <- getPrevPath l p   = TheoryProof l prevPath
--      | Just firstPath <- getFirstPath l p = TheoryProof l firstPath
      | Just prevLemma <- getPrevLemma l   = TheoryProof prevLemma (lastPath prevLemma)
      | otherwise                          = TheoryCaseDist TypedCaseDist 0 0
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


-- | Extract proof paths out of a proof.
getProofPaths :: LTree CaseName (ProofStep a) -> [([String], ProofMethod)]
getProofPaths proof = ([], psMethod . root $ proof) : go proof
  where
    go = concatMap paths . M.toList . children
    paths (lbl, prf) = ([lbl], psMethod . root $ prf) : map (first (lbl:)) (go prf)


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
markStatus :: HtmlDocument d => (Maybe System, Maybe Bool) -> d -> d
markStatus (Nothing, _         ) = withTag "span" [("class","hl_superfluous")]
markStatus (Just _,  Just True ) = withTag "span" [("class","hl_good")]
markStatus (Just _,  Just False) = withTag "span" [("class","hl_bad")]
markStatus (Just _,  Nothing   ) = id

-- | Annotate a proof for pretty printing.
-- The boolean flag indicates that the given proof step's children
-- are (a) all annotated and (b) contain no sorry steps.
annotateLemmaProof :: Lemma IncrementalProof
                   -> Proof (Maybe System, Maybe Bool)
annotateLemmaProof lem =
    mapProofInfo (second interpret) prf
  where
    prf = annotateProof annotate $ get lProof lem
    annotate step cs =
        ( psInfo step
        , mconcat $ proofStepStatus step : incomplete ++ map snd cs
        )
      where
        incomplete = if isNothing (psInfo step) then [IncompleteProof] else []

    interpret status = case (get lTraceQuantifier lem, status) of
      (_,           IncompleteProof)   -> Nothing
      (_,           UndeterminedProof) -> Nothing
      (AllTraces,   TraceFound)        -> Just False
      (AllTraces,   CompleteProof)     -> Just True
      (ExistsTrace, TraceFound)        -> Just True
      (ExistsTrace, CompleteProof)     -> Just False

