{-# LANGUAGE QuasiQuotes #-}

{- |
Module      :  Web.Hamlet
Description :  Hamlet templates.
Copyright   :  (c) 2011 Cedric Staub
License     :  GPL-3

Maintainer  :  Ralf Sasse <ralf.sasse@gmail.com>
Stability   :  experimental
Portability :  non-portable
-}

module Web.Hamlet
  ( rootTpl
  , overviewTpl
  , overviewDiffTpl
  ) where

import Text.PrettyPrint.Html
import Theory
import Web.Theory
import Web.Types

import Yesod.Core

import Data.List
import Data.Map qualified as M
import Data.Ord
import Data.Time.Format
import Data.Version (showVersion)

import Paths_tamarin_prover (version)

--
-- Templates
--

{-
-- | Simple template for serving sites which are loaded through
-- AJAX instead of a normal request (no html/head/body tags).
--
-- Note: Don't use ajaxLayout and defaultLayout together, use
-- only one or the other.
-- ajaxLayout :: Monad m => GenericWidget m () -> GenericHandler m RepHtml
ajaxLayout w = error "ajaxLayout" $ fmap fst $ unGWidget w -- do
  -- (body, _, _) <- runRWST (unGWidget $ extractBody w) () 0
  -- (body, _, _) <- unGWidget $ w -- () 0
  -- hamletToRepHtml [whamlet|^{body}|]
-}

-- | Template for root/welcome page.
rootTpl :: TheoryMap      -- ^ Map of loaded theories
        -> Widget
-- rootTpl theories form enctype nonce = [whamlet|
rootTpl theories = [whamlet|
    $newline never
    <div class="ui-layout-container">
      <div class="ui-layout-north">
        <div class="ui-layout-pane">
          <div class="layout-pane-north">
            <div class="ui-layout-pane-north">
              <div id="introbar">
                <div id="header-info">
                  Running
                  \ <a href=@{RootR}><span class="tamarin">Tamarin</span></a>
                  \ #{showVersion version}
    \^{introTpl}
    <div class="intropage">
      <p>
        \^{theoriesTpl theories}
      <h2>Loading a new theory
      <p>
        You can load a new theory file from disk in order to work with it.
      <form class=root-form enctype="multipart/form-data" action=@{RootR} method=POST>
        Filename:
        <input type=file name="uploadedTheory">
        <div .submit-form>
          <input type=submit value="Load new theory">
      <p>Note: You can save a theory by downloading the source.
  |]

-- | Template for listing theories.
theoriesTpl :: TheoryMap -> Widget
theoriesTpl thmap = [whamlet|
    $newline never
    $if M.null thmap
      <strong>No theories loaded!</strong>
    $else
      <table>
        <thead>
          <th>Theory name
          <th>Time
          <th>Version
          <th>Origin
        $forall tgroup <- processMap thmap
          ^{theoryTpl (head tgroup)}
          $forall th <- ntail 4 tgroup
            ^{theoryTpl th}
    <br>
  |]
  where
    processMap =
      groupBy (\x y -> comparing tiName x y == EQ) .
      sortBy (comparing snd) . M.toList

    tiName x = getEitherTheoryName $ snd x

    ntail _ [] = []
    ntail i (_:xs)
      | length xs <= i = xs
      | otherwise      = ntail i xs


-- | Template for single line in table on root page.
theoryTpl :: (TheoryIdx, EitherTheoryInfo) -> Widget
theoryTpl th = [whamlet|
    $newline never
    <tr>
      $if isTheoryInfo (snd th)
        <td>
          <a href=@{OverviewR (fst th) TheoryHelp}>
            \#{getEitherTheoryName $ snd th}
      $else
        <td>
          <a href=@{OverviewDiffR (fst th) DiffTheoryHelp}>
            \#{getEitherTheoryName $ snd th}
      <td>#{formatTime defaultTimeLocale "%T" $ getEitherTheoryTime $ snd th}
      $if getEitherTheoryPrimary (snd th)
        <td>Original
      $else
        <td><em>Modified
      <td>#{origin th}
  |]
  where
    origin (_, ti) = case getEitherTheoryOrigin ti of
      Local path -> path
      Upload name ->  name
      Interactive -> "(interactively created)"

-- | Template for listing threads.
-- threadsTpl :: (HamletValue h, HamletUrl h ~ WebUIRoute) => [T.Text] -> h
{-
threadsTpl threads = [whamlet|
    $newline never
    <h2>Threads
    <p>
      This page lists all threads that are currently registered as
      \ evaluating a request within the server. This is meant for debugging
      \ lockups within the server.
    $if null threads
      <strong>No threads registered!</strong>
    $else
      <table>
        <thead>
          <th>Request path
          <th>Kill?
        $forall th <- threads
          <tr>
            <td>#{th}
            <td><a href="@{KillThreadR}?path=#{th}">Kill</a>
  |]
-}

-- | Template for header frame (various information)
headerTpl :: TheoryInfo -> Widget
headerTpl info = [whamlet|
    $newline never
    <div class="layout-pane-north">
      <div #header-info>
        Running
        \ <a href=@{RootR}><span class="tamarin">Tamarin</span></a>
        \ #{showVersion version}
    <div #header-links>
      <a class=plain-link href=@{RootR}>Index</a>
      <a class=plain-link href=@{DownloadTheoryR idx filename}>Download</a>
      <a class=save-link  href=@{AppendNewLemmasR idx filename}>Append modified Lemmas to file</a>
      <ul #navigation>
        <li><a href="#">Actions</a>
          <ul>
            <li><a target=_blank href=@{TheorySourceR idx}>Show source</a>
        <li><a href="#">Options</a>
          <ul>
            <li><a id=abbrv-toggle href="#">Abbreviate terms</a>
            <li><a id=agent-toggle href="#">Clustering by role</a>
            <li><a id=auto-toggle href="#">Show annotation auto-sources</a>
            <li><a id=lvl0-toggle href="#">Graph simplification off</a>
            <li><a id=lvl1-toggle href="#">Graph simplification L1</a>
            <li><a id=lvl2-toggle href="#">Graph simplification L2</a>
            <li><a id=lvl3-toggle href="#">Graph simplification L3</a>
  |]
  where
            -- <li><a id=debug-toggle href="#">Debug pane</a>
            -- <li><a href=@{TheoryVariantsR idx}>Show variants</a>
            -- <li><a class=edit-link href=@{EditTheoryR idx}>Edit theory</a>
            -- <li><a class=edit-link href=@{EditPathR idx (TheoryLemma "")}>Add lemma</a>
            --
    idx = info.index
    filename = info.theory._thyName ++ ".spthy"

      {- use this snipped to reactivate saving local theories
    localTheory (Local _) = True
    localTheory _         = False

      $if localTheory (tiOrigin info)
        <a class=save-link href=@{SaveTheoryR idx}>Save</a>

    -}

-- | Template for header frame (various information)
headerDiffTpl :: DiffTheoryInfo -> Widget
headerDiffTpl info = [whamlet|
    $newline never
    <div class="layout-pane-north">
      <div #header-info>
        Running
        \ <a href=@{RootR}><span class="tamarin">Tamarin</span></a>
        \ #{showVersion version}
    <div #header-links>
      <a class=plain-link href=@{RootR}>Index</a>
      <a class=plain-link href=@{DownloadTheoryDiffR idx filename}>Download</a>
      <ul #navigation>
        <li><a href="#">Actions</a>
          <ul>
            <li><a target=_blank href=@{TheorySourceDiffR idx}>Show source</a>
        <li><a href="#">Options</a>
          <ul>
            <li><a id=abbrv-toggle href="#">Abbreviate terms</a>
            <li><a id=agent-toggle href="#">Clusturing by role</a>
            <li><a id=auto-toggle href="#">Show annotation auto-sources</a>
            <li><a id=lvl0-toggle href="#">Graph simplification off</a>
            <li><a id=lvl1-toggle href="#">Graph simplification L1</a>
            <li><a id=lvl2-toggle href="#">Graph simplification L2</a>
            <li><a id=lvl3-toggle href="#">Graph simplification L3</a>

  |]
  where
            -- <li><a id=debug-toggle href="#">Debug pane</a>
            -- <li><a href=@{TheoryVariantsR idx}>Show variants</a>
            -- <li><a class=edit-link href=@{EditTheoryR idx}>Edit theory</a>
            -- <li><a class=edit-link href=@{EditPathR idx (TheoryLemma "")}>Add lemma</a>
            --
    idx = info.index
    filename = info.theory._diffThyName ++ ".spthy"

    {- use this snipped to reactivate saving local theories
    localTheory (Local _) = True
    localTheory _         = False

      $if localTheory (tiOrigin info)
        <a class=save-link href=@{SaveTheoryR idx}>Save</a>

    -}

-- | Template for proof state (tree) frame.
proofStateTpl :: RenderUrl -> TheoryInfo -> IO Widget
proofStateTpl renderUrl ti = do
  let res = renderHtmlDoc $ theoryIndex renderUrl ti.index ti.theory
  pure [whamlet|
         $newline never
         #{preEscapedToMarkup res} |]

-- | Template for proof state (tree) frame.
proofStateDiffTpl :: RenderUrl -> DiffTheoryInfo -> IO Widget
proofStateDiffTpl renderUrl ti = do
  let res = renderHtmlDoc $ diffTheoryIndex renderUrl ti.index ti.theory
  pure [whamlet|
         $newline never
         #{preEscapedToMarkup res} |]

-- | Framing/UI-layout template (based on JavaScript/JQuery)
overviewTpl :: RenderUrl
            -> RenderUrl -- ^ URL renderer that includes GET parameters for the image.
            -> TheoryInfo -- ^ Theory information
            -> TheoryPath -- ^ Theory path to load into main
            -> String     -- ^ The lemma plaintext for editing
            -> IO Widget
overviewTpl renderUrl renderImgUrl info path lptxt = do
  proofState <- proofStateTpl renderUrl info
  mainView <- pathTpl renderUrl renderImgUrl info path lptxt
  pure [whamlet|
    $newline never
    <div .ui-layout-north>
      ^{headerTpl info}
    <div .ui-layout-west>
      <h1 .pane-head>Proof scripts
      <div #proof-wrapper .scroll-wrapper>
        <div #proof .monospace>
          ^{proofState}
    <div .ui-layout-east>
      <h1 .pane-head>&nbsp;Debug information
      <div #debug-wrapper .scroll-wrapper>
        <div #ui-debug-display>
    <div .ui-layout-center>
      <h1 #main-title .pane-head>Visualization display
      <div #main-wrapper .scroll-wrapper tabindex=0>
        <div #ui-main-display>
          \^{mainView}
  |]

-- | Framing/UI-layout template (based on JavaScript/JQuery)
overviewDiffTpl :: RenderUrl
                -> DiffTheoryInfo -- ^ Theory information
                -> DiffTheoryPath -- ^ Theory path to load into main
                -> IO Widget
overviewDiffTpl renderUrl info path = do
  proofState <- proofStateDiffTpl renderUrl info
  mainView <- pathDiffTpl renderUrl info path
  pure [whamlet|
    $newline never
    <div .ui-layout-north>
      ^{headerDiffTpl info}
    <div .ui-layout-west>
      <h1 .pane-head>Proof scripts
      <div #proof-wrapper .scroll-wrapper>
        <div #proof .monospace>
          ^{proofState}
    <div .ui-layout-east>
      <h1 .pane-head>&nbsp;Debug information
      <div #debug-wrapper .scroll-wrapper>
        <div #ui-debug-display>
    <div .ui-layout-center>
      <h1 #main-title .pane-head>Visualization display
      <div #main-wrapper .scroll-wrapper tabindex=0>
        <div #ui-main-display>
          \^{mainView}
  |]


-- | Theory path, displayed when loading main screen for first time.
pathTpl :: RenderUrl
        -> RenderUrl      -- ^ URL renderer that includes GET parameters for the image.
        -> TheoryInfo     -- ^ The theory
        -> TheoryPath     -- ^ Path to display on load
        -> String         -- ^ plaintext of lemma for editing
        -> IO Widget
pathTpl renderUrl renderImgUrl info path lptxt =
  pure [whamlet|
         $newline never
         #{htmlThyPath renderUrl renderImgUrl info path lptxt} |]

-- | Theory path, displayed when loading main screen for first time.
pathDiffTpl :: RenderUrl
            -> DiffTheoryInfo   -- ^ The theory
            -> DiffTheoryPath   -- ^ Path to display on load
            -> IO Widget
pathDiffTpl renderUrl info path =
  pure [whamlet|
         $newline never
         #{htmlDiffThyPath renderUrl info path} |]

-- | Template for introduction.
introTpl :: Widget
introTpl = [whamlet|
    $newline never
      <div id="logo">
        <p>
          <img src="/static/img/tamarin-logo-3-0-0.png">
      <noscript>
        <div class="warning">
          Warning: JavaScript must be enabled for the <span class="tamarin">Tamarin</span> prover GUI to function properly.
    <div class="intropage">
      <p>
        Core team:
        \ <a href="https://www.inf.ethz.ch/personal/basin/">David Basin</a>,
        \ <a href="https://cispa.saarland/group/cremers/">Cas Cremers</a>,
        \ <a href="https://www.jannikdreier.net">Jannik Dreier</a>,
        \ <a href="mailto:iridcode@gmail.com">Simon Meier</a>,
        \ <a href="https://people.inf.ethz.ch/rsasse/">Ralf Sasse</a>,
        \ <a href="https://beschmi.net">Benedikt Schmidt</a><br>
        Tamarin is a collaborative effort: see the <a href="https://tamarin-prover.com/manual/index.html">manual</a> for a more extensive overview of its development and additional contributors.
      <p>
        This program comes with ABSOLUTELY NO WARRANTY. It is free software, and
        \ you are welcome to redistribute it according to its
        \ <a href="/static/LICENSE" type="text/plain">LICENSE.</a>
      <p>
        More information about Tamarin and technical papers describing the underlying
        \ theory can be found on the
        \ <a href="https://tamarin-prover.com"><span class="tamarin">Tamarin</span>
        \ webpage</a>.
  |]

{-
-- | Template for editing a theory.
-- formTpl :: (HamletValue h, HamletUrl h ~ WebUIRoute, h ~ Widget ())
--         => WebUIRoute  -- ^ Form action route
--         -> String      -- ^ Submit button label
--         -> Widget ()   -- ^ Form widget
--         -> Enctype     -- ^ Form encoding type
--         -> Html        -- ^ Nonce field
--         -> h
formTpl action label form enctype nonce = [whamlet|
    $newline never
    <form action=@{action} method=POST enctype=#{enctype}>
      ^{form}
      <div .submit-form>
        ^{addHtml nonce}
        <input type=submit value=#{label}>
        <input type=button id=cancel-form value=Cancel>
  |]
-}
