{- |
Module      :  Web.Hamlet
Description :  Hamlet templates.
Copyright   :  (c) 2011 Cedric Staub
License     :  GPL-3

Maintainer  :  Cedric Staub <cstaub@ethz.ch>
Stability   :  experimental
Portability :  non-portable
-}

{-# LANGUAGE
    TypeFamilies, QuasiQuotes, TypeSynonymInstances, 
    PatternGuards, FlexibleInstances, CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Web.Hamlet where

import Theory
import Web.Types
import Web.Theory
import Data.Label
import Text.PrettyPrint.Html

import Yesod.Core
import Yesod.Form
import Text.Hamlet

import Data.Ord
import Data.List
import Data.Time.Format
import Data.Version (showVersion)
import qualified Data.Map as M
import qualified Data.Text as T

import Control.Monad.RWS (runRWST)
import qualified Control.Exception as E
import System.Locale

import Paths_tamarin_prover (version)

-- Quasi-quotation syntax changed from GHC 6 to 7,
-- so we need this switch in order to support both
#if __GLASGOW_HASKELL__ >= 700
#define HAMLET hamlet
#else
#define HAMLET $hamlet
#endif

--
-- Wrappers
--

-- | Wrapper for @HtmlDoc@ values.
wrapHtmlDoc :: HamletValue h => HtmlDoc Doc -> h
wrapHtmlDoc doc
  | null res  = exceptionTpl err
  | otherwise = [HAMLET|#{preEscapedString res}|]
  where
    res = renderHtmlDoc doc
    err = "Trying to render document yielded empty string. This is a bug."

-- | Run a ThHtml value, catch exceptions.
wrapThHtml :: HamletValue h => HtmlDoc Doc -> IO h
wrapThHtml th = E.catch (return $ wrapHtmlDoc th) handleEx
  where
    handleEx :: HamletValue h => E.SomeException -> IO h
    handleEx e = do
      putStrLn "----------------"
      putStrLn "Caught exception"
      putStrLn "----------------"
      print e
      return (exceptionTpl (show e))

--
-- Templates
--

-- | Exception/error template.
exceptionTpl :: HamletValue h => String -> h
exceptionTpl err = [HAMLET|
    <h1>Caught exception!
    \#{err}
  |]

-- | Simple template for serving sites which are loaded through
-- AJAX instead of a normal request (no html/head/body tags).
--
-- Note: Don't use ajaxLayout and defaultLayout together, use
-- only one or the other.
ajaxLayout :: Monad m => GenericWidget m () -> GenericHandler m RepHtml
ajaxLayout w = do
  (body, _, _) <- runRWST (unGWidget $ extractBody w) () 0
  hamletToRepHtml [HAMLET|^{body}|]

-- | Template for root/welcome page.
rootTpl :: (HamletValue h, HamletUrl h ~ WebUIRoute, h ~ Widget ())
        => TheoryMap      -- ^ Map of loaded theories
        -> Widget ()      -- ^ Form widget (for loading new theories)
        -> Enctype        -- ^ Form encoding type (for form)
        -> Html           -- ^ Nonce field (for form)
        -> h
rootTpl theories form enctype nonce = [HAMLET|
    \^{introTpl}
    <h2>Currently loaded theories
    <p
      Here is a list of the theories that are currently loaded.<br/>
      \^{theoriesTpl theories}
    <h2>Loading a new theory
    <p
      You can load a new theory file from disk in order to work with it.
    <form class=root-form action=@{RootR} method=POST enctype=#{enctype}>
      ^{form}
      <div .submit-form>
        ^{addHtml nonce}
        <input type=submit value="Load new theory">
    <p>Note: You can save a theory by downloading the source. 
  |]

-- | Template for listing theories.
theoriesTpl :: (HamletValue h, HamletUrl h ~ WebUIRoute) => TheoryMap -> h
theoriesTpl thmap = [HAMLET|
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

    tiName = get thyName . tiTheory . snd

    ntail _ [] = []
    ntail i (_:xs)
      | length xs <= i = xs
      | otherwise      = ntail i xs

-- | Template for single line in table on root page.
theoryTpl :: (HamletValue h, HamletUrl h ~ WebUIRoute)
          => (TheoryIdx, TheoryInfo) -> h
theoryTpl th = [HAMLET|
    <tr>
      <td>
        <a href=@{OverviewR (fst th)}>
          \#{get thyName $ tiTheory $ snd th}
        </a>
      <td>#{formatTime defaultTimeLocale "%T" $ tiTime $ snd th}
      $if tiPrimary (snd th)
        <td>Original
      $else
        <td><em>Modified</em>
      <td>#{origin th}
  |]
  where
    origin (_, ti) = case tiOrigin ti of
      Local path -> path
      Upload name ->  name
      Interactive -> "(interactively created)"

-- | Template for listing threads.
threadsTpl :: (HamletValue h, HamletUrl h ~ WebUIRoute) => [T.Text] -> h
threadsTpl threads = [HAMLET|
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

-- | Template for header frame (various information)
headerTpl :: (HamletValue h, HamletUrl h ~ WebUIRoute)
          => TheoryInfo   -- ^ Theory information
          -> h
headerTpl info = [HAMLET|
    <div #header-info>
      Running \
      <a href="http://people.inf.ethz.ch/meiersi/espl">tamarin prover</a>
      \ #{showVersion version}
    <div #header-links>
      <a class=plain-link href=@{RootR}>Index</a>
      $if localTheory (tiOrigin info)
        <a class=save-link href=@{SaveTheoryR idx}>Save</a>
      <a class=plain-link href=@{DownloadTheoryR idx filename}>Download</a>
      <ul #navigation>
        <li><a href="#">Actions</a>
          <ul>
            <li><a target=_blank href=@{TheorySourceR idx}>Show source</a>
            <li><a href=@{TheoryVariantsR idx}>Show variants</a>
            <li><a class=edit-link href=@{EditTheoryR idx}>Edit theory</a>
            <li><a class=edit-link href=@{EditPathR idx (TheoryLemma "")}>Add lemma</a>
        <li><a href="#">Options</a>
          <ul>
            <li><a id=graph-toggle href="#">Compact graphs</a>
            <li><a id=seqnt-toggle href="#">Compress sequents</a>
            <li><a id=debug-toggle href="#">Debug pane</a>
  |]
  where
    idx = tiIndex info
    filename = get thyName (tiTheory info) ++ ".spthy"

    localTheory (Local _) = True
    localTheory _         = False

-- | Template for proof state (tree) frame.
proofStateTpl :: (HamletValue h, HamletUrl h ~ WebUIRoute)
              => TheoryInfo   -- ^ Theory information
              -> IO h
proofStateTpl = wrapThHtml . theoryIndex . tiTheory

-- | Framing/UI-layout template (based on JavaScript/JQuery)
overviewTpl :: (HamletValue h, HamletUrl h ~ WebUIRoute)
            => TheoryInfo -- ^ Theory information
            -> TheoryPath -- ^ Theory path to load into main
            -> IO h
overviewTpl info path = do
  proofState <- proofStateTpl info
  mainView <- pathTpl info path
  return [HAMLET|
    <div .ui-layout-north>
      ^{headerTpl info}
    <div .ui-layout-west>
      <h1 .pane-head>&nbsp;Proof scripts
      <div #proof-wrapper .scroll-wrapper>
        <div #proof .monospace>
          ^{proofState}
    <div .ui-layout-east>
      <h1 .pane-head>&nbsp;Debug information
      <div #debug-wrapper .scroll-wrapper>
        <div #ui-debug-display>
    <div .ui-layout-center>
      <h1 #main-title .pane-head>&nbsp;Visualization display
      <div #main-wrapper .scroll-wrapper tabindex=0>
        <div #ui-main-display>
          \^{mainView}
  |]

-- | Theory path, displayed when loading main screen for first time.
pathTpl :: (HamletValue h, HamletUrl h ~ WebUIRoute)
        => TheoryInfo   -- ^ The theory
        -> TheoryPath   -- ^ Path to display on load
        -> IO h
pathTpl info TheoryMain = return [HAMLET|
    <h2>Welcome!</h2><br/>
    <h3>Theory information</h3>
      <ul
        <li>Theory: #{get thyName $ tiTheory info}
        <li>Loaded at #{formatTime defaultTimeLocale "%T" $ tiTime info}
        <li>Origin: #{show $ tiOrigin info}
    <h3>Quick introduction</h3>
    <p>
      <em>Left pane:</em> Proof scripts display. You \
      can select proof states and examine them further \
      by clicking on them!
    <p>
      <em>Center pane:</em> Visualization and \
      information display relating to the currently \
      selected item.
    <p>
      <em>Keyboard shortcuts:</em> The interactive interface supports \
      multiple keyboard shortcuts for convenience. 
      <ul>
        <li>
          Keys <span class=keys>j and k</span>: Jump to the next/previous \
          proof path within the currently focused lemma.
        <li>
          Keys <span class=keys>J and K</span>: Jump to the next/previous \
          open goal within the currently focused lemma, or to the \
          next/previous lemma if there are no more open goals in the current \
          lemma.
        <li>
          Keys <span class=keys>1 to 9</span>: Apply the proof method with \
          the given number as shown in the applicable proof method section \
          in the main view.
  |]
pathTpl info path = wrapThHtml $ htmlThyPath (tiTheory info) path

-- | Template for introduction.
introTpl :: (HamletValue h, HamletUrl h ~ WebUIRoute) => h
introTpl = [HAMLET|
    <h1>Welcome!</h1>
    <h2>About
    <p>
      You are running the\
      <strong>
        <a href="http://people.inf.ethz.ch/meiersi/espl">tamarin prover</a>
      </strong>
      \ version #{showVersion version} in interactive mode.
      \ &copy;&nbsp;2010&nbsp;-&nbsp;2012 \
      <a href="https://www1.ethz.ch/infsec/people/benschmi">Benedikt Schmidt</a>
      , <a href="http://people.inf.ethz.ch/meiersi">Simon Meier</a>
      , <a href="https://cssx.ch">Cedric Staub</a>
      , <a href="http://www.infsec.ethz.ch">Information Security Institute</a>
      , <a href="http://www.ethz.ch">ETH Zurich</a>
    <p>
      This program comes with ABSOLUTELY NO WARRANTY. It is free software, and
      \ you are welcome to redistribute it according to its
      \ <a href="/static/LICENSE" type="text/plain">LICENSE</a>.
  |]

-- | Template for editing a theory.
formTpl :: (HamletValue h, HamletUrl h ~ WebUIRoute, h ~ Widget ())
        => WebUIRoute  -- ^ Form action route
        -> String      -- ^ Submit button label
        -> Widget ()   -- ^ Form widget
        -> Enctype     -- ^ Form encoding type
        -> Html        -- ^ Nonce field
        -> h
formTpl action label form enctype nonce = [HAMLET|
    <form action=@{action} method=POST enctype=#{enctype}>
      ^{form}
      <div .submit-form>
        ^{addHtml nonce}
        <input type=submit value=#{label}>
        <input type=button id=cancel-form value=Cancel>
  |]
