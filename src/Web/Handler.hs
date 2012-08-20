{- |
Module      :  Web.Handler
Description :  Application-specific handler functions.
Copyright   :  (c) 2011 Cedric Staub, 2012 Benedikt Schmidt
License     :  GPL-3

Maintainer  :  Cedric Staub <cstaub@ethz.ch>
Stability   :  experimental
Portability :  non-portable
-}

{-# LANGUAGE
    OverloadedStrings, QuasiQuotes, TypeFamilies, FlexibleContexts,
    RankNTypes, TemplateHaskell, CPP #-}

module Web.Handler
  ( getOverviewR
  , getRootR
  , postRootR
  , getTheorySourceR
  , getTheoryMessageDeductionR
  , getTheoryVariantsR
  , getTheoryPathMR
  -- , getTheoryPathDR
  , getTheoryGraphR
  , getAutoProverR
  , getDeleteStepR
  , getKillThreadR
  , getNextTheoryPathR
  , getPrevTheoryPathR
  , getSaveTheoryR
  , getDownloadTheoryR
  -- , getEditTheoryR
  -- , postEditTheoryR
  -- , getEditPathR
  -- , postEditPathR
  , getUnloadTheoryR
  -- , getThreadsR
  )
where

import           Theory                       (
    ClosedTheory,
    thyName, removeLemma,
    openTheory, sorryProver, runAutoProver,
    prettyClosedTheory, prettyOpenTheory
  )
import           Theory.Proof (AutoProver(..), SolutionExtractor(..), Prover, apHeuristic)
import           Text.PrettyPrint.Html
import           Theory.Constraint.System.Dot
import           Web.Hamlet
import           Web.Instances                ()
import           Web.Settings
import           Web.Theory
import           Web.Types

import           Yesod.Core
import           Yesod.Json()

import           Data.Aeson
import           Data.Label
import           Data.Maybe
import           Data.String                  (fromString)
import           Data.List                    (intersperse)
import           Data.Monoid                  (mconcat)

import qualified Blaze.ByteString.Builder     as B
import qualified Data.ByteString.Lazy.Char8   as BS
import qualified Data.Map                     as M
import qualified Data.Text                    as T
import           Data.Text.Encoding
import qualified Data.Traversable             as Tr
import           Network.HTTP.Types           ( urlDecode )
import           Text.Blaze.Html5             (toHtml)

import           Control.Applicative
import           Control.Concurrent
import qualified Control.Concurrent.Thread    as Thread ( forkIO )
import           Control.DeepSeq
import           Control.Exception.Base
import qualified Control.Exception.Lifted     as E
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Control
import qualified Data.Binary                  as Bin
import           Data.Time.LocalTime
import           System.Directory

import           Debug.Trace                  (trace)

-- Quasi-quotation syntax changed from GHC 6 to 7,
-- so we need this switch in order to support both
#if __GLASGOW_HASKELL__ >= 700
#define HAMLET hamlet
#else
#define HAMLET $hamlet
#endif


------------------------------------------------------------------------------
-- Manipulate the state
------------------------------------------------------------------------------

-- | Store theory map in file if option enabled.
storeTheory :: WebUI
            -> TheoryInfo
            -> TheoryIdx
            -> IO ()
storeTheory yesod thy idx =
    when (autosaveProofstate yesod) $ do
      let f = workDir yesod++"/"++autosaveSubdir++"/"++show idx++".img"
      Bin.encodeFile (f++".tmp") thy
      renameFile (f++".tmp") f

-- | Load a theory given an index.
getTheory :: TheoryIdx -> Handler (Maybe TheoryInfo)
getTheory idx = do
    yesod <- getYesod
    liftIO $ withMVar (theoryVar yesod) $ return . M.lookup idx

-- | Store a theory, return index.
putTheory :: Maybe TheoryInfo     -- ^ Index of parent theory
          -> Maybe TheoryOrigin   -- ^ Origin of this theory
          -> ClosedTheory         -- ^ The new closed theory
          -> Handler TheoryIdx
putTheory parent origin thy = do
    yesod <- getYesod
    liftIO $ modifyMVar (theoryVar yesod) $ \theories -> do
      time <- getZonedTime
      let idx | M.null theories = 1
              | otherwise       = fst (M.findMax theories) + 1
          parentIdx    = tiIndex <$> parent
          parentOrigin = tiOrigin <$> parent
          newOrigin    = parentOrigin <|> origin <|> (Just Interactive)
          newThy       =
              TheoryInfo idx thy time parentIdx False (fromJust newOrigin)
                         (maybe (defaultAutoProver yesod) tiAutoProver parent)
      storeTheory yesod newThy idx
      return (M.insert idx newThy theories, idx)

-- | Delete theory.
delTheory :: TheoryIdx -> Handler ()
delTheory idx = do
    yesod <- getYesod
    liftIO $ modifyMVar_ (theoryVar yesod) $ \theories -> do
      let theories' = M.delete idx theories
      -- FIXME: delete from autosave directory?
      return theories'

-- | Get a map of all stored theories.
getTheories :: Handler TheoryMap
getTheories = do
    yesod <- getYesod
    liftIO $ withMVar (theoryVar yesod) return


-- | Modify a theory in the map of theories.
adjTheory :: TheoryIdx
          -> (TheoryInfo -> TheoryInfo)
          -> Handler ()
adjTheory idx f = do
    yesod <- getYesod
    liftIO $ modifyMVar_ (theoryVar yesod) $ \theories ->
      case M.lookup idx theories of
        Just thy -> do
          let newThy =  f thy
          storeTheory yesod newThy idx
          return $ M.insert idx newThy theories
        Nothing -> error "adjTheory: invalid theory index"

-- | Debug tracing.
dtrace :: WebUI -> String -> a -> a
dtrace yesod msg | debug yesod = trace msg
                 | otherwise   = id

-- | Register a thread for killing.
putThread :: T.Text                      -- ^ Request path
          -> ThreadId                    -- ^ Thread ID
          -> Handler ()
putThread str tid = do
    yesod <- getYesod
    liftIO $ dtrace yesod msg $
      modifyMVar_ (threadVar yesod) $ return . (M.insert str tid)
  where
    msg = "Registering thread: " ++ T.unpack str

-- | Unregister a thread for killing.
delThread :: T.Text       -- ^ Request path
          -> Handler ()
delThread str = do
    yesod <- getYesod
    liftIO $ dtrace yesod msg $
      modifyMVar_ (threadVar yesod) $ return . (M.delete str)
  where
    msg = "Deleting thread: " ++ T.unpack str


-- | Get a thread for the given request URL.
getThread :: T.Text       -- ^ Request path
          -> Handler (Maybe ThreadId)
getThread str = do
    yesod <- getYesod
    liftIO $ dtrace yesod msg $
      withMVar (threadVar yesod) $ return . M.lookup str
  where
    msg = "Retrieving thread id of: " ++ T.unpack str

{-
-- | Get the map of all threads.
-- getThreads :: MonadIO m
--            => GenericHandler m [T.Text]
getThreads = do
    yesod <- getYesod
    liftIO $ withMVar (threadVar yesod) (return . M.keys)
-}

------------------------------------------------------------------------------
-- Helper functions
------------------------------------------------------------------------------

-- | Print exceptions, if they happen.
traceExceptions :: MonadBaseControl IO m => String -> m a -> m a
traceExceptions info =
    E.handle handler
  where
    handler :: MonadBaseControl IO m => E.SomeException -> m a
    handler e =
      trace (info ++ ": exception `" ++ show e ++ "'") $ E.throwIO e

-- | Helper functions for generating JSON reponses.
jsonResp :: JsonResponse -> GHandler m WebUI RepJson
jsonResp = return . RepJson . toContent . responseToJson

responseToJson :: JsonResponse -> Value
responseToJson = go
  where
    jsonObj key val = object [ key .= val ]

    go (JsonAlert msg)          = jsonObj "alert" $ toJSON msg
    go (JsonRedirect url)       = jsonObj "redirect" $ toJSON url
    go (JsonHtml title content) = object
      [ "html"  .= contentToJson content
      , "title" .= title ]

    contentToJson (ContentBuilder b _) = toJSON $ B.toLazyByteString b
    contentToJson _ = error "Unsupported content format in json response!"

-- | Fully evaluate a value in a thread that can be canceled.
evalInThread :: NFData a
             => IO a
             -> Handler (Either SomeException a)
evalInThread io = do
    renderF <- getUrlRender
    maybeRoute <- getCurrentRoute
    case maybeRoute of
      Just route -> do
        let key = renderF route
        (tid, wait) <- liftIO $ Thread.forkIO $ do x <- io
                                                   evaluate (rnf x)
                                                   return x
        putThread key tid
        res <- liftIO $ wait
        delThread key
        return res
      Nothing -> Right `liftM` liftIO io

-- | Evaluate a handler with a given theory specified by the index,
-- return notFound if theory does not exist.
withTheory :: TheoryIdx
           -> (TheoryInfo -> Handler a)
           -> Handler a
withTheory idx handler = do
  maybeThy <- getTheory idx
  case maybeThy of
    Just ti -> handler ti
    Nothing -> notFound

{-
-- | Run a form and provide a JSON response.
-- formHandler :: (HamletValue h, HamletUrl h ~ WebUIRoute, h ~ Widget ())
--             => T.Text                              -- ^ The form title
--             -> Form WebUI WebUI a                  -- ^ The formlet to run
--             -> (Widget () -> Enctype -> Html -> h) -- ^ Template to render form with
--             -> (a -> GenericHandler IO RepJson)    -- ^ Function to call on success
--             -> Handler RepJson
formHandler title formlet template success = do
    -- (result, widget, enctype, nonce) <- runFormPost formlet
    ((result, widget), enctype) <- runFormPost formlet
    case result of
      FormMissing -> do
        RepHtml content <- ajaxLayout (template widget enctype)
        jsonResp $ JsonHtml title content
      FormFailure _ -> jsonResp $ JsonAlert
        "Missing fields in form. Please fill out all required fields."
      FormSuccess ret -> lift (success ret)
-}


-- | Modify a theory, redirect if successful.
modifyTheory :: TheoryInfo                                -- ^ Theory to modify
             -> (ClosedTheory -> IO (Maybe ClosedTheory)) -- ^ Function to apply
             -> (ClosedTheory -> TheoryPath)              -- ^ Compute the new path
             -> JsonResponse                              -- ^ Response on failure
             -> Handler Value
modifyTheory ti f fpath errResponse = do
    res <- evalInThread (liftIO $ f (tiTheory ti))
    case res of
      Left e           -> return (excResponse e)
      Right Nothing    -> return (responseToJson errResponse)
      Right (Just thy) -> do
        newThyIdx <- putTheory (Just ti) Nothing thy
        newUrl <- getUrlRender <*> pure (OverviewR newThyIdx (fpath thy))
        return . responseToJson $ JsonRedirect newUrl
  where
   excResponse e = responseToJson
                     (JsonAlert $ "Last request failed with exception: " `T.append` (T.pack (show e)))

------------------------------------------------------------------------------
-- Handler functions
------------------------------------------------------------------------------

-- | The root handler lists all theories by default,
-- or load a new theory if the corresponding form was submitted.
getRootR :: Handler RepHtml
getRootR = do
    theories <- getTheories
    defaultLayout $ do
      setTitle "Welcome to the Tamarin prover"
      addWidget (rootTpl theories)

data File = File T.Text
  deriving Show

postRootR :: Handler RepHtml
postRootR = do
    result <- lookupFile "uploadedTheory"
    case result of
      Nothing ->
        setMessage "Post request failed."
      Just fileinfo
        | BS.null $ fileContent fileinfo -> setMessage "No theory file given."
        | otherwise                      -> do
            yesod <- getYesod
            closedThy <- liftIO $ parseThy yesod (BS.unpack $ fileContent fileinfo)
            case closedThy of
              Left err  -> setMessage $ "Theory loading failed:\n" <> toHtml err
              Right thy -> do
                  void $ putTheory Nothing
                           (Just $ Upload $ T.unpack $ fileName fileinfo) thy
                  setMessage "Loaded new theory!"
    theories <- getTheories
    defaultLayout $ do
      setTitle "Welcome to the Tamarin prover"
      addWidget (rootTpl theories)


-- | Show overview over theory (framed layout).
getOverviewR :: TheoryIdx -> TheoryPath -> Handler RepHtml
getOverviewR idx path = withTheory idx $ \ti -> do
  renderF <- getUrlRender
  defaultLayout $ do
    overview <- liftIO $ overviewTpl renderF ti path
    setTitle (toHtml $ "Theory: " ++ get thyName (tiTheory ti))
    addWidget overview

-- | Show source (pretty-printed open theory).
getTheorySourceR :: TheoryIdx -> Handler RepPlain
getTheorySourceR idx = withTheory idx $ \ti ->
  return $ RepPlain $ toContent $ prettyRender ti
  where
    prettyRender = render . prettyClosedTheory . tiTheory

-- | Show variants (pretty-printed closed theory).
getTheoryVariantsR :: TheoryIdx -> Handler RepPlain
getTheoryVariantsR idx = withTheory idx $ \ti ->
  return $ RepPlain $ toContent $ prettyRender ti
  where prettyRender = render . prettyClosedTheory . tiTheory

-- | Show variants (pretty-printed closed theory).
getTheoryMessageDeductionR :: TheoryIdx -> Handler RepPlain
getTheoryMessageDeductionR idx = withTheory idx $ \ti ->
  return $ RepPlain $ toContent $ prettyRender ti
  where prettyRender = render . prettyClosedTheory . tiTheory


-- | Show a given path within a theory (main view).
getTheoryPathMR :: TheoryIdx
                -> TheoryPath
                -> Handler RepJson
getTheoryPathMR idx path = do
    renderUrl <- getUrlRender
    jsonValue <- withTheory idx (go renderUrl path)
    return $ RepJson $ toContent jsonValue
  where
    --
    -- Handle method paths by trying to solve the given goal/method
    --
    go _ (TheoryMethod lemma proofPath i) ti = modifyTheory ti
        (\thy -> return $ applyMethodAtPath thy lemma proofPath heuristic i)
        (\thy -> nextSmartThyPath thy (TheoryProof lemma proofPath))
        (JsonAlert "Sorry, but the prover failed on the selected method!")
      where
        heuristic = apHeuristic (tiAutoProver ti)

    --
    -- Handle generic paths by trying to render them
    --
    go renderUrl _ ti = do
      let title = T.pack $ titleThyPath (tiTheory ti) path
      let html = htmlThyPath renderUrl ti path
      return $ responseToJson (JsonHtml title $ toContent html)

-- | Run the some prover on a given proof path.
getProverR :: (T.Text, AutoProver -> Prover)
           -> TheoryIdx -> TheoryPath -> Handler RepJson
getProverR (name, mkProver) idx path = do
    jsonValue <- withTheory idx (go path)
    return $ RepJson $ toContent jsonValue
  where
    go (TheoryProof lemma proofPath) ti = modifyTheory ti
        (\thy ->
            return $ applyProverAtPath thy lemma proofPath autoProver)
        (\thy -> nextSmartThyPath thy path)
        (JsonAlert $ "Sorry, but " <> name <> " failed!")
      where
        autoProver = mkProver (tiAutoProver ti)

    go _ _ = return $ responseToJson $ JsonAlert $
      "Can't run " <> name <> " on the given theory path!"

-- | Run an autoprover on a given proof path.
getAutoProverR :: TheoryIdx
               -> SolutionExtractor
               -> Int                             -- autoprover bound to use
               -> TheoryPath -> Handler RepJson
getAutoProverR idx extractor bound =
    getProverR (fullName, runAutoProver . adapt) idx
  where
    adapt autoProver = autoProver { apBound = actualBound, apCut = extractor }

    withCommas = intersperse ", "
    fullName   = mconcat $ proverName : " (" : withCommas qualifiers ++ [")"]
    qualifiers = extractorQualfier ++ boundQualifier

    (actualBound, boundQualifier)
        | bound > 0 = (Just bound, ["bound " <> T.pack (show bound)])
        | otherwise = (Nothing,    []                               )

    (proverName, extractorQualfier) = case extractor of
        CutNothing -> ("characterization", ["dfs"])
        CutDFS     -> ("the autoprover",   []     )
        CutBFS     -> ("the autoprover",   ["bfs"])


{-
-- | Show a given path within a theory (debug view).
getTheoryPathDR :: TheoryIdx -> TheoryPath -> Handler RepHtml
getTheoryPathDR idx path = withTheory idx $ \ti -> ajaxLayout $ do
  -- let maybeDebug = htmlThyDbgPath (tiTheory ti) path
  -- let maybeWidget = wrapHtmlDoc <$> maybeDebug
  return [hamlet|
    <h2>Theory information</h2>
    <ul>
      <li>Index = #{show (tiIndex ti)}
      <li>Path = #{show path}
      <li>Time = #{show (tiTime ti)}
      <li>Origin = #{show (tiOrigin ti)}
      <li>NextPath = #{show (nextThyPath (tiTheory ti) path)}
      <li>PrevPath = #{show (prevThyPath (tiTheory ti) path)}
      <li>NextSmartPath = #{show (nextSmartThyPath (tiTheory ti) path)}
      <li>PrevSmartPath = #{show (prevSmartThyPath (tiTheory ti) path)}
  |]
    {-
    $if isJust maybeWidget
      <h2>Current sequent</h2><br>
      \^{fromJust maybeWidget}
  |]
  -}
-}

-- | Get rendered graph for theory and given path.
getTheoryGraphR :: TheoryIdx -> TheoryPath -> Handler ()
getTheoryGraphR idx path = withTheory idx $ \ti -> do
      yesod <- getYesod
      compact <- isNothing <$> lookupGetParam "uncompact"
      compress <- isNothing <$> lookupGetParam "uncompress"
      img <- liftIO $ traceExceptions "getTheoryGraphR" $
        imgThyPath
          (imageFormat yesod)
          (dotCmd yesod)
          (cacheDir yesod)
          (graphStyle compact compress)
          (tiTheory ti) path
      sendFile (fromString . imageFormatMIME $ imageFormat yesod) img
  where
    graphStyle d c = dotStyle d . compression c
    dotStyle True = dotSystemCompact CompactBoringNodes
    dotStyle False = dotSystemCompact FullBoringNodes
    compression True = compressSystem
    compression False = id


-- | Kill a thread (aka 'cancel request').
getKillThreadR :: Handler RepPlain
getKillThreadR = do
    maybeKey <- lookupGetParam "path"
    case maybeKey of
      Just key0 -> do
        let key = decodeUtf8 . urlDecode True . encodeUtf8 $ key0
        tryKillThread key
        return $ RepPlain $ toContent ("Canceled request!" :: T.Text)
      Nothing -> invalidArgs ["No path to kill specified!"]
  where
    -- thread waiting for the result is responsible for
    -- updating the ThreadMap.
    tryKillThread k = do
      maybeTid <- getThread k
      case maybeTid of
        Nothing  -> trace ("Killing failed: "++ T.unpack k) $ return ()
        Just tid -> trace ("Killing: " ++ T.unpack k)
                          (liftIO $ killThread tid)

-- | Get the 'next' theory path for a given path.
-- This function is used for implementing keyboard shortcuts.
getNextTheoryPathR :: TheoryIdx         -- ^ Theory index
                   -> String            -- ^ Jumping mode (smart?)
                   -> TheoryPath        -- ^ Current path
                   -> Handler RepPlain
getNextTheoryPathR idx md path = withTheory idx $ \ti -> do
    url <- getUrlRender <*> pure (TheoryPathMR idx $ next md (tiTheory ti) path)
    return . RepPlain $ toContent url
  where
    next "normal" = nextThyPath
    next "smart"  = nextSmartThyPath
    next _        = const id

-- | Get the 'prev' theory path for a given path.
-- This function is used for implementing keyboard shortcuts.
getPrevTheoryPathR :: TheoryIdx -> String -> TheoryPath -> Handler RepPlain
getPrevTheoryPathR idx md path = withTheory idx $ \ti -> do
    url <- getUrlRender <*> pure (TheoryPathMR idx $ prev md (tiTheory ti) path)
    return $ RepPlain $ toContent url
  where
    prev "normal" = prevThyPath
    prev "smart" = prevSmartThyPath
    prev _ = const id

{-
-- | Get the edit theory page.
getEditTheoryR :: TheoryIdx -> Handler RepJson
getEditTheoryR = postEditTheoryR

-- | Post edit theory page form data.
postEditTheoryR :: TheoryIdx -> Handler RepJson
postEditTheoryR idx = withTheory idx $ \ti -> formHandler
    "Edit theory"
    (theoryFormlet ti)
    theoryFormTpl $ \(Textarea input) ->
      E.handle exHandler $ do
        yesod <- getYesod
        closedThy <- checkProofs <$> parseThy yesod (T.unpack input)
        newIdx <- putTheory (Just ti) Nothing closedThy
        jsonResp . JsonRedirect =<<
          getUrlRender <*> pure (OverviewR newIdx)
  where
    -- theoryFormlet ti = fieldsToDivs $ textareaField
    theoryFormlet ti = textareaField
      (FieldSettings
        ("Edit theory source: " `T.append` name ti)
        (toHtml $ name ti) Nothing Nothing)
      (Just $ Textarea $ T.pack $ render $ prettyClosedTheory $ tiTheory ti)

    exHandler :: MonadBaseControl IO m => E.SomeException -> GHandler m RepJson
    exHandler err = jsonResp $ JsonAlert $ T.unlines
      [ "Unable to load theory due to parse error!"
      , "Parser returned the message:"
      , T.pack $ show err ]

    name = T.pack . get thyName . tiTheory
    theoryFormTpl = formTpl (EditTheoryR idx) "Load as new theory"
-}

{-
-- | Get the add lemma page.
getEditPathR :: TheoryIdx -> TheoryPath -> Handler RepJson
getEditPathR = postEditPathR

-- | Post edit theory page form data.
postEditPathR :: TheoryIdx -> TheoryPath -> Handler RepJson
postEditPathR idx (TheoryLemma lemmaName) = withTheory idx $ \ti -> do
    yesod <- getYesod
    let lemma = lookupLemma lemmaName (tiTheory ti)
    formHandler
      (T.pack $ action lemma)
      (formlet lemma)
      (lemmaFormTpl lemma) $ \(Textarea input) ->
        case parseLemma (T.unpack input) of
          Left err -> jsonResp $ JsonAlert $ T.unlines
            [ "Unable to add lemma to theory due to parse error!"
            , "Parser returned the message:"
            , T.pack $ show err ]
          Right newLemma -> (RepJson . toContent . fromValue) <$> modifyTheory ti
            -- Add or replace lemma
            (\thy -> do
              let openThy  = openTheory thy
                  openThy' = case lemma of
                    Nothing -> addLemma newLemma openThy
                    Just _  -> removeLemma lemmaName openThy
                                  >>= addLemma newLemma
              traverse (closeThy yesod) openThy')
            -- Error response
            (JsonAlert $ T.unwords
               [ "Unable to add lemma to theory."
               , "Does a lemma with the same name already exist?" ])
  where
    path (Just l) = TheoryLemma (get lName l)
    path Nothing = TheoryLemma ""

    action (Just l) = "Edit lemma " ++ get lName l
    action Nothing = "Add new lemma"

    -- formlet lemma = fieldsToDivs $ textareaField
    formlet lemma = textareaField
      (FieldSettings
        (T.pack $ action lemma)
        (toHtml $ action lemma)
        Nothing Nothing)
      (Textarea . T.pack . render . prettyLemma prettyProof <$> lemma)

    lemmaFormTpl lemma = formTpl (EditPathR idx (path lemma)) "Submit"

postEditPathR _ _ =
  jsonResp $ JsonAlert $ "Editing for this path is not implemented!"
-}

-- | Delete a given proof step.
getDeleteStepR :: TheoryIdx -> TheoryPath -> Handler RepJson
getDeleteStepR idx path = do
    jsonValue <- withTheory idx (go path)
    return $ RepJson $ toContent jsonValue
  where
    go (TheoryLemma lemma) ti = modifyTheory ti
      (return . removeLemma lemma)
      (const path)
      (JsonAlert "Sorry, but removing the selected lemma failed!")

    go (TheoryProof lemma proofPath) ti = modifyTheory ti
      (\thy -> return $
          applyProverAtPath thy lemma proofPath (sorryProver (Just "removed")))
      (const path)
      (JsonAlert "Sorry, but removing the selected proof step failed!")

    go _ _ = return . responseToJson $ JsonAlert
      "Can't delete the given theory path!"

-- | Save a theory to the working directory.
getSaveTheoryR :: TheoryIdx -> Handler RepJson
getSaveTheoryR idx = withTheory idx $ \ti -> do
    let origin = tiOrigin ti
    case origin of
      -- Saving interactive/uploaded files not supported yet.
      Interactive -> notFound
      Upload _ -> notFound
      -- Saving of local files implemented.
      Local file -> do
        -- Save theory to disk
        liftIO $ writeFile file (prettyRender ti)
        -- Find original theorie(s) with same origin
        -- Set original -> modified
        thys <- M.filter (same origin) <$> getTheories
        _ <- Tr.mapM (\t -> adjTheory (tiIndex t) (setPrimary False)) thys
        -- Find current theory
        -- Set modified -> original
        adjTheory (tiIndex ti) (setPrimary True)
        -- Return message
        jsonResp (JsonAlert $ T.pack $ "Saved theory to file: " ++ file)
  where
    prettyRender = render . prettyOpenTheory . openTheory . tiTheory
    same origin ti = tiPrimary ti && (tiOrigin ti == origin)
    setPrimary bool ti = ti { tiPrimary = bool }


-- | Prompt downloading of theory.
getDownloadTheoryR :: TheoryIdx -> String -> Handler (ContentType, Content)
getDownloadTheoryR idx _ = do
    RepPlain source <- getTheorySourceR idx
    return (typeOctet, source)

-- | Unload a theory from the interactive server.
getUnloadTheoryR :: TheoryIdx -> Handler RepPlain
getUnloadTheoryR idx = do
    delTheory idx
    redirect RootR

{-
-- | Show a list of all currently running threads.
getThreadsR :: Handler RepHtml
getThreadsR = do
    threads <- getThreads
    defaultLayout $ do
      setTitle "Registered threads"
      addWidget (threadsTpl threads)
-}
