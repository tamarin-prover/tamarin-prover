{- |
Module      :  Web.Handler
Description :  Application-specific handler functions.
Copyright   :  (c) 2011 Cedric Staub, 2012 Benedikt Schmidt
License     :  GPL-3

Stability   :  experimental
Portability :  non-portable
-}

module Web.Handler
  ( getOverviewR
  , getOverviewDiffR
  , getRootR
  , postRootR
  , getTheorySourceR
  , getTheorySourceDiffR
  , getTheoryMessageDeductionR
  , getTheoryMessageDeductionDiffR
  , getTheoryVariantsR
  , getTheoryVariantsDiffR
  , getTheoryPathMR
  , getTheoryPathDiffMR
  -- , getTheoryPathDR
  , getTheoryGraphR
  , getTheoryGraphDiffR
  , getTheoryMirrorDiffR
  , getAutoProverR
  , getAutoDiffProverR
  , getAutoProverDiffR
  , getAutoProverAllR
  , getProverDiffAllR
  , getAutoProverAllDiffR
  , getDeleteStepR
  , getDeleteStepDiffR
  , getKillThreadR
  , getNextTheoryPathR
  , getNextTheoryPathDiffR
  , getPrevTheoryPathR
  , getPrevTheoryPathDiffR
  , getSaveTheoryR
  , getDownloadTheoryR
  , getDownloadTheoryDiffR
  -- , getEditTheoryR
  -- , postEditTheoryR
  -- , getEditPathR
  -- , postEditPathR
  , getUnloadTheoryR
  , getUnloadTheoryDiffR
  -- , getThreadsR
  )
where

import Items.LemmaItem (ProtoLemma(..), DiffLemma(..))
import Theory
  ( Theory(..), DiffTheory(..), ClosedTheory, ClosedDiffTheory, Side
  , removeLemma, removeLemmaDiff, removeDiffLemma, openTheory, sorryProver
  , runAutoProver, sorryDiffProver, runAutoDiffProver
  , prettyClosedTheory, prettyOpenTheory
  , openDiffTheory, prettyClosedDiffTheory, prettyOpenDiffTheory
  , getLemmas, getDiffLemmas, getEitherLemmas, toSignatureWithMaude
  )
import Theory.Constraint.System.Dot
import Theory.Constraint.System.Graph.Graph
import Theory.Constraint.System.JSON  -- for export of constraint system to JSON
import Theory.Proof (AutoProver(..), SolutionExtractor(..), Prover, DiffProver)
import Theory.Tools.Wellformedness (prettyWfErrorReport)

import Main.Console (renderDoc)
import Main.TheoryLoader

import Control.Applicative
import Control.Concurrent
import Control.Concurrent.Thread qualified as Thread ( forkIO )
import Control.DeepSeq
import Control.Exception.Base       as E
import Control.Monad
import Control.Monad.Except (runExceptT)
import Control.Monad.Trans.Resource (runResourceT)
import Data.Binary qualified as Bin
import Data.ByteString.Char8 qualified as BS
import Data.ByteString.Builder qualified as B
import Data.Conduit as C (runConduit,(.|))
import Data.Conduit.List (consume)
import Data.List (intersperse)
import Data.Map qualified as M
import Data.Maybe
import Data.String (fromString)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T (encodeUtf8, decodeUtf8)
import Data.Text.Lazy.Encoding qualified as TLE
import Data.Time.LocalTime
import Debug.Trace
import Network.HTTP.Types (urlDecode)
import System.Directory
import System.FilePath ((</>))
import Text.PrettyPrint.Html ( render, htmlDoc, renderHtmlDoc )
import Text.Read (readMaybe)

import Web.Hamlet
import Web.Settings
import Web.Theory
import Web.Types
import Yesod.Core

------------------------------------------------------------------------------
-- Manipulate the state
------------------------------------------------------------------------------

-- | Store theory map in file if option enabled.
storeTheory
  :: WebUI
  -> EitherTheoryInfo
  -> TheoryIdx
  -> IO ()
storeTheory yesod thy idx =
  when yesod.autosaveProofstate $ do
    let f = yesod.workDir </> autosaveSubdir </> show idx <> ".img"
    Bin.encodeFile (f++".tmp") thy
    renameFile (f++".tmp") f

-- | Load a theory given an index.
getTheory :: TheoryIdx -> Handler (Maybe EitherTheoryInfo)
getTheory idx = do
  yesod <- getYesod
  liftIO $ withMVar yesod.theoryVar $ pure . M.lookup idx

-- | Store a theory, return index.
putTheory
  :: Maybe TheoryInfo     -- ^ Index of parent theory
  -> Maybe TheoryOrigin   -- ^ Origin of this theory
  -> ClosedTheory         -- ^ The new closed theory
  -> String
  -> Handler TheoryIdx
putTheory parent origin thy rep = do
  yesod <- getYesod
  liftIO $ modifyMVar yesod.theoryVar $ \theories -> do
    time <- getZonedTime
    let idx | M.null theories = 1
            | otherwise       = fst (M.findMax theories) + 1
        parentIdx    = (.index) <$> parent
        parentOrigin = (.origin) <$> parent
        newOrigin    = parentOrigin <|> origin <|> Just Interactive
        newThy       = Trace (
            TheoryInfo idx thy time parentIdx False (fromJust newOrigin)
                    (maybe yesod.defaultAutoProver (.autoProver) parent) rep)
    storeTheory yesod newThy idx
    pure (M.insert idx newThy theories, idx)

-- | Store a theory, return index.
putDiffTheory
  :: Maybe DiffTheoryInfo  -- ^ Index of parent theory
  -> Maybe TheoryOrigin    -- ^ Origin of this theory
  -> ClosedDiffTheory      -- ^ The new closed theory
  -> String
  -> Handler TheoryIdx
putDiffTheory parent origin thy rep = do
  yesod <- getYesod
  liftIO $ modifyMVar yesod.theoryVar $ \theories -> do
    time <- getZonedTime
    let idx | M.null theories = 1
            | otherwise       = fst (M.findMax theories) + 1
        parentIdx    = (.index) <$> parent
        parentOrigin = (.origin) <$> parent
        newOrigin    = parentOrigin <|> origin <|> Just Interactive
        newThy       = Diff (
            TheoryInfo idx thy time parentIdx False (fromJust newOrigin)
                    (maybe yesod.defaultAutoProver (.autoProver) parent) rep)
    storeTheory yesod newThy idx
    pure (M.insert idx newThy theories, idx)

-- | Delete theory.
delTheory :: TheoryIdx -> Handler ()
delTheory idx = do
  yesod <- getYesod
  liftIO $ modifyMVar_ yesod.theoryVar $ \theories -> do
    let theories' = M.delete idx theories
    -- FIXME: delete from autosave directory?
    pure theories'

-- | Get a map of all stored theories.
getTheories :: Handler TheoryMap
getTheories = do
  yesod <- getYesod
  liftIO $ withMVar yesod.theoryVar pure


-- -- | Modify a theory in the map of theories.
-- adjTheory :: TheoryIdx
--           -> (TheoryInfo -> TheoryInfo)
--           -> Handler ()
-- adjTheory idx f = do
--     yesod <- getYesod
--     liftIO $ modifyMVar_ (theoryVar yesod) $ \theories ->
--       case M.lookup idx theories of
--         Just th -> do
--           case th of
--             Trace thy -> do
--               let newThy =  f thy
--               storeTheory yesod (Trace newThy) idx
--               pure $ M.insert idx (Trace newThy) theories
--             Diff _ -> error "adjTheory: found DiffTheory"
--         Nothing -> error "adjTheory: invalid theory index"

-- | Modify a theory in the map of theories.
adjEitherTheory
  :: TheoryIdx
  -> (EitherTheoryInfo -> EitherTheoryInfo)
  -> Handler ()
adjEitherTheory idx f = do
  yesod <- getYesod
  liftIO $ modifyMVar_ yesod.theoryVar $ \theories ->
    case M.lookup idx theories of
      Just thy -> do
        let newThy = f thy
        storeTheory yesod newThy idx
        pure $ M.insert idx newThy theories
      Nothing -> error "adjEitherTheory: invalid theory index"

-- -- | Modify a theory in the map of theories.
-- adjDiffTheory :: TheoryIdx
--               -> (DiffTheoryInfo -> DiffTheoryInfo)
--               -> Handler ()
-- adjDiffTheory idx f = do
--     yesod <- getYesod
--     liftIO $ modifyMVar_ (theoryVar yesod) $ \theories ->
--       case M.lookup idx theories of
--         Just th -> do
--           case th of
--             Diff thy -> do
--               let newThy =  f thy
--               storeTheory yesod (Diff newThy) idx
--               pure $ M.insert idx (Diff newThy) theories
--             Trace _ -> error "adjTheory: found normal Theory"
--         Nothing -> error "adjTheory: invalid theory index"


-- | Debug tracing.
dtrace :: WebUI -> String -> a -> a
dtrace yesod msg | yesod.debug = trace msg
                 | otherwise   = id

-- | Register a thread for killing.
putThread
  :: T.Text    -- ^ Request path
  -> ThreadId  -- ^ Thread ID
  -> Handler ()
putThread str tid = do
  yesod <- getYesod
  liftIO $ dtrace yesod msg $
    modifyMVar_ yesod.threadVar $ pure . M.insert str tid
  where
    msg = "Registering thread: " ++ T.unpack str

-- | Unregister a thread for killing.
delThread
  :: T.Text  -- ^ Request path
  -> Handler ()
delThread str = do
  yesod <- getYesod
  liftIO $ dtrace yesod msg $
    modifyMVar_ yesod.threadVar $ pure . M.delete str
  where
    msg = "Deleting thread: " ++ T.unpack str


-- | Get a thread for the given request URL.
getThread
  :: T.Text  -- ^ Request path
  -> Handler (Maybe ThreadId)
getThread str = do
    yesod <- getYesod
    liftIO $ dtrace yesod msg $
      withMVar yesod.threadVar $ pure . M.lookup str
  where
    msg = "Retrieving thread id of: " ++ T.unpack str

{-
-- | Get the map of all threads.
-- getThreads :: MonadIO m
--            => GenericHandler m [T.Text]
getThreads = do
    yesod <- getYesod
    liftIO $ withMVar (threadVar yesod) (pure . M.keys)
-}

------------------------------------------------------------------------------
-- Helper functions
------------------------------------------------------------------------------

-- | Print exceptions, if they happen.
traceExceptions :: String -> IO a -> IO a
traceExceptions info =
    E.handle handler
  where
    handler :: E.SomeException -> IO a
    handler e =
      trace (info ++ ": exception `" ++ show e ++ "'") $ E.throwIO e

-- | Helper functions for generating JSON reponses.
jsonResp :: JsonResponse -> Handler RepJson
jsonResp = pure . RepJson . toContent . responseToJson

responseToJson :: JsonResponse -> Value
responseToJson = go
  where
    jsonObj key val = object [ key .= val ]

    go (JsonAlert msg)          = jsonObj "alert" $ toJSON msg
    go (JsonRedirect url)       = jsonObj "redirect" $ toJSON url
    go (JsonHtml title content) = object
      [ "html"  .= contentToJson content
      , "title" .= title ]

    contentToJson (ContentBuilder b _) = toJSON $ TLE.decodeUtf8 $ B.toLazyByteString b
    contentToJson _ = error "Unsupported content format in json response!"

-- | Fully evaluate a value in a thread that can be canceled.
evalInThread
  :: NFData a
  => IO a
  -> Handler (Either E.SomeException a)
evalInThread io = do
  renderF <- getUrlRender
  maybeRoute <- getCurrentRoute
  case maybeRoute of
    Just route -> do
      let key = renderF route
      (tid, wait) <- liftIO $ Thread.forkIO $ do x <- io
                                                 evaluate (rnf x)
                                                 pure x
      putThread key tid
      res <- liftIO wait
      delThread key
      pure res
    Nothing -> Right <$> liftIO io

-- | Evaluate a handler with a given theory specified by the index,
-- return notFound if theory does not exist.
withTheory
  :: TheoryIdx
  -> (TheoryInfo -> Handler a)
  -> Handler a
withTheory idx handler = do
  maybeThy <- getTheory idx
  case maybeThy of
    Just eitherTi -> case eitherTi of
                          Trace ti -> handler ti
                          Diff _   -> notFound
    Nothing -> notFound

-- | Evaluate a handler with a given theory specified by the index,
-- return notFound if theory does not exist.
withBothTheory
  :: TheoryIdx
  -> (TheoryInfo -> Handler a)
  -> (DiffTheoryInfo -> Handler a)
  -> Handler a
withBothTheory idx handler diffhandler = do
  maybeThy <- getTheory idx
  case maybeThy of
    Just eitherTi -> case eitherTi of
                          Trace ti  -> handler ti
                          Diff ti -> diffhandler ti
    Nothing -> notFound


-- | Evaluate a handler with a given theory specified by the index,
-- return notFound if theory does not exist.
withDiffTheory
  :: TheoryIdx
  -> (DiffTheoryInfo -> Handler a)
  -> Handler a
withDiffTheory idx handler = do
  maybeThy <- getTheory idx
  case maybeThy of
    Just eitherTi -> case eitherTi of
                          Trace _  -> notFound
                          Diff  ti -> handler ti
    Nothing -> notFound

-- | Evaluate a handler with a given theory specified by the index,
-- return notFound if theory does not exist.
withEitherTheory
  :: TheoryIdx
  -> (EitherTheoryInfo -> Handler a)
  -> Handler a
withEitherTheory idx handler = do
  maybeThy <- getTheory idx
  maybe notFound handler maybeThy

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
modifyTheory
  :: TheoryInfo                                -- ^ Theory to modify
  -> (ClosedTheory -> IO (Maybe ClosedTheory)) -- ^ Function to apply
  -> (ClosedTheory -> TheoryPath)              -- ^ Compute the new path
  -> JsonResponse                              -- ^ Response on failure
  -> Handler Value
modifyTheory ti f fpath errResponse = do
  res <- evalInThread (liftIO $ f ti.theory)
  case res of
    Left e           -> pure (excResponse e)
    Right Nothing    -> pure (responseToJson errResponse)
    Right (Just thy) -> do
      newThyIdx <- putTheory (Just ti) Nothing thy ti.errorsHtml
      newUrl <- getUrlRender <*> pure (OverviewR newThyIdx (fpath thy))
      pure . responseToJson $ JsonRedirect newUrl
  where
   excResponse e = responseToJson
                     (JsonAlert $ "Last request failed with exception: " <> T.pack (show e))

-- | Modify a theory, redirect if successful.
modifyDiffTheory
  :: DiffTheoryInfo                                    -- ^ Theory to modify
  -> (ClosedDiffTheory -> IO (Maybe ClosedDiffTheory)) -- ^ Function to apply
  -> (ClosedDiffTheory -> DiffTheoryPath)              -- ^ Compute the new path
  -> JsonResponse                                      -- ^ Response on failure
  -> Handler Value
modifyDiffTheory ti f fpath errResponse = do
  res <- evalInThread (liftIO $ f ti.theory)
  case res of
    Left e           -> pure (excResponse e)
    Right Nothing    -> pure (responseToJson errResponse)
    Right (Just thy) -> do
      newThyIdx <- putDiffTheory (Just ti) Nothing thy ti.errorsHtml
      newUrl <- getUrlRender <*> pure (OverviewDiffR newThyIdx (fpath thy))
      pure . responseToJson $ JsonRedirect newUrl
  where
   excResponse e = responseToJson
                     (JsonAlert $ "Last request failed with exception: " <> T.pack (show e))

 ------------------------------------------------------------------------------
-- Handler functions
------------------------------------------------------------------------------

-- | The root handler lists all theories by default,
-- or load a new theory if the corresponding form was submitted.
getRootR :: Handler Html
getRootR = do
    theories <- getTheories
    defaultLayout $ do
      setTitle "Welcome to the Tamarin prover"
      rootTpl theories

newtype File = File T.Text
  deriving Show

postRootR :: Handler Html
postRootR = do
  result <- lookupFile "uploadedTheory"
  case result of
    Nothing ->
      setMessage "Post request failed."
    Just fileinfo -> do
      -- content <- liftIO $ LBS.fromChunks <$> (fileSource fileinfo $$ consume)
      -- content <- liftIO $ runResourceT (fileSource fileinfo C.$$ consume)
      content <- liftIO $ runResourceT $ C.runConduit (fileSource fileinfo C..| consume)
      if null content
        then setMessage "No theory file given."
      else do
        yesod <- getYesod
        thyWithRep <- liftIO $ runExceptT $ do
          openThy <- yesod.loadThy
                       (T.unpack $ T.decodeUtf8 $ BS.concat content)
                       (T.unpack $ fileName fileinfo)

          let sig = either (._thySignature) (._diffThySignature) openThy
          sig'   <- liftIO $ toSignatureWithMaude yesod.thyOpts.maudePath sig

          -- let tactic = get thyTactic openThy
          --tactic'   <- liftIO $ toSignatureWithMaude (get oMaudePath (thyOpts yesod)) tactic

          yesod.closeThy sig' openThy

        case thyWithRep of
          Left err -> setMessage $ "Theory loading failed:\n" <> toHtml (show err)
          Right (report, thy) -> do
            wfErrors <- case report of
              [] -> pure ""
              _ -> pure $ "<div class=\"wf-warning\">\nWARNING: the following wellformedness checks failed!<br /><br />\n" ++ (renderHtmlDoc . htmlDoc $ prettyWfErrorReport report) ++ "\n</div>"
            void $ either (putTheory Nothing (Just $ Upload $ T.unpack $ fileName fileinfo))
                          (putDiffTheory Nothing (Just $ Upload $ T.unpack $ fileName fileinfo)) thy wfErrors
            setMessage $ toHtml $ "Loaded new theory!" ++
                                  " WARNING: ignoring the following wellformedness errors: " ++
                                  renderDoc (prettyWfErrorReport report)

  theories <- getTheories
  defaultLayout $ do
    setTitle "Welcome to the Tamarin prover"
    rootTpl theories


-- | Show overview over theory (framed layout).
getOverviewR :: TheoryIdx -> TheoryPath -> Handler Html
getOverviewR idx path = withTheory idx $ \ti -> do
  renderF <- getUrlRender
  renderParamsF <- getUrlRenderParams
  defaultLayout $ do
    getParams <- reqGetParams <$> getRequest
    let renderParamsF' route = renderParamsF route getParams
    overview <- liftIO $ overviewTpl renderF renderParamsF' ti path
    setTitle (toHtml $ "Theory: " ++ ti.theory._thyName)
    overview

-- | Show overview over diff theory (framed layout).
getOverviewDiffR :: TheoryIdx -> DiffTheoryPath -> Handler Html
getOverviewDiffR idx path = withDiffTheory idx $ \ti -> do
  renderF <- getUrlRender
  defaultLayout $ do
    overview <- liftIO $ overviewDiffTpl renderF ti path
    setTitle (toHtml $ "DiffTheory: " ++ ti.theory._diffThyName)
    overview

-- | Show source (pretty-printed open theory).
getTheorySourceR :: TheoryIdx -> Handler RepPlain
getTheorySourceR idx = withBothTheory idx
  (pure . RepPlain . toContent . prettyRender)
  (pure . RepPlain . toContent . prettyRenderDiff)
  where
    prettyRender = render . prettyClosedTheory . (.theory)
    prettyRenderDiff = render . prettyClosedDiffTheory . (.theory)

-- | Show source (pretty-printed open diff theory).
getTheorySourceDiffR :: TheoryIdx -> Handler RepPlain
getTheorySourceDiffR idx = withBothTheory idx
  (pure . RepPlain . toContent . prettyRender)
  (pure . RepPlain . toContent . prettyRenderDiff)
  where
    prettyRender = render . prettyClosedTheory . (.theory)
    prettyRenderDiff = render . prettyClosedDiffTheory . (.theory)

-- | Show variants (pretty-printed closed theory).
getTheoryVariantsR :: TheoryIdx -> Handler RepPlain
getTheoryVariantsR idx = withBothTheory idx
  (pure . RepPlain . toContent . prettyRender)
  (pure . RepPlain . toContent . prettyRenderDiff)
  where prettyRender = render . prettyClosedTheory . (.theory)
        prettyRenderDiff = render . prettyClosedDiffTheory . (.theory)

-- | Show variants (pretty-printed closed diff theory).
getTheoryVariantsDiffR :: TheoryIdx -> Handler RepPlain
getTheoryVariantsDiffR idx = withBothTheory idx
  (pure . RepPlain . toContent . prettyRender)
  (pure . RepPlain . toContent . prettyRenderDiff)
  where prettyRender = render . prettyClosedTheory . (.theory)
        prettyRenderDiff = render . prettyClosedDiffTheory . (.theory)

-- | Show variants (pretty-printed closed theory).
getTheoryMessageDeductionR :: TheoryIdx -> Handler RepPlain
getTheoryMessageDeductionR idx = withBothTheory idx
  (pure . RepPlain . toContent . prettyRender)
  (pure . RepPlain . toContent . prettyRenderDiff)
  where prettyRender = render . prettyClosedTheory . (.theory)
        prettyRenderDiff = render . prettyClosedDiffTheory . (.theory)

-- | Show variants (pretty-printed closed theory).
getTheoryMessageDeductionDiffR :: TheoryIdx -> Handler RepPlain
getTheoryMessageDeductionDiffR idx = withBothTheory idx
  (pure . RepPlain . toContent . prettyRender )
  (pure . RepPlain . toContent . prettyRenderDiff)
  where prettyRender = render . prettyClosedTheory . (.theory)
        prettyRenderDiff = render . prettyClosedDiffTheory . (.theory)


-- | Show a given path within a theory (main view).
getTheoryPathMR
  :: TheoryIdx
  -> TheoryPath
  -> Handler RepJson
getTheoryPathMR idx path = do
  renderUrl <- getUrlRender
  jsonValue <- withTheory idx (go renderUrl path)
  pure $ RepJson $ toContent jsonValue
  where
    --
    -- Handle method paths by trying to solve the given goal/method
    --
    go _ (TheoryMethod lemma proofPath i) ti = modifyTheory ti
        (\thy -> pure $ applyMethodAtPath thy lemma proofPath ti.autoProver i)
        (\thy -> nextSmartThyPath thy (TheoryProof lemma proofPath))
        (JsonAlert "Sorry, but the prover failed on the selected method!")

    --
    -- Handle generic paths by trying to render them
    --
    go renderUrl _ ti = do
      let title = T.pack $ titleThyPath ti.theory path
      let html = htmlThyPath renderUrl renderUrl ti path
      pure $ responseToJson (JsonHtml title $ toContent html)

-- | Show a given path within a diff theory (main view).
getTheoryPathDiffMR
  :: TheoryIdx
  -> DiffTheoryPath
  -> Handler RepJson
getTheoryPathDiffMR idx path = do
  renderUrl <- getUrlRender
  jsonValue <- withDiffTheory idx (goDiff renderUrl path)
  pure $ RepJson $ toContent jsonValue
  where
    --
    -- Handle method paths by trying to solve the given goal/method
    --
    goDiff _ (DiffTheoryMethod s lemma proofPath i) ti = modifyDiffTheory ti
        (\thy -> pure $ applyMethodAtPathDiff thy s lemma proofPath ti.autoProver i)
        (\thy -> nextSmartDiffThyPath thy (DiffTheoryProof s lemma proofPath))
        (JsonAlert "Sorry, but the prover failed on the selected method!")
    goDiff _ (DiffTheoryDiffMethod lemma proofPath i) ti = modifyDiffTheory ti
        (\thy -> pure $ applyDiffMethodAtPath thy lemma proofPath ti.autoProver i)
        (\thy -> nextSmartDiffThyPath thy (DiffTheoryDiffProof lemma proofPath))
        (JsonAlert "Sorry, but the prover failed on the selected method!")

    --
    -- Handle generic paths by trying to render them
    --
    goDiff renderUrl _ ti = do
      let title = T.pack $ titleDiffThyPath ti.theory path
      let html = htmlDiffThyPath renderUrl ti path
      pure $ responseToJson (JsonHtml title $ toContent html)


-- | Run the some prover on a given proof path.
getProverR
  :: (T.Text, AutoProver -> Prover)
  -> TheoryIdx
  -> TheoryPath
  -> Handler RepJson
getProverR (name, mkProver) idx path = do
  jsonValue <- withTheory idx (go path)
  pure $ RepJson $ toContent jsonValue
  where
    go (TheoryProof lemma proofPath) ti = modifyTheory ti
      (\thy -> pure $ applyProverAtPath thy lemma proofPath autoProver)
      (`nextSmartThyPath` path)
      (JsonAlert $ "Sorry, but " <> name <> " failed!")
      where
        autoProver = mkProver ti.autoProver

    go _ _ = pure $ responseToJson $ JsonAlert $
      "Can't run " <> name <> " on the given theory path!"

-- | Run the some prover on a given proof path.
getProverAllR
  :: (T.Text, AutoProver -> Prover)
  -> TheoryIdx -> Handler RepJson
getProverAllR (name, mkProver) idx = do
  jsonValue <- withTheory idx go
  pure $ RepJson $ toContent jsonValue
  where
    go ti = modifyTheory ti
        proveAll
        (\thy -> nextSmartThyPath thy (TheoryProof (last $ names thy) []))
        (JsonAlert $ "Sorry, but " <> name <> " failed!")
      where
        names thy = (._lName) <$> getLemmas thy
        autoProver = mkProver ti.autoProver
        proveAll thy = pure $ foldM (\tha lemma -> applyProverAtPath tha lemma [] autoProver) thy $ names thy

-- | Run the some prover on a given proof path.
getProverDiffR
  :: (T.Text, AutoProver -> Prover)
  -> TheoryIdx
  -> Side
  -> DiffTheoryPath
  -> Handler RepJson
getProverDiffR (name, mkProver) idx s path = do
  jsonValue <- withDiffTheory idx (goDiff s path)
  pure $ RepJson $ toContent jsonValue
  where
    goDiff s'' (DiffTheoryProof s' lemma proofPath) ti =
      if s'' == s' then
        modifyDiffTheory ti
          (\thy -> pure $ applyProverAtPathDiff thy s' lemma proofPath autoProver)
          (`nextSmartDiffThyPath` path)
          (JsonAlert $ "Sorry, but " <> name <> " failed!")
      else
        pure $ responseToJson $ JsonAlert $
                 "Can't run " <> name <> " on the given theory path!"
      where
        autoProver = mkProver ti.autoProver

    goDiff _ _ _ = pure $ responseToJson $ JsonAlert $
      "Can't run " <> name <> " on the given theory path!"

-- | Run the some prover on a given proof path.
getDiffProverR
  :: (T.Text, AutoProver -> DiffProver)
  -> TheoryIdx
  -> DiffTheoryPath
  -> Handler RepJson
getDiffProverR (name, mkProver) idx path = do
  jsonValue <- withDiffTheory idx (goDiff path)
  pure $ RepJson $ toContent jsonValue
  where
    goDiff (DiffTheoryDiffProof lemma proofPath) ti =
      modifyDiffTheory ti
        (\thy -> pure $ applyDiffProverAtPath thy lemma proofPath autoProver)
        (`nextSmartDiffThyPath` path)
        (JsonAlert $ "Sorry, but " <> name <> " failed!")
      where
        autoProver = mkProver ti.autoProver

    goDiff _ _ = pure $ responseToJson $ JsonAlert $
      "Can't run " <> name <> " on the given theory path!"

-- | Run the some prover on a given proof path.
getProverDiffAllR
  :: (T.Text, AutoProver -> Prover, AutoProver -> DiffProver)
  -> TheoryIdx
  -> Handler RepJson
getProverDiffAllR (name, mkProver, mkDiffProver) idx  = do
  jsonValue <- withDiffTheory idx goDiff
  pure $ RepJson $ toContent jsonValue
  where
    goDiff ti = modifyDiffTheory ti
        proveAllDiff
        (\thy -> nextSmartDiffThyPath thy (DiffTheoryDiffProof (last $ namesDiff thy) []))
        (JsonAlert $ "Sorry, but " <> name <> " failed!")
      where
        namesDiff thy = (._lDiffName) <$> getDiffLemmas thy
        autoDiffProver = mkDiffProver ti.autoProver
        names thy = map (\(x, y) -> (x, y._lName)) $ getEitherLemmas thy
        autoProver = mkProver ti.autoProver
        proveDiff thy = foldM (\tha lemma -> applyDiffProverAtPath tha lemma [] autoDiffProver) thy $ namesDiff thy
        proveAllDiff thy = pure $ do
          thb <- proveDiff thy
          foldM (\tha (s, lemma) -> applyProverAtPathDiff tha s lemma [] autoProver) thb $ names thb

-- | Run an autoprover on a given proof path.
getAutoProverR
  :: TheoryIdx
  -> SolutionExtractor
  -> Int   -- autoprover bound to use
  -> Bool  -- Quit on empty oracle
  -> TheoryPath
  -> Handler RepJson
getAutoProverR idx extractor bound quitOnEmpty =
  getProverR (fullName, runAutoProver . adapt) idx
  where
    adapt autoProver = autoProver
      { apBound = actualBound
      , apCut = if quitOnEmpty then CutAfterSorry else extractor
      , quitOnEmptyOracle = quitOnEmpty }

    withCommas = intersperse ", "
    fullName   = mconcat $ proverName : " (" : withCommas qualifiers ++ [")"]
    qualifiers = extractorQualfier ++ boundQualifier

    (actualBound, boundQualifier)
        | bound > 0 = (Just bound, ["bound " <> T.pack (show bound)])
        | otherwise = (Nothing,    []                               )

    (proverName, extractorQualfier) = case extractor of
        CutNothing         -> ("characterization", ["dfs"]   )
        CutDFS             -> ("the autoprover",   []        )
        CutBFS             -> ("the autoprover",   ["bfs"]   )
        CutSingleThreadDFS -> ("the autoprover",   ["seqdfs"])

-- | Run an autoprover on a given proof path.
getAutoProverAllR
  :: TheoryIdx
  -> SolutionExtractor
  -> Int  -- autoprover bound to use
  -> TheoryPath
  -> Handler RepJson
getAutoProverAllR idx extractor bound _ =
  getProverAllR (fullName, runAutoProver . adapt) idx
  where
    adapt autoProver = autoProver { apBound = actualBound, apCut = extractor }

    withCommas = intersperse ", "
    fullName   = mconcat $ proverName : " (" : withCommas qualifiers ++ [")"]
    qualifiers = extractorQualfier ++ boundQualifier

    (actualBound, boundQualifier)
        | bound > 0 = (Just bound, ["bound " <> T.pack (show bound)])
        | otherwise = (Nothing,    []                               )

    (proverName, extractorQualfier) = case extractor of
        CutNothing         -> ("characterization", ["dfs"]   )
        CutDFS             -> ("the autoprover",   []        )
        CutBFS             -> ("the autoprover",   ["bfs"]   )
        CutSingleThreadDFS -> ("the autoprover",   ["seqdfs"])


-- | Run an autoprover on a given proof path.
getAutoProverDiffR
  :: TheoryIdx
  -> SolutionExtractor
  -> Int  -- autoprover bound to use
  -> Side
  -> DiffTheoryPath
  -> Handler RepJson
getAutoProverDiffR idx extractor bound =
  getProverDiffR (fullName, runAutoProver . adapt) idx
  where
    adapt autoProver = autoProver { apBound = actualBound, apCut = extractor }

    withCommas = intersperse ", "
    fullName   = mconcat $ proverName : " (" : withCommas qualifiers ++ [")"]
    qualifiers = extractorQualfier ++ boundQualifier

    (actualBound, boundQualifier)
        | bound > 0 = (Just bound, ["bound " <> T.pack (show bound)])
        | otherwise = (Nothing,    []                               )

    (proverName, extractorQualfier) = case extractor of
        CutNothing         -> ("characterization", ["dfs"]   )
        CutDFS             -> ("the autoprover",   []        )
        CutBFS             -> ("the autoprover",   ["bfs"]   )
        CutSingleThreadDFS -> ("the autoprover",   ["seqdfs"])


-- | Run an autoprover on a given proof path.
getAutoProverAllDiffR
  :: TheoryIdx
  -> SolutionExtractor
  -> Int -- autoprover bound to use
  -> Handler RepJson
getAutoProverAllDiffR idx extractor bound =
  getProverDiffAllR (fullName, runAutoProver . adapt, runAutoDiffProver . adapt) idx
  where
    adapt autoProver = autoProver { apBound = actualBound, apCut = extractor }

    withCommas = intersperse ", "
    fullName   = mconcat $ proverName : " (" : withCommas qualifiers ++ [")"]
    qualifiers = extractorQualfier ++ boundQualifier

    (actualBound, boundQualifier)
        | bound > 0 = (Just bound, ["bound " <> T.pack (show bound)])
        | otherwise = (Nothing,    []                               )

    (proverName, extractorQualfier) = case extractor of
        CutNothing         -> ("characterization", ["dfs"]   )
        CutDFS             -> ("the autoprover",   []        )
        CutBFS             -> ("the autoprover",   ["bfs"]   )
        CutSingleThreadDFS -> ("the autoprover",   ["seqdfs"])


-- | Run an autoprover on a given proof path.
getAutoDiffProverR
  :: TheoryIdx
  -> SolutionExtractor
  -> Int  -- autoprover bound to use
  -> DiffTheoryPath
  -> Handler RepJson
getAutoDiffProverR idx extractor bound =
    getDiffProverR (fullName, runAutoDiffProver . adapt) idx
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
        CutSingleThreadDFS -> ("the autoprover",   []     )
        CutBFS     -> ("the autoprover",   ["bfs"])


{-
-- | Show a given path within a theory (debug view).
getTheoryPathDR :: TheoryIdx -> TheoryPath -> Handler Html
getTheoryPathDR idx path = withTheory idx $ \ti -> ajaxLayout $ do
  -- let maybeDebug = htmlThyDbgPath (tiTheory ti) path
  -- let maybeWidget = wrapHtmlDoc <$> maybeDebug
  pure [hamlet|
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

-- | Read the render options from a request to render a sequent.
getOptions :: Handler (GraphOptions, DotOptions)
getOptions = do
  compact <- isNothing <$> lookupGetParam "uncompact"
  let nodeStyle = if compact then CompactBoringNodes else FullBoringNodes
  compress <- isNothing <$> lookupGetParam "uncompress"
  abbreviate <- isNothing <$> lookupGetParam "unabbreviate"
  simpl <- lookupGetParam "simplification"
  showAutosource <- isNothing <$> lookupGetParam "no-auto-sources"
  clustering <- lookupGetParam "clustering"
  let simplificationLevel = fromMaybe SL2 (simpl >>= readMaybe . T.unpack)
      graphOptions = defaultGraphOptions
        { _goSimplificationLevel = simplificationLevel
        , _goCompress = compress
        , _goShowAutoSource = showAutosource
        , _goAbbreviate = abbreviate
        , _goClustering = isJust clustering
        }
  let dotOptions = defaultDotOptions { _doNodeStyle = nodeStyle }
  pure (graphOptions, dotOptions)


-- | Get rendered graph for theory and given path.
getTheoryGraphR :: TheoryIdx -> TheoryPath -> Handler ()
getTheoryGraphR idx path = withTheory idx $ \ti -> do
  yesod <- getYesod
  (graphOptions, dotOptions) <- getOptions
  img' <- liftIO $ traceExceptions "getTheoryGraphR" $
    imgThyPath
      yesod.imageFormat
      yesod.outputCmd
      yesod.cacheDir
      (dotSystemCompact graphOptions dotOptions)
      (\label system -> sequentsToJSONPretty graphOptions [(label, system)])
      ti.theory path
  case img' of
    Nothing -> notFound
    Just img -> sendFile (fromString . imageFormatMIME $ yesod.imageFormat) img

-- | Get rendered graph for theory and given path.
getTheoryGraphDiffR :: TheoryIdx -> DiffTheoryPath -> Handler ()
getTheoryGraphDiffR idx path = getTheoryGraphDiffR' idx path False

-- | Get rendered graph for theory and given path.
getTheoryGraphDiffR' :: TheoryIdx -> DiffTheoryPath -> Bool -> Handler ()
getTheoryGraphDiffR' idx path mirror = withDiffTheory idx $ \ti -> do
  yesod <- getYesod
  (graphOptions, dotOptions) <- getOptions
  img' <- liftIO $ traceExceptions "getTheoryGraphDiffR" $
    imgDiffThyPath
      yesod.imageFormat
      -- a.d. TODO should diff theories support JSON output?
      yesod.outputCmd.ocGraphCommand
      yesod.cacheDir
      (dotSystemCompact graphOptions dotOptions)
      ti.theory path
      mirror
  case img' of
    Nothing -> notFound
    Just img -> sendFile (fromString . imageFormatMIME $ yesod.imageFormat) img

-- | Get rendered mirror graph for theory and given path.
getTheoryMirrorDiffR :: TheoryIdx -> DiffTheoryPath -> Handler ()
getTheoryMirrorDiffR idx path =  getTheoryGraphDiffR' idx path True

-- | Kill a thread (aka 'cancel request').
getKillThreadR :: Handler RepPlain
getKillThreadR = do
  maybeKey <- lookupGetParam "path"
  case maybeKey of
    Just key0 -> do
      let key = T.decodeUtf8 . urlDecode True . T.encodeUtf8 $ key0
      tryKillThread key
      pure $ RepPlain $ toContent ("Canceled request!" :: T.Text)
    Nothing -> invalidArgs ["No path to kill specified!"]
  where
    -- thread waiting for the result is responsible for
    -- updating the ThreadMap.
    tryKillThread k = do
      maybeTid <- getThread k
      case maybeTid of
        Nothing  -> trace ("Killing failed: "++ T.unpack k) $ pure ()
        Just tid -> trace ("Killing: " ++ T.unpack k)
                          (liftIO $ killThread tid)

-- | Get the 'next' theory path for a given path.
-- This function is used for implementing keyboard shortcuts.
getNextTheoryPathR
  :: TheoryIdx   -- ^ Theory index
  -> String      -- ^ Jumping mode (smart?)
  -> TheoryPath  -- ^ Current path
  -> Handler RepPlain
getNextTheoryPathR idx md path = withTheory idx $ \ti -> do
  url <- getUrlRender <*> pure (TheoryPathMR idx $ next md ti.theory path)
  pure . RepPlain $ toContent url
  where
    next "normal" = nextThyPath
    next "smart"  = nextSmartThyPath
    next _        = const id

-- | Get the 'next' theory path for a given path.
-- This function is used for implementing keyboard shortcuts.
getNextTheoryPathDiffR
  :: TheoryIdx       -- ^ Theory index
  -> String          -- ^ Jumping mode (smart?)
  -> DiffTheoryPath  -- ^ Current path
  -> Handler RepPlain
getNextTheoryPathDiffR idx md path = withDiffTheory idx $ \ti -> do
  url <- getUrlRender <*> pure (TheoryPathDiffMR idx $ nextDiff md ti.theory path)
  pure . RepPlain $ toContent url
  where
    nextDiff "normal" = nextDiffThyPath
    nextDiff "smart"  = nextSmartDiffThyPath
    nextDiff _        = const id

-- | Get the 'prev' theory path for a given path.
-- This function is used for implementing keyboard shortcuts.
getPrevTheoryPathR :: TheoryIdx -> String -> TheoryPath -> Handler RepPlain
getPrevTheoryPathR idx md path = withTheory idx $ \ti -> do
  url <- getUrlRender <*> pure (TheoryPathMR idx $ prev md ti.theory path)
  pure $ RepPlain $ toContent url
  where
    prev "normal" = prevThyPath
    prev "smart" = prevSmartThyPath
    prev _ = const id

-- | Get the 'prev' theory path for a given path.
-- This function is used for implementing keyboard shortcuts.
getPrevTheoryPathDiffR :: TheoryIdx -> String -> DiffTheoryPath -> Handler RepPlain
getPrevTheoryPathDiffR idx md path = withDiffTheory idx $ \ti -> do
  url <- getUrlRender <*> pure (TheoryPathDiffMR idx $ prevDiff md ti.theory path)
  pure $ RepPlain $ toContent url
  where
    prevDiff "normal" = prevDiffThyPath
    prevDiff "smart" = prevSmartDiffThyPath
    prevDiff _ = const id

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
SM: Path editing hs bitrotted. Re-enable/implement once we really need it.

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
              -- SM: Theory closing has to be implemented again.
              -- Probably, the whole path editing has to be rethought.
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
  pure $ RepJson $ toContent jsonValue
  where
    go (TheoryLemma lemma) ti = modifyTheory ti
      (pure . removeLemma lemma)
      (const path)
      (JsonAlert "Sorry, but removing the selected lemma failed!")

    go (TheoryProof lemma proofPath) ti = modifyTheory ti
      (\thy -> pure $
          applyProverAtPath thy lemma proofPath (sorryProver (Just "removed")))
      (const path)
      (JsonAlert "Sorry, but removing the selected proof step failed!")

    go _ _ = pure . responseToJson $ JsonAlert
      "Can't delete the given theory path!"

-- | Delete a given proof step.
getDeleteStepDiffR :: TheoryIdx -> DiffTheoryPath -> Handler RepJson
getDeleteStepDiffR idx path = do
  jsonValue <- withDiffTheory idx (goDiff path)
  pure $ RepJson $ toContent jsonValue
  where
    goDiff (DiffTheoryLemma s lemma) ti = modifyDiffTheory ti
      (pure . removeLemmaDiff s lemma)
      (const path)
      (JsonAlert "Sorry, but removing the selected lemma failed!")

    goDiff (DiffTheoryProof s lemma proofPath) ti = modifyDiffTheory ti
      (\thy -> pure $
          applyProverAtPathDiff thy s lemma proofPath (sorryProver (Just "removed")))
      (const path)
      (JsonAlert "Sorry, but removing the selected proof step failed!")

    goDiff (DiffTheoryDiffLemma lemma) ti = modifyDiffTheory ti
      (pure . removeDiffLemma lemma)
      (const path)
      (JsonAlert "Sorry, but removing the selected lemma failed!")

    goDiff (DiffTheoryDiffProof lemma proofPath) ti = modifyDiffTheory ti
      (\thy -> pure $
          applyDiffProverAtPath thy lemma proofPath (sorryDiffProver (Just "removed")))
      (const path)
      (JsonAlert "Sorry, but removing the selected proof step failed!")

    goDiff _ _ = pure . responseToJson $ JsonAlert
      "Can't delete the given theory path!"

-- | Save a theory to the working directory.
getSaveTheoryR :: TheoryIdx -> Handler RepJson
getSaveTheoryR idx = withEitherTheory idx $ \case
  Trace ti -> handler ti (prettyOpenTheory . openTheory)
  Diff ti  -> handler ti (prettyOpenDiffTheory . openDiffTheory)
  where
    handler ti prettyOpenTheoryF =
      case ti.origin of
       -- Saving interactive/uploaded files not supported yet.
       Interactive -> notFound
       Upload _ -> notFound
       -- Saving of local files implemented.
       Local file -> do
         -- Save theory to disk
         liftIO $ writeFile file (render $ prettyOpenTheoryF ti.theory)
         -- Find original theorie(s) with same origin
         -- Set original -> modified
         thys <- M.filter (same ti.origin) <$> getTheories
         mapM_ (\t -> adjEitherTheory (getEitherTheoryIndex t) (setPrimary False)) thys
         -- Find current theory
         -- Set modified -> original
         adjEitherTheory ti.index (setPrimary True)
         -- Return message
         jsonResp (JsonAlert $ T.pack $ "Saved theory to file: " ++ file)

    same origin (Trace ti) = ti.primary && (ti.origin == origin)
    same origin (Diff ti)  = ti.primary && (ti.origin == origin)
    setPrimary :: Bool -> EitherTheoryInfo -> EitherTheoryInfo
    setPrimary primary (Trace ti) = Trace (ti { primary })
    setPrimary primary (Diff ti)  = Diff  (ti { primary })

-- | Prompt downloading of theory.
getDownloadTheoryR :: TheoryIdx -> String -> Handler (ContentType, Content)
getDownloadTheoryR idx _ = do
  RepPlain source <- getTheorySourceR idx
  pure (typeOctet, source)

-- | Prompt downloading of theory.
getDownloadTheoryDiffR :: TheoryIdx -> String -> Handler (ContentType, Content)
getDownloadTheoryDiffR = getDownloadTheoryR

-- | Unload a theory from the interactive server.
getUnloadTheoryR :: TheoryIdx -> Handler RepPlain
getUnloadTheoryR idx = do
  delTheory idx
  redirect RootR

-- | Unload a theory from the interactive server.
getUnloadTheoryDiffR :: TheoryIdx -> Handler RepPlain
getUnloadTheoryDiffR = getUnloadTheoryR

{-
-- | Show a list of all currently running threads.
getThreadsR :: Handler Html
getThreadsR = do
    threads <- getThreads
    defaultLayout $ do
      setTitle "Registered threads"
      addWidget (threadsTpl threads)
-}
