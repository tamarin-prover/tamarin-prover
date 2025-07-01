{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE ViewPatterns      #-}
{-# LANGUAGE DeriveAnyClass    #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

{- |
Module      :  Types.hs
Description :  Central data type and Yesod typeclass instances.
Copyright   :  (c) 2011 Cedric Staub
License     :  GPL-3

Stability   :  experimental
Portability :  non-portable
-}


module Web.Types
  ( WebUI(..)
  , Route (..)
  , resourcesWebUI
  , GenericTheoryInfo(..)
  , TheoryInfo
  , DiffTheoryInfo
  , EitherTheoryInfo(..)
  , isTheoryInfo
  , isDiffTheoryInfo
  , getEitherTheoryName
  , getEitherTheoryTime
  , getEitherTheoryPrimary
  , getEitherTheoryOrigin
  , getEitherTheoryIndex
  , getStatic
  , TheoryPath(..)
  , DiffTheoryPath(..)
  , TheoryOrigin(..)
  , JsonResponse(..)
  , TheoryIdx
  , TheoryMap
  , ThreadMap
  -- , GenericHandler
  , Handler
  -- , URL rendering function
  , RenderUrl
  -- , GenericWidget
  , Widget
  -- Image rendering
  , ImageFormat(..)
  , imageFormatMIME
  , OutputFormat(..)
  , OutputCommand(..)
  )
where

import Control.Concurrent
import Control.DeepSeq
import Control.Monad.Except (ExceptT)
import Data.Binary qualified as Bin
import Data.Binary.Orphans()
import Data.Binary.Instances()
import Data.Map qualified as M
import Data.Maybe (listToMaybe)
import Data.Ord (comparing)
import Data.Text qualified as T
import Data.Time.LocalTime

import GHC.Generics (Generic)

import Text.Hamlet
import Yesod.Core
import Yesod.Static

import Theory
import Theory.Tools.Wellformedness (WfErrorReport)
import Main.TheoryLoader


------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

-- | Type synonym for a generic handler inside our site.
-- type GenericHandler m = Handler WebUI WebUI m
-- type Handler a = Handler WebUI WebUI a

-- | Type synonym for a generic widget inside our site.
-- type GenericWidget m = Widget WebUI (GenericHandler m)
-- type Widget a = Widget WebUI WebUI a

-- | Type synonym representing a numeric index for a theory.
type TheoryIdx = Int

-- | Type synonym representing a map of theories.
type TheoryMap = M.Map TheoryIdx EitherTheoryInfo

-- | Type synonym representing a map of threads.
type ThreadMap = M.Map T.Text ThreadId

-- | The image format used for rendering graphs.
data ImageFormat = PNG | SVG

-- | The output format for serializing a graph.
data OutputFormat = OutJSON | OutDot

-- | Describes how a constraint system should be converted to an image.
data OutputCommand = OutputCommand
  { ocFormat       :: OutputFormat
  , ocGraphCommand :: FilePath
  }

instance Show ImageFormat where
  show PNG = "png"
  show SVG = "svg"

instance Show OutputFormat where
    show OutJSON = "json"
    show OutDot  = "dot"

-- | convert image format to MIME type.
imageFormatMIME :: ImageFormat -> String
imageFormatMIME PNG = "image/png"
imageFormatMIME SVG = "image/svg+xml"

-- | The so-called site argument for our application, which can hold various
-- information that can use to keep info that needs to be available to the
-- handler functions.
data WebUI = WebUI
  { getStatic          :: Static
    -- ^ Settings for static file serving.
  , cacheDir           :: FilePath
    -- ^ The caching directory (for storing rendered graphs).
  , workDir            :: FilePath
    -- ^ The working directory (for storing/loading theories).
  , thyOpts            :: TheoryLoadOptions
    -- ^ Options for loading theories
  , loadThy            :: String -> FilePath -> ExceptT TheoryLoadError IO (Either OpenTheory OpenDiffTheory)
    -- ^ Load a theory according to command-line arguments.
  , closeThy           :: SignatureWithMaude -> Either OpenTheory OpenDiffTheory -> ExceptT TheoryLoadError IO (WfErrorReport, Either ClosedTheory ClosedDiffTheory)
    -- ^ Close an open theory according to command-line arguments.
  , theoryVar          :: MVar TheoryMap
    -- ^ MVar that holds the theory map
  , threadVar          :: MVar ThreadMap
    -- ^ MVar that holds the thread map
  , autosaveProofstate :: Bool
    -- ^ Automatically store theory map
  , outputCmd           :: OutputCommand
    -- ^ The dot or json command with additional flag to indicate choice dot, json, ...
  , imageFormat        :: ImageFormat
    -- ^ The image-format used for rendering graphs
  , defaultAutoProver  :: AutoProver
    -- ^ The default prover to use for automatic proving.
  , debug              :: Bool
    -- ^ Output debug messages
  }


-- | Simple data type for generating JSON responses.
data JsonResponse
  = JsonHtml T.Text Content   -- ^ Title and HTML content
  | JsonAlert T.Text          -- ^ Alert/dialog box with message
  | JsonRedirect T.Text       -- ^ Redirect to given URL

-- | Data type representing origin of theory.
-- Command line with file path, upload with filename (not path),
-- or created by interactive mode (e.g. through editing).
data TheoryOrigin = Local FilePath | Upload String | Interactive
  deriving (Show, Eq, Ord, Generic, Bin.Binary, NFData)

-- | Data type containg both the theory and it's index, making it easier to
-- pass the two around (since they are always tied to each other). We also
-- keep some extra bookkeeping information.
data GenericTheoryInfo theory = TheoryInfo
  { index      :: TheoryIdx       -- ^ Index of theory.
  , theory     :: theory          -- ^ The closed theory.
  , time       :: ZonedTime       -- ^ Time theory was loaded.
  , parent     :: Maybe TheoryIdx -- ^ Prev theory in history
  , primary    :: Bool            -- ^ This is the orginally loaded theory.
  , origin     :: TheoryOrigin    -- ^ Origin of theory.
  , autoProver :: AutoProver      -- ^ The automatic prover to use.
  , errorsHtml :: String
  } deriving (Generic, Bin.Binary)

type TheoryInfo = GenericTheoryInfo ClosedTheory
type DiffTheoryInfo = GenericTheoryInfo ClosedDiffTheory

-- | We use the ordering in order to display loaded theories to the user.
-- We first compare by name, then by time loaded, and then by source: Theories
-- that were loaded from the command-line are displayed earlier then
-- interactively loaded ones.
compareTI :: TheoryInfo -> TheoryInfo -> Ordering
compareTI (TheoryInfo _ i1 t1 p1 a1 o1 _ _) (TheoryInfo _ i2 t2 p2 a2 o2 _ _) =
  mconcat
    [ comparing (._thyName) i1 i2
    , comparing zonedTimeToUTC t1 t2
    , compare a1 a2
    , compare p1 p2
    , compare o1 o2
    ]

-- | We use the ordering in order to display loaded theories to the user.
-- We first compare by name, then by time loaded, and then by source: Theories
-- that were loaded from the command-line are displayed earlier then
-- interactively loaded ones.
compareDTI :: DiffTheoryInfo -> DiffTheoryInfo -> Ordering
compareDTI (TheoryInfo _ i1 t1 p1 a1 o1 _ _) (TheoryInfo _ i2 t2 p2 a2 o2 _ _) =
  mconcat
    [ comparing (._diffThyName) i1 i2
    , comparing zonedTimeToUTC t1 t2
    , compare a1 a2
    , compare p1 p2
    , compare o1 o2
    ]

data EitherTheoryInfo
  = Trace TheoryInfo
  | Diff DiffTheoryInfo
  deriving (Generic, Bin.Binary)

-- instance Bin.Binary TheoryInfo
-- instance Bin.Binary DiffTheoryInfo
-- instance Bin.Binary EitherTheoryInfo

{- instance Bin.Binary EitherTheoryInfo where
       put (Trace i) = do Bin.put (0 :: Bin.Word8)
                            Bin.put i
       put (Diff i)    = do Bin.put (1 :: Bin.Word8)
       Bin.put i -}
{-       get = do t <- get :: Bin.Get Bin.Word8
                case t of
                           0 -> do i <- Bin.get
                                   pure (Trace i)
                           1 -> do i <- Bin.get
                           pure (Diff i) -}
{-       get = do tag <- Bin.getWord8
                case tag of
                    0 -> liftM Trace get
                    1 -> liftM Diff get -}

-- Direct access functionf for Either Theory Type
getEitherTheoryName :: EitherTheoryInfo -> String
getEitherTheoryName (Trace i) = i.theory._thyName
getEitherTheoryName (Diff i) = i.theory._diffThyName

isTheoryInfo :: EitherTheoryInfo -> Bool
isTheoryInfo (Trace _) = True
isTheoryInfo (Diff  _) = False

isDiffTheoryInfo :: EitherTheoryInfo -> Bool
isDiffTheoryInfo (Trace _) = False
isDiffTheoryInfo (Diff  _) = True

getEitherTheoryTime :: EitherTheoryInfo -> ZonedTime
getEitherTheoryTime (Trace i) = i.time
getEitherTheoryTime (Diff i) = i.time

getEitherTheoryPrimary :: EitherTheoryInfo -> Bool
getEitherTheoryPrimary (Trace i) = i.primary
getEitherTheoryPrimary (Diff i) = i.primary

getEitherTheoryOrigin :: EitherTheoryInfo -> TheoryOrigin
getEitherTheoryOrigin (Trace i) = i.origin
getEitherTheoryOrigin (Diff i) = i.origin

getEitherTheoryIndex :: EitherTheoryInfo -> TheoryIdx
getEitherTheoryIndex (Trace i) = i.index
getEitherTheoryIndex (Diff i) = i.index

-- | We use the ordering in order to display loaded theories to the user.
-- We first compare by name, then by time loaded, and then by source: Theories
-- that were loaded from the command-line are displayed earlier then
-- interactively loaded ones.
compareEDTI :: EitherTheoryInfo -> EitherTheoryInfo -> Ordering
compareEDTI (Trace (TheoryInfo _ i1 t1 p1 a1 o1 _ _)) (Trace (TheoryInfo _ i2 t2 p2 a2 o2 _ _)) =
  mconcat
    [ comparing (._thyName) i1 i2
    , comparing zonedTimeToUTC t1 t2
    , compare a1 a2
    , compare p1 p2
    , compare o1 o2
    ]
compareEDTI (Diff (TheoryInfo _ i1 t1 p1 a1 o1 _ _)) (Diff (TheoryInfo _ i2 t2 p2 a2 o2 _ _)) =
  mconcat
    [ comparing (._diffThyName) i1 i2
    , comparing zonedTimeToUTC t1 t2
    , compare a1 a2
    , compare p1 p2
    , compare o1 o2
    ]
compareEDTI (Diff (TheoryInfo _ i1 t1 p1 a1 o1 _ _)) (Trace (TheoryInfo _ i2 t2 p2 a2 o2 _ _)) =
  mconcat
    [ compare i1._diffThyName i2._thyName
    , comparing zonedTimeToUTC t1 t2
    , compare a1 a2
    , compare p1 p2
    , compare o1 o2
    ]
compareEDTI (Trace (TheoryInfo _ i1 t1 p1 a1 o1 _ _)) (Diff (TheoryInfo _ i2 t2 p2 a2 o2 _ _)) =
  mconcat
    [ compare i1._thyName i2._diffThyName
    , comparing zonedTimeToUTC t1 t2
    , compare a1 a2
    , compare p1 p2
    , compare o1 o2
    ]


instance Eq TheoryInfo where
  (==) t1 t2 = compareTI t1 t2 == EQ

instance Ord TheoryInfo where
  compare = compareTI

instance Eq DiffTheoryInfo where
  (==) t1 t2 = compareDTI t1 t2 == EQ

instance Ord DiffTheoryInfo where
  compare = compareDTI


instance Eq EitherTheoryInfo where
  (==) t1 t2 = compareEDTI t1 t2 == EQ

instance Ord EitherTheoryInfo where
  compare = compareEDTI

-- | Simple data type for specifying a path to a specific
-- item within a theory.
data TheoryPath
  = TheoryHelp                          -- ^ The help view (help and info about theory)
  | TheoryLemma String                  -- ^ Theory lemma with given name
  | TheorySource SourceKind Int Int     -- ^ Required cases (i'th source, j'th case)
  | TheoryProof String ProofPath        -- ^ Proof path within proof for given lemma
  | TheoryMethod String ProofPath Int   -- ^ Apply the proof method to proof path
  | TheoryRules                         -- ^ Theory rules
  | TheoryMessage                       -- ^ Theory message deduction
  | TheoryTactic                        -- ^ Theory tactic
  | TheoryEdit  String                  -- ^ edit lemma at runtime
  | TheoryDelete String                 -- ^ remove lemma at runtime
  | TheoryAdd String                    -- ^ add new lemma at index at runtime
  deriving (Eq, Show, Read)

-- | Simple data type for specifying a path to a specific
-- item within a theory.
data DiffTheoryPath
  = DiffTheoryHelp                                    -- ^ The help view (help and info about theory)
  | DiffTheoryLemma Side String                       -- ^ Theory lemma with given name and side
  | DiffTheoryDiffLemma String                        -- ^ Theory DiffLemma with given name
  | DiffTheorySource Side SourceKind Bool Int Int     -- ^ Required cases (i'th source, j'th case)
  | DiffTheoryProof Side String ProofPath             -- ^ Proof path within proof for given lemma
  | DiffTheoryDiffProof String ProofPath              -- ^ Proof path within proof for given lemma
  | DiffTheoryMethod Side String ProofPath Int        -- ^ Apply the proof method to proof path
  | DiffTheoryDiffMethod String ProofPath Int         -- ^ Apply the proof method to proof path
  | DiffTheoryRules Side Bool                         -- ^ Theory rules per side
  | DiffTheoryDiffRules                               -- ^ Theory rules unprocessed
  | DiffTheoryMessage Side Bool                       -- ^ Theory message deduction per side
  deriving (Eq, Show, Read)

-- | Render a theory path to a list of strings. Note that we prefix an
-- underscore to the empty string and strings starting with an underscore.
-- This avoids empty path segments, which seem to trip up certain versions of
-- Yesod.
renderTheoryPath :: TheoryPath -> [String]
renderTheoryPath =
  map prefixWithUnderscore . \case
    TheoryHelp -> ["help"]
    TheoryRules -> ["rules"]
    TheoryMessage -> ["message"]
    TheoryLemma name -> ["lemma", name]
    TheorySource k i j -> ["cases", show k, show i, show j]
    TheoryProof lemma path -> "proof" : lemma : path
    TheoryMethod lemma path idx -> "method" : lemma : show idx : path
    TheoryTactic -> ["tactic"]
    TheoryEdit name -> ["edit", name]
    TheoryAdd name -> ["add", name]
    TheoryDelete name -> ["delete", name]

-- | Render a theory path to a list of strings. Note that we prefix an
-- underscore to the empty string and strings starting with an underscore.
-- This avoids empty path segments, which seem to trip up certain versions of
-- Yesod.
renderDiffTheoryPath :: DiffTheoryPath -> [String]
renderDiffTheoryPath =
  map prefixWithUnderscore . \case
    DiffTheoryHelp -> ["help"]
    DiffTheoryLemma s name -> ["lemma", show s, name]
    DiffTheoryDiffLemma name -> ["difflemma", name]
    DiffTheorySource s k i j d -> ["cases", show s, show k, show i, show j, show d]
    DiffTheoryProof s lemma path -> "proof" : show s : lemma : path
    DiffTheoryDiffProof lemma path -> "diffProof" : lemma : path
    DiffTheoryMethod s lemma path idx -> "method" : show s : lemma : show idx : path
    DiffTheoryDiffMethod lemma path idx -> "diffMethod" : lemma : show idx : path
    DiffTheoryRules s d -> ["rules", show s, show d]
    DiffTheoryDiffRules -> ["diffrules"]
    DiffTheoryMessage s d -> ["message", show s, show d]

-- | Prefix an underscore to the empty string and strings starting with an
-- underscore.
prefixWithUnderscore :: String -> String
prefixWithUnderscore ""         = "_"
prefixWithUnderscore cs@('_':_) = '_' : cs
prefixWithUnderscore cs         = cs

-- | Remove an underscore prefix. It holds that
--
-- > unprefixUnderscore . prefixWithUnderscore = id
--
-- The inverted composition holds for all strings except the empty string and
-- strings starting with an underscore.
unprefixUnderscore :: String -> String
unprefixUnderscore "_"              = ""
unprefixUnderscore ('_':cs@('_':_)) = cs
unprefixUnderscore cs               = cs

-- | Parse a list of strings into a theory path.
parseTheoryPath :: [String] -> Maybe TheoryPath
parseTheoryPath =
  parse . map unprefixUnderscore
  where
    parse []     = Nothing
    parse (x:xs) = case x of
      "help"    -> Just TheoryHelp
      "rules"   -> Just TheoryRules
      "message" -> Just TheoryMessage
      "tactic"  -> Just TheoryTactic
      "lemma"   -> parseLemma xs
      "cases"   -> parseCases xs
      "proof"   -> parseProof xs
      "method"  -> parseMethod xs
      "edit"    -> TheoryEdit <$> listToMaybe xs
      "add"     -> TheoryAdd <$> listToMaybe xs
      "delete"  -> TheoryDelete <$> listToMaybe xs
      _         -> Nothing

    safeRead = listToMaybe . map fst . reads

    -- parseAdd (y:_) = TheoryAdd <$> safeRead y
    -- parseAdd _ = Nothing

    parseLemma ys = TheoryLemma <$> listToMaybe ys

    parseProof (y:ys) = Just (TheoryProof y ys)
    parseProof _      = Nothing

    parseMethod (y:z:zs) = safeRead z >>= Just . TheoryMethod y zs
    parseMethod _        = Nothing

    parseCases (kind:y:z:_) = do
      k <- case kind of "refined" -> pure RefinedSource
                        "raw"     -> pure RawSource
                        _         -> Nothing
      m <- safeRead y
      n <- safeRead z
      pure (TheorySource k m n)
    parseCases _       = Nothing

-- | Parse a list of strings into a theory path.
parseDiffTheoryPath :: [String] -> Maybe DiffTheoryPath
parseDiffTheoryPath =
  parse . map unprefixUnderscore
  where
    parse []     = Nothing
    parse (x:xs) = case x of
      "help"      -> Just DiffTheoryHelp
      "diffrules" -> Just DiffTheoryDiffRules
      "rules"     -> parseRules xs
      "message"   -> parseMessage xs
      "lemma"     -> parseLemma xs
      "difflemma" -> parseDiffLemma xs
      "cases"     -> parseCases xs
      "proof"     -> parseProof xs
      "diffProof" -> parseDiffProof xs
      "method"    -> parseMethod xs
      "diffMethod"-> parseDiffMethod xs
      _           -> Nothing

    safeRead :: Read a => String -> Maybe a
    safeRead  = listToMaybe . map fst . reads

    parseRules :: [String] -> Maybe DiffTheoryPath
    parseRules (y:z:_) = do
      s <- case y of "LHS" -> pure LHS
                     "RHS" -> pure RHS
                     _     -> Nothing
      d <- case z of "True"  -> pure True
                     "False" -> pure False
                     _       -> Nothing
      pure (DiffTheoryRules s d)
    parseRules _         = Nothing

    parseMessage :: [String] -> Maybe DiffTheoryPath
    parseMessage (y:z:_) = do
      s <- case y of "LHS" -> pure LHS
                     "RHS" -> pure RHS
                     _     -> Nothing
      d <- case z of "True"  -> pure True
                     "False" -> pure False
                     _       -> Nothing
      pure (DiffTheoryMessage s d)
    parseMessage _         = Nothing

    parseLemma :: [String] -> Maybe DiffTheoryPath
    parseLemma (y:ys) = do
      s <- case y of "LHS" -> pure LHS
                     "RHS" -> pure RHS
                     _     -> Nothing
      pure (DiffTheoryLemma s (head ys))
    parseLemma _         = Nothing

    parseDiffLemma :: [String] -> Maybe DiffTheoryPath
    parseDiffLemma ys = DiffTheoryDiffLemma <$> listToMaybe ys

    parseProof :: [String] -> Maybe DiffTheoryPath
    parseProof (y:z:zs) = do
      s <- case y of "LHS" -> pure LHS
                     "RHS" -> pure RHS
                     _     -> Nothing
      pure (DiffTheoryProof s z zs)
    parseProof _         = Nothing

    parseDiffProof :: [String] -> Maybe DiffTheoryPath
    parseDiffProof (z:zs) = do
      pure (DiffTheoryDiffProof z zs)
    parseDiffProof _         = Nothing

    parseMethod :: [String] -> Maybe DiffTheoryPath
    parseMethod (x:y:z:zs) = do
      s <- case x of "LHS" -> pure LHS
                     "RHS" -> pure RHS
                     _     -> Nothing
      i <- safeRead z
      pure (DiffTheoryMethod s y zs i)
    parseMethod _        = Nothing

    parseDiffMethod :: [String] -> Maybe DiffTheoryPath
    parseDiffMethod (y:z:zs) = do
      i <- safeRead z
      pure (DiffTheoryDiffMethod y zs i)
    parseDiffMethod _        = Nothing

    parseCases :: [String] -> Maybe DiffTheoryPath
    parseCases (x:kind:pd:y:z:_) = do
      s <- case x of "LHS" -> pure LHS
                     "RHS" -> pure RHS
                     _     -> Nothing
      k <- case kind of "refined" -> pure RefinedSource
                        "raw"     -> pure RawSource
                        _         -> Nothing
      d <- case pd of "True"  -> pure True
                      "False" -> pure False
                      _       -> Nothing
      m <- safeRead y
      n <- safeRead z
      pure (DiffTheorySource s k d m n)
    parseCases _       = Nothing

type RenderUrl = Route WebUI -> T.Text

------------------------------------------------------------------------------
-- Routing
------------------------------------------------------------------------------

getStatic :: WebUI -> Static
getStatic = (.getStatic)

-- | Static routing for our application.
-- Note that handlers ending in R are general handlers,
-- whereas handlers ending in MR are for the main view
-- and the ones ending in DR are for the debug view.
mkYesodData "WebUI" [parseRoutes|
/                                          RootR                   GET POST
/thy/trace/#Int/edit/*TheoryPath           TheoryEditR             POST
/thy/trace/#Int/verify/*TheoryPath         TheoryVerifyR           GET
/thy/trace/#Int/overview/*TheoryPath          OverviewR               GET
/thy/trace/#Int/source                           TheorySourceR           GET
/thy/trace/#Int/message                          TheoryMessageDeductionR GET
/thy/trace/#Int/main/*TheoryPath              TheoryPathMR            GET
-- /thy/trace/#Int/debug/*TheoryPath             TheoryPathDR            GET
/thy/trace/#Int/graph/*TheoryPath             TheoryGraphR            GET
/thy/trace/#Int/autoprove/#SolutionExtractor/#Int/#Bool/*TheoryPath AutoProverR             GET
/thy/trace/#Int/autoproveAll/#SolutionExtractor/#Int/*TheoryPath AutoProverAllR             GET
/thy/trace/#Int/next/#String/*TheoryPath      NextTheoryPathR         GET
/thy/trace/#Int/prev/#String/*TheoryPath      PrevTheoryPathR         GET
-- /thy/trace/#Int/save                             SaveTheoryR             GET
/thy/trace/#Int/download/#String                 DownloadTheoryR         GET
/thy/trace/#Int/get_and_append/#String           AppendNewLemmasR         GET
-- /thy/trace/#Int/edit/source                      EditTheoryR             GET POST
-- /thy/trace/#Int/edit/path/*TheoryPath         EditPathR               GET POST
/thy/trace/#Int/del/path/*TheoryPath          DeleteStepR             GET
/thy/trace/#Int/unload                           UnloadTheoryR           GET
/thy/equiv/#Int/overview/*DiffTheoryPath      OverviewDiffR               GET
/thy/equiv/#Int/source                           TheorySourceDiffR           GET
/thy/equiv/#Int/message                          TheoryMessageDeductionDiffR GET
/thy/equiv/#Int/main/*DiffTheoryPath          TheoryPathDiffMR            GET
-- /thy/equiv/#Int/debug/*DiffTheoryPath             TheoryPathDiffDR            GET
/thy/equiv/#Int/graph/*DiffTheoryPath         TheoryGraphDiffR            GET
/thy/equiv/#Int/mirror/*DiffTheoryPath        TheoryMirrorDiffR            GET
/thy/equiv/#Int/autoprove/#SolutionExtractor/#Int/#Side/*DiffTheoryPath AutoProverDiffR             GET
/thy/equiv/#Int/autoproveAll/#SolutionExtractor/#Int AutoProverAllDiffR             GET
/thy/equiv/#Int/autoproveDiff/#SolutionExtractor/#Int/*DiffTheoryPath AutoDiffProverR             GET
/thy/equiv/#Int/next/#String/*DiffTheoryPath  NextTheoryPathDiffR         GET
/thy/equiv/#Int/prev/#String/*DiffTheoryPath  PrevTheoryPathDiffR         GET
-- /thy/equiv/#Int/save                             SaveTheoryR             GET
/thy/equiv/#Int/download/#String                 DownloadTheoryDiffR         GET
-- /thy/equiv/#Int/edit/source                      EditTheoryR             GET POST
-- /thy/equiv/#Int/edit/path/*DiffTheoryPath         EditPathDiffR               GET POST
/thy/equiv/#Int/del/path/*DiffTheoryPath      DeleteStepDiffR             GET
/thy/equiv/#Int/unload                           UnloadTheoryDiffR           GET
/kill                                      KillThreadR             GET
-- /threads                                   ThreadsR                GET
/robots.txt                                RobotsR                 GET
/favicon.ico                               FaviconR                GET
/static                                    StaticR                 Static getStatic
|]


instance PathPiece SolutionExtractor where
  toPathPiece CutNothing         = "characterize"
  toPathPiece CutDFS             = "idfs"
  toPathPiece CutBFS             = "bfs"
  toPathPiece CutSingleThreadDFS = "seqdfs"

  fromPathPiece "characterize" = Just CutNothing
  fromPathPiece "idfs"         = Just CutDFS
  fromPathPiece "bfs"          = Just CutBFS
  fromPathPiece "seqdfs"       = Just CutSingleThreadDFS
  fromPathPiece _              = Nothing

instance PathPiece Side where
  toPathPiece LHS = "LHS"
  toPathPiece RHS = "RHS"

  fromPathPiece "LHS" = Just LHS
  fromPathPiece "RHS" = Just RHS
  fromPathPiece _     = Nothing


-- | MultiPiece instance for TheoryPath.
instance PathMultiPiece TheoryPath where
  toPathMultiPiece   = map T.pack . renderTheoryPath
  fromPathMultiPiece = parseTheoryPath . map T.unpack

-- | MultiPiece instance for DiffTheoryPath.
instance PathMultiPiece DiffTheoryPath where
  toPathMultiPiece   = map T.pack . renderDiffTheoryPath
  fromPathMultiPiece = parseDiffTheoryPath . map T.unpack

-- Instance of the Yesod typeclass.
instance Yesod WebUI where
  -- | The approot. We can leave this empty because the
  -- application is always served from the root of the server.
  approot = ApprootStatic T.empty

  makeSessionBackend _ = return Nothing

  -- | The default layout for rendering.
  defaultLayout = defaultLayout'

  -- | The path cleaning function. We make sure empty strings
  -- are not scrubbed from the end of the list. The default
  -- cleanPath function forces canonical URLs.
  cleanPath _ = Right

------------------------------------------------------------------------------
-- Default layout
------------------------------------------------------------------------------

-- | Our application's default layout template.
-- Note: We define the default layout here even tough it doesn't really
-- belong in the "types" module in order to avoid mutually recursive modules.
-- defaultLayout' :: (Yesod master, Route master ~ WebUIRoute)
--                => Widget master ()      -- ^ Widget to embed in layout
--                -> Handler master Html
defaultLayout' :: Widget -> Handler Html
defaultLayout' w = do
  page <- widgetToPageContent w
  message <- getMessage
  withUrlRenderer [hamlet|
    $newline never
    !!!
    <html>
      <head>
        <title>#{pageTitle page}
        <link rel=stylesheet href=/static/css/tamarin-prover-ui.css>
        <link rel=stylesheet href=/static/css/jquery-contextmenu.css>
        <link rel=stylesheet href=/static/css/smoothness/jquery-ui.css>
        <script src=/static/js/jquery.js></script>
        <script src=/static/js/jquery-ui.js></script>
        <script src=/static/js/jquery-layout.js></script>
        <script src=/static/js/jquery-cookie.js></script>
        <script src=/static/js/jquery-superfish.js></script>
        <script src=/static/js/jquery-contextmenu.js></script>
        <script src=/static/js/tamarin-prover-ui.js></script>
        ^{pageHead page}
      <body>
        $maybe msg <- message
          <p.message>#{msg}
        <p.loading>
          Loading, please wait...
          \  <a id=cancel href='#'>Cancel</a>
        ^{pageBody page}
        <div#dialog>
        <ul#contextMenu>
          <li.autoprove>
            <a href="#autoprove">Autoprove</a>
  |]
          -- <li.delstep>
            -- <a href="#del/path">Remove step</a>
