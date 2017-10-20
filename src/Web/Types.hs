{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE Rank2Types        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE ViewPatterns      #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DeriveAnyClass    #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

{- |
Module      :  Types.hs
Description :  Central data type and Yesod typeclass instances.
Copyright   :  (c) 2011 Cedric Staub
License     :  GPL-3

Maintainer  :  Simon Meier <iridcode@gmail.com>
Stability   :  experimental
Portability :  non-portable
-}


module Web.Types
  ( WebUI(..)
  , Route (..)
  , resourcesWebUI
  , TheoryInfo(..)
  , DiffTheoryInfo(..)
  , EitherTheoryInfo(..)
  , isTheoryInfo
  , isDiffTheoryInfo
  , getEitherTheoryName
  , getEitherTheoryTime
  , getEitherTheoryPrimary
  , getEitherTheoryOrigin
  , getEitherTheoryIndex
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
  )
where


-- import           Control.Applicative
import           Control.Concurrent
import           Data.Label
import qualified Data.Map            as M
import           Data.Maybe          (listToMaybe)
-- import           Data.Monoid         (mconcat)
import           Data.Ord            (comparing)
import qualified Data.Text           as T
import           Data.Time.LocalTime
import qualified Data.Binary         as Bin
import           Data.Binary.Orphans()

import           Control.DeepSeq
import           Control.Monad
-- import           Control.Monad
import           GHC.Generics (Generic)

import           Text.Hamlet
import           Yesod.Core
import           Yesod.Static

import           Theory


-- | Derived Instances to fix things
instance Bin.Binary ZonedTime where
  get = liftM2 ZonedTime Bin.get Bin.get
  put (ZonedTime d tod) = Bin.put d >> Bin.put tod

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
type TheoryMap = M.Map TheoryIdx (EitherTheoryInfo)

-- | Type synonym representing a map of threads.
type ThreadMap = M.Map T.Text ThreadId

-- | The image format used for rendering graphs.
data ImageFormat = PNG | SVG

instance Show ImageFormat where
    show PNG = "png"
    show SVG = "svg"

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
  -- , parseThy    :: MonadIO m => String -> GenericHandler m ClosedTheory
  , parseThy           :: String -> IO (Either String (ClosedTheory))
    -- ^ Close an open theory according to command-line arguments.
  , diffParseThy       :: String -> IO (Either String (ClosedDiffTheory))
    -- ^ Close an open theory according to command-line arguments.
  , thyWf              :: String -> IO String
    -- ^ Report on the wellformedness of a theory according to command-line arguments.
  , theoryVar          :: MVar (TheoryMap)
    -- ^ MVar that holds the theory map
  , threadVar          :: MVar ThreadMap
    -- ^ MVar that holds the thread map
  , autosaveProofstate :: Bool
    -- ^ Automatically store theory map
  , graphCmd           :: (String, FilePath)
    -- ^ The dot or json command with additional flag to indicate choice dot, json, ...
  , imageFormat        :: ImageFormat
    -- ^ The image-format used for rendering graphs
  , defaultAutoProver  :: AutoProver
    -- ^ The default prover to use for automatic proving.
  , debug              :: Bool
    -- ^ Output debug messages
  , isDiffTheory       :: Bool
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
data TheoryInfo = TheoryInfo
  { tiIndex      :: TheoryIdx       -- ^ Index of theory.
  , tiTheory     :: ClosedTheory    -- ^ The closed theory.
  , tiTime       :: ZonedTime       -- ^ Time theory was loaded.
  , tiParent     :: Maybe TheoryIdx -- ^ Prev theory in history
  , tiPrimary    :: Bool            -- ^ This is the orginally loaded theory.
  , tiOrigin     :: TheoryOrigin    -- ^ Origin of theory.
  , tiAutoProver :: AutoProver      -- ^ The automatic prover to use.
  } deriving (Generic, Bin.Binary)

-- | Data type containg both the theory and it's index, making it easier to
-- pass the two around (since they are always tied to each other). We also
-- keep some extra bookkeeping information.
data DiffTheoryInfo = DiffTheoryInfo
  { dtiIndex      :: TheoryIdx       -- ^ Index of theory.
  , dtiTheory     :: ClosedDiffTheory -- ^ The closed theory.
  , dtiTime       :: ZonedTime       -- ^ Time theory was loaded.
  , dtiParent     :: Maybe TheoryIdx -- ^ Prev theory in history
  , dtiPrimary    :: Bool            -- ^ This is the orginally loaded theory.
  , dtiOrigin     :: TheoryOrigin    -- ^ Origin of theory.
  , dtiAutoProver :: AutoProver      -- ^ The automatic prover to use.
  } deriving (Generic, Bin.Binary)


-- | We use the ordering in order to display loaded theories to the user.
-- We first compare by name, then by time loaded, and then by source: Theories
-- that were loaded from the command-line are displayed earlier then
-- interactively loaded ones.
compareTI :: TheoryInfo -> TheoryInfo -> Ordering
compareTI (TheoryInfo _ i1 t1 p1 a1 o1 _) (TheoryInfo _ i2 t2 p2 a2 o2 _) =
  mconcat
    [ comparing (get thyName) i1 i2
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
compareDTI (DiffTheoryInfo _ i1 t1 p1 a1 o1 _) (DiffTheoryInfo _ i2 t2 p2 a2 o2 _) =
  mconcat
    [ comparing (get diffThyName) i1 i2
    , comparing zonedTimeToUTC t1 t2
    , compare a1 a2
    , compare p1 p2
    , compare o1 o2
    ]

data EitherTheoryInfo = Trace TheoryInfo | Diff DiffTheoryInfo deriving (Generic, Bin.Binary)

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
                                   return (Trace i)
                           1 -> do i <- Bin.get
                           return (Diff i) -}
{-       get = do tag <- Bin.getWord8
                case tag of
                    0 -> liftM Trace get
                    1 -> liftM Diff get -}

-- Direct access functionf for Either Theory Type
getEitherTheoryName :: EitherTheoryInfo -> String
getEitherTheoryName (Trace i)  = get thyName (tiTheory i)
getEitherTheoryName (Diff i) = get diffThyName (dtiTheory i)

isTheoryInfo :: EitherTheoryInfo -> Bool
isTheoryInfo (Trace _) = True
isTheoryInfo (Diff  _) = False

isDiffTheoryInfo :: EitherTheoryInfo -> Bool
isDiffTheoryInfo (Trace _) = False
isDiffTheoryInfo (Diff  _) = True

getEitherTheoryTime :: EitherTheoryInfo -> ZonedTime
getEitherTheoryTime (Trace i)  = (tiTime i)
getEitherTheoryTime (Diff i) = (dtiTime i)

getEitherTheoryPrimary :: EitherTheoryInfo -> Bool
getEitherTheoryPrimary (Trace i)  = (tiPrimary i)
getEitherTheoryPrimary (Diff i) = (dtiPrimary i)

getEitherTheoryOrigin :: EitherTheoryInfo -> TheoryOrigin
getEitherTheoryOrigin (Trace i)  = (tiOrigin i)
getEitherTheoryOrigin (Diff i) = (dtiOrigin i)

getEitherTheoryIndex :: EitherTheoryInfo -> TheoryIdx
getEitherTheoryIndex (Trace i)  = (tiIndex i)
getEitherTheoryIndex (Diff i) = (dtiIndex i)

-- | We use the ordering in order to display loaded theories to the user.
-- We first compare by name, then by time loaded, and then by source: Theories
-- that were loaded from the command-line are displayed earlier then
-- interactively loaded ones.
compareEDTI :: EitherTheoryInfo -> EitherTheoryInfo -> Ordering
compareEDTI (Trace (TheoryInfo _ i1 t1 p1 a1 o1 _)) (Trace (TheoryInfo _ i2 t2 p2 a2 o2 _)) =
  mconcat
    [ comparing (get thyName) i1 i2
    , comparing zonedTimeToUTC t1 t2
    , compare a1 a2
    , compare p1 p2
    , compare o1 o2
    ]
compareEDTI (Diff (DiffTheoryInfo _ i1 t1 p1 a1 o1 _)) (Diff (DiffTheoryInfo _ i2 t2 p2 a2 o2 _)) =
  mconcat
    [ comparing (get diffThyName) i1 i2
    , comparing zonedTimeToUTC t1 t2
    , compare a1 a2
    , compare p1 p2
    , compare o1 o2
    ]
compareEDTI (Diff (DiffTheoryInfo _ i1 t1 p1 a1 o1 _)) (Trace (TheoryInfo _ i2 t2 p2 a2 o2 _)) =
  mconcat
    [ compare ((get diffThyName) i1) ((get thyName) i2)
    , comparing zonedTimeToUTC t1 t2
    , compare a1 a2
    , compare p1 p2
    , compare o1 o2
    ]
compareEDTI (Trace (TheoryInfo _ i1 t1 p1 a1 o1 _)) (Diff (DiffTheoryInfo _ i2 t2 p2 a2 o2 _)) =
  mconcat
    [ compare ((get thyName) i1) ((get diffThyName) i2)
    , comparing zonedTimeToUTC t1 t2
    , compare a1 a2
    , compare p1 p2
    , compare o1 o2
    ]


instance Eq (TheoryInfo) where
  (==) t1 t2 = compareTI t1 t2 == EQ

instance Ord (TheoryInfo) where
  compare = compareTI

instance Eq (DiffTheoryInfo) where
  (==) t1 t2 = compareDTI t1 t2 == EQ

instance Ord (DiffTheoryInfo) where
  compare = compareDTI


instance Eq (EitherTheoryInfo) where
  (==) t1 t2 = compareEDTI t1 t2 == EQ

instance Ord (EitherTheoryInfo) where
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
    map prefixWithUnderscore . go
  where
    go TheoryHelp = ["help"]
    go TheoryRules = ["rules"]
    go TheoryMessage = ["message"]
    go (TheoryLemma name) = ["lemma", name]
    go (TheorySource k i j) = ["cases", show k, show i, show j]
    go (TheoryProof lemma path) = "proof" : lemma : path
    go (TheoryMethod lemma path idx) = "method" : lemma : show idx : path

-- | Render a theory path to a list of strings. Note that we prefix an
-- underscore to the empty string and strings starting with an underscore.
-- This avoids empty path segments, which seem to trip up certain versions of
-- Yesod.
renderDiffTheoryPath :: DiffTheoryPath -> [String]
renderDiffTheoryPath =
    map prefixWithUnderscore . go
  where
    go DiffTheoryHelp = ["help"]
    go (DiffTheoryLemma s name) = ["lemma", show s, name]
    go (DiffTheoryDiffLemma name) = ["difflemma", name]
    go (DiffTheorySource s k i j d) = ["cases", show s, show k, show i, show j, show d]
    go (DiffTheoryProof s lemma path) = "proof" : show s : lemma : path
    go (DiffTheoryDiffProof lemma path) = "diffProof" : lemma : path
    go (DiffTheoryMethod s lemma path idx) = "method" : show s : lemma : show idx : path
    go (DiffTheoryDiffMethod lemma path idx) = "diffMethod" : lemma : show idx : path
    go (DiffTheoryRules s d) = ["rules", show s, show d]
    go (DiffTheoryDiffRules) = ["diffrules"]
    go (DiffTheoryMessage s d) = ["message", show s, show d]

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
      "lemma"   -> parseLemma xs
      "cases"   -> parseCases xs
      "proof"   -> parseProof xs
      "method"  -> parseMethod xs
      _         -> Nothing

    safeRead = listToMaybe . map fst . reads

    parseLemma ys = TheoryLemma <$> listToMaybe ys

    parseProof (y:ys) = Just (TheoryProof y ys)
    parseProof _      = Nothing

    parseMethod (y:z:zs) = safeRead z >>= Just . TheoryMethod y zs
    parseMethod _        = Nothing

    parseCases (kind:y:z:_) = do
      k <- case kind of "refined" -> return RefinedSource
                        "raw"     -> return RawSource
                        _         -> Nothing
      m <- safeRead y
      n <- safeRead z
      return (TheorySource k m n)
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
      s <- case y of "LHS" -> return LHS
                     "RHS" -> return RHS
                     _     -> Nothing
      d <- case z of "True"  -> return True
                     "False" -> return False
                     _       -> Nothing
      return (DiffTheoryRules s d)
    parseRules _         = Nothing
    
    parseMessage :: [String] -> Maybe DiffTheoryPath
    parseMessage (y:z:_) = do
      s <- case y of "LHS" -> return LHS
                     "RHS" -> return RHS
                     _     -> Nothing
      d <- case z of "True"  -> return True
                     "False" -> return False
                     _       -> Nothing
      return (DiffTheoryMessage s d)
    parseMessage _         = Nothing
    
    parseLemma :: [String] -> Maybe DiffTheoryPath
    parseLemma (y:ys) = do
      s <- case y of "LHS" -> return LHS
                     "RHS" -> return RHS
                     _     -> Nothing
      return (DiffTheoryLemma s (head ys))
    parseLemma _         = Nothing

    parseDiffLemma :: [String] -> Maybe DiffTheoryPath
    parseDiffLemma ys = DiffTheoryDiffLemma <$> listToMaybe ys

    parseProof :: [String] -> Maybe DiffTheoryPath
    parseProof (y:z:zs) = do
      s <- case y of "LHS" -> return LHS
                     "RHS" -> return RHS
                     _     -> Nothing
      return (DiffTheoryProof s z zs)
    parseProof _         = Nothing

    parseDiffProof :: [String] -> Maybe DiffTheoryPath
    parseDiffProof (z:zs) = do
      return (DiffTheoryDiffProof z zs)
    parseDiffProof _         = Nothing

    parseMethod :: [String] -> Maybe DiffTheoryPath
    parseMethod (x:y:z:zs) = do
      s <- case x of "LHS" -> return LHS    
                     "RHS" -> return RHS
                     _     -> Nothing
      i <- safeRead z
      return (DiffTheoryMethod s y zs i)
    parseMethod _        = Nothing

    parseDiffMethod :: [String] -> Maybe DiffTheoryPath
    parseDiffMethod (y:z:zs) = do
      i <- safeRead z
      return (DiffTheoryDiffMethod y zs i)
    parseDiffMethod _        = Nothing

    parseCases :: [String] -> Maybe DiffTheoryPath
    parseCases (x:kind:pd:y:z:_) = do
      s <- case x of "LHS" -> return LHS
                     "RHS" -> return RHS
                     _     -> Nothing
      k <- case kind of "refined" -> return RefinedSource
                        "raw"     -> return RawSource
                        _         -> Nothing
      d <- case pd of "True"  -> return True
                      "False" -> return False
                      _       -> Nothing
      m <- safeRead y
      n <- safeRead z
      return (DiffTheorySource s k d m n)
    parseCases _       = Nothing

type RenderUrl = Route (WebUI) -> T.Text

------------------------------------------------------------------------------
-- Routing
------------------------------------------------------------------------------

-- | Static routing for our application.
-- Note that handlers ending in R are general handlers,
-- whereas handlers ending in MR are for the main view
-- and the ones ending in DR are for the debug view.
mkYesodData "WebUI" [parseRoutes|
/                                          RootR                   GET POST
/thy/trace/#Int/overview/*TheoryPath          OverviewR               GET
/thy/trace/#Int/source                           TheorySourceR           GET
/thy/trace/#Int/message                          TheoryMessageDeductionR GET
/thy/trace/#Int/main/*TheoryPath              TheoryPathMR            GET
-- /thy/trace/#Int/debug/*TheoryPath             TheoryPathDR            GET
/thy/trace/#Int/graph/*TheoryPath             TheoryGraphR            GET
/thy/trace/#Int/autoprove/#SolutionExtractor/#Int/*TheoryPath AutoProverR             GET
/thy/trace/#Int/next/#String/*TheoryPath      NextTheoryPathR         GET
/thy/trace/#Int/prev/#String/*TheoryPath      PrevTheoryPathR         GET
-- /thy/trace/#Int/save                             SaveTheoryR             GET
/thy/trace/#Int/download/#String                 DownloadTheoryR         GET
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
  toPathPiece CutNothing = "characterize"
  toPathPiece CutDFS     = "idfs"
  toPathPiece CutBFS     = "bfs"

  fromPathPiece "characterize" = Just CutNothing
  fromPathPiece "idfs"         = Just CutDFS
  fromPathPiece "bfs"          = Just CutBFS
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

