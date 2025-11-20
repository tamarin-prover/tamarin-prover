-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Support for interaction with the console: argument parsing.

module Main.Console (

    defaultMain

  -- * Static information about the Tamarin prover
  , programName

  -- * Constructing interaction modes for Tamarin prover
  , TamarinMode
  , tamarinMode

  , helpAndExit

  -- * Maude Version
  , maudePath
  , ensureMaude
  , ensureMaudeAndGetVersion
  , testProcess
  , commandLine

  -- * Argument parsing
  , Arguments
  , ArgKey
  , ArgVal

  -- ** Setting arguments
  , updateArg
  , addEmptyArg

  , helpFlag

  -- ** Retrieving arguments
  , getArg
  , findArg
  , argExists

  -- * Pretty printing and console output
  , lineWidth
  , shortLineWidth

  , renderDoc

  -- Version
  , gitVersion
  , compileTime
  ) where

import Data.Maybe
import Data.Version                    (showVersion)
import Data.Time
import Data.List
import Data.Char                       (isSpace)
import Safe

import Control.Exception as E
import Control.Monad

import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Text
import System.Exit
import System.IO
import System.Process

import Text.PrettyPrint.Class qualified as PP

import Paths_tamarin_prover (version)

import Language.Haskell.TH
import Development.GitRev

------------------------------------------------------------------------------
-- Maude version functions - previously in Environment.hs
------------------------------------------------------------------------------

-- | Path to maude tool
maudePath :: Arguments -> FilePath
maudePath = fromMaybe "maude" . findArg "withMaude"

getVersionIO :: String -> IO String
getVersionIO maudeVersion = do
  let tamarinVersion = showVersion version
  pure $ "Generated from:\nTamarin version " ++ tamarinVersion
         ++ "\nMaude version " ++ maudeVersion ++ gitVersion
         ++ "\n" ++ compileTime

commandLine :: String -> [String] -> String
commandLine prog args = unwords $ prog : args

testProcess
  :: (String -> String -> Either String String)
  -- ^ Analysis of stdout, stderr. Use 'Left' to report error.
  -> String         -- ^ Default error message to display to the user.
  -> String         -- ^ Test description to display.
  -> FilePath       -- ^ Process to start
  -> [String]       -- ^ Arguments
  -> String         -- ^ Stdin
  -> Bool           -- ^ Whether to ignore ExitFailure
  -> Bool           -- ^ Whether Maude is being tested - hard fail for exceptions on Maude.
  -> IO (Maybe String)    -- ^ String with the process output, if test was successful
testProcess check defaultMsg testName prog args inp ignoreExitCode maudeTest = do
  putStrErr testName
  hFlush stdout
  hFlush stderr
  handle handler $ do
    (exitCode, out, err) <- readProcessWithExitCode prog args inp
    let errMsg reason = do
          putStrErrLn reason
          putStrErrLn $ "Detailed results from testing '" ++ prog ++ "'"
          putStrErrLn $ " command: " ++ commandLine prog args
          putStrErrLn $ " stdin:   " ++ inp
          putStrErrLn $ " stdout:  " ++ out
          putStrErrLn $ " stderr:  " ++ err
          pure Nothing

    let check' = case check out err of
                   Left msg  -> errMsg msg
                   Right msg -> do putStrErrLn msg
                                   pure (Just out)

    if not ignoreExitCode then
      case exitCode of
        ExitFailure code -> errMsg $
          "failed with exit code " ++ show code ++ "\n\n" ++ defaultMsg
        ExitSuccess      -> check'
    else check'

  where
    putStrErrLn = hPutStrLn stderr
    putStrErr = hPutStr stderr

    handler :: IOException -> IO (Maybe String)
    handler exception = do
      putStrErrLn "caught exception while executing:"
      putStrErrLn $ commandLine prog args
      putStrErrLn $ "with input: " ++ inp
      putStrErrLn "Exception: "
      putStrErrLn $ "   " ++ show exception
      if maudeTest then
        error "Maude is not installed. Ensure Maude is available and on the path."
        else putStrErrLn ""
      pure Nothing

ensureMaude :: Arguments -> IO (Bool, String)
ensureMaude as = do
  hPutStrLn stderr $ "maude tool: '" ++ maude ++ "'"
  t1 <- testProcess checkVersion errMsg' " checking version: " maude ["--version"] "" False True
  t2 <- testProcess checkInstall errMsg' " checking installation: "   maude [] "quit\n" False True
  (_, out, _) <- readProcessWithExitCode maude ["--version"] ""
  pure $
    if isNothing t1 || isNothing t2 then
      (False, if out == "" then "unknown version\n" else init out ++ " (unsupported)\n")
    else
      (True, out)
  where
    maude = maudePath as
    checkVersion out _
      | strip out `elem` supportedVersions = Right (strip out ++ ". OK.")
      | otherwise                          = Left  $ errMsg $
          " 'maude --version' returned unsupported version '" ++ strip out ++ "'"

    strip = reverse . dropWhile isSpace . reverse

    checkInstall _ []  = Right "OK."
    checkInstall _ err = Left  $ errMsg err

    --  Maude versions prior to 2.7.1 are no longer supported,
    --  because the 'get variants' command is incompatible.
    supportedVersions = ["2.7.1", "3.0", "3.1", "3.2.1", "3.2.2", "3.3", "3.3.1", "3.4", "3.5", "3.5.1"]

    errMsg' = errMsg $ "'" ++ maude ++ "' executable not found / does not work"

    errMsg reason = unlines
      [ "WARNING:"
      , ""
      , reason
      , " Please install one of the following versions of Maude: " ++ intercalate ", " supportedVersions
      ]

-- Maude Version
ensureMaudeAndGetVersion :: Arguments -> IO String
ensureMaudeAndGetVersion as = do
  -- Ensure Maude version and get Maude version
  (_, maudeVersion) <- ensureMaude as
  -- Get String for version and put it in the arguments __version__
  getVersionIO maudeVersion

------------------------------------------------------------------------------
-- Static constants for the tamarin-prover
------------------------------------------------------------------------------

-- | Git Version
gitVersion :: String
gitVersion = concat
  [ "Git revision: "
  , $(gitHash)
  , if $(gitDirty) then
      " (with uncommited changes)"
    else ""
  , ", branch: "
  , $(gitBranch)
  ]

-- | Compile Time
compileTime :: String
compileTime = "Compiled at: " ++ $(stringE =<< runIO (show `fmap` Data.Time.getCurrentTime))

-- | Program name
programName :: String
programName = "tamarin-prover"

-- | Version string
versionStr :: String
versionStr = unlines
  [ concat
    [ programName
    , " "
    , showVersion version
    , ", (C) David Basin, Cas Cremers, Jannik Dreier, Simon Meier, Ralf Sasse, Benedikt Schmidt, 2010-2023"
    ]
  , ""
  , "This program comes with ABSOLUTELY NO WARRANTY. It is free software, and you"
  , "are welcome to redistribute it according to its LICENSE, see"
  , "'https://github.com/tamarin-prover/tamarin-prover/blob/master/LICENSE'."
  ]

-- | Line width to use.
lineWidth :: Int
lineWidth = 110

shortLineWidth :: Int
shortLineWidth = 78


------------------------------------------------------------------------------
-- A simple generic representation of arguments
------------------------------------------------------------------------------

-- | A name of an argument.
type ArgKey = String

-- | A value of an argument.
type ArgVal = String

-- | It is most convenient to view arguments just as 'String' based key-value
-- pairs. If there are multiple values for the same key, then the left-most
-- one is preferred.
type Arguments = [(ArgKey,ArgVal)]

-- | Does an argument exist.
argExists :: String -> Arguments -> Bool
argExists a = isJust . findArg a

-- | Find the value(s) corresponding to the given key.
findArg :: MonadPlus m => ArgKey -> Arguments -> m ArgVal
findArg a' as = msum [ pure v | (a,v) <- as, a == a' ]

-- | Find the value corresponding to the given key. Throw an error if no value
-- exists.
getArg :: ArgKey -> Arguments -> ArgVal
getArg a =
  fromMaybe (error $ "getArg: argument '" ++ a ++ "' not found") . findArg a

-- | Add an argument to the from of the list of arguments.
addArg :: ArgKey -> ArgVal -> Arguments -> Arguments
addArg a v = ((a,v):)

-- | Add an argument with the empty string as the value.
addEmptyArg :: String -> Arguments -> Arguments
addEmptyArg a = addArg a ""

-- | Update an argument.
updateArg :: ArgKey -> ArgVal -> Arguments -> Either a Arguments
updateArg a v = Right . addArg a v

-- | Add the help flag.
helpFlag :: Flag Arguments
helpFlag = flagHelpSimple (addEmptyArg "help")

------------------------------------------------------------------------------

-- Modes for using the Tamarin prover
------------------------------------------------------------------------------

-- | A representation of an interaction mode with the Tamarin prover.
data TamarinMode = TamarinMode
  { name        :: String
  , cmdArgsMode :: Mode Arguments
    -- ^ Run is given a reference to the mode. This enables changing the
    -- static information of a mode and keeping the same 'run' function.
    -- We use this for implementing the 'main' mode.
  , run         :: TamarinMode -> Arguments -> IO ()
  , isMainMode  :: Bool
  }

-- | Smart constructor for a 'TamarinMode'.
tamarinMode :: String -> Help
            -> (Mode Arguments -> Mode Arguments) -- ^ Changes to default mode.
            -> (TamarinMode -> Arguments -> IO ())
            -> TamarinMode
tamarinMode name help adaptMode run0 = TamarinMode
  { name = name
  , cmdArgsMode = adaptMode $ Mode
      { modeGroupModes = toGroup []
      , modeNames      = [name]
      , modeValue      = []
      , modeCheck      = updateArg "mode" name
      , modeExpandAt   = False
      , modeReform     = const Nothing-- no reform possibility
      , modeHelp       = help
      , modeHelpSuffix = []
      , modeArgs       = ([], Nothing)   -- no positional arguments
      , modeGroupFlags = toGroup [] -- no flags
      }
  , run        = run
  , isMainMode = False
  }
  where
    run thisMode as
      | argExists "help"    as = helpAndExit thisMode Nothing
      | argExists "version" as = do putStrLn versionStr
                                    versionMaude <- ensureMaudeAndGetVersion as
                                    putStrLn versionMaude
      | otherwise              = run0 thisMode as

-- | Disply help message of a tamarin mode and exit.
helpAndExit :: TamarinMode -> Maybe String -> IO ()
helpAndExit tmode mayMsg = do
  putStrLn $ showText (Wrap lineWidth)
           $ helpText header HelpFormatOne tmode.cmdArgsMode
  -- output example info
  putStrLn $ unlines
    [ separator
    , "To show help for differents commands, type tamarin-prover [Command] --help."
    , separator
    , "See 'https://github.com/tamarin-prover/tamarin-prover/blob/master/README.md'"
    , "for usage instructions and pointers to examples."
    , separator
    ]
  end
  where
    separator = replicate shortLineWidth '-'
    (header, end) = case mayMsg of
        Nothing  -> ([], pure ())
        Just msg -> (["error: " ++ msg], exitFailure)

-- | Main function.
defaultMain :: TamarinMode -> [TamarinMode] -> IO ()
defaultMain firstMode otherModes = do
  as <- processArgs mainMode.cmdArgsMode
  case findArg "mode" as of
    Nothing   -> error "defaultMain: impossible - mode not set"
    Just name -> headNote "defaultMain: impossible - no mode found" $ do
      tmode <- mainMode : (setGroupModes <$> otherModes)
      guard (tmode.name == name)
      pure $ tmode.run tmode as
  where
    mainMode = setGroupModes $ firstMode
      { name        = programName
      , cmdArgsMode = firstMode.cmdArgsMode
          { modeNames = [programName]
          , modeCheck      = updateArg "mode" programName
          , modeGroupFlags = firstMode.cmdArgsMode.modeGroupFlags
              { groupNamed =
                  [ ("About"
                    , [ helpFlag
                      , flagVersion (addEmptyArg "version")
                      ] )
                  ]
              }
          }
      , isMainMode = True
      }

    setGroupModes m = m { cmdArgsMode = m.cmdArgsMode { modeGroupModes } }
    modeGroupModes = toGroup (map (.cmdArgsMode) otherModes)


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Render a pretty-printing document.
renderDoc :: PP.Doc -> String
renderDoc = PP.renderStyle (PP.defaultStyle { PP.lineLength = lineWidth })
