-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Support for interaction with the console: argument parsing.

{-# LANGUAGE TemplateHaskell #-}

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

import           Data.Maybe
import           Data.Version                    (showVersion)
import           Data.Time
import           Data.List
import           Data.Char                       (isSpace, toLower)
import           Safe

import           Control.Monad
import           Control.Exception               as E

import           System.Console.CmdArgs.Explicit
import           System.Console.CmdArgs.Text
import           System.Exit
import           System.FilePath
import           System.IO
import           System.Process

import qualified Text.PrettyPrint.Class          as PP

import           Paths_tamarin_prover (version)

import           Language.Haskell.TH
import           Development.GitRev

------------------------------------------------------------------------------
-- Maude version functions - previously in Environment.hs
------------------------------------------------------------------------------

-- | Path to maude tool
maudePath :: Arguments -> FilePath
maudePath = fromMaybe "maude" . findArg "withMaude"

getVersionIO :: String -> IO String
getVersionIO maudeVersion = do
              let tamarinVersion = showVersion version
              let versionExport = "Generated from:\nTamarin version " ++ tamarinVersion
                        ++  "\nMaude version " ++ maudeVersion ++ gitVersion
                        ++ "\n" ++ compileTime
              return versionExport

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
    putStr testName
    hFlush stdout
    handle handler $ do
        (exitCode, out, err) <- readProcessWithExitCode prog args inp
        let errMsg reason = do
                putStrLn reason
                putStrLn $ "Detailed results from testing '" ++ prog ++ "'"
                putStrLn $ " command: " ++ commandLine prog args
                putStrLn $ " stdin:   " ++ inp
                putStrLn $ " stdout:  " ++ out
                putStrLn $ " stderr:  " ++ err
                return Nothing

        let check' = case check out err of
                      Left msg     -> errMsg msg
                      Right msg    -> do putStrLn msg
                                         return (Just out)

        if not ignoreExitCode
           then case exitCode of
                  ExitFailure code -> errMsg $
                    "failed with exit code " ++ show code ++ "\n\n" ++ defaultMsg
                  ExitSuccess      -> check'
           else check'

  where
    handler :: IOException -> IO (Maybe String)
    handler _ = do putStrLn "caught exception while executing:"
                   putStrLn $ commandLine prog args
                   putStrLn $ "with input: " ++ inp
                   if maudeTest then
                     error "Maude is not installed. Ensure Maude is available and on the path."
                     else putStrLn ""
                   return Nothing

ensureMaude :: Arguments -> IO (Maybe String)
ensureMaude as = do
    putStrLn $ "maude tool: '" ++ maude ++ "'"
    t1 <- testProcess checkVersion errMsg' " checking version: " maude ["--version"] "" False True
    t2 <- testProcess checkInstall errMsg' " checking installation: "   maude [] "quit\n" False True
    return (if isNothing t1 || isNothing t2 then Nothing else t1)
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
    supportedVersions = ["2.7.1", "3.0", "3.1", "3.2.1", "3.2.2"]

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
          maybeMaudeVersion <- ensureMaude as
          let maudeVersion = fromMaybe "Nothing" maybeMaudeVersion
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
compileTime = concat
    [ "Compiled at: "
    , $(stringE =<< runIO (show `fmap` Data.Time.getCurrentTime))
    ]

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
    , ", (C) David Basin, Cas Cremers, Jannik Dreier, Simon Meier, Ralf Sasse, Benedikt Schmidt, ETH Zurich 2010-2020"
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
findArg a' as = msum [ return v | (a,v) <- as, a == a' ]

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
       { tmName        :: String
       , tmCmdArgsMode :: Mode Arguments
         -- ^ Run is given a reference to the mode. This enables changing the
         -- static information of a mode and keeping the same 'run' function.
         -- We use this for implementing the 'main' mode.
       , tmRun         :: TamarinMode -> Arguments -> IO ()
       , tmIsMainMode  :: Bool
       }

-- | Smart constructor for a 'TamarinMode'.
tamarinMode :: String -> Help
            -> (Mode Arguments -> Mode Arguments) -- ^ Changes to default mode.
            -> (TamarinMode -> Arguments -> IO ())
            -> TamarinMode
tamarinMode name help adaptMode run0 = TamarinMode
  { tmName = name
  , tmCmdArgsMode = adaptMode $ Mode
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
  , tmRun        = run
  , tmIsMainMode = False
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
             $ helpText header HelpFormatOne (tmCmdArgsMode tmode)
    -- output example info
    putStrLn $ unlines
        [ separator
        , "To show help for differents commands, type tamarin-prover [Command] --help."
        , "See 'https://github.com/tamarin-prover/tamarin-prover/blob/master/README.md'"
        , "for usage instructions and pointers to examples."
        , separator
        ]
    end
  where
    separator = replicate shortLineWidth '-'
    (header, end) = case mayMsg of
        Nothing  -> ([], return ())
        Just msg -> (["error: " ++ msg], exitFailure)

-- | Main function.
defaultMain :: TamarinMode -> [TamarinMode] -> IO ()
defaultMain firstMode otherModes = do
    as <- processArgs $ tmCmdArgsMode mainMode
    case findArg "mode" as of
      Nothing   -> error $ "defaultMain: impossible - mode not set"
      Just name -> headNote "defaultMain: impossible - no mode found" $ do
          allModes <- [interMode:intruderMode:testMode:[]]
          tmode <- (mainMode : allModes)
          guard (tmName tmode == name)
          return $ tmRun tmode tmode as
  where
    mainMode = firstMode
      { tmName        = programName
      , tmCmdArgsMode = (tmCmdArgsMode firstMode)
          { modeNames = [programName]
          , modeCheck      = updateArg "mode" programName
          , modeGroupModes = toGroup (map tmCmdArgsMode $ otherModes)
          , modeGroupFlags = (modeGroupFlags $ tmCmdArgsMode firstMode)
              { groupNamed =
                  [ ("About"
                    , [ helpFlag
                      , flagVersion (addEmptyArg "version")
                      ] )
                  ]
              }
          }
      , tmIsMainMode = True
      }
    interMode = (head otherModes)
      {
        tmCmdArgsMode = (tmCmdArgsMode $ head otherModes)
        {
          modeGroupModes = toGroup (map tmCmdArgsMode $ firstMode : (tail otherModes))
        }
      }
    intruderMode = (otherModes !! 1)
      {
        tmCmdArgsMode = (tmCmdArgsMode $ otherModes !! 1)
        {
          modeGroupModes = toGroup (map tmCmdArgsMode $ firstMode : (head otherModes : last otherModes : []))
        }
      }
    testMode = (otherModes !! 2)
      {
        tmCmdArgsMode = (tmCmdArgsMode $ otherModes !! 2)
        {
          modeGroupModes = toGroup (map tmCmdArgsMode $ firstMode : (init otherModes))
        }
      }


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Render a pretty-printing document.
renderDoc :: PP.Doc -> String
renderDoc = PP.renderStyle (PP.defaultStyle { PP.lineLength = lineWidth })
