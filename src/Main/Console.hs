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
  ) where

import           Data.Maybe
import           Data.Version                    (showVersion)
import           Data.Time
import           Safe

import           Control.Monad

import           System.Console.CmdArgs.Explicit
import           System.Console.CmdArgs.Text
import           System.Exit

import qualified Text.PrettyPrint.Class          as PP

import           Paths_tamarin_prover (version)

import           Language.Haskell.TH
import           Development.GitRev

------------------------------------------------------------------------------
-- Static constants for the tamarin-prover
------------------------------------------------------------------------------

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
    , ", (C) David Basin, Cas Cremers, Jannik Dreier, Simon Meier, Ralf Sasse, Benedikt Schmidt, ETH Zurich 2010-2017"
    ]
  , concat
    [ "Git revision: "
    , $(gitHash)
    , case $(gitDirty) of
          True  -> " (with uncommited changes)"
          False -> ""
    , ", branch: "
    , $(gitBranch)
    ]
  , concat
    [ "Compiled at: "
    , $(stringE =<< runIO (show `fmap` Data.Time.getCurrentTime))
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
      | argExists "version" as = putStrLn versionStr
      | otherwise              = run0 thisMode as

-- | Disply help message of a tamarin mode and exit.
helpAndExit :: TamarinMode -> Maybe String -> IO ()
helpAndExit tmode mayMsg = do
    putStrLn $ showText (Wrap lineWidth)
             $ helpText header HelpFormatOne (tmCmdArgsMode tmode)
    -- output example info
    when (tmIsMainMode tmode) $ do
      putStrLn $ unlines
        [ separator
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
          tmode <- (mainMode : otherModes)
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


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Render a pretty-printing document.
renderDoc :: PP.Doc -> String
renderDoc = PP.renderStyle (PP.defaultStyle { PP.lineLength = lineWidth })
