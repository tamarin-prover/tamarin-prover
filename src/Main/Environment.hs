{-# LANGUAGE DeriveDataTypeable #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Helpers for inspecting the environment of the tamarin prover.
module Main.Environment where

import           Data.List
import           Data.Char (isSpace, toLower)
import           Data.Maybe (fromMaybe)

import           Control.Monad
import           Control.Exception as E

import           System.Console.CmdArgs.Explicit
import           System.Exit
import           System.Environment
import           System.IO
import           System.Process

import           Paths_tamarin_prover

import           Main.Console

------------------------------------------------------------------------------
-- Retrieving the paths to required tools.
------------------------------------------------------------------------------

-- | Flags for handing over the path to the maude and 'dot' tool.
toolFlags :: [Flag Arguments]
toolFlags = 
  [ flagOpt "dot" ["with-dot"] (updateArg "withDot") "FILE" "Path to GraphViz 'dot' tool"
  , flagOpt "maude" ["with-maude"] (updateArg "withMaude") "FILE"  "Path to 'maude' rewriting tool"
  ]

-- | Path to maude tool
maudePath :: Arguments -> FilePath
maudePath = fromMaybe "maude" . findArg "withMaude"

-- | Path to dot tool
dotPath :: Arguments -> FilePath
dotPath = fromMaybe "dot" . findArg "withDot"


------------------------------------------------------------------------------
-- Inspecting the environment
------------------------------------------------------------------------------

-- | Get the string constituting the command line.
getCommandLine :: IO String
getCommandLine = do
  arguments <- getArgs
  return . concat . intersperse " " $ programName : arguments

-- | Read the cpu info using a call to cat /proc/cpuinfo
getCpuModel :: IO String
getCpuModel = 
  handle handler $ do
    (_, info, _) <- readProcessWithExitCode "cat" ["/proc/cpuinfo"] []
    return $ maybe errMsg
               (("Linux running on an "++) . drop 2 . dropWhile (/=':'))
               (find (isPrefixOf "model name") $ lines info)
  where
  errMsg = "could not extract CPU model"
  handler :: IOException -> IO String
  handler _ = return errMsg

-- | Get the path to the Html template file.
getHtmlTemplate :: IO FilePath
getHtmlTemplate = getDataFileName "HTML_TEMPLATE"


-- | Build the command line corresponding to a program arguments tuple.
commandLine :: String -> [String] -> String
commandLine prog args = concat $ intersperse " " $ prog : args

-- | Test if a process is executable and check its response. This is used to
-- determine the versions and capabilities of tools that we depend on.
testProcess :: (String -> String -> Either String String) 
                              -- ^ Analysis of stdout, stderr. Use 'Left' to report error.
            -> String         -- ^ Test description to display.
            -> FilePath       -- ^ Process to start
            -> [String]       -- ^ Arguments
            -> String         -- ^ Stdin
            -> IO Bool        -- ^ True, if test was successful
testProcess check testName prog args inp = do
    putStr testName
    hFlush stdout
    handle handler $ do
        (exitCode, out, err) <- readProcessWithExitCode prog args inp
        let errMsg reason = do
                putStrLn reason
                putStrLn $ " command: " ++ commandLine prog args
                putStrLn $ " stdin:   " ++ inp
                putStrLn $ " stdout:  " ++ out
                putStrLn $ " stderr:  " ++ err
                return False

        case exitCode of
            ExitFailure code -> errMsg $ "failed with exit code " ++ show code
            ExitSuccess      -> 
              case check out err of
                Left msg     -> errMsg msg
                Right msg    -> do putStrLn msg
                                   return True
  where
    handler :: IOException -> IO Bool
    handler _ = do putStrLn "caught exception while executing:"
                   putStrLn $ commandLine prog args
                   putStrLn $ "with input: " ++ inp
                   return False

-- | Ensure a suitable version of the Graphviz dot tool is installed.
ensureGraphVizDot :: Arguments -> IO ()
ensureGraphVizDot as = do
    putStrLn $ "GraphViz tool: '" ++ dot ++ "'"
    success <- testProcess check " checking version: " dot ["-V"] ""
    unless success $ putStrLn errMsg
  where
    dot = dotPath as
    check _ err
      | "graphviz" `isInfixOf` map toLower err = Right $ init err ++ ". OK."
      | otherwise                              = Left  $ errMsg
    errMsg = unlines
      [ "WARNING:"
      , ""
      , " The dot tool seems not to be provided by Graphviz."
      , " Graph generation might not work."
      , " Please download an official version from:"
      , "         http://www.graphviz.org/"
      ]

-- | Ensure a suitable version of Maude is installed.
ensureMaude :: Arguments -> IO ()
ensureMaude as = do
    putStrLn $ "maude tool: '" ++ maude ++ "'"
    success <- testProcess check " checking version: " maude ["--version"] ""
    unless success $ putStrLn $ errMsg "tool not found / does not work"
  where
    maude = maudePath as
    check out _ 
      | filter (not . isSpace) out == "2.6" = Right "2.6. OK."
      | otherwise                           = Left  $ errMsg $
          " 'maude --version' returned wrong verison '" ++ out ++ "'"

    errMsg reason = unlines
          [ "WARNING:"
          , ""
          , reason
          , " " ++ programName ++ " will likely not work."
          , " Please download 'Core Maude 2.6' from:"
          , "    http://maude.cs.uiuc.edu/download/"
          ]
