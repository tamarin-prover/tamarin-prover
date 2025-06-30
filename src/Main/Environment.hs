-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Helpers for inspecting the environment of the Tamarin prover.
module Main.Environment where

import Data.Char (toLower)
import Data.List
import Data.Maybe (fromMaybe, isJust)

import Control.Exception as E

import System.Console.CmdArgs.Explicit
import System.Environment
import System.IO
import System.Process

import Main.Console
import Web.Types (OutputCommand(..), OutputFormat(..))

------------------------------------------------------------------------------
-- Retrieving the paths to required tools.
------------------------------------------------------------------------------

-- | Flags for handing over the path to the maude and graph rendering tool (dot or json).
toolFlags :: [Flag Arguments]
toolFlags =
  [ flagOpt "dot" ["with-dot"] (updateArg "withDot") "FILE" "Path to GraphViz 'dot' tool"
  , flagOpt "json" ["with-json"] (updateArg "withJson") "FILE" "Path to JSON rendering tool (not working with --diff)"
  , flagOpt "maude" ["with-maude"] (updateArg "withMaude") "FILE" "Path to 'maude' rewriting tool"
  ]

-- | Path to dot tool
dotPath :: Arguments -> FilePath
dotPath = fromMaybe "dot" . findArg "withDot"

-- | Path to dot or json tool
readOutputCommand :: Arguments -> OutputCommand
readOutputCommand as =
  if argExists "withJson" as
     then OutputCommand OutJSON $ (fromMaybe "json" . findArg "withJson") as
     else OutputCommand OutDot $ (fromMaybe "dot" . findArg "withDot") as


------------------------------------------------------------------------------
-- Inspecting the environment
------------------------------------------------------------------------------

-- | Get the string constituting the command line.
getCommandLine :: IO String
getCommandLine = do
  arguments <- getArgs
  pure . unwords $ programName : arguments

-- | Read the cpu info using a call to cat /proc/cpuinfo
getCpuModel :: IO String
getCpuModel =
  handle handler $ do
    (_, info, _) <- readProcessWithExitCode "cat" ["/proc/cpuinfo"] []
    pure $ maybe errMsg
             (("Linux running on an "++) . drop 2 . dropWhile (/=':'))
             (find (isPrefixOf "model name") $ lines info)
  where
  errMsg = "could not extract CPU model"
  handler :: IOException -> IO String
  handler _ = pure errMsg

-- | Ensure a suitable version of the Graphviz dot tool is installed.
ensureGraphVizDot :: Arguments -> IO (Maybe String)
ensureGraphVizDot as = do
  hPutStrLn stderr $ "GraphViz tool: '" ++ dot ++ "'"
  dotExists <- testProcess (check "graphviz" "") errMsg1 " checking version: " dot ["-V"] "" False False
  if isJust dotExists
     then testProcess (check "png" "OK.") errMsg2 " checking PNG support: " dot ["-T?"] "" True False
     else pure dotExists
  where
    dot = dotPath as
    check str okMsg _ err
      | str `isInfixOf` err' = Right msg
      | otherwise = Left "Error."
      where err' = map toLower err
            msg  = if null okMsg
                      then init err' ++ ". OK."
                      else okMsg
    errMsg1 = unlines
      [ "WARNING:"
      , ""
      , " The dot tool seems not to be provided by Graphviz."
      , " Graph generation might not work."
      , " Please download an official version from:"
      , "         http://www.graphviz.org/"
      ]
    errMsg2 = unlines
      [ "WARNING:"
      , ""
      , " The dot tool does not seem to support PNG."
      , " Graph generation might not work."
      ]

-- | Check whether a the graph rendering command supplied is pointing to an existing file
ensureGraphCommand :: Arguments -> IO (Maybe String)
ensureGraphCommand as = do
  hPutStrLn stderr $ "Graph rendering command: " ++ cmd
  testProcess check errMsg "Checking availablity ..." "which" [cmd] "" False False
  where
    cmd = ocmd.ocGraphCommand
    ocmd = readOutputCommand as
    check _ err
      | err == ""  = Right " OK."
      | otherwise  = Left  errMsg
    errMsg = unlines
      [ "Command not found" ]
