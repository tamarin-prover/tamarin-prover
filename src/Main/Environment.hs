{-# LANGUAGE DeriveDataTypeable #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Helpers for inspecting the environment of the Tamarin prover.
module Main.Environment where

import           Data.Char                       (isSpace, toLower)
import           Data.List
import           Data.Maybe                      (fromMaybe)

import           Control.Exception               as E

import           System.Console.CmdArgs.Explicit
import           System.Environment
import           System.Exit
import           System.IO
import           System.Process

import           Main.Console


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

-- | Path to maude tool
maudePath :: Arguments -> FilePath
maudePath = fromMaybe "maude" . findArg "withMaude"

-- | Path to dot tool
dotPath :: Arguments -> FilePath
dotPath = fromMaybe "dot" . findArg "withDot"

-- | Path to dot or json tool
graphPath :: Arguments -> (String, FilePath)
graphPath as = 
  if (argExists "withJson" as) then ("json", (fromMaybe "json" . findArg "withJson") as)
                               else ("dot", (fromMaybe "dot" . findArg "withDot") as)


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

-- | Build the command line corresponding to a program arguments tuple.
commandLine :: String -> [String] -> String
commandLine prog args = concat $ intersperse " " $ prog : args

-- | Test if a process is executable and check its response. This is used to
-- determine the versions and capabilities of tools that we depend on.
testProcess
  :: (String -> String -> Either String String)
     -- ^ Analysis of stdout, stderr. Use 'Left' to report error.
  -> String         -- ^ Default error message to display to the user.
  -> String         -- ^ Test description to display.
  -> FilePath       -- ^ Process to start
  -> [String]       -- ^ Arguments
  -> String         -- ^ Stdin
  -> Bool           -- ^ Whether Maude is being tested - hard fail for exceptions on Maude.
  -> IO Bool        -- ^ True, if test was successful
testProcess check defaultMsg testName prog args inp maudeTest = do
    putStr testName
    hFlush stdout
    handle handler $ do
        (exitCode, out, err) <- readProcessWithExitCode prog args inp
        let errMsg reason = do
                putStrLn reason
                putStrLn $ "Detailed results from testing '" ++ prog ++ "'"
                putStrLn $ " command: " ++ commandLine prog args
                putStrLn $ " stdin:   " ++ inp
                putStrLn $ " stdout:\n" ++ out
                putStrLn $ " stderr:\n" ++ err
                return False

        case exitCode of
            ExitFailure code -> errMsg $
              "failed with exit code " ++ show code ++ "\n\n" ++ defaultMsg
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
                   if maudeTest then
                     error "Maude is not installed. Ensure Maude is available and on the path."
                     else putStrLn ""
                   return False

-- | Ensure a suitable version of the Graphviz dot tool is installed.
ensureGraphVizDot :: Arguments -> IO Bool
ensureGraphVizDot as = do
    putStrLn $ "GraphViz tool: '" ++ dot ++ "'"
    testProcess check errMsg " checking version: " dot ["-V"] "" False
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

-- | Check whether a the graph rendering command supplied is pointing to an existing file
ensureGraphCommand :: Arguments -> IO Bool
ensureGraphCommand as = do
    putStrLn $ "Graph rendering command: " ++ cmd
    testProcess check errMsg "Checking availablity ..." "which" [cmd] "" False
  where
    cmd = snd $ graphPath as
    check _ err
      | err == ""  = Right $ " OK."
      | otherwise  = Left  $ errMsg
    errMsg = unlines
      [ "Command not found" ]
      
-- | Check whether Sapic is installed
ensureSapic :: Arguments -> IO Bool
ensureSapic _ = do
    putStrLn $ "SAPIC tool: '" ++ cmd ++ "'"
    testProcess check errMsg "Checking availablity ..." "which" [cmd] "" False
  where
    cmd = "sapic"
    check _ err
      | err == ""  = Right $ " OK."
      | otherwise  = Left  $ errMsg
    errMsg = unlines
      [ "SAPIC not found."
      , "SAPIC files will not be supported." ]

-- | Ensure a suitable version of Maude is installed.
ensureMaude :: Arguments -> IO Bool
ensureMaude as = do
    putStrLn $ "maude tool: '" ++ maude ++ "'"
    t1 <- testProcess checkVersion errMsg' " checking version: " maude ["--version"] "" True
    t2 <- testProcess checkInstall errMsg' " checking installation: "   maude [] "quit\n" True
    return (t1 && t2)
  where
    maude = maudePath as
    checkVersion out _
      | filter (not . isSpace) out == "2.6"   = Right "2.6. OK."
      | filter (not . isSpace) out == "2.7"   = Right "2.7. OK."
      | filter (not . isSpace) out == "2.7.1" = Right "2.7.1. OK."
      | otherwise                           = Left  $ errMsg $
          " 'maude --version' returned wrong version '" ++ out ++ "'"

    checkInstall _ []  = Right "OK."
    checkInstall _ err = Left  $ errMsg err

    errMsg' = errMsg $ "'" ++ maude ++ "' executable not found / does not work"
    errMsg reason = unlines
          [ "WARNING:"
          , ""
          , reason
          , " " ++ programName ++ " will likely not work."
          , " Please download 'Core Maude 2.7.1' (or 2.6) from:"
          , "    http://maude.cs.uiuc.edu/download/"
          , " Note that 'prelude.maude' must be in the same directory as the 'maude' executable."
          ]
