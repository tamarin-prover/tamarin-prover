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
  if argExists "withJson" as
     then ("json", (fromMaybe "json" . findArg "withJson") as)
     else ("dot", (fromMaybe "dot" . findArg "withDot") as)


------------------------------------------------------------------------------
-- Inspecting the environment
------------------------------------------------------------------------------

-- | Get the string constituting the command line.
getCommandLine :: IO String
getCommandLine = do
  arguments <- getArgs
  return . unwords $ programName : arguments

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
commandLine prog args = unwords $ prog : args

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
  -> Bool           -- ^ Whether to ignore ExitFailure
  -> Bool           -- ^ Whether Maude is being tested - hard fail for exceptions on Maude.
  -> IO Bool        -- ^ True, if test was successful
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
                return False

        let check' = case check out err of
                      Left msg     -> errMsg msg
                      Right msg    -> do putStrLn msg
                                         return True

        if not ignoreExitCode
           then case exitCode of
                  ExitFailure code -> errMsg $
                    "failed with exit code " ++ show code ++ "\n\n" ++ defaultMsg
                  ExitSuccess      -> check'
           else check'

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
    dotExists <- testProcess (check "graphviz" "") errMsg1 " checking version: " dot ["-V"] "" False False
    if dotExists 
       then testProcess (check "png" "OK.") errMsg2 " checking PNG support: " dot ["-T?"] "" True False
       else return dotExists
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
ensureGraphCommand :: Arguments -> IO Bool
ensureGraphCommand as = do
    putStrLn $ "Graph rendering command: " ++ cmd
    testProcess check errMsg "Checking availablity ..." "which" [cmd] "" False False
  where
    cmd = snd $ graphPath as
    check _ err
      | err == ""  = Right $ " OK."
      | otherwise  = Left  $ errMsg
    errMsg = unlines
      [ "Command not found" ]

-- | Ensure a suitable version of Maude is installed.
ensureMaude :: Arguments -> IO Bool
ensureMaude as = do
    putStrLn $ "maude tool: '" ++ maude ++ "'"
    t1 <- testProcess checkVersion errMsg' " checking version: " maude ["--version"] "" False True
    t2 <- testProcess checkInstall errMsg' " checking installation: "   maude [] "quit\n" False True
    return (t1 && t2)
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
    supportedVersions = ["2.7.1", "3.0", "3.1", "3.2.1"]

    errMsg' = errMsg $ "'" ++ maude ++ "' executable not found / does not work"

    errMsg reason = unlines
          [ "WARNING:"
          , ""
          , reason
          , " Please install one of the following versions of Maude: " ++ intercalate ", " supportedVersions
          ]
