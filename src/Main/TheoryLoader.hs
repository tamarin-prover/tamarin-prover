{-# LANGUAGE DeriveDataTypeable #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Theory loading infrastructure.
module Main.TheoryLoader (
  -- * Static theory loading settings
    intruderVariantsFile
  , theoryLoadFlags

  -- ** Loading open theories
  , loadOpenThy

  -- ** Loading and closing theories
  , loadClosedThy
  , loadClosedWfThy
  , loadClosedThyString

  , closeThy

  ) where

import           Prelude hiding (id, (.))

import           Data.Monoid
import           Data.Char (toLower)
import           Data.Label

import           Control.Basics
import           Control.Category

import           System.Console.CmdArgs.Explicit
import           System.Directory

import           Extension.Prelude

import           Theory
import           Theory.Parser
import           Theory.Wellformedness
import           Theory.AbstractInterpretation (EvaluationStyle(..))

import           Main.Console
import           Main.Environment

import           Paths_tamarin_prover (getDataFileName)


------------------------------------------------------------------------------
-- Theory loading: shared between interactive and batch mode
------------------------------------------------------------------------------

-- | The name of the intruder variants file.
intruderVariantsFile :: FilePath
intruderVariantsFile = "intruder_variants_dh.spthy"


-- | Flags for loading a theory.
theoryLoadFlags :: [Flag Arguments]
theoryLoadFlags = 
  [ flagNone ["prove"] (addEmptyArg "addProofs")
      "Attempt to prove all security properties"

  , flagOpt "dfs" ["stop-on-trace"] (updateArg "stopOnTrace") "DFS|BFS|NONE"
      "How to search for traces (default DFS)"

  , flagOpt "5" ["bound", "b"]   (updateArg "bound") "INT"
      "Bound the depth of the proofs"

  --, flagOpt "" ["intruder","i"] (updateArg "intruderVariants") "FILE"
  --    "Cached intruder rules to use"

  , flagOpt "summary" ["partial-evaluation"] (updateArg "partialEvaluation")
      "SUMMARY|VERBOSE"
      "Partially evaluate multiset rewriting system"

  , flagOpt "" ["defines","D"] (updateArg "defines") "STRING"
      "Define flags for pseudo-preprocessor."
  ]

loadOpenThy :: Arguments -> FilePath -> IO OpenTheory
loadOpenThy = fst . loadThy

loadClosedThy :: Arguments -> FilePath -> IO ClosedTheory
loadClosedThy = uncurry (>=>) . loadThy

loadClosedWfThy :: Arguments -> FilePath -> IO ClosedTheory
loadClosedWfThy as file = do
    thy <- loadOpen file
    case checkWellformedness thy of
      []     -> close thy
      report -> do 
          putStrLn $ "WARNING: ignoring the following errors"
          putStrLn $ renderDoc $ prettyWfErrorReport report
          close thy
      -- report -> error $ renderDoc $ prettyWfErrorReport report
  where
    (loadOpen, close) = loadThy as

loadClosedThyString :: Arguments -> String -> IO ClosedTheory
loadClosedThyString = uncurry (>=>) . loadThyString

-- | Load an open/closed theory from a file.
loadThy :: Arguments -> (FilePath -> IO OpenTheory, OpenTheory -> IO ClosedTheory)
loadThy as = loadGenericThy (parseOpenTheory (defines as)) as 

-- | Load an open/closed theory from a string.
loadThyString :: Arguments -> (String -> IO OpenTheory, OpenTheory -> IO ClosedTheory)
loadThyString as = loadGenericThy loader as
  where
    loader str =
      case parseOpenTheoryString (defines as) str of
        Right thy -> return thy
        Left err -> error $ show err 

-- | The defined pre-processor flags in the argument.
defines :: Arguments -> [String]
defines = findArg "defines"

-- | Load an open/closed theory given a loader function.
loadGenericThy :: (a -> IO OpenTheory)
               -> Arguments 
               -> (a -> IO OpenTheory, OpenTheory -> IO ClosedTheory)
loadGenericThy loader as =
    (loader, (closeThy as) <=< tryAddIntrVariants)
  where
    -- intruder variants
    --------------------
    tryAddIntrVariants :: OpenTheory -> IO OpenTheory
    tryAddIntrVariants thy0 = do
      let msig = get (sigpMaudeSig . thySignature) thy0
          thy  = addIntrRuleACs (subtermIntruderRules msig ++ specialIntruderRules) thy0
      if (enableDH msig) then
         do variantsFile <- getDataFileName intruderVariantsFile
            ifM (doesFileExist variantsFile)
                (do intrVariants <- parseIntruderRulesDH variantsFile
                    return $ addIntrRuleACs intrVariants thy
                )
                (error $ "could not find intruder message deduction theory '" 
                           ++ variantsFile ++ "'")
         else return thy

-- | Close a theory according to arguments.
closeThy :: Arguments -> OpenTheory -> IO ClosedTheory
closeThy as = 
      fmap (proveTheory prover . partialEvaluation) 
    . closeTheory (maudePath as)
    -- FIXME: wf-check is at the wrong position here. Needs to be more
    -- fine-grained.
    . wfCheck 
  where
    -- handles to relevant arguments
    --------------------------------
    proofBound      = read <$> findArg "bound" as
    requireProofs   = argExists "addProofs" as

    stopOnTrace :: Maybe String
    stopOnTrace = findArg "stopOnTrace" as

    -- apply partial application
    ----------------------------
    partialEvaluation = case map toLower <$> findArg "partialEvaluation" as of
      Just "verbose" -> applyPartialEvaluation Tracing
      Just _         -> applyPartialEvaluation Summary
      _              -> id

    -- wellformedness check
    -----------------------
    wfCheck :: OpenTheory -> OpenTheory
    wfCheck thy = 
      noteWellformedness
        (checkWellformedness thy) thy

    -- protocol transformation
    --------------------------
    prover :: Prover
    prover 
       | requireProofs = cutAttack $ maybe id boundProver proofBound autoProver
       | otherwise     = mempty
       where 
         cutAttack = mapProverProof $ case map toLower <$> stopOnTrace of
           Nothing     -> cutOnAttackDFS
           Just "dfs"  -> cutOnAttackDFS
           Just "none" -> id
           Just "bfs"  -> cutOnAttackBFS
           Just other  -> error $ "unknown stop-on-trace method: " ++ other

