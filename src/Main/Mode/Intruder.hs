{-# LANGUAGE DeriveDataTypeable #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Main module for the tamarin prover.
module Main.Mode.Intruder (
    intruderMode
  ) where

import Data.Maybe

import Control.Basics
import Control.Monad.Reader

import System.Console.CmdArgs.Explicit as CmdArgs
import System.FilePath
import System.IO

import Theory

import Main.Console
import Main.Environment
import Main.TheoryLoader (intruderVariantsFile)
import Main.Utils


intruderMode :: TamarinMode
intruderMode = tamarinMode 
    "variants" 
    "Compute the variants of the intruder rules for DH-exponentiation."
    setupFlags
    run
  where
    setupFlags defaultMode = defaultMode
      { modeArgs       = ([], Nothing )  -- no positional argumants
      , modeGroupFlags = Group outputFlags [] [("About", [helpFlag])]
      }

    outputFlags = 
      [ flagOpt "" ["output","o"] (updateArg "outFile") "FILE" "Output file"
      , flagOpt "" ["Output","O"] (updateArg "outDir") "DIR"  "Output directory"
      ]

-- | Compute the intruder variants.
run :: TamarinMode -> Arguments -> IO ()
run _thisMode as = do
    _ <- ensureMaude as
    hnd <- startMaude (maudePath as) dhMaudeSig
    let rules       = dhIntruderRules `runReader` hnd
        rulesString = renderDoc $ prettyIntruderVariants rules
    putStrLn rulesString
    writeRules rulesString
  where
    -- output generation
    --------------------

    writeRules rulesString = case optOutPath of
      Just outPath -> writeFileWithDirs outPath rulesString
      Nothing      -> return ()

    -- Output file name, if output is desired.
    optOutPath :: Maybe FilePath
    optOutPath = 
      do outFile <- findArg "outFile" as
         guard (outFile /= "")
         return outFile
      <|>
      do outDir <- findArg "outDir" as
         return $ outDir </> intruderVariantsFile 
