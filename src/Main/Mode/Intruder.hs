{-# LANGUAGE DeriveDataTypeable #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Main module for the Tamarin prover.
module Main.Mode.Intruder (
    intruderMode
  ) where

import           Control.Monad.Reader

import           System.Console.CmdArgs.Explicit as CmdArgs
import           System.FilePath

import           Theory

import           Theory.Tools.IntruderRules

import           Main.Console
import           Main.Environment
import           Main.TheoryLoader               (dhIntruderVariantsFile,bpIntruderVariantsFile)
import           Main.Utils


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
      [ flagOpt "" ["Output","O"] (updateArg "outDir") "DIR"  "Output directory"
      ]

-- | Compute the intruder variants.
run :: TamarinMode -> Arguments -> IO ()
run _thisMode as = do
    _ <- ensureMaude as
    dhHnd <- startMaude (maudePath as) dhMaudeSig
    bpHnd <- startMaude (maudePath as) bpMaudeSig
    let dhRules    = (dhIntruderRules False) `runReader` dhHnd
        bpRules    = (bpIntruderRules False) `runReader` bpHnd
        dhS = renderDoc . prettyIntruderVariants $ dhRules
        bpS = renderDoc . prettyIntruderVariants $ bpRules

    putStrLn (dhS++bpS)
    writeRules dhS bpS
  where
    -- output generation
    --------------------

    writeRules dhS bpS = case findArg "outDir" as of
      Just outDir ->
          do writeFileWithDirs (outDir </> dhIntruderVariantsFile) dhS
             writeFileWithDirs (outDir </> bpIntruderVariantsFile) bpS
      Nothing     -> return ()
