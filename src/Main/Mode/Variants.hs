{-# LANGUAGE DeriveDataTypeable #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Main module for the Tamarin prover.
module Main.Mode.Variants (
    variantsMode
  ) where

import           Control.Monad.Reader

import           System.Console.CmdArgs.Explicit as CmdArgs

import           Theory

import           Main.Console
import           Main.Environment
import           Term.Narrowing.Variants
import           Text.PrettyPrint.Class
import           Data.List
import           Theory.Text.Parser
import           Theory.Text.Parser.Token
import           Text.Parsec                hiding ((<|>))

import           System.IO
import           Control.Applicative
import           Data.Foldable (asum)

variantsMode :: TamarinMode
variantsMode = tamarinMode
    "variants"
    "Compute variants and perform unification."
    setupFlags
    run
  where
    setupFlags defaultMode = defaultMode
      { modeArgs       = ([], Nothing )  -- no positional argumants
      , modeGroupFlags = Group outputFlags [] [("About", [helpFlag])]
      }

    outputFlags =
      [ -- flagOpt "" ["Input","I"] (updateArg "outDir") "DIR"  "Output directory"
      ]

-- | Read-eval-print mode for computing variants.
run :: TamarinMode -> Arguments -> IO ()
run _thisMode as = do
    _ <- ensureMaude as
    sig <- evalSignature msetMaudeSig -- only AC symbol +
    maudeHnd <- startMaude (maudePath as) sig
    evalVariants maudeHnd sig
  where
    evalSignature sig = do
      putStr "# " >> hFlush stdout
      ps <- getLine
      let parser = (setState sig >> asum [ try functions, try equations] >> eof >> getState)
      case (ps, parseString "<unknown source>" parser ps) of
        (".",_ )       -> putStrLn "Finished." >> return sig
        (_, Left  e)   -> putStrLn ("Parsing failed: "++show e++".") >> evalSignature sig
        (_, Right sig') -> do
          putStrLn $ "added "++ ps
          evalSignature sig'
      
    evalVariants hnd sig = do
      putStr "> " >> hFlush stdout
      ps <- getLine
      case (ps, parseString "<unknown source>" (setState sig *> multterm llit <* eof) ps) of
        (".",_)     -> putStrLn "Finished."
        (_,Left  e) -> putStrLn ("parsing failed: "++(show e)) >> evalVariants hnd sig
        (_,Right t) -> do
          putStrLn $ "variants of " ++(render $ prettyLNTerm t)++":"
          let substs = computeVariants t `runReader` hnd
          forM_ substs $ \s ->
            putStrLn $ "{"++ppSubst s++"}"
          evalVariants hnd sig

    ppSubst s = intercalate ", "
                 $ map (\(v,t) -> (render (prettyLNTerm t))++"/"++render (prettyLVar v))
                 $ substToListVFresh s

