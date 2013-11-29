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
import           Term.Rewriting.Norm
import           Text.PrettyPrint.Class (render)
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

data Cmd =
    Variants LNTerm
  | Unify LNTerm LNTerm
  | Match LNTerm LNTerm
  | Norm LNTerm
  | Quit

-- | Read-eval-print mode for computing variants.
run :: TamarinMode -> Arguments -> IO ()
run _thisMode as = do
    _ <- ensureMaude as
    sig <- evalSignature msetMaudeSig -- only AC symbol +
    maudeHnd <- startMaude (maudePath as) sig
    evalCmds maudeHnd sig
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

    parseCmd sig = do
      setState sig
      cmd <- asum
        [ Variants <$> (symbol "variants" *> multterm llit)
        , Norm <$> (symbol "norm" *> multterm llit)
        , Unify <$> (symbol "unify" *> multterm llit) <*> (equalSign *> multterm llit)
        , Match <$> (symbol "match" *> multterm llit) <*> (equalSign *> multterm llit)
        , pure Quit <* dot
        ]
      eof
      return cmd
      
    evalCmds hnd sig = do
      putStr "> " >> hFlush stdout
      ps <- getLine
      case parseString "<unknown source>" (parseCmd sig) ps of
        Left  e -> putStrLn ("parsing failed: "++(show e)) >> evalCmds hnd sig
        Right Quit -> putStrLn "Finished."
        Right (Variants t) -> do
          putStrLn $ "variants of " ++ppTerm t++":"
          let substs = computeVariants t `runReader` hnd
          forM_ substs $ \s ->
            putStrLn $ "{"++ppSubst (substToListVFresh s)++"}"
          evalCmds hnd sig
        Right (Norm t) -> do
          putStrLn $ "Norm :" ++ppTerm t
          let t' = norm' t `runReader` hnd
          putStrLn $ ppTerm t'
          evalCmds hnd sig
        Right (Unify t t') -> do
          putStrLn $ "unify " ++ppTerm t++" with "++ppTerm t'
          let substs = unifyLNTerm [Equal t t'] `runReader` hnd
          forM_ substs $ \s ->
            putStrLn $ "{"++ppSubst (substToListVFresh s)++"}"
          evalCmds hnd sig
        Right (Match t p) -> do
          putStrLn $ "match term " ++ppTerm t++" with pattern "++ppTerm p
          let substs = solveMatchLNTerm (t `matchWith` p) `runReader` hnd
          forM_ substs $ \s ->
            putStrLn $ "{"++ppSubst (substToList s)++"}"

          evalCmds hnd sig

    ppTerm = render . prettyLNTerm
    ppSubst sl = intercalate ", "
                 $ map (\(v,t) -> ppTerm t++"/"++render (prettyLVar v))
                 $ sl

