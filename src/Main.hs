{-# LANGUAGE CPP #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
--
-- Main module for the Tamarin prover without a GUI
module Main where

#ifdef NO_GUI
import qualified Main_NoGui as M
#else
import qualified Main_Full as M
#endif

main :: IO ()
main = M.main
