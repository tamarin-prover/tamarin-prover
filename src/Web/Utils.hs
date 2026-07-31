{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE QuasiQuotes   #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{- |
Module      :  Web.Utils
Description :  Utility functions for abbreviating long terms in a constraint system.
Copyright   :  (c) 2019 Hizbullah Abdul Aziz Jabbar
License     :  GPL-3

Maintainer  :  Hizbullah Abdul Aziz Jabbar <archbung@gmail.com>
Stability   :  experimental
Portability :  non-portable
-}
module Web.Utils
  ( abbrev
  )
where

import Control.Monad.State (State)
import qualified Control.Monad.State as State
import qualified Data.ByteString.Char8 as BC

import Extension.Data.Label (get, modify)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Theory.Model
import Theory.Constraint.System


-- | A legend maps a term to a shorter term
type Legend = Map LNTerm LNTerm
type TermState = Map String Int


-- | Get all terms appearing in a constraint system
getTerms :: System -> [LNTerm]
getTerms = concatMap (concatMap factTerms . (\r -> get rConcs r ++ get rPrems r)) . get sNodes


-- | Count the number of occurences of all terms in a given constraint system.
termCount :: System -> Map LNTerm Int
termCount = M.fromList . map (\x -> (head x, length x)) . classify . getTerms
    where
    classify :: Eq a => [a] -> [[a]]
    classify [] = []
    classify a@(x:xs) = filter (== x) a : classify (filter (/= x) xs)


-- | Compute the score of a term
-- The score of a term defined as the product of its count and its size.
termScore :: LNTerm -> Map LNTerm Int -> Int
termScore t m = size t * m M.! t


-- | Compute a legend by picking some terms to shorten and maps them to their shortened forms.
-- A term is eligible for shortening if its score is at least @n@, other terms stay unchanged.
computeLegend :: Int -> System -> State TermState Legend
computeLegend n sys = do
  let terms = filter ((>= n) . size) $ getTerms sys
  terms' <- mapM shorten terms
  return $ M.fromList $ zip terms terms'


-- | Compute a shorter name for a function application.
-- Only cares about NoEq function symbols for now, since only these contain free function symbols.
-- Also see Term.Term.FunctionSymbols
shorten :: LNTerm -> State TermState LNTerm
shorten (viewTerm -> FApp (NoEq (bs, _)) _) = do
  m <- State.get
  -- The bare symbol name (unpack, not show — show would bake literal
  -- quotes into the displayed abbreviation label).
  let str = BC.unpack bs
      nameId = case M.lookup str m of
        Just n -> str ++ show n
        Nothing -> str
  updateState str
  return $ lit $ Con (Name AbbrevName (NameId nameId))
  where
    updateState :: String -> State TermState ()
    updateState str = State.modify $
      \s -> case M.lookup str s of
        Just _ -> M.adjust (+1) str s
        Nothing -> M.insert str 1 s

shorten (viewTerm -> x) = return $ termViewToTerm x


-- | Update the given constraint system with shorter terms.
updateSystem :: Legend -> System -> System
updateSystem l = modify sNodes (M.map change)
    where
      change :: RuleACInst -> RuleACInst
      change = modify rPrems go . modify rConcs go

      go :: [LNFact] -> [LNFact]
      go = map (\(tag, a, ts) -> Fact tag a ts) . (\fs -> zip3 (tags fs) (annotations fs) (terms fs))
        where
          tags = map factTag
          annotations = map factAnnotations
          terms = map (map aux . factTerms)
          aux t = case M.lookup t l of
                    Just t' -> t'
                    Nothing -> t


abbrev :: Bool        -- ^ Whether to apply abbreviations
       -> Int         -- ^ Minimal term score to abbreviate
       -> System      -- ^ Constraint system
       -> State TermState (System, Legend)
abbrev False _ sys = return (sys, M.empty)
abbrev True n sys = do
  legend <- computeLegend n sys
  return (updateSystem legend sys, legend)
