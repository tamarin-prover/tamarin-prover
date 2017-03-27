{-# LANGUAGE TemplateHaskell, FlexibleInstances, DeriveDataTypeable, ViewPatterns, DeriveGeneric, DeriveAnyClass #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2011-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Context Subterm rewriting rules.
module Term.SubtermRule (
      StRhs(..)
    , CtxtStRule(..)
    , rRuleToCtxtStRule
    , ctxtStRuleToRRule

    -- * Pretty Printing
    , prettyCtxtStRule
    , module Term.Rewriting.Definitions
    ) where

import Control.DeepSeq

import GHC.Generics (Generic)
import Data.Binary

import Term.LTerm
import Term.Positions
import Term.Rewriting.Definitions
import Text.PrettyPrint.Highlight

-- | The righthand-side of a context subterm rewrite rule.
--   Does not enforce that the term for RhsGround must be ground.
data StRhs = StRhs [Position] LNTerm
    deriving (Show,Ord,Eq, Generic, NFData, Binary)

-- | A context subterm rewrite rule.
--   The left hand side as a LNTerm, and a StRHS.
data CtxtStRule = CtxtStRule LNTerm StRhs
    deriving (Show,Ord,Eq, Generic, NFData, Binary)

-- | Convert a rewrite rule to a context subterm rewrite rule if possible.
rRuleToCtxtStRule :: RRule LNTerm -> Maybe CtxtStRule
rRuleToCtxtStRule (lhs `RRule` rhs)
  | frees rhs == [] = Just $ CtxtStRule lhs (StRhs (constantPositions lhs) rhs)
  | otherwise       = case findAllSubterms lhs rhs of
                        []:_     -> Nothing  -- proper subterm required
                        []       -> Nothing
                        pos      -> Just $ CtxtStRule lhs (StRhs pos rhs)
  where
    subterms :: [LNTerm] -> [LNTerm] -> Int -> [Position]
    subterms []     _    _ = []
    subterms (t:ts) done i = (concat $ map 
        (\(x, y) -> (map (x:) (findSubterm y t []))) terms) 
            ++ subterms ts (done++[t]) (i+1)  
      where 
        terms = (zip [i..] ts) ++ (zip [0..] done)
    
    constantPositions (viewTerm -> FApp _ args) 
        | containsPrivate lhs = positions lhs
        | otherwise           = case subterms args [] 1 of
                                     []  -> positions lhs
                                     pos -> pos
    
    findSubterm :: LNTerm -> LNTerm -> Position -> [Position]
    findSubterm lst r rpos | lst == r            = [reverse rpos]
    findSubterm (viewTerm -> FApp _ args) r rpos =
        concat $ zipWith (\lst i -> findSubterm lst r (i:rpos)) args [0..]
    findSubterm (viewTerm -> Lit _)         _ _  = []
    
    findAllSubterms l r@(viewTerm -> FApp _ args)
        | fSt == [] = concat $ map (\rst -> findAllSubterms l rst) args
        | otherwise = fSt
            where fSt = findSubterm l r []
    findAllSubterms l r@(viewTerm -> Lit _)       = findSubterm l r []

-- | Convert a context subterm rewrite rule to a rewrite rule.
ctxtStRuleToRRule :: CtxtStRule -> RRule LNTerm
ctxtStRuleToRRule (CtxtStRule lhs (StRhs _ rhsterm)) = lhs `RRule` rhsterm

------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

-- | Pretty print an 'CtxtStRule'
prettyCtxtStRule :: HighlightDocument d => CtxtStRule -> d
prettyCtxtStRule r = case ctxtStRuleToRRule r of
  (lhs `RRule` rhs) -> sep [ nest 2 $ prettyLNTerm lhs
                           , operator_ "=" <-> prettyLNTerm rhs ]

