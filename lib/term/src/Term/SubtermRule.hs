{-# LANGUAGE TemplateHaskell, FlexibleInstances, DeriveDataTypeable, ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2011-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Subterm rewriting rules.
module Term.SubtermRule (
      StRhs(..)
    , StRule(..)
    , rRuleToStRule
    , stRuleToRRule

    -- * Pretty Printing
    , prettyStRule
    , module Term.Rewriting.Definitions
    ) where

import Control.DeepSeq

import Data.DeriveTH
import Data.Binary

import Term.LTerm
import Term.Positions
import Term.Rewriting.Definitions
import Text.PrettyPrint.Highlight

-- | The righthand-side of a subterm rewrite rule.
--   Does not enforce that the term for RhsGround must be ground.
data StRhs = StRhs [Position] LNTerm
    deriving (Show,Ord,Eq)

-- | A subterm rewrite rule. To be renamed.
data StRule = StRule LNTerm StRhs
    deriving (Show,Ord,Eq)

-- | Convert a rewrite rule to a subterm rewrite rule if possible.
rRuleToStRule :: RRule LNTerm -> Maybe StRule
rRuleToStRule (lhs `RRule` rhs)
  | frees rhs == [] = Just $ StRule lhs (StRhs [] rhs)
  | otherwise       = case findAllSubterms lhs rhs of
                        []:_     -> Nothing  -- proper subterm required
                        []       -> Nothing
                        pos      -> Just $ StRule lhs (StRhs pos rhs)
  where
    findSubterm lst r rpos | lst == r            = [reverse rpos]
    findSubterm (viewTerm -> FApp _ args) r rpos =
        concat $ zipWith (\lst i -> findSubterm lst r (i:rpos)) args [0..]
    findSubterm (viewTerm -> Lit _)         _ _  = []
    
    findAllSubterms l r@(viewTerm -> FApp _ args)
        | fSt == [] = concat $ map (\rst -> findAllSubterms l rst) args
        | otherwise = fSt
            where fSt = findSubterm l r []
    findAllSubterms l r@(viewTerm -> Lit _)       = findSubterm l r []

-- | Convert a subterm rewrite rule to a rewrite rule.
stRuleToRRule :: StRule -> RRule LNTerm
stRuleToRRule (StRule lhs (StRhs _ rhsterm)) = lhs `RRule` rhsterm

------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

-- | Pretty print an 'StRule'
prettyStRule :: HighlightDocument d => StRule -> d
prettyStRule r = case stRuleToRRule r of
  (lhs `RRule` rhs) -> sep [ nest 2 $ prettyLNTerm lhs
                           , operator_ "=" <-> prettyLNTerm rhs ]

-- derived instances
--------------------

$(derive makeBinary ''StRhs)
$(derive makeBinary ''StRule)

$(derive makeNFData ''StRhs)
$(derive makeNFData ''StRule)
