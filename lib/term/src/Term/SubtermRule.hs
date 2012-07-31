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
data StRhs = RhsGround LNTerm | RhsPosition Position
    deriving (Show,Ord,Eq)

-- | A subterm rewrite rule.
data StRule = StRule LNTerm StRhs
    deriving (Show,Ord,Eq)

-- | Convert a rewrite rule to a subterm rewrite rule if possible.
rRuleToStRule :: RRule LNTerm -> Maybe StRule
rRuleToStRule (lhs `RRule` rhs)
  | frees rhs == [] = Just $ StRule lhs (RhsGround rhs)
  | otherwise       = case findSubterm lhs [] of
                        []:_     -> Nothing  -- proper subterm required
                        pos:_    -> Just $ StRule lhs (RhsPosition (reverse pos))
                        []       -> Nothing
  where
    findSubterm t rpos | t == rhs  = [rpos]
    findSubterm (viewTerm -> FApp _ args) rpos =
        concat $ zipWith (\t i -> findSubterm t (i:rpos)) args [0..]
    findSubterm (viewTerm -> Lit _)         _  = []

-- | Convert a subterm rewrite rule to a rewrite rule.
stRuleToRRule :: StRule -> RRule LNTerm
stRuleToRRule (StRule lhs rhs) = case rhs of
                                     RhsGround t   -> lhs `RRule` t
                                     RhsPosition p -> lhs `RRule` (lhs `atPos` p)

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
