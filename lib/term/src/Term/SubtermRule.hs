{-# LANGUAGE TemplateHaskell, FlexibleInstances, DeriveDataTypeable, ViewPatterns, DeriveGeneric, DeriveAnyClass #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2011-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
--
-- Context Subterm rewriting rules.
module Term.SubtermRule (
      StRhs(..)
    , CtxtStRule(..)
    , filterNonSubtermCtxtRule
    , isSubtermConvergentCtxtRule
    , rRuleToCtxtStRule
    , ctxtStRuleToRRule
    , findAllSubterms
    , findSubterm

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
import Data.ByteString (find)

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
  | otherwise       = do
                         sbtms <- findAllSubterms lhs rhs
                         case sbtms of
                            []:_     -> Nothing  -- proper subterm required
                            []       -> Nothing
                            pos      -> Just $ CtxtStRule lhs (StRhs pos rhs)
  where
    subterms :: [LNTerm] -> [LNTerm] -> Int -> [Position]
    subterms []     _    _ = []
    subterms (t:ts) done i = (concat $ map 
        (\(x, y) -> (map (x:) (findSubterm y t))) terms) 
            ++ subterms ts (done++[t]) (i+1)  
      where 
        terms = (zip [i..] ts) ++ (zip [0..] done)
    
    constantPositions (viewTerm -> FApp _ args) 
        | containsPrivate lhs = positions lhs
        | otherwise           = case subterms args [] 1 of
                                     []  -> positions lhs
                                     pos -> pos

-- | Finds all occurrences of a subterm in a term.
findSubterm :: LNTerm -> LNTerm -> [Position]
findSubterm lst r = findSubtermPrime lst r []
  where 
      findSubtermPrime :: LNTerm -> LNTerm -> Position -> [Position]
      findSubtermPrime lst r rpos | lst == r            = [reverse rpos]
      findSubtermPrime (viewTerm -> FApp _ args) r rpos =
            concat $ zipWith (\lst i -> findSubtermPrime lst r (i:rpos)) args [0..]
      findSubtermPrime (viewTerm -> Lit _)         _ _  = []

-- | Given a term l, finds all occurrences of r in l.
-- If r does not occur in l, returns the occurrences of subterms of r.
-- Returns Nothing if some variable in r does never appear in l.
findAllSubterms :: LNTerm -> LNTerm -> Maybe [Position]
findAllSubterms l r@(viewTerm -> FApp _ args)
    | fSt == [] = do
        stms <- mapM (\rst -> findAllSubterms l rst) args
        return $ concat stms
    | otherwise = Just $ fSt
        where fSt = findSubterm l r
findAllSubterms l r@(viewTerm -> Lit (Var _))
    | fSt == [] = Nothing
    | otherwise = Just fSt
        where fSt = findSubterm l r
-- There should not be constants on the right hand side (enforced by the parser).
findAllSubterms _ (viewTerm -> Lit (Con _)) = Nothing

-- | Convert a context subterm rewrite rule to a rewrite rule.
ctxtStRuleToRRule :: CtxtStRule -> RRule LNTerm
ctxtStRuleToRRule (CtxtStRule lhs (StRhs _ rhsterm)) = lhs `RRule` rhsterm

-- | Checks if a list of CtxtStRule contains rules that are not subterm convergent.
filterNonSubtermCtxtRule :: [CtxtStRule] -> [CtxtStRule]
filterNonSubtermCtxtRule = filter (not . isSubtermConvergentCtxtRule)

-- | Checks if RHS is a subterm of LHS in a specific rule.
isSubtermConvergentCtxtRule :: CtxtStRule -> Bool
isSubtermConvergentCtxtRule (CtxtStRule lhs (StRhs _ rhs))
  | isConstant rhs = True
  | otherwise      = not (null (findSubterm lhs rhs))

-- Checks if LNTerm is constant 
isConstant :: LNTerm -> Bool
isConstant term = null (frees term)
------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

-- | Pretty print an 'CtxtStRule'
prettyCtxtStRule :: HighlightDocument d => CtxtStRule -> d
prettyCtxtStRule r = case ctxtStRuleToRRule r of
  (lhs `RRule` rhs) -> sep [ nest 2 $ prettyLNTerm lhs
                           , operator_ "=" <-> prettyLNTerm rhs ]
