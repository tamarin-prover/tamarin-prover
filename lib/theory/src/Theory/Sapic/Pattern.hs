{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}


{-# LANGUAGE DeriveGeneric        #-}

{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE PatternGuards       #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Data types for SAPIC processes in theories
module Theory.Sapic.Pattern (
    -- types
    PatternSapicLVar(..)
    -- converters
    , unpattern
    , unpatternVar
    -- utitlities
    , validPattern
    , validMSR
    , extractMatchingVariables
    , unextractMatchingVariables
) where

import Data.Binary
import Data.Data
import qualified Data.Set as S
import Data.List ( group, sort )
import GHC.Generics (Generic)
import Control.Parallel.Strategies
-- import Theory.Model.Fact
import Theory.Model.Formula
import Theory.Sapic.Term
import Term.LTerm

-- | Pattern variables either bind new variables or match with existing
data PatternSapicLVar =  PatternBind SapicLVar | PatternMatch SapicLVar
     deriving( Ord, Eq, Typeable, Data, Generic, NFData, Binary, IsVar )

instance Show PatternSapicLVar where
    show (PatternBind v) = show v
    show (PatternMatch v) = "=" ++ show v

instance Hinted PatternSapicLVar where
  hint (PatternBind v) = hint v
  hint (PatternMatch v) = hint v

-- | Translate Pattern into term
unpattern :: SapicNTerm PatternSapicLVar -> SapicNTerm SapicLVar
unpattern = fmap (fmap unpatternVar)

unpatternVar :: PatternSapicLVar -> SapicLVar
unpatternVar (PatternBind  v) = v
unpatternVar (PatternMatch v) = v

-- | Check a pattern for validity w.r.t. a set of variables or names that are
--    already bound, i.e.,
--   1. no variable that is already bound should occur as PatternBind
--   2. no variable that already occurs as PatternMatch should occur as PatternBind
--   3. a variable should not be bound twice.
validPattern :: S.Set SapicLVar -> Term (Lit n PatternSapicLVar) -> Bool
validPattern alreadyBound pt = (alreadyBound `S.union` matched) `S.disjoint` tobind && duplicate tobind'
    where
        (tobind',matched') = freesPatternSapicLVar pt
        tobind  = S.fromList tobind'
        matched = S.fromList matched'
        duplicate = not . any ((>1) . length) . group . sort

-- | Check an MSR (l,a,r) with a pattern on the lhs for validity:
-- 1. a and r do not contain "="
-- 2. variables in l are either matched or bound but not both
-- 3. l does not rebind variables
validMSR :: (Foldable t1, Foldable t2) => S.Set SapicLVar -> (t1 (t2 (VTerm n1 PatternSapicLVar)), t1 (t2 (VTerm n2 PatternSapicLVar)), t1 (t2 (VTerm n3 PatternSapicLVar))) -> Bool
validMSR alreadyBound (l,a,r)
    | (tobind_l',matched_l') <- freesPatternFactList l
    , (_,[]) <- freesPatternFactList a
    , (_,[]) <- freesPatternFactList r
    , matched_l <- S.fromList matched_l'
    , tobind_l <- S.fromList tobind_l'
      =  (alreadyBound `S.union` matched_l) `S.disjoint`  tobind_l
    | otherwise = False
    where
        freesPatternFactList = foldMap (foldMap freesPatternSapicLVar)


extractMatchingVariables :: SapicNTerm PatternSapicLVar -> S.Set SapicLVar
extractMatchingVariables pt = S.fromList $ foldMap (foldMap isPatternMatch) pt
    where
        isPatternMatch (PatternMatch v) = [v]
        isPatternMatch (PatternBind  _) = []
    
-- | Transform term and list of variables to pattern term with those variables bound
unextractMatchingVariables ::  S.Set SapicLVar -> SapicTerm -> SapicNTerm PatternSapicLVar
unextractMatchingVariables vs = fmap (fmap f) 
    where
        f v = if v `elem` vs then PatternMatch v else PatternBind v
        

-- | list of variables that occur in pattern term.
-- guarantees to capture them from right to left, including duplicates.
freesPatternSapicLVar :: VTerm n PatternSapicLVar -> ([SapicLVar], [SapicLVar])
freesPatternSapicLVar pt = foldr f ([],[]) (freesSapicTerm pt)
    where
        f (PatternBind  v) (bs,ms) = (v:bs,ms)
        f (PatternMatch v) (bs,ms) = (bs,v:ms)
