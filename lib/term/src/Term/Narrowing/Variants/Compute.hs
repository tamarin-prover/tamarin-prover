-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Computing the variants of a term.
module Term.Narrowing.Variants.Compute (
    computeVariantsBound
  , computeVariants
  
  -- * for testing
  , compareSubstVariant
) where

import Term.LTerm
import Term.Substitution
import Term.Unification
import Term.Narrowing.Variants.Check (leqSubstVariant,variantsFrom)

import Extension.Prelude

import Data.Ord
import Data.List                     (partition,sortBy)
import Data.Maybe
import Control.Arrow
-- import Control.Applicative
import Control.Monad.Reader

import Debug.Trace.Ignore

----------------------------------------------------------------------
-- Variant Narrowing
----------------------------------------------------------------------

-- | @substCompareVariant t s1 t2@ compares two substitutions using the variant order
--   with respect to @t@.
compareSubstVariant :: LNTerm -> LNSubstVFresh -> LNSubstVFresh
                    -> WithMaude (Maybe Ordering)
compareSubstVariant t s1 s2
  | s1 == s2 = return $ Just EQ
  | otherwise = do
      isSmaller <- leqSubstVariant t s1 s2
      isGreater <- leqSubstVariant t s2 s1
      return $ case (isSmaller, isGreater) of
        (True,  True)  -> Just EQ
        (True,  False) -> Just LT
        (False, True)  -> Just GT
        (False, False) -> Nothing

-- | A @Variant@ consists of its position in the narrowing tree and
--   its substitution.
data Variant = Variant {
      varPos    :: [Int]             -- ^ the position in the search tree
    , varSubst  :: LNSubstVFresh     -- ^ the composed substitution
    }
 deriving (Eq, Ord, Show)

instance Sized Variant where
    size = size . varSubst

-- | @narrowVariant rules t maxdepth@ either returns @Nothing@
--   if variant narrrowing hit the bound and there are still unexplored steps
--   or @Just explored@ if the search finished before hitting the
--   bound.
narrowVariant :: LNTerm -- ^ The term.
              -> Maybe Int -- ^ The step bound.
              -> WithMaude (Maybe [Variant])
narrowVariant tstart maxdepth =
    reader $ \hnd -> go maxdepth [ Variant [] emptySubstVFresh ] [] hnd
  where
    go :: Maybe Int -> [Variant] -> [Variant] -> MaudeHandle
       -> Maybe [Variant]
    go _        []           explored _ = Just explored
    go (Just 0) _unexplored _explored _ = Nothing
    go n unexplored explored hnd = (\res -> (trace (show (n, unexplored, explored, res, new0, explored', new)) res)) $
        go (fmap pred n) new explored' hnd
      where
        runWithMaude = (`runReader` hnd)
        explored0 = explored++unexplored
        new0 = filter (\newVariant -> varSubst newVariant `notElem` map varSubst explored0)
                 $ concatMap variantsFrom' unexplored
        variants = reverse $ sortOn narrowSeqStepComplexity $ (tag False new0 ++ tag True explored0)
        minimized = filterMaximalBy fst cmp variants
        tag t xs = [ (t,a) | a <- xs]
        (explored',new) = map snd *** map snd $ partition fst minimized
        cmp a b = runWithMaude $ compareSubstVariant tstart (varSubst.snd $ a) (varSubst.snd $ b)

        variantsFrom' (Variant pos0 substComposed) =
          zipWith (\i substComposed' -> Variant (pos0++[i]) substComposed')
                  [1..]
                  (runWithMaude $ variantsFrom tstart substComposed)

-- | @filterMaximalBy flags fastcmp alreadyFiltered cmp xs@ returns a
--   list of maximal elements of @xs@ with respect to @cmp@.
filterMaximalBy :: (a -> Bool)                -- ^ a function to check if an element has been
                                              --   already filtered in the last iteration
                -> (a -> a -> Maybe Ordering) -- ^ the comparison function
                -> [a]                        -- ^ the list that we want to filter
                -> [a]
filterMaximalBy _               _   []  = []
filterMaximalBy alreadyFiltered cmp xs0 =
    go (last xs0) (init xs0,[])
  where
    go x ([],[])  = [x]
    go x (y:todo,done)
      -- x and y have already been filtered earlier and are therefore incomparable
      | alreadyFiltered x && alreadyFiltered y = go x (todo,y:done)
      -- either x or y is new, so we have to compare the two
      | otherwise
      = case cmp x y of
          Nothing -> go x (todo,y:done)
          Just EQ | alreadyFiltered x -> keepx
                  | otherwise -> keepy
          Just GT -> keepx
          Just LT -> keepy
      where keepx = go x (todo,done)
            keepy = go y (todo++done,[])
    -- x is maximal, start comparing a new element to the others
    go x ([],y:done)   = x:(go y (reverse done,[]))

-- | This is used to sort narrowing steps such that similar steps are close
narrowSeqStepComplexity :: (Bool,Variant) -> (Bool,Int,Int,Int)
narrowSeqStepComplexity (checked, var@(Variant _ subst)) =
    (not checked, length (varPos var), size subst, length (varsRangeVFresh subst))

-- | @computeVariants t d@ compute the variants of term @t@ with bound @d@.
--   The rewriting rules are taken from the Maude context.
computeVariantsBound :: LNTerm -> Maybe Int 
                     -> WithMaude (Maybe [LNSubstVFresh])
computeVariantsBound t d = reader $ \hnd -> (\res -> trace (show ("ComputeVariantsBound", t, res)) res) $
    case (`runReader` hnd) $ narrowVariant t d of
      Nothing -> Nothing
      Just explored ->
        Just (map varSubst (sortBy (comparing size) explored))

-- | @variantsList ts@ computes all variants of @ts@ considered as a single term
--   without a bound or symmetry substitution.
--   The rewriting rules are taken from the Maude context.
computeVariants :: LNTerm -> WithMaude [LNSubstVFresh]
computeVariants t =
    fromMaybe err <$> computeVariantsBound t Nothing
  where
    err = error "impossible: Variant computation failed without giving a bound"
