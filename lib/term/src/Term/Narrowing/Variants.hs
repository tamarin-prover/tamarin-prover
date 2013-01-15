-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Computing and checking the variants of a term.
module Term.Narrowing.Variants (
    computeVariantsCheck
  , module Term.Narrowing.Variants.Compute
  , module Term.Narrowing.Variants.Check
) where

import Term.Narrowing.Variants.Compute
import Term.Narrowing.Variants.Check
import Term.Unification

import Control.Monad.Reader

-- | @variantsListCheck ts@ computes all variants of @ts@ considered as a single term
--   without a bound or symmetry substitution. Before returning the result, it checks
--   if the set of variants is complete and minimal. If that is not the case, it
--   fails with an error
computeVariantsCheck :: LNTerm -> WithMaude [LNSubstVFresh]
computeVariantsCheck t =
    reader checkWithMaude
  where
    checkWithMaude hnd
      | not $ run $ checkComplete t vars
      = error $ "computeVariantsCheck: variant computation for "++ show t ++" failed. Computed set not complete."
      | not $ run $ checkMinimal t vars
      = error $ "computeVariantsCheck: variant computation for "++ show t ++" failed. Computed set not minimal."
      | otherwise
      = vars
      where
        vars = run $ computeVariants t
        run  = (`runReader` hnd)
