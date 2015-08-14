-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Completeness and minimality checking for the variants of a term.
module Term.Narrowing.Variants.Check (
    checkComplete
  , checkMinimal

  , variantsFrom
  , isNormalInstance

  , leqSubstVariant
) where

import Term.Substitution
import Term.Unification
import Term.Rewriting.Norm
import Term.Subsumption      (factorSubstVia,canonizeSubst)
import Term.Narrowing.Narrow

import Extension.Prelude
import Utils.Misc

import Control.Basics
import Control.Monad.Reader
import Data.List             (delete)

import Debug.Trace.Ignore

-- Variant Order
----------------------------------------------------------------------

-- | @isNormalInstance t s s'@ returns @True@ if @s'(norm(s(t)))@ is in normal
--   form.
isNormalInstance :: LNTerm -> LNSubst -> LNSubst -> WithMaude Bool
isNormalInstance t s s' = {- trace ("isnormalInstance " ++ show (t,s,s')) $ -}
                           do t' <- norm' (applyVTerm s t)
                              nf' (applyVTerm s' t')

-- | @leqSubstVariant t s1 s2@ compares two substitutions using the variant order 
--   with respect to @t@ and returns @True@ if @s1@ is less or equal than @s2@
--   and @False@ otherwise. Use the more expensive @compareSubstVariant@
--   which uses two AC matchings instead of one if you also want to distinguish
--   @Nothing@, @Just EQ@, and @Just GT@.
-- 
--   s1 is smaller or equal to s2 wrt. to the variant order (less general) iff there
--   is an s1' such that s1 = s2' . s2 restricted to vars(t) and s2'(norm(s2(t)))
--   is in normal form, or equivalently norm(s1(t)) =AC= s2'(norm(s2(1))). This
--   means s1 is redundant since it is just an AC instance of s2 that does
--   not "require additional normalization steps."
leqSubstVariant :: LNTerm -> LNSubstVFresh -> LNSubstVFresh -> WithMaude Bool
leqSubstVariant t s1_0 s2_0 = reader $ \hnd ->
    s1_0 == s2_0 ||
    any (\s -> isNormalInstance t s2 s `runReader` hnd)
        ( {- (\x -> trace (show x) x) -} (factorSubstVia tvars s1 s2 `runReader` hnd))
  where
    tvars = frees t
    s1 = restrictVFresh tvars s1_0 `freshToFreeAvoiding` t
    s2 = restrictVFresh tvars s2_0 `freshToFreeAvoiding` t

-- Completeness checking for a set of variants
----------------------------------------------------------------------

-- | @checkComplete t substs@ checks if @substs@ is a complete set of variants
--   for @t@ and returns @Just (subst1,subst2)@ if there is a narrowing step
--   from @subst1@ that yields a new variant @subst2@.
checkComplete :: LNTerm
              -> [LNSubstVFresh] 
              -> WithMaude Bool
checkComplete t substs0 = reader $ \hnd ->
    let newSubsts = concatMap ((`runReader` hnd) . variantsFrom t) substs
        substs = sortOn (size &&& length . varsRangeVFresh) substs0
    in 
      emptySubstVFresh `elem` substs0 && 
      all (\s -> not $ isMaximalIn s substs t `runReader` hnd) newSubsts

-- | @variantsFrom rules t subst@ returns all the "one-step variants" of
--   @norm (t subst)@ for the given set of @rules@.
variantsFrom :: LNTerm
             -> LNSubstVFresh
             -> WithMaude [LNSubstVFresh]
variantsFrom t substFrom0 = reader $ \hnd -> (\res -> trace (show ("variantsFrom", t, substFrom0, res)) res) $ sortednub $ do
    let substFrom = substFrom0 `freshToFreeAvoiding` t
    substTo0 <- (narrowSubsts =<<  (norm' (applyVTerm substFrom t))) `runReader` hnd
    let substTo = restrictVFresh (frees t) $ composeVFresh substTo0 substFrom
    guard (nfSubstVFresh' substTo `runReader` hnd) -- prune substitutions that are not in normal-form
    return $ canonizeSubst $ removeRenamings $ substTo

-- | @isMaximalIn s substs t@ returns @True@ if @s@ is minimal in substs wrt.
--   <_Var^t, i.e., the function returns @True@ if there is no s'
--   in substs with s' <=_Var^t s.
isMaximalIn :: LNSubstVFresh -> [LNSubstVFresh] -> LNTerm -> WithMaude Bool
isMaximalIn s substs t = reader $ \hnd ->
    all (\s' -> (\res -> trace (show ("isMaximal:", not res , "=", s, "<=", s')) res ) $
        not (leqSubstVariant t s s' `runReader` hnd)) substs

-- Minimality checking for a set of variants
----------------------------------------------------------------------

-- | @checkMinimal t substs@ checks if @substs@ is a minimal set of variants
--   for @t@ and returns @False@ if there are subst1 /= subst2 in substs with
--   subst1 <=_Var_t subst2.
checkMinimal :: LNTerm -> [LNSubstVFresh] -> WithMaude Bool
checkMinimal t substs = reader $ \hnd ->
    noDuplicates substs && 
    all (\s -> (\res -> trace (show (s,substs,res)) res) $
        (`runReader` hnd) $ isMaximalIn s (delete s substs) t) substs
