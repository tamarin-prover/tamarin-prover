{-# LANGUAGE TupleSections, TypeSynonymInstances, GADTs,FlexibleContexts,EmptyDataDecls,StandaloneDeriving, DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses, DeriveFunctor, ScopedTypeVariables #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Standard and fresh substitutions.
module Term.Substitution (

  -- ** Composition of fresh and free substitutions
    composeVFresh

  -- ** Conversion between fresh and free
  , freshToFree
  , freshToFreeAvoiding

  , freeToFreshRaw

  -- ** Convenience exports
  , module Term.LTerm
  , module Term.Substitution.SubstVFree
  , module Term.Substitution.SubstVFresh
) where

import Term.LTerm
import Term.Substitution.SubstVFree
import Term.Substitution.SubstVFresh

import Extension.Prelude

import Control.Monad.Bind
import Control.Applicative


-- Composition of VFresh and VFresh substitutions
----------------------------------------------------------------------

-- | @composeVFresh s1 s2@ composes the fresh substitution s1 and the free substitution s2.
--   The result is the fresh substitution s = s1.s2.
composeVFresh :: (IsConst c, Show (Lit c LVar))
              => SubstVFresh c LVar -> Subst c LVar -> SubstVFresh c LVar
composeVFresh s1_0 s2 =
    freeToFreshRaw (s1 `compose` s2)
  where
    s1 = freshToFreeAvoiding (extendWithRenaming (varsRange s2)  s1_0) (s2,s1_0)

-- Conversion between substitutions
----------------------------------------------------------------------

-- | @freshToFreeSimp s@ converts the bound variables in @s@ to free variables
-- using fresh variable names. We try to preserve variables names if possible.
freshToFree :: (MonadFresh m, IsConst c)
            => SubstVFresh c LVar -> m (Subst c LVar)
freshToFree subst = (`evalBindT` noBindings) $ do
    let slist = sortOn (size . snd) $ substToListVFresh subst
          -- import oldvar ~> newvar mappings first, keep namehint from oldvar
    substFromList <$> mapM convertMapping slist
  where
    convertMapping (lv,t) = (lv,) <$> mapFrees (Arbitrary importVar) t
      where
        importVar v = importBinding (\s i -> LVar s (lvarSort v) i) v (namehint v)
        namehint v  = case viewTerm t of
            Lit (Var _) -> lvarName lv -- keep name of oldvar
            _           -> lvarName v


-- | @freshToFreeSimpAvoiding s t@ converts all fresh variables in the range of
--   @s@ to free variables avoiding free variables in @t@.
freshToFreeAvoiding :: (HasFrees t, IsConst c) => SubstVFresh c LVar -> t -> Subst c LVar
freshToFreeAvoiding s t = freshToFree s `evalFreshAvoiding` t

-- | @freeToFreshRaw s@ considers all variables in the range of @s@ as fresh.
freeToFreshRaw :: Subst c LVar -> SubstVFresh c LVar
freeToFreshRaw s@(Subst _) = substFromListVFresh $ substToList s