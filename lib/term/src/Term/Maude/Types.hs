{-# LANGUAGE FlexibleContexts #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Types for communicating with Maude.
module Term.Maude.Types (
  -- * Maude terms
    MaudeLit(..)
  , MSubst
  , MTerm

  -- * conversion from/to maude terms
  , lTermToMTerm
  , lTermToMTerm'
  , mTermToLNTerm
  , runConversion
  , msubstToLSubstVFresh
  , msubstToLSubstVFree

  ) where

import           Term.Term
import           Term.LTerm
import           Term.Substitution

import           Utils.Misc

import           Control.Monad.Fresh
import           Control.Monad.Bind
-- import           Control.Applicative

-- import           Data.Traversable hiding (mapM)
import           Data.Maybe
import qualified Data.Map as M
import           Data.Map (Map)

-- Maude Terms
----------------------------------------------------------------------

data MaudeLit = MaudeVar   Integer LSort
              | FreshVar   Integer LSort
              | MaudeConst Integer LSort
  deriving (Eq, Ord, Show)

type MTerm = Term MaudeLit

type MSubst = [((LSort, Integer), MTerm)]


------------------------------------------------------------------------
-- Convert between MTerms and LNTerms
------------------------------------------------------------------------

-- | Convert an @LNTerm@ to an @MTerm@.
lTermToMTerm' :: (MonadBind (Lit Name LVar) MaudeLit m, MonadFresh m)
              => LNTerm -- ^ The term to translate.
              -> m MTerm
lTermToMTerm' = lTermToMTerm sortOfName


-- | Convert an @LNTerm@ with arbitrary names to an @MTerm@.
lTermToMTerm :: (MonadBind (Lit c LVar) MaudeLit m, MonadFresh m, Ord c)
             => (c -> LSort) -- ^ A function that returns the sort of a constant.
             -> VTerm c LVar -- ^ The term to translate.
             -> m MTerm
lTermToMTerm sortOf =
    go . viewTerm
  where
    go (Lit l)     = lit <$> exportLit l
    go (FApp o as) = fApp o <$> mapM (go . viewTerm) as
    exportLit a@(Var lv) =
        importBinding (\_ i -> MaudeVar i (lvarSort lv)) a "x"
    exportLit a@(Con n) = importBinding (\_ i -> MaudeConst i (sortOf n)) a "a"


-- | Convert an 'MTerm' to an 'LNTerm' under the assumption that the bindings
-- for the constants are already available.
mTermToLNTerm :: (MonadBind MaudeLit (Lit c LVar) m, MonadFresh m, Show (Lit c LVar), Ord c, Show c)
             => String -- ^ Name hint for freshly generated variables.
             -> MTerm  -- ^ The maude term to convert.
             -> m (VTerm c LVar)
mTermToLNTerm nameHint =
    go . viewTerm
 where
    go (Lit l)     = lit <$> importLit l
    go (FApp o as) = fApp o <$> mapM (go . viewTerm) as
    importLit a@(MaudeVar _ lsort) = importBinding (\n i -> Var (LVar n lsort i)) a nameHint
    importLit a@(FreshVar _ lsort) = importBinding (\n i -> Var (LVar n lsort i)) a nameHint
    importLit a = fromMaybe (error $ "fromMTerm: unknown constant `" ++ show a ++ "'") <$>
                      lookupBinding a


-- Back and forth conversions
------------------------------------------------------------------------

-- | Run a @BindT (Lit c LVar) MaudeLit Fresh@ computation
--   with an empty fresh supply and an empty binding map and return
--   the result and the resulting inverted binding map.
runConversion :: BindT (Lit c LVar) MaudeLit Fresh a -- ^ Computation to execute.
              -> (a, Map MaudeLit (Lit c LVar))
runConversion to =
    (x, invertMap bindings)
  where (x, bindings) = runBindT to noBindings `evalFresh` nothingUsed

-- | Run a @BindT  MaudeLit (Lit c LVar) Fresh@ computation using the
--   supplied binding map and the corresponding fresh supply.
runBackConversion :: BindT MaudeLit (Lit c LVar) Fresh a -- ^ Computation to execute.
                  -> Map MaudeLit (Lit c LVar) -- ^ Binding map that should be used.
                  -> a
runBackConversion back bindings =
    evalBindT back bindings `evalFreshAvoiding` M.elems bindings

------------------------------------------------------------------------
-- Conversion between Maude and Standard substitutions
------------------------------------------------------------------------

-- | @msubstToLSubstVFresh bindings substMaude@ converts a substitution
--   returned by Maude to a 'VFresh' substitution. It expects that the
--   range of the maude substitution contains only fresh variables in its
--   range and raises an error otherwise.
msubstToLSubstVFresh :: (Ord c, Show (Lit c LVar), Show c)
                     => Map MaudeLit (Lit c LVar) -- ^ The binding map to use for constants.
                     -> MSubst -- ^ The maude substitution.
                     -> SubstVFresh c LVar
msubstToLSubstVFresh bindings substMaude
    | not $ null [i | (_,t) <- substMaude, MaudeVar _ i <- lits t] =
        error $ "msubstToLSubstVFresh: nonfresh variables in `"++show substMaude++"'"
    | otherwise = removeRenamings $ substFromListVFresh slist
 where
   slist = runBackConversion (traverse translate substMaude) bindings
   -- try to keep variable name for xi -> xj mappings
   -- commented out, seems wrong
   --  translate ((s,i), mt@(Lit (FreshVar _ _))) = do
   --    lv <- lookupVar s i
   --    (lv,)  <$> mTermToLNTerm (lvarName lv) mt
   translate ((s,i),mt) = (,) <$> lookupVar s i <*> mTermToLNTerm "x" mt
   lookupVar s i = do b <- lookupBinding (MaudeVar i s)
                      case b of
                          Just (Var lv) -> return lv
                          _ -> error $ "msubstToLSubstVFrsh: binding for maude variable `"
                                       ++show (s,i) ++"' not found in "++show bindings

-- | @msubstToLSubstVFree bindings substMaude@ converts a substitution
--   returned by Maude to a 'VFree' substitution. It expects that the
--   maude substitution contains no fresh variables in its range and raises an
--   error otherwise.
msubstToLSubstVFree ::  (Ord c, Show (Lit c LVar), Show c)
                    => Map MaudeLit (Lit c LVar) -> MSubst -> Subst c LVar
msubstToLSubstVFree bindings substMaude
    | not $ null [i | (_,t) <- substMaude, FreshVar _ i <- lits t] =
        error $ "msubstToLSubstVFree: fresh variables in `"++show substMaude
    | otherwise = substFromList slist
  where
   slist = evalBindT (traverse translate substMaude) bindings
           `evalFreshAvoiding` M.elems bindings
   translate ((s,i),mt) = (,) <$> lookupVar s i <*> mTermToLNTerm "x" mt
   lookupVar s i = do b <- lookupBinding (MaudeVar i s)
                      case b of
                         Just (Var lv) -> return lv
                         _ -> error $ "msubstToLSubstVFree: binding for maude variable `"
                                      ++show (s,i)++"' not found in "++show bindings
