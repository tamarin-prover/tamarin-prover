{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Substitutions with fresh (or bound) variables in the range.
module Term.Substitution.SubstVFresh (
  -- * General Substitutions
    SubstVFresh(..)

  -- * smart constructors for substitutions
  , substFromListVFresh
  , emptySubstVFresh

  -- * operations
  , restrictVFresh
  , mapRangeVFresh
  , extendWithRenaming

  -- * queries
  , varsRangeVFresh
  , domVFresh
  , rangeVFresh
  , isRenaming
  , imageOfVFresh

  -- * views
  , substToListVFresh


  -- * Pretty printing
  , prettySubstVFresh

  -- * operations on fresh substitutions
  , renameFresh
  , renameFreshAvoiding
  , removeRenamings

  -- * Substitution of LVars 
  , LSubstVFresh
  , LNSubstVFresh
  , prettyLSubstVFresh
  , prettyDisjLNSubstsVFresh
) where


import           Term.LTerm
import           Text.PrettyPrint.Highlight

-- import           Control.Applicative
import           Control.Monad.Fresh
import           Control.DeepSeq

import           Logic.Connectives

import           Utils.Misc

import           Data.Map ( Map )
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.List
-- import           Data.Traversable hiding ( mapM )
import           Data.Binary
-- import           Data.Monoid ( mempty )

----------------------------------------------------------------------
-- Substitutions
----------------------------------------------------------------------

-- | We use the data type @SubstVFresh c v@ of substitutions.
--   @c@ denotes the type of constants and @v@ the type of variables.
--   Fresh substitutions cannot be applied directly, they have to be converted
--   to free substitutions in a certain context (MonadFresh).
newtype SubstVFresh c v = SubstVFresh { svMap :: Map v (VTerm c v) }
  deriving ( Eq, Ord, NFData, Binary )

-- | Fresh substitution with logical variables
type LSubstVFresh c = SubstVFresh c LVar

-- | Fresh substitution with logical variables and names
type LNSubstVFresh = SubstVFresh Name LVar

-- Smart constructors for substitutions
----------------------------------------------------------------------

-- | Convert a list of mappings to a fresh substitution.
substFromListVFresh :: IsVar v => [(v, VTerm c v)] -> SubstVFresh c v
substFromListVFresh xs = SubstVFresh (M.fromList xs)

-- | @emptySubstVFresh@ is the fresh substitution with empty domain.
emptySubstVFresh :: SubstVFresh c v
emptySubstVFresh = SubstVFresh M.empty

-- Operations
----------------------------------------------------------------------

-- | @restrictVFresh vars subst@ restricts the domain of the substitution @subst@ to @vars@.
restrictVFresh :: IsVar v => [v] -> SubstVFresh c v -> SubstVFresh c v
restrictVFresh vs (SubstVFresh smap) = SubstVFresh (M.filterWithKey (\v _ -> v `elem` vs) smap)

-- | @mapRangeVFresh f subst@ maps the function @f@ over the range of the substitution @subst@.
--   Note that all introduced variables are considered fresh.
mapRangeVFresh :: (VTerm c v      -> VTerm c2 v)
               -> SubstVFresh c v -> SubstVFresh c2 v
mapRangeVFresh f subst = SubstVFresh $ M.map f (svMap subst)


-- | @extendWithRenaming vs s@ extends the substitution @s@ with renamings (with
--   fresh variables) for the variables in @vs@ that are not already in @dom s@.
extendWithRenaming :: Ord c
                   => [LVar] -> SubstVFresh c LVar -> SubstVFresh c LVar
extendWithRenaming vs0 s =
    substFromListVFresh $
      substToListVFresh s ++ substToListVFresh (renameFreshAvoiding s2 (varsRangeVFresh s))
  where s2 = substFromListVFresh [(v, lit (Var v)) | v <- vs ]
        vs = vs0 \\ domVFresh s

-- Queries
----------------------------------------------------------------------

-- | @domVFresh subst@ returns the domain of the substitution @substs@.
domVFresh :: SubstVFresh c v -> [v]
domVFresh = M.keys . svMap

-- | @rangeVFresh subst@ returns the range of the substitution @substs@.
rangeVFresh :: SubstVFresh c v -> [VTerm c v]
rangeVFresh = M.elems . svMap

-- | @varsRangeVFresh subst@ returns all variables in the range of the substitution
varsRangeVFresh :: IsVar v => SubstVFresh c v -> [v]
varsRangeVFresh = varsVTerm . fAppList . rangeVFresh

-- | Returns @True@ if the given variable in the domain of the
--   substitution is just renamed by the substitution.
isRenamedVar :: LVar -> LSubstVFresh c -> Bool
isRenamedVar lv subst =
    case viewTerm <$> imageOfVFresh subst lv of
      Just (Lit (Var lv')) | lvarSort lv == lvarSort lv' ->
          lv' `notElem` (varsVTerm . fAppList $ [ t | (v,t) <- substToListVFresh subst, v /= lv ])
      _ -> False

-- | Returns @True@ if the substitution is a renaming.
isRenaming :: LSubstVFresh c -> Bool
isRenaming subst = all (`isRenamedVar` subst) $ domVFresh subst

-- | Returns the image of @i@ under @subst@ if @i@ is in the domain of @subst@.
imageOfVFresh :: IsVar v => SubstVFresh c v -> v -> Maybe (VTerm c v)
imageOfVFresh subst i = M.lookup i (svMap subst)

-- Views
----------------------------------------------------------------------

-- | Convert substitution to list.
substToListVFresh :: SubstVFresh c v -> [(v,VTerm c v)]
substToListVFresh = M.toList . svMap

-- Operations on fresh substitutions
----------------------------------------------------------------------

-- | @renameFresh s@  renames the fresh variables in @s@ using fresh variables.
--   This function can be used to prevent overshadowing which might
--   make output hard to read.
renameFresh :: (Ord c, MonadFresh m) => SubstVFresh c LVar -> m (SubstVFresh c LVar)
renameFresh subst = substFromListVFresh . zip (map fst slist) <$> rename (map snd slist)
  where slist = substToListVFresh subst

-- | @renameFreshAvoiding s t@ renames the fresh variables in the range of @s@ away from
--   variables that are free in @t@. This is an internal function.
renameFreshAvoiding :: (Ord c, HasFrees t) => LSubstVFresh c -> t -> SubstVFresh c LVar
renameFreshAvoiding s t = renameFresh s `evalFreshAvoiding` t

-- | @removeRenamings s@ removes all renamings (see 'isRenamedVar') from @s@.
removeRenamings :: LSubstVFresh c -> LSubstVFresh c
removeRenamings s =
    substFromListVFresh $ filter (not .  (`isRenamedVar` s) . fst) $ substToListVFresh s

----------------------------------------------------------------------
-- Instances
----------------------------------------------------------------------

instance (Show c, Show v) => Show (SubstVFresh c v) where
    show subst = "VFresh: {" ++ mappings ++"}"
      where
        mappings = intercalate ", " [ show t ++" <~ "++show v | (v,t) <- substToListVFresh subst ]


instance Sized (SubstVFresh c v) where
    size = sum . map size . rangeVFresh


instance HasFrees (SubstVFresh n LVar) where
    foldFrees f = foldFrees f . M.keys . svMap
    foldFreesOcc _ _ = const mempty -- we ignore occurences in substitutions for now
    mapFrees   f = 
        (substFromListVFresh <$>) . traverse mapDomain   . substToListVFresh
      where
        mapDomain (v, t) = (,t) <$> mapFrees f v

----------------------------------------------------------------------
-- Pretty Printing
----------------------------------------------------------------------

-- | Pretty print a substitution.
prettySubstVFresh :: (Ord c, Ord v, HighlightDocument d, Show c, Show v)
                  => (v -> d) -> (Lit c v -> d) -> SubstVFresh c v -> [d]
prettySubstVFresh ppVar ppLit =
    map pp . M.toList . equivClasses . substToListVFresh
  where
    pp (t, vs)  = prettyTerm ppLit t <-> operator_ " <~ {" <>
        (fsep $ punctuate comma $ map ppVar $ S.toList vs) <> operator_ "}"

-- | Pretty print a substitution with logical variables.
prettyLSubstVFresh :: (Show (Lit c LVar), Ord c, HighlightDocument d, Show c)
                   => LSubstVFresh c -> d
prettyLSubstVFresh = vcat . prettySubstVFresh (text . show) (text . show)

-- | Pretty print a disjunction of substitutions.
prettyDisjLNSubstsVFresh :: Document d => Disj LNSubstVFresh -> d
prettyDisjLNSubstsVFresh (Disj substs) =
    numbered' (map ppConj substs)
  where 
    ppConj = vcat . map prettyEq . substToListVFresh
    prettyEq (a,b) = 
      prettyNTerm (lit (Var a)) $$ nest (6::Int) (text "=" <-> prettyNTerm b)
