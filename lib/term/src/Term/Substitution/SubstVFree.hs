{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
--
-- Standard substitutions (with free variables).
module Term.Substitution.SubstVFree (
  -- * General Substitutions
    Subst(..)

  -- * application of substitutions
  , applyVTerm
  , applyVTermProj
  , applyLit

  -- * smart constructors for substitutions
  , substFromList
  , substFromMap
  , emptySubst

  -- * Composition of substitutions
  , compose
  , applySubst

  -- * operations
  , restrict
  , mapRange

  -- * queries
  , varsRange
  , dom
  , range
  , imageOf

  -- * views
  , substToListOn
  , substToList

  -- *Apply class
  , Apply(..)

  -- * Pretty printing
  , prettySubst

  -- * Substitution of LVars
  , LSubst
  , LNSubst
  , prettyLNSubst
) where


import           Term.LTerm
import           Term.Rewriting.Definitions

import           Text.PrettyPrint.Highlight
import           Logic.Connectives

import           Utils.Misc

import           Data.Maybe
import           Data.Map ( Map )
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.List
import           Data.Binary
-- import           Data.Monoid (mempty)

-- import           Control.Applicative
import           Control.DeepSeq
import Data.Data (Data)

----------------------------------------------------------------------
-- Substitutions
----------------------------------------------------------------------

-- | We use the data type @Subst c v@ of substitutions. @c@ is the type of constants
--   and @v@ the type of variables.
newtype Subst c v = Subst { sMap :: Map v (VTerm c v) }
    deriving ( Eq, Ord, NFData, Binary)



-- | A substitution for logical variables.
type LSubst c = Subst c LVar

-- | A substitution with names and logical variables.
type LNSubst = Subst Name LVar

-- Application
----------------------------------------------------------------------

-- | @applyLit subst l@ applies the substitution @subst@ to the literal @l@.
applyLit :: IsVar v => Subst c v -> Lit c v -> VTerm c v
applyLit subst v@(Var i)  = fromMaybe (lit v) $ M.lookup i (sMap subst)
applyLit _     c@(Con _)  = lit c

-- | @applyVTerm subst t@ applies the substitution @subst@ to the term @t@.
applyVTerm :: (IsConst c, IsVar v) => Subst c v -> VTerm c v -> VTerm c v
applyVTerm = applyVTermProj applyLit

-- | Variant of @applyVTerm@ with custom function to apply literals
applyVTermProj :: Ord a => (t1 -> t2 -> Term a) -> t1 -> Term t2 -> Term a
applyVTermProj f subst t = case viewTerm t of
    Lit l            -> f subst l
    FApp (AC o) ts   -> fAppAC   o (map (applyVTermProj f subst) ts)
    FApp (C o)  ts   -> fAppC    o (map (applyVTermProj f subst) ts)
    FApp (NoEq o) ts -> fAppNoEq o (map (applyVTermProj f subst) ts)
    FApp List ts     -> fAppList   (map (applyVTermProj f subst) ts)


-- Construction
----------------------------------------------------------------------

-- | Convert a list to a substitution. The @x/x@ mappings are removed.
substFromList :: IsVar v => [(v, VTerm c v)] -> Subst c v
substFromList xs  =
    Subst (M.fromList [ (v,t) | (v,t) <- xs, not (equalToVar t v) ])

-- | Returns @True@ if given term is equal to given variable.
equalToVar :: IsVar v => VTerm c v -> v -> Bool
equalToVar (viewTerm -> Lit (Var v')) v = v == v'
equalToVar _                          _ = False

-- | Convert a map to a substitution. The @x/x@ mappings are removed.
-- FIXME: implement directly, use substFromMap for substFromList.
substFromMap :: IsVar v => Map v (VTerm c v) -> Subst c v
substFromMap = Subst . M.filterWithKey (\v t -> not $ equalToVar t v)

-- | @emptySubVFree@ is the substitution with empty domain.
emptySubst :: Subst c v
emptySubst = Subst M.empty

-- Composition
----------------------------------------------------------------------

-- | @applySubst subst subst'@ applies the substitution @subst@ to the range of
--   the substitution @subst'@.
applySubst :: (IsConst c, IsVar v)
           => Subst c v -> Subst c v -> Subst c v
applySubst subst subst' = mapRange (applyVTerm subst) subst'

-- | @compose s1 s2@ composes the substitutions s1 and s2. The result is
--   @s1.s2@, i.e., it has the same effect as @(t s2) s1 = s1(s2(t))@
--   when applied to a term @t@.
compose :: (IsConst c, IsVar v)
        => Subst c v -> Subst c v -> Subst c v
compose s1 s2 =
    Subst $ sMap (applySubst s1 s2) `M.union` sMap (restrict (dom s1 \\ dom s2) s1)

-- Operations
----------------------------------------------------------------------

-- | @restrict vars subst@ restricts the domain of the substitution @subst@ to @vars@.
restrict :: IsVar v => [v] -> Subst c v -> Subst c v
restrict vs (Subst smap) = Subst (M.filterWithKey (\v _ -> v `elem` vs) smap)

-- | @mapRange f subst@ maps the function @f@ over the range of the substitution @subst@.
mapRange :: (IsVar v)
         => (VTerm c v -> VTerm c2 v)
         -> Subst c v  -> Subst c2 v
mapRange f subst@(Subst _) =
    Subst $ M.mapMaybeWithKey (\i t -> filterRefl i (f t)) (sMap subst)
  where
    filterRefl i (viewTerm -> Lit (Var j)) | i == j = Nothing
    filterRefl _ t                                  = Just t


-- Queries
----------------------------------------------------------------------

-- | @dom subst@ returns the domain of the substitution @substs@.
dom :: Subst c v -> [v]
dom = M.keys . sMap

-- | @range subst@ returns the range of the substitution @substs@.
range :: Subst c v -> [VTerm c v]
range = M.elems . sMap

-- | @varsRange subst@ returns all variables in the range of the substitution.
varsRange :: IsVar v => Subst c v -> [v]
varsRange = varsVTerm . fAppList . range

-- Views
----------------------------------------------------------------------

-- | Convert substitution to list.
substToList :: Subst c v -> [(v,VTerm c v)]
substToList = M.toList . sMap

-- | @substToPairOn vs sigma@ converts the list of variables @[x1,..,xk]@ to
--   @[sigma(x1),..,sigma(xk)]@.
substToListOn :: (IsVar v) => [v] -> Subst c v -> [VTerm c v]
substToListOn vs subst = map (applyLit subst) (map Var vs)

-- | Returns the image of @i@ under @subst@ if @i@ is in the domain of @subst@.
imageOf :: IsVar v => Subst c v -> v -> Maybe (VTerm c v)
imageOf subst i = M.lookup i (sMap subst)

----------------------------------------------------------------------
-- Boilerplate instances
----------------------------------------------------------------------

instance (Show v, Show c) => Show (Subst c v) where
    show subst@(Subst _) = "{" ++ mappings ++"}"
      where
        mappings =
            intercalate ", " [ show t ++" <~ "++show v | (v,t) <- substToList subst ]

instance Sized (Subst c v) where
    size = sum . map size . range

-- Instances
------------

instance Ord c => HasFrees (LSubst c) where
    foldFrees  f = foldFrees f . sMap
    foldFreesOcc = mempty -- we ignore occurences in substitutions for now
    mapFrees   f = (substFromList <$>) . mapFrees   f . substToList

-- | Types that support the application of some type
class Apply t' t where
    apply :: t' -> t -> t

instance  (Apply s v) => Apply s (Lit c v) where
        apply subst (Var v)   = Var (apply subst v)
        apply _     l@(Con _) = l

-- the overlapping instance overwrites the overlappable instance it there is
-- only one overlapping instance. We use this to get a fast implementation for
-- substitutions that map the term, but also have the generality to define
-- substitutions that don't match the variables used in the term.

instance {-# OVERLAPPING #-} (Show c, Show v, IsVar v) => Apply (Subst c v) v where
    apply subst x = maybe x extractVar $ imageOf subst x
      where
        extractVar (viewTerm -> Lit (Var x')) = x'
        extractVar t              =
          error $ "apply (LVar): variable '" ++ show x ++
                  "' substituted with term '" ++ show t ++ "'"

instance {-# OVERLAPPING #-}  (IsConst c, IsVar v) => Apply (Subst c v) (VTerm c v) where
    apply subst = applyVTerm subst

instance {-# OVERLAPPABLE #-}  (Ord c, Ord v, Apply s (Lit c v)) => Apply s (Term (Lit c v)) where
    apply subst t = applyVTermProj (\s' t' -> lit $ apply s' t') subst t

instance {-# OVERLAPPABLE #-}  (Apply s v) => Apply s (BVar v) where
    apply _     x@(Bound _) = x
    apply subst (Free  v) = Free (apply subst v)

instance {-# OVERLAPPING #-} (IsConst c, IsVar v) => Apply (Subst c v) (VTerm c (BVar v)) where
    apply subst = (`bindTerm` applyBLLit)
      where
        applyBLLit l@(Var (Free v)) =
            maybe (lit l) (fmapTerm (fmap Free)) (imageOf subst v)
        applyBLLit l                = lit l

instance Apply s () where
    apply _ = id

instance Apply s Char where
    apply _ = id

instance Apply s Int where
    apply _ = id

instance Apply s Bool where
    apply _ = id

instance (Apply s a, Apply s b) => Apply s (a, b) where
    apply subst (x,y) = (apply subst x, apply subst y)

instance (Apply s a, Apply s b, Apply s c) => Apply s (a, b, c) where
    apply subst (x,y,z) = (apply subst x, apply subst y, apply subst z)

instance (Apply s a, Apply s b, Apply s c, Apply s d) => Apply s (a, b, c, d) where
    apply subst (x,y,z,t) = (apply subst x, apply subst y, apply subst z, apply subst t)

instance Apply s a => Apply s (Maybe a) where
    apply subst = fmap (apply subst)

instance (Apply s a, Apply s b) => Apply s (Either a b) where
    apply subst = either (Left . apply subst) (Right . apply subst)

instance Apply s a => Apply s [a] where
    apply subst = fmap (apply subst)

instance Apply s a => Apply s (Map k a) where
    apply subst = fmap (apply subst)

instance Apply s a => Apply s (Conj a) where
    apply subst = fmap (apply subst)

instance Apply s a => Apply s (Disj a) where
    apply subst = fmap (apply subst)

instance (Ord a, Apply s a) => Apply s (S.Set a) where
    apply subst = S.map (apply subst)

instance Apply s t => Apply s (Equal t) where
    apply subst = fmap (apply subst)

----------------------------------------------------------------------
-- Pretty Printing
----------------------------------------------------------------------

-- | Pretty print a substitution.
prettySubst :: (Ord c, Ord v, HighlightDocument d, Show c, Show v)
            => (v -> d) -> (Lit c v -> d) -> Subst c v -> [d]
prettySubst ppVar ppLit =
    map pp . M.toList . equivClasses . substToList
  where
    pp (t, vs)  = prettyTerm ppLit t <-> operator_ " <~ {" <>
        (fsep $ punctuate comma $ map ppVar $ S.toList vs) <> operator_ "}"

-- | Pretty print a substitution with logical variables.
prettyLNSubst :: (Ord c, HighlightDocument d, Show c)
              => LSubst c -> d
prettyLNSubst = vcat . prettySubst (text . show) (text . show)
