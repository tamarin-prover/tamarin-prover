{-# LANGUAGE TupleSections, TypeSynonymInstances, GADTs,FlexibleContexts,EmptyDataDecls,StandaloneDeriving, DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses, DeriveFunctor, ScopedTypeVariables #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Standard substitutions (with free variables).
module Term.Substitution.SubstVFree (
  -- * General Substitutions
    Subst(..)

  -- * application of substitutions
  , applyVTerm
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

  -- *
  , Apply(..)

  -- * Pretty printing
  , prettySubst

  -- * Substitution of LVars
  , LSubst
  , LNSubst
  , prettyLNSubst
) where


import Term.LTerm
import Term.Rewriting.NormAC
import Text.PrettyPrint.Highlight
import Logic.Connectives

import Extension.Prelude
import Utils.Misc

import Data.Maybe
import Data.Map ( Map )
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List
import Control.Applicative

----------------------------------------------------------------------
-- Substitutions
----------------------------------------------------------------------

-- | We use the data type @Subst c v@ of substitutions. @c@ is the type of constants
--   and @v@ the type of variables.
data Subst c v = Subst { sMap :: Map v (VTerm c v) }
    deriving ( Eq, Ord )

-- | A substitution for logical variables.
type LSubst c = Subst c LVar

-- | A substitution with names and logical variables.
type LNSubst = Subst Name LVar

-- Application
----------------------------------------------------------------------

-- | @applyLit subst l@ applies the substitution @subst@ to the literal @l@.
applyLit :: IsVar v => Subst c v -> Lit c v -> VTerm c v
applyLit subst v@(Var i)  = fromMaybe (Lit v) $ M.lookup i (sMap subst)
applyLit _     c@(Con _)  = Lit c



-- | @applyTermVFree subst t@ applies the substitution @subst@ to the term @t@.
applyVTerm :: (IsConst c, IsVar v) => Subst c v -> VTerm c v -> VTerm c v
applyVTerm subst = (>>= applyLit subst)


-- Construction
----------------------------------------------------------------------

-- | Convert a list to a substitution. The @x/x@ mappings are removed.
substFromList :: IsVar v => [(v, VTerm c v)] -> Subst c v
substFromList xs  =
    Subst (M.fromList [ (v,t) | (v,t) <- xs, not (t `equalToVar` v) ])
  where
    equalToVar (Lit (Var v')) v = v == v'
    equalToVar _              _ = False

-- | Convert a map to a substitution. The @x/x@ mappings are removed.
-- FIXME: implement directly, use substFromMap for substFromList.
substFromMap :: IsVar v => Map v (VTerm c v) -> Subst c v
substFromMap = substFromList . M.toList

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
    Subst $
      sMap (applySubst s1 s2) `M.union` sMap (restrict (dom s1 \\ dom s2) s1)

-- Operations
----------------------------------------------------------------------

-- | @restrict vars subst@ restricts the domain of the substitution @subst@ to @vars@.
restrict :: IsVar v => [v] -> Subst c v -> Subst c v
restrict vs (Subst smap) = Subst (M.filterWithKey (\v _ -> v `elem` vs) smap)

-- | @mapRange f subst@ maps the function @f@ over the range of the substitution @subst@.
mapRange :: (IsConst c, IsVar v, IsConst c2)
         => (VTerm c v -> VTerm c2 v)
         -> Subst c v  -> Subst c2 v
mapRange f subst@(Subst _) =
    Subst $ M.mapMaybeWithKey (\i t -> filterRefl i (f t)) (sMap subst)
  where
    filterRefl i (Lit (Var j)) | i == j = Nothing
    filterRefl _ t                      = Just t


-- Queries
----------------------------------------------------------------------

-- | @dom subst@ returns the domain of the substitution @substs@.
dom :: Subst c v -> [v]
dom = M.keys . sMap

-- | @range subst@ returns the range of the substitution @substs@.
range :: Subst c v -> [VTerm c v]
range = M.elems . sMap

-- | @varsRange subst@ returns all variables in the range of the substitution
--   FIXME: use Monoid, dlist, write occurs function.
varsRange :: IsVar v => Subst c v -> [v]
varsRange = sortednub . concatMap varsVTerm . range

-- Views
----------------------------------------------------------------------

-- | Convert substitution to list.
substToList :: Subst c v -> [(v,VTerm c v)]
substToList = M.toList . sMap

-- | @substToPairOn vs sigma@ converts the list of variables @[x1,..,xk]@ to
--   @[sigma(x1),..,sigma(xk)]@.
substToListOn :: (IsConst c, IsVar v) => [v] -> Subst c v -> [VTerm c v]
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

instance HasFrees (LSubst c) where
    foldFrees  f = foldFrees f . sMap
    mapFrees   f = (substFromList <$>) . mapFrees   f . substToList

-- | Types that support the application of 'LSubst's.
class Apply t where
    apply :: LNSubst -> t -> t

instance Apply LVar where
    apply subst x = maybe x extractVar $ imageOf subst x
      where
        extractVar (Lit (Var x')) = x'
        extractVar t              = 
          error $ "apply (LVar): variable '" ++ show x ++ 
                  "' substituted with term '" ++ show t ++ "'"

instance Apply LNTerm where
    apply subst = normAC . applyVTerm subst

instance Apply () where
    apply _ = id

instance Apply Char where
    apply _ = id

instance Apply Int where
    apply _ = id

instance Apply a => Apply [a] where
    apply subst = fmap (apply subst)

instance Apply a => Apply (Conj a) where
    apply subst = fmap (apply subst)

instance Apply a => Apply (Disj a) where
    apply subst = fmap (apply subst)

instance (Ord a, Apply a) => Apply (S.Set a) where
    apply subst = S.map (apply subst)

instance Apply t => Apply (Equal t) where
    apply subst = fmap (apply subst)


----------------------------------------------------------------------
-- Pretty Printing
----------------------------------------------------------------------

-- | Pretty print a substitution.
prettySubst :: (Ord c, Ord v, HighlightDocument d) 
            => (v -> d) -> (Lit c v -> d) -> Subst c v -> [d]
prettySubst ppVar ppLit = 
    map pp . M.toList . equivClasses . substToList
  where
    pp (t, vs)  = prettyTerm ppLit t <-> operator_ " <~ {" <> 
        (fsep $ punctuate comma $ map ppVar $ S.toList vs) <> operator_ "}"

-- | Pretty print a substitution with logical variables.
prettyLNSubst :: (Show (Lit c LVar), Ord c, HighlightDocument d)
              => LSubst c -> d
prettyLNSubst = vcat . prettySubst (text . show) (text . show)
