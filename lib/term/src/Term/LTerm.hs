{-# LANGUAGE
      CPP, FlexibleContexts, FlexibleInstances, TypeSynonymInstances,
      MultiParamTypeClasses, DeriveDataTypeable, StandaloneDeriving,
      TemplateHaskell, GeneralizedNewtypeDeriving, ViewPatterns
  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Terms with logical variables  and names.
module Term.LTerm (

  -- * Names
    Name(..)
  , NameTag(..)
  , NameId(..)

  , NTerm

  -- ** Queries
  , sortOfName

  -- ** Construction
  , freshTerm
  , pubTerm

  -- * LVar
  , LSort(..)
  , LVar(..)
  , NodeId
  , LTerm
  , LNTerm

  , freshLVar
  , sortPrefix
  , sortSuffix
  , sortCompare
  , sortOfLTerm
  , sortOfLNTerm
  , isMsgVar
  , isFreshVar
  , isSimpleTerm
  , inputTerms

  -- ** Destructors
  , ltermVar
  , ltermVar'
  , ltermNodeId
  , ltermNodeId'
  , bltermNodeId
  , bltermNodeId'


  -- ** Manging Free LVars

  , HasFrees(..)
  , MonotoneFunction(..)
  , occurs
  , freesList
  , frees
  , someInst
  , rename
  , renamePrecise
  , eqModuloFreshnessNoAC
  , avoid
  , evalFreshAvoiding
  , evalFreshTAvoiding
  , renameAvoiding

  -- * BVar
  , BVar(..)
  , BLVar
  , BLTerm
  , foldBVar
  , fromFree

  -- * Pretty-Printing
  , prettyLVar
  , prettyNodeId
  , prettyNTerm
  , prettyLNTerm

  -- * Convenience exports
  , module Term.VTerm
) where

import Term.VTerm
import Term.Rewriting.Definitions

import Text.PrettyPrint.Class

import Control.Applicative
import Control.Monad.Fresh
import Control.Monad.Bind
import Control.DeepSeq
import Control.Monad.Identity

import Data.DeriveTH
import qualified Data.Set   as S
import qualified Data.Map as M

import Data.Generics hiding (GT)

import qualified Data.DList as D
import Data.Traversable
import Data.Monoid
import Data.Binary
import Data.Foldable hiding (concatMap, elem)

import Safe (fromJustNote)

import Extension.Prelude
import Extension.Data.Monoid

import Logic.Connectives

------------------------------------------------------------------------------
-- Sorts.
------------------------------------------------------------------------------

-- | Sorts for logical variables. They satisfy the following sub-sort relation:
--
-- >  LSortMsg   < LSortMSet
-- >  LSortFresh < LSortMsg
-- >  LSortPub   < LSortMsg
--
data LSort = LSortPub   -- ^ Arbitrary public names.
           | LSortFresh -- ^ Arbitrary fresh names.
           | LSortMsg   -- ^ Arbitrary messages.
           | LSortMSet  -- ^ Sort for multisets.
           | LSortNode  -- ^ Sort for variables denoting nodes of derivation graphs.
           deriving( Eq, Ord, Show, Enum, Bounded, Typeable, Data )

-- | @sortCompare s1 s2@ compares @s1@ and @s2@ with respect to the partial order on sorts.
--   Partial order: Node      MSet
--                             |
--                            Msg
--                           /   \
--                         Pub  Fresh
sortCompare :: LSort -> LSort -> Maybe Ordering
sortCompare s1 s2 = case (s1, s2) of
    (a, b) | a == b          -> Just EQ
    -- Node is incomparable to all other sorts, invalid input
    (LSortNode,  _        )  -> Nothing
    (_,          LSortNode)  -> Nothing
    -- MSet is greater than all except Node
    (LSortMSet,  _        )  -> Just GT
    (_,          LSortMSet)  -> Just LT
    -- Msg is greater than all sorts except Node and MSet
    (LSortMsg,   _        )  -> Just GT
    (_,          LSortMsg )  -> Just LT
    -- The remaining combinations (Pub/Fresh) are incomparable
    _                        -> Nothing

-- | @sortPrefix s@ is the prefix we use for annotating variables of sort @s@.
sortPrefix :: LSort -> String
sortPrefix LSortMsg   = ""
sortPrefix LSortFresh = "~"
sortPrefix LSortPub   = "$"
sortPrefix LSortNode  = "#"
sortPrefix LSortMSet  = "%"

-- | @sortSuffix s@ is the suffix we use for annotating variables of sort @s@.
sortSuffix :: LSort -> String
sortSuffix LSortMsg   = "msg"
sortSuffix LSortFresh = "fresh"
sortSuffix LSortPub   = "pub"
sortSuffix LSortNode  = "node"
sortSuffix LSortMSet  = "mset"


------------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------------

-- | Type safety for names.
newtype NameId = NameId { getNameId :: String }
    deriving( Eq, Ord, Typeable, Data, NFData, Binary )

-- | Tags for names.
data NameTag = FreshName | PubName
    deriving( Eq, Ord, Show, Typeable, Data )

-- | Names.
data Name = Name {nTag :: NameTag, nId :: NameId}
    deriving( Eq, Ord, Typeable, Data )

-- | Terms with literals containing names and arbitrary variables.
type NTerm v = VTerm Name v


-- Instances
------------

instance IsConst Name where

instance Show Name where
  show (Name FreshName n) = "~'" ++ show n ++ "'"
  show (Name PubName   n) = "'"  ++ show n ++ "'"

instance Show NameId where
  show = getNameId

-- Construction of terms with names
-----------------------------------

-- | @freshTerm f@ represents the fresh name @f@.
freshTerm :: String -> NTerm v
freshTerm = lit . Con . Name FreshName . NameId

-- | @pubTerm f@ represents the pub name @f@.
pubTerm :: String -> NTerm v
pubTerm = lit . Con . Name PubName . NameId

-- | Return 'LSort' for given 'Name'.
sortOfName :: Name -> LSort
sortOfName (Name FreshName _) = LSortFresh
sortOfName (Name PubName   _) = LSortPub

------------------------------------------------------------------------------
-- LVar: logical variables
------------------------------------------------------------------------------


-- | Logical variables. Variables with the same name and index but different
-- sorts are regarded as different variables.
data LVar = LVar
     { lvarName :: String
     , lvarSort :: !LSort     -- FIXME: Rename to 'sortOfLVar' for consistency
                              -- with the other 'sortOf' functions.
     , lvarIdx  :: !Integer
     }
     deriving( Typeable, Data )

-- | An alternative name for logical variables, which are intented to be
-- variables of sort 'LSortNode'.
type NodeId = LVar

-- | Terms used for proving; i.e., variables fixed to logical variables.
type LTerm c = VTerm c LVar

-- | Terms used for proving; i.e., variables fixed to logical variables
--   and constants to Names.
type LNTerm = VTerm Name LVar

-- | @freshLVar v@ represents a fresh logical variable with name @v@.
freshLVar :: MonadFresh m => String -> LSort -> m LVar
freshLVar n s = LVar n s <$> freshIdents 1

-- | Returns the most precise sort of an 'LTerm'.
sortOfLTerm :: Show c => (c -> LSort) -> LTerm c -> LSort
sortOfLTerm sortOfConst t = case viewTerm2 t of
    Lit2 (Con c)  -> sortOfConst c
    Lit2 (Var lv) -> lvarSort lv
    Empty         -> LSortMSet
    FUnion _      -> LSortMSet
    _             -> LSortMsg

-- | Returns the most precise sort of an 'LNTerm'.
sortOfLNTerm :: LNTerm -> LSort
sortOfLNTerm = sortOfLTerm sortOfName

-- | Is a term a message variable?
isMsgVar :: LNTerm -> Bool
isMsgVar (viewTerm -> Lit (Var v)) = (lvarSort v == LSortMsg)
isMsgVar _                         = False

-- | Is a term a fresh variable?
isFreshVar :: LNTerm -> Bool
isFreshVar (viewTerm -> Lit (Var v)) = (lvarSort v == LSortFresh)
isFreshVar _                         = False

-- | The required components to construct the message.
inputTerms :: LNTerm -> [LNTerm]
inputTerms (viewTerm2 -> FMult ts)    = concatMap inputTerms ts
inputTerms (viewTerm2 -> FInv t1)     = inputTerms t1
inputTerms (viewTerm2 -> FPair t1 t2) = inputTerms t1 ++ inputTerms t2
inputTerms t                          = [t]

{-
-- | Is a message trivial; i.e., can for sure be instantiated with something
-- known to the intruder?
trivial :: LNTerm -> Bool
trivial (viewTerm -> FApp _ [])                  = True
trivial (viewTerm -> Lit (Con (Name PubName _))) = True
trivial (viewTerm -> Lit (Var v))                = case lvarSort v of
                                                     LSortPub -> True
                                                     LSortMsg -> True
                                                     _        -> False
trivial _                                        = False
-}

-- | A term is *simple* iff there is an instance of this term that can be
-- constructed from public names only. i.e., the term does not contain any
-- fresh names or fresh variables.
isSimpleTerm :: LNTerm -> Bool
isSimpleTerm =
    getAll . foldMap (All . (LSortFresh /=) . sortOfLit)
  where
    sortOfLit (Con n) = sortOfName n
    sortOfLit (Var v) = lvarSort v


-- Destructors
--------------

-- | Extract a variable of the given sort from a term that may be such a
-- variable. Use 'termVar', if you do not want to restrict the sort.
ltermVar :: LSort -> LTerm c -> Maybe LVar
ltermVar s t = do v <- termVar t; guard (s == lvarSort v); return v

-- | Extract a variable of the given sort from a term that must be such a
-- variable. Fails with an error, if that is not possible.
ltermVar' :: Show c => LSort -> LTerm c -> LVar
ltermVar' s t =
    fromJustNote err (ltermVar s t)
  where
    err = "ltermVar': expected variable term of sort " ++ show s ++ ", but got " ++ show t

-- | Extract a node-id variable from a term that may be a node-id variable.
ltermNodeId  :: LTerm c -> Maybe LVar
ltermNodeId = ltermVar LSortNode

-- | Extract a node-id variable from a term that must be a node-id variable.
ltermNodeId' :: Show c => LTerm c -> LVar
ltermNodeId' = ltermVar' LSortNode



-- BVar: Bound variables
------------------------

-- | Bound and free variables.
data BVar v = Bound Integer  -- ^ A bound variable in De-Brujin notation.
            | Free  v        -- ^ A free variable.
            deriving( Eq, Ord, Show, Data, Typeable )

-- | 'LVar's combined with quantified variables. They occur only in 'LFormula's.
type BLVar = BVar LVar

-- | Terms built over names and 'LVar's combined with quantified variables.
type BLTerm = NTerm BLVar


-- | Fold a possibly bound variable.
{-# INLINE foldBVar #-}
foldBVar :: (Integer -> a) -> (v -> a) -> BVar v -> a
foldBVar fBound fFree = go
  where
    go (Bound i) = fBound i
    go (Free v)  = fFree v

instance Functor BVar where
    fmap f = foldBVar Bound (Free . f)

instance Foldable BVar where
    foldMap f = foldBVar mempty f

instance Traversable BVar where
    traverse f = foldBVar (pure . Bound) (fmap Free . f)

instance Applicative BVar where
   pure  = return
   (<*>) = ap

instance Monad BVar where
    return  = Free
    m >>= f = foldBVar Bound f m

-- | Extract the name of free variable under the assumption the variable is
-- guaranteed to be of the form @Free a@.
fromFree :: BVar v -> v
fromFree (Free v)  = v
fromFree (Bound i) = error $ "fromFree: bound variable '" ++ show i ++ "'"

-- | Extract a node-id variable from a term that may be a node-id variable.
bltermNodeId  :: BLTerm -> Maybe LVar
bltermNodeId t = do
    Free v <- termVar t; guard (LSortNode == lvarSort v); return v

-- | Extract a node-id variable from a term that must be a node-id variable.
bltermNodeId' :: BLTerm -> LVar
bltermNodeId' t =
    fromJustNote err (bltermNodeId t)
  where
    err = "bltermNodeId': expected free node-id variable term, but got " ++
           show t

-- Instances
------------

instance Eq LVar where
  (LVar n1 s1 i1) == (LVar n2 s2 i2) = i1 == i2 && s1 == s2 && n1 == n2

-- An ord instane that prefers the 'lvarIdx' over the 'lvarName'.
instance Ord LVar where
    compare (LVar x1 x2 x3) (LVar y1 y2 y3) =
        compare x3 y3 & compare x2 y2 & compare x1 y1 & EQ
      where
        EQ & x = x
        x  & _ = x

instance Show LVar where
    show (LVar v s i) =
        sortPrefix s ++ body
      where
        body | null v           = show i
--             | isDigit (last v) = v ++ "." ++ show i
             | i == 0           = v
             | otherwise        = v ++ "." ++ show i

instance IsVar LVar where

------------------------------------------------------------------------------
-- Managing bound and free LVars
------------------------------------------------------------------------------

-- | For performance reasons, we distinguish between monotone functions on
-- 'LVar's and arbitrary functions. The monotone functions much map 'LVar's to
-- equal or larger 'LVar's. This ensures that the AC-normal form does not have
-- to be recomputed. If you are unsure about what to use, then use the
-- 'Arbitrary' function.
data MonotoneFunction f = Monotone (LVar -> f LVar )
                        | Arbitrary (LVar -> f LVar )

-- | @HasFree t@ denotes that the type @t@ has free @LVar@ variables. They can
-- be collected using 'foldFrees' and mapped in the context of an applicative
-- functor using 'mapFrees'.
--
-- When defining instances of this class, you have to ensure that only the free
-- LVars are collected and mapped and no others. The instances for standard
-- Haskell types assume that all variables free in all type arguments are free.
--
-- Once we need it, we can use type synonym instances to parametrize over the
-- variable type.
--
class HasFrees t where
    foldFrees  :: Monoid m      => (LVar -> m      ) -> t -> m
    mapFrees   :: Applicative f => MonotoneFunction f -> t -> f t

-- | @v `occurs` t@ iff variable @v@ occurs as a free variable in @t@.
occurs :: HasFrees t => LVar -> t -> Bool
occurs x = getAny . foldFrees (Any . (x ==))

-- | @freesDList t@ is the difference list of all free variables of @t@.
freesDList :: HasFrees t => t -> D.DList LVar
freesDList = foldFrees pure

-- | @freesList t@ is the list of all free variables of @t@.
freesList :: HasFrees t => t -> [LVar]
freesList = D.toList . freesDList

-- | @frees t@ is the sorted and duplicate-free list of all free variables in
-- @t@.
frees :: HasFrees t => t -> [LVar]
frees = sortednub . freesList

-- | @someInst t@ returns an instance of @t@ where all free variables whose
-- binding is not yet determined by the caller are replaced with fresh
-- variables.
someInst :: (MonadFresh m, MonadBind LVar LVar m, HasFrees t) => t -> m t
someInst = mapFrees (Arbitrary $ \x -> importBinding (`LVar` lvarSort x) x (lvarName x))

-- | @rename t@ replaces all variables in @t@ with fresh variables.
--   Note that the result is not guaranteed to be equal for terms that are
--   equal modulo changing the indices of variables.
rename :: (MonadFresh m, HasFrees a) => a -> m a
rename x = case boundsVarIdx x of
    Nothing                     -> return x
    Just (minVarIdx, maxVarIdx) -> do
      freshStart <- freshIdents (succ (maxVarIdx - minVarIdx))
      return . runIdentity . mapFrees (Monotone $ incVar (freshStart - minVarIdx)) $ x
  where
    incVar shift (LVar n so i) = pure $ LVar n so (i+shift)

-- | @renamePrecise t@ replaces all variables in @t@ with fresh variables.
--   If 'Control.Monad.PreciseFresh' is used with non-AC terms and identical
--   fresh state, the same result is returned for two terms that only differ
--   in the indices of variables.
renamePrecise :: (MonadFresh m, HasFrees a) => a -> m a
renamePrecise x = evalBindT (someInst x) noBindings

-- | @eqModuloFreshness t1 t2@ checks whether @t1@ is equal to @t2@ modulo
-- renaming of indices of free variables. Note that the normal form is not
-- unique with respect to AC symbols.
eqModuloFreshnessNoAC :: (HasFrees a, Eq a) => a -> a -> Bool
eqModuloFreshnessNoAC t1 =
     -- this formulation shares normalisation of t1 among further calls to
     -- different t2.
    (normIndices t1 ==) . normIndices
  where
    normIndices = (`evalFresh` nothingUsed) . (`evalBindT` noBindings) .
                  mapFrees (Arbitrary $ \x -> importBinding (`LVar` lvarSort x) x "")

-- | The mininum and maximum index of all free variables.
boundsVarIdx :: HasFrees t => t -> Maybe (Integer, Integer)
boundsVarIdx = getMinMax . foldFrees (minMaxSingleton . lvarIdx)

-- | @avoid t@ computes a 'FreshState' that avoids generating
-- variables occurring in @t@.
avoid :: HasFrees t => t -> FreshState
avoid = maybe 0 (succ . snd) . boundsVarIdx

-- | @m `evalFreshAvoiding` t@ evaluates the monadic action @m@ with a
-- fresh-variable supply that avoids generating variables occurring in @t@.
evalFreshAvoiding :: HasFrees t => Fresh a -> t -> a
evalFreshAvoiding m = evalFresh m . avoid

-- | @m `evalFreshTAvoiding` t@ evaluates the monadic action @m@ in the
-- underlying monad with a fresh-variable supply that avoids generating
-- variables occurring in @t@.
evalFreshTAvoiding :: (Monad m, HasFrees t) => FreshT m a -> t -> m a
evalFreshTAvoiding m = evalFreshT m . avoid

-- | @s `renameAvoiding` t@ replaces all free variables in @s@ by
--   fresh variables avoiding variables in @t@.
renameAvoiding :: (HasFrees s, HasFrees t) => s -> t -> s
s `renameAvoiding` t = rename s `evalFreshAvoiding` t

-- Instances
------------

instance HasFrees LVar where
    foldFrees = id
    mapFrees  (Arbitrary f) = f
    mapFrees  (Monotone f)  = f

instance HasFrees v => HasFrees (Lit c v) where
    foldFrees f (Var x) = foldFrees f x
    foldFrees _ _       = mempty

    mapFrees f (Var x) = Var <$> mapFrees f x
    mapFrees _ l       = pure l

instance HasFrees v => HasFrees (BVar v) where
    foldFrees _ (Bound _) = mempty
    foldFrees f (Free v)  = foldFrees f v

    mapFrees _ b@(Bound _) = pure b
    mapFrees f   (Free v)  = Free <$> mapFrees f v

instance (HasFrees l, Ord l) => HasFrees (Term l) where
    foldFrees  f = foldMap (foldFrees f)
    mapFrees   f (viewTerm -> Lit l)    = lit <$> mapFrees f l
    mapFrees   f@(Arbitrary _) (viewTerm -> FApp o l) = fApp o <$> mapFrees f l
    mapFrees   f@(Monotone _)  (viewTerm -> FApp o l) = unsafefApp o <$> mapFrees f l

instance HasFrees a => HasFrees (Equal a) where
    foldFrees f = foldMap (foldFrees f)
    mapFrees  f = traverse (mapFrees f)

instance HasFrees a => HasFrees (Match a) where
    foldFrees f = foldMap (foldFrees f)
    mapFrees  f = traverse (mapFrees f)

instance HasFrees a => HasFrees (RRule a) where
    foldFrees f = foldMap (foldFrees f)
    mapFrees  f = traverse (mapFrees f)


instance HasFrees () where
    foldFrees  _ = const mempty
    mapFrees   _ = pure

instance HasFrees Int where
    foldFrees  _ = const mempty
    mapFrees   _ = pure

instance HasFrees Integer where
    foldFrees  _ = const mempty
    mapFrees   _ = pure

instance HasFrees Bool where
    foldFrees  _ = const mempty
    mapFrees   _ = pure

instance HasFrees Char where
    foldFrees  _ = const mempty
    mapFrees   _ = pure

instance HasFrees a => HasFrees (Maybe a) where
    foldFrees  f = foldMap (foldFrees f)
    mapFrees   f = traverse (mapFrees f)

instance (HasFrees a, HasFrees b) => HasFrees (Either a b) where
    foldFrees  f = either (foldFrees f) (foldFrees f)
    mapFrees   f = either (fmap Left . mapFrees   f) (fmap Right . mapFrees   f)

instance (HasFrees a, HasFrees b) => HasFrees (a, b) where
    foldFrees  f (x, y) = foldFrees f x `mappend` foldFrees f y
    mapFrees   f (x, y) = (,) <$> mapFrees   f x <*> mapFrees   f y

instance (HasFrees a, HasFrees b, HasFrees c) => HasFrees (a, b, c) where
    foldFrees  f (x, y, z)    = foldFrees f (x, (y, z))
    mapFrees   f (x0, y0, z0) =
        (\(x, (y, z)) -> (x, y, z)) <$> mapFrees f (x0, (y0, z0))

instance HasFrees a => HasFrees [a] where
    foldFrees  f = foldMap  (foldFrees f)
    mapFrees   f = traverse (mapFrees f)

instance HasFrees a => HasFrees (Disj a) where
    foldFrees  f = foldMap  (foldFrees f)
    mapFrees   f = traverse (mapFrees f)

instance HasFrees a => HasFrees (Conj a) where
    foldFrees  f = foldMap  (foldFrees f)
    mapFrees   f = traverse (mapFrees f)

instance (Ord a, HasFrees a) => HasFrees (S.Set a) where
    foldFrees  f = foldMap  (foldFrees f)
    mapFrees   f = fmap S.fromList . mapFrees f . S.toList

instance (Ord k, HasFrees k, HasFrees v) => HasFrees (M.Map k v) where
    foldFrees  f = M.foldrWithKey combine mempty
      where
        combine k v m = foldFrees f k `mappend` (foldFrees f v `mappend` m)
    mapFrees   f = fmap M.fromList . mapFrees f . M.toList


------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

-- | Pretty print a 'LVar'.
prettyLVar :: Document d => LVar -> d
prettyLVar = text . show

-- | Pretty print a 'NodeId'.
prettyNodeId :: Document d => NodeId -> d
prettyNodeId = text . show

-- | Pretty print an @NTerm@.
prettyNTerm :: (Show v, Document d) => NTerm v -> d
prettyNTerm = prettyTerm (text . show)

-- | Pretty print an @LTerm@.
prettyLNTerm :: Document d => LNTerm -> d
prettyLNTerm = prettyNTerm


-- derived instances
--------------------

$( derive makeBinary ''NameTag)
$( derive makeBinary ''Name)
$( derive makeBinary ''LSort)
$( derive makeBinary ''LVar)
$( derive makeBinary ''BVar)

$( derive makeNFData ''NameTag)
$( derive makeNFData ''Name)
$( derive makeNFData ''LSort)
$( derive makeNFData ''LVar)
$( derive makeNFData ''BVar)
