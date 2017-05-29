{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
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
  , sortOfLit
  , isMsgVar
  , isFreshVar
  , isSimpleTerm
  , getVar
  , getMsgVar
  , niFactors
  , containsPrivate
  , containsNoPrivateExcept
  , neverContainsFreshPriv

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
  , renameIgnoring
  , eqModuloFreshnessNoAC
  , avoid
  , evalFreshAvoiding
  , evalFreshTAvoiding
  , renameAvoiding
  , renameAvoidingIgnoring
  , avoidPrecise
  , renamePrecise
  , renameDropNamehint
  , varOccurences

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
  , showLitName

  -- * Convenience exports
  , module Term.VTerm
) where

import           Text.PrettyPrint.Class

-- import           Control.Applicative
import           Control.DeepSeq
import           Control.Monad.Bind
import           Control.Monad.Identity
import qualified Control.Monad.Trans.PreciseFresh as Precise

import           GHC.Generics                     (Generic)
import           Data.Binary
import qualified Data.DList                       as D
import           Data.Foldable                    hiding (concatMap, elem, notElem, any)
import           Data.Data
import qualified Data.Map                         as M
import           Data.Monoid
import qualified Data.Set                         as S
-- import           Data.Traversable
import qualified Data.ByteString.Char8            as BC

import           Safe                             (fromJustNote)

import           Extension.Data.Monoid
import           Extension.Prelude


import           Logic.Connectives

import           Term.Rewriting.Definitions
import           Term.VTerm

------------------------------------------------------------------------------
-- Sorts.
------------------------------------------------------------------------------

-- | Sorts for logical variables. They satisfy the following sub-sort relation:
--
-- >  LSortFresh < LSortMsg
-- >  LSortPub   < LSortMsg
--
data LSort = LSortPub   -- ^ Arbitrary public names.
           | LSortFresh -- ^ Arbitrary fresh names.
           | LSortMsg   -- ^ Arbitrary messages.
           | LSortNode  -- ^ Sort for variables denoting nodes of derivation graphs.
           deriving( Eq, Ord, Show, Enum, Bounded, Typeable, Data, Generic, NFData, Binary )

-- | @sortCompare s1 s2@ compares @s1@ and @s2@ with respect to the partial order on sorts.
--   Partial order: Node      Msg
--                           /   \
--                         Pub  Fresh
sortCompare :: LSort -> LSort -> Maybe Ordering
sortCompare s1 s2 = case (s1, s2) of
    (a, b) | a == b          -> Just EQ
    -- Node is incomparable to all other sorts, invalid input
    (LSortNode,  _        )  -> Nothing
    (_,          LSortNode)  -> Nothing
    -- Msg is greater than all sorts except Node
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

-- | @sortSuffix s@ is the suffix we use for annotating variables of sort @s@.
sortSuffix :: LSort -> String
sortSuffix LSortMsg   = "msg"
sortSuffix LSortFresh = "fresh"
sortSuffix LSortPub   = "pub"
sortSuffix LSortNode  = "node"


------------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------------

-- | Type safety for names.
newtype NameId = NameId { getNameId :: String }
    deriving( Eq, Ord, Typeable, Data, Generic, NFData, Binary )

-- | Tags for names.
data NameTag = FreshName | PubName | NodeName
    deriving( Eq, Ord, Show, Typeable, Data, Generic, NFData, Binary )

-- | Names.
data Name = Name {nTag :: NameTag, nId :: NameId}
    deriving( Eq, Ord, Typeable, Data, Generic, NFData, Binary)

-- | Terms with literals containing names and arbitrary variables.
type NTerm v = VTerm Name v


-- Instances
------------

instance IsConst Name where

instance Show Name where
  show (Name FreshName  n) = "~'" ++ show n ++ "'"
  show (Name PubName    n) = "'"  ++ show n ++ "'"
  show (Name NodeName   n) = "#'" ++ show n ++ "'"

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
sortOfName (Name NodeName  _) = LSortNode

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
     deriving( Typeable, Data, Generic, NFData, Binary )

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
freshLVar n s = LVar n s <$> freshIdent n

-- | Returns the most precise sort of an 'LTerm'.
sortOfLTerm :: Show c => (c -> LSort) -> LTerm c -> LSort
sortOfLTerm sortOfConst t = case viewTerm2 t of
    Lit2 (Con c)  -> sortOfConst c
    Lit2 (Var lv) -> lvarSort lv
    _             -> LSortMsg

-- | Returns the most precise sort of an 'LNTerm'.
sortOfLNTerm :: LNTerm -> LSort
sortOfLNTerm = sortOfLTerm sortOfName

-- | Returns the most precise sort of a 'Lit'.
sortOfLit :: Lit Name LVar -> LSort
sortOfLit (Con n) = sortOfName n
sortOfLit (Var v) = lvarSort v


-- | Is a term a message variable?
isMsgVar :: LNTerm -> Bool
isMsgVar (viewTerm -> Lit (Var v)) = (lvarSort v == LSortMsg)
isMsgVar _                         = False

-- | Is a term a fresh variable?
isFreshVar :: LNTerm -> Bool
isFreshVar (viewTerm -> Lit (Var v)) = (lvarSort v == LSortFresh)
isFreshVar _                         = False

-- | If the term is a variable, return it, nothing otherwise.
getVar :: LNTerm -> Maybe [LVar]
getVar (viewTerm -> Lit (Var v)) = Just [v]
getVar _                         = Nothing

-- | If the term is a message variable, return it, nothing otherwise.
getMsgVar :: LNTerm -> Maybe [LVar]
getMsgVar (viewTerm -> Lit (Var v)) | (lvarSort v == LSortMsg) = Just [v]
getMsgVar _                                                    = Nothing


-- Utility functions for constraint solving
-------------------------------------------

-- | The non-inverse factors of a term.
niFactors :: LNTerm -> [LNTerm]
niFactors t = case viewTerm2 t of
                FMult ts -> concatMap niFactors ts
                FInv t1  -> niFactors t1
                _        -> [t]

-- | @containsPrivate t@ returns @True@ if @t@ contains private function symbols.
containsPrivate :: Term t -> Bool
containsPrivate t = case viewTerm t of
    Lit _                          -> False
    FApp (NoEq (_,(_,Private))) _  -> True
    FApp _                      as -> any containsPrivate as

-- | containsNoPrivateExcept t t2@ returns @True@ if @t2@ contains private function symbols other than @t@.
containsNoPrivateExcept :: [BC.ByteString] -> Term t -> Bool
containsNoPrivateExcept funs t = case viewTerm t of
    Lit _                          -> True
    FApp (NoEq (f,(_,Private))) as -> (elem f funs) && (all (containsNoPrivateExcept funs) as)
    FApp _                      as -> all (containsNoPrivateExcept funs) as

    
-- | A term is *simple* iff there is an instance of this term that can be
-- constructed from public names only. i.e., the term does not contain any
-- fresh names, fresh variables, or private function symbols.
isSimpleTerm :: LNTerm -> Bool
isSimpleTerm t =
    not (containsPrivate t) && 
    (getAll . foldMap (All . (LSortFresh /=) . sortOfLit) $ t)

-- | 'True' iff no instance of this term contains fresh names or private function symbols.
neverContainsFreshPriv :: LNTerm -> Bool
neverContainsFreshPriv t =
    not (containsPrivate t) && 
    (getAll . foldMap (All . (`notElem` [LSortMsg, LSortFresh]) . sortOfLit) $ t)

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
            deriving( Eq, Ord, Show, Data, Typeable, Generic, NFData, Binary )

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

-- An ord instance that prefers the 'lvarIdx' over the 'lvarName'.
instance Ord LVar where
    compare (LVar x1 x2 x3) (LVar y1 y2 y3) =
        compare x3 y3 <> compare x2 y2 <> compare x1 y1

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


-- | This type captures the occurence of a variable in a certain context.
type Occurence = [String]

-- | For performance reasons, we distinguish between monotone functions on
-- 'LVar's and arbitrary functions. For a monotone f, if @x <= y@, then
-- @f x <= f y@. This ensures that the AC-normal form does not have
-- to be recomputed. If you are unsure about what to use, then use the
-- 'Arbitrary' function.
data MonotoneFunction f = Monotone (LVar -> f LVar )
                        | Arbitrary (LVar -> f LVar )

-- | @HasFree t@ denotes that the type @t@ has free @LVar@ variables. They can
-- be collected using 'foldFrees' and 'foldFreesOcc' and mapped in the context
-- of an applicative functor using 'mapFrees'.
--
-- When defining instances of this class, you have to ensure that only the free
-- LVars are collected and mapped and no others. The instances for standard
-- Haskell types assume that all variables free in all type arguments are free.
-- The 'foldFreesOcc' is only used to define the function 'varOccurences'. See
-- below for required properties of the instance methods.
--
-- Once we need it, we can use type synonym instances to parametrize over the
-- variable type.
--
class HasFrees t where
    foldFrees  :: Monoid m      => (LVar -> m      ) -> t -> m
    foldFreesOcc :: Monoid m => (Occurence -> LVar -> m) -> Occurence -> t -> m
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

-- | Returns the variables occuring in @t@ together with the contexts they appear in.
-- Note that certain contexts (and variables only occuring in such contexts) are
-- ignored by this function.
-- The function is used to "guess" renamings of variables, i.e., if t is a renaming of s,
-- then variables that occur in equal contexts in t and s are probably renamings of
-- each other.
varOccurences :: HasFrees a => a -> [(LVar, S.Set Occurence)]
varOccurences t =
    map (\((v,ctx1):rest) -> (v, S.fromList (ctx1:(map snd rest)))) . groupOn fst . sortOn fst
    . foldFreesOcc (\ c v -> [(v,c)]) [] $ t

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

-- | @renameIgnoring t vars@ replaces all variables in @t@ with fresh variables, excpet for the variables in @vars@.
--   Note that the result is not guaranteed to be equal for terms that are
--   equal modulo changing the indices of variables.
renameIgnoring :: (MonadFresh m, HasFrees a) => [LVar] -> a -> m a
renameIgnoring vars x = case boundsVarIdx x of
    Nothing                     -> return x
    Just (minVarIdx, maxVarIdx) -> do
      freshStart <- freshIdents (succ (maxVarIdx - minVarIdx))
      return . runIdentity . mapFrees (Monotone $ incVar (freshStart - minVarIdx)) $ x
  where
    incVar shift (LVar n so i) = pure $ if elem (LVar n so i) vars then (LVar n so i) else (LVar n so (i+shift))

    
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
evalFreshAvoiding m a = evalFresh m (avoid a)

-- | @m `evalFreshTAvoiding` t@ evaluates the monadic action @m@ in the
-- underlying monad with a fresh-variable supply that avoids generating
-- variables occurring in @t@.
evalFreshTAvoiding :: (Monad m, HasFrees t) => FreshT m a -> t -> m a
evalFreshTAvoiding m = evalFreshT m . avoid

-- | @s `renameAvoiding` t@ replaces all free variables in @s@ by
--   fresh variables avoiding variables in @t@.
renameAvoiding :: (HasFrees s, HasFrees t) => s -> t -> s
renameAvoiding s t = evalFreshAvoiding (rename s) t

-- | @s `renameAvoiding` t@ replaces all free variables in @s@ by
--   fresh variables avoiding variables in @t@.
renameAvoidingIgnoring :: (HasFrees s, HasFrees t) => s -> t -> [LVar] -> s
renameAvoidingIgnoring s t vars = renameIgnoring vars s `evalFreshAvoiding` t


-- | @avoidPrecise t@ computes a 'Precise.FreshState' that avoids generating
-- variables occurring in @t@.
avoidPrecise :: HasFrees t => t -> Precise.FreshState
avoidPrecise =
    foldl' ins M.empty . frees
  where
    ins m v = M.insertWith' max (lvarName v) (lvarIdx v + 1) m

-- | @renamePrecise t@ replaces all variables in @t@ with fresh variables.
--   If 'Control.Monad.PreciseFresh' is used with non-AC terms and identical
--   fresh state, the same result is returned for two terms that only differ
--   in the indices of variables.
renamePrecise :: (MonadFresh m, HasFrees a) => a -> m a
renamePrecise x = evalBindT (someInst x) noBindings


renameDropNamehint :: (MonadFresh m, MonadBind LVar LVar m, HasFrees a) => a -> m a
renameDropNamehint =
    mapFrees (Arbitrary $ \x -> importBinding (`LVar` lvarSort x) x "")


-- Instances
------------

instance HasFrees LVar where
    foldFrees = id
    foldFreesOcc f c v = f c v
    mapFrees (Arbitrary f) = f
    mapFrees (Monotone f)  = f

instance HasFrees v => HasFrees (Lit c v) where
    foldFrees f (Var x) = foldFrees f x
    foldFrees _ _       = mempty

    foldFreesOcc f c (Var x) = foldFreesOcc f c x
    foldFreesOcc _ _ _       = mempty

    mapFrees f (Var x) = Var <$> mapFrees f x
    mapFrees _ l       = pure l

instance HasFrees v => HasFrees (BVar v) where
    foldFrees _ (Bound _) = mempty
    foldFrees f (Free v)  = foldFrees f v

    foldFreesOcc _ _ (Bound _) = mempty
    foldFreesOcc f c (Free v)  = foldFreesOcc f c v

    mapFrees _ b@(Bound _) = pure b
    mapFrees f   (Free v)  = Free <$> mapFrees f v

instance (HasFrees l, Ord l) => HasFrees (Term l) where
    foldFrees f = foldMap (foldFrees f)

    foldFreesOcc f c t = case viewTerm t of
        Lit  l             -> foldFreesOcc f c l
        FApp (NoEq o) as -> foldFreesOcc f ((BC.unpack . fst $ o):c) as
        FApp o        as -> mconcat $ map (foldFreesOcc f (show o:c)) as
          -- AC or C symbols

    mapFrees f (viewTerm -> Lit l)                  = lit <$> mapFrees f l
    mapFrees f@(Arbitrary _) (viewTerm -> FApp o l) = fApp o <$> mapFrees f l
    mapFrees f@(Monotone _)  (viewTerm -> FApp o l) = unsafefApp o <$> mapFrees f l

instance HasFrees a => HasFrees (Equal a) where
    foldFrees    f               = foldMap (foldFrees f)
    foldFreesOcc f p (Equal a b) = foldFreesOcc f p (a,b)
    mapFrees     f               = traverse (mapFrees f)

instance HasFrees a => HasFrees (Match a) where
    foldFrees    f                       = foldMap (foldFrees f)
    foldFreesOcc _ _ NoMatch             = mempty
    foldFreesOcc f p (DelayedMatches ms) = foldFreesOcc f p ms
    mapFrees     f                       = traverse (mapFrees f)

instance HasFrees a => HasFrees (RRule a) where
    foldFrees    f               = foldMap (foldFrees f)
    foldFreesOcc f p (RRule a b) = foldFreesOcc f p (a,b)
    mapFrees     f               = traverse (mapFrees f)

instance HasFrees () where
    foldFrees    _   = const mempty
    foldFreesOcc _ _ = const mempty
    mapFrees     _   = pure

instance HasFrees Int where
    foldFrees    _   = const mempty
    foldFreesOcc _ _ = const mempty
    mapFrees     _   = pure

instance HasFrees Integer where
    foldFrees    _   = const mempty
    foldFreesOcc _ _ = const mempty
    mapFrees     _   = pure

instance HasFrees Bool where
    foldFrees    _   = const mempty
    foldFreesOcc _ _ = const mempty
    mapFrees     _   = pure

instance HasFrees Char where
    foldFrees    _   = const mempty
    foldFreesOcc _ _ = const mempty
    mapFrees     _   = pure

instance HasFrees a => HasFrees (Maybe a) where
    foldFrees    f            = foldMap (foldFrees f)
    foldFreesOcc _ _ Nothing  = mempty
    foldFreesOcc f p (Just x) = foldFreesOcc f p x
    mapFrees     f            = traverse (mapFrees f)

instance (HasFrees a, HasFrees b) => HasFrees (Either a b) where
    foldFrees    f   = either (foldFrees f) (foldFrees f)
    foldFreesOcc f p = either (foldFreesOcc f ("0":p)) (foldFreesOcc f ("1":p))
    mapFrees     f   = either (fmap Left . mapFrees   f) (fmap Right . mapFrees   f)

instance (HasFrees a, HasFrees b) => HasFrees (a, b) where
    foldFrees    f   (x, y) = foldFrees f x `mappend` foldFrees f y
    foldFreesOcc f p (x, y) = foldFreesOcc f ("0":p) x `mappend` foldFreesOcc f ("1":p) y
    mapFrees     f   (x, y) = (,) <$> mapFrees   f x <*> mapFrees   f y

instance (HasFrees a, HasFrees b, HasFrees c) => HasFrees (a, b, c) where
    foldFrees    f (x, y, z)    = foldFrees f (x, (y, z))
    foldFreesOcc f p (x, y, z)  =
        foldFreesOcc f ("0":p) x `mappend` foldFreesOcc f ("1":p) y `mappend` foldFreesOcc f ("2":p) z
    mapFrees     f (x0, y0, z0) =
        (\(x, (y, z)) -> (x, y, z)) <$> mapFrees f (x0, (y0, z0))

instance HasFrees a => HasFrees [a] where
    foldFrees    f      = foldMap  (foldFrees f)
    foldFreesOcc f c xs = mconcat $ (map (\(i,x) -> foldFreesOcc f (show i:c) x)) $ zip [(0::Int)..] xs
    mapFrees     f      = traverse (mapFrees f)

instance HasFrees a => HasFrees (Disj a) where
    foldFrees    f     = foldMap  (foldFrees f)
    foldFreesOcc f p d = foldFreesOcc f p (getDisj d)
    mapFrees     f     = traverse (mapFrees f)

instance HasFrees a => HasFrees (Conj a) where
    foldFrees    f     = foldMap  (foldFrees f)
    foldFreesOcc f p c = foldFreesOcc f p (getConj c)
    mapFrees     f     = traverse (mapFrees f)

instance (Ord a, HasFrees a) => HasFrees (S.Set a) where
    foldFrees   f    = foldMap  (foldFrees f)
    foldFreesOcc f p = foldMap (foldFreesOcc f ("0":p))
    mapFrees     f   = fmap S.fromList . mapFrees f . S.toList

instance (Ord k, HasFrees k, HasFrees v) => HasFrees (M.Map k v) where
    foldFrees f = M.foldrWithKey combine mempty
      where
        combine k v m = foldFrees f k `mappend` (foldFrees f v `mappend` m)
    foldFreesOcc f p = M.foldrWithKey combine mempty
      where
        combine k v m = foldFreesOcc f p (k,v) `mappend` m
    mapFrees f = fmap M.fromList . mapFrees f . M.toList


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


-- | Pretty print a literal for case generation.
showLitName :: Lit Name LVar -> String
showLitName (Con (Name FreshName n)) = "Const_fresh_" ++ show n
showLitName (Con (Name PubName   n)) = "Const_pub_"   ++ show n
showLitName (Var (LVar v s i))       = "Var_" ++ sortSuffix s ++ "_" ++ body
      where
        body | null v           = show i
             | i == 0           = v
             | otherwise        = show i ++ "_" ++ v

