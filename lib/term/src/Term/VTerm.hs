{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Terms with variables and constants.

module Term.VTerm (
    -- * Terms with constants and variables
      Lit(..)
    , VTerm

    , varTerm
    , constTerm
    , varsVTerm
    , occursVTerm
    , constsVTerm
    , isVar

    -- ** Destructors
    , termVar
    , termVar'

    , IsVar
    , IsConst
    , module Term.Term
    ) where

-- import Data.Foldable
-- import Data.Traversable
import GHC.Generics (Generic)
import qualified Data.DList as D
import Data.Typeable
import Data.Data
import Data.Binary
import Data.Monoid
import Control.DeepSeq
-- import Control.Basics

import Extension.Prelude

import Safe (fromJustNote)

import Term.Term

----------------------------------------------------------------------
-- Terms with constants and variables
----------------------------------------------------------------------

-- | A Lit is either a constant or a variable. (@Const@ is taken by Control.Applicative)
data Lit c v = Con c | Var v
  deriving (Eq, Ord, Data, Typeable, Generic, NFData, Binary)

-- | A VTerm is a term with constants and variables
type VTerm c v = Term (Lit c v)

-- | collect class constraints for variables
class (Ord v, Eq v, Show v) => IsVar v where

-- | collect class constraints for constants
class (Ord c, Eq c, Show c, Data c) => IsConst c where

-- | Functor instance in the variable.
instance Functor (Lit c) where
    fmap f (Var v)  = Var (f v)
    fmap _ (Con c) = Con c

-- | Foldable instance in the variable.
instance Foldable (Lit c) where
    foldMap f (Var v)  = f v
    foldMap _ (Con _) = mempty

-- | Traversable instance in the variable.
instance Traversable (Lit c) where
    sequenceA (Var v)  = Var <$> v
    sequenceA (Con n) = pure $ Con n

-- | Applicative instance in the variable.
instance Applicative (Lit c) where
    pure = Var
    (Var f)  <*> (Var x)  = Var (f x)
    (Var _)  <*> (Con n) = Con n
    (Con n) <*> _        = Con n

-- | Monad instance in the variable
instance Monad (Lit c) where
    return         = Var
    (Var x)  >>= f = f x
    (Con n)  >>= _ = Con n

instance Sized (Lit c v) where
    size _ = 1

instance (Show v, Show c) => Show (Lit c v) where
    show (Var x) = show x
    show (Con n) = show n

-- | @varTerm v@ is the 'VTerm' with the variable @v@.
varTerm :: v -> VTerm c v
varTerm = lit . Var

-- | @constTerm c@ is the 'VTerm' with the const @c@.
constTerm :: c -> VTerm c v
constTerm = lit . Con

-- | @isVar t returns @True@ if @t@ is a variable.
isVar :: VTerm c v -> Bool
isVar (viewTerm -> Lit (Var _)) = True
isVar _ = False

-- | @vars t@ returns a duplicate-free list of variables that occur in @t@.
varsVTerm :: Ord v => VTerm c v -> [v]
varsVTerm = sortednub . D.toList . foldMap (foldMap return)

-- | @occurs v t@ returns @True@ if @v@ occurs in @t@
occursVTerm :: Eq v => v -> VTerm c v -> Bool
occursVTerm v = getAny . foldMap (foldMap (Any . (v==)))

-- | @constsVTerm t@ returns a duplicate-free list of constants that occur in @t@.
constsVTerm :: IsConst c => VTerm c v -> [c]
constsVTerm = sortednub . D.toList . foldMap fLit
  where fLit (Var _)  = mempty
        fLit (Con n) = return n

-- Destructors
--------------

-- | Extract just the variable from a term that may be variable.
termVar :: VTerm c v -> Maybe v
termVar (viewTerm -> Lit (Var v)) = Just v
termVar _                         = Nothing

-- | Extract just the variable from a term that must be variable, throw an
-- error if this fails.
termVar' :: (Show c, Show v) => VTerm c v -> v
termVar' t =
    fromJustNote ("termVar': non-variable term " ++ show t) (termVar t)

