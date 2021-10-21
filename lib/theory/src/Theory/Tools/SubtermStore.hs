{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ViewPatterns               #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt, Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
-- Support for reasoning with and about subterms.
module Theory.Tools.SubtermStore (
  -- ** Construction
    SubtermStore(..)
  , emptySubtermStore

  -- ** Accessors
  , addNegSubterm
  , addSubterm
  , removeSubterm
  , isContradicting
  , simpSubtermStore

  -- ** Pretty printing
  , prettySubtermStore
) where

import           GHC.Generics          (Generic)
--import           Logic.Connectives
import           Term.Unification
import           Theory.Text.Pretty
import           Theory.Constraint.System.Constraints

--import           Control.Monad.Fresh
--import           Control.Monad.Bind
--import           Control.Monad.Reader
--import           Extension.Prelude
--import           Utils.Misc

--import           Debug.Trace

--import           Control.Basics
import           Control.DeepSeq
--import           Control.Monad.State   hiding (get, modify, put)
--import qualified Control.Monad.State   as MS

import           Data.Binary
--import qualified Data.Foldable         as F
--import           Data.List          (delete,find,intersect,intersperse,nub,(\\))
--import           Data.Maybe
import qualified Data.Set              as S
import           Extension.Data.Label  hiding (for, get)
--import qualified Extension.Data.Label  as L
-- import           Extension.Data.Monoid

------------------------------------------------------------------------------
-- Subterm Store
------------------------------------------------------------------------------

data SubtermStore = SubtermStore {
      _negSubterms    :: S.Set (LNTerm, LNTerm)
    , _subterms       :: S.Set (LNTerm, LNTerm)
    , _solvedSubterms :: S.Set (LNTerm, LNTerm)
    }
  deriving( Eq, Ord, Generic )

instance NFData SubtermStore
instance Binary SubtermStore

$(mkLabels [''SubtermStore])

-- | @emptyEqStore@ is the empty equation store.
emptySubtermStore :: SubtermStore
emptySubtermStore = SubtermStore S.empty S.empty S.empty

addSubterm :: (LNTerm, LNTerm) -> SubtermStore -> (SubtermStore, Maybe Goal)
addSubterm _ sst = (sst, Nothing)

removeSubterm :: (LNTerm, LNTerm) -> SubtermStore -> SubtermStore
removeSubterm _ sst = sst

addNegSubterm :: (LNTerm, LNTerm) -> SubtermStore -> (SubtermStore, [Equal LNTerm])
addNegSubterm _ sst = (sst, [])

isContradicting :: SubtermStore -> Bool
isContradicting _ = False

simpSubtermStore :: SubtermStore -> (SubtermStore, [Equal LNTerm], [Goal])
simpSubtermStore sst = (sst, [], [])


-- Instances
------------


instance HasFrees SubtermStore where
    foldFrees f (SubtermStore negSt st solvedSt) =
        foldFrees f negSt <> foldFrees f st <> foldFrees f solvedSt
    foldFreesOcc  _ _ = const mempty
    mapFrees f (SubtermStore negSt st solvedSt) =
        SubtermStore <$> mapFrees f negSt
                <*> mapFrees f st
                <*> mapFrees f solvedSt


instance Apply SubtermStore where
    apply subst (SubtermStore a b c) = SubtermStore (apply subst a) (apply subst b) (apply subst c)


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Pretty print an 'EqStore'.
prettySubtermStore :: HighlightDocument d => SubtermStore -> d
prettySubtermStore (SubtermStore negSt st solvedSt) = vcat $
  map combine
    [ ("Subterms", numbered' $ map ppSt (S.toList st))
    , ("Negative Subterms", numbered' $ map ppSt (S.toList negSt))
    , ("Solved Subterms", numbered' $ map ppSt (S.toList solvedSt))
    ]
  where
    combine (header, d) = fsep [keyword_ header <> colon, nest 2 d]

    ppSt (a,b) =
      prettyNTerm (lit (Var a)) $$ nest (3::Int) (opSubterm <-> prettyNTerm b)



-- Derived and delayed instances
--------------------------------

instance Show SubtermStore where
    show = render . prettySubtermStore
