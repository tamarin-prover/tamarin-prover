{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE ViewPatterns       #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Common types for our constraint solver. They must be declared jointly
-- because there is a recursive dependency between goals, proof contexts, and
-- case distinctions.

-- Needed to move common types to System, now this modul is just passing them through.
module Theory.Constraint.Solver.Types (
--     module Logic.Connectives
--     module Theory.Constraint.System
--   , module Theory.Text.Pretty
--   , module Theory.Model

) where

-- import           Prelude                  hiding (id, (.))
-- 
-- import           Data.Binary
-- import           Data.DeriveTH
-- import           Data.Label               hiding (get)
-- import qualified Data.Label               as L
-- import           Data.Monoid              (Monoid(..))
-- import qualified Data.Set                 as S
-- 
-- import           Control.Basics
-- import           Control.Category
-- import           Control.DeepSeq

-- import           Logic.Connectives
-- import           Theory.Constraint.System
-- import           Theory.Text.Pretty
-- import           Theory.Model
