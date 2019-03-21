{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveTraversable       #-}
{-# LANGUAGE DeriveAnyClass       #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Printers for processes.
module Theory.Sapic.Print (
    Process
    , ProcessCombinator(..)
    , AnProcess(..)
    , SapicAction(..)
    , SapicTerm
    , paddAnn
    , pfoldMap
    , prettySapic
    , prettySapicAction
    , prettySapicComb
    , prettySapicTopLevel
    , ProcessPosition
    , prettyPosition
    , lhs
    , rhs
) where

import           Data.Binary
import           GHC.Generics                (Generic)
import           Control.Parallel.Strategies
import           Data.Foldable
import           Theory.Model.Fact
import           Theory.Model.Rule
import           Theory.Sapic
import           Term.LTerm
import           Theory.Text.Pretty


rulePrinter l a r = render $ prettyRule l a r

-- | Instantiate prenters with rulePrinter from Theory.Text.Pretty
prettySapicAction = prettySapicAction' rulePrinter
prettySapic = prettySapic' rulePrinter
prettySapicTopLevel = prettySapicTopLevel' rulePrinter
