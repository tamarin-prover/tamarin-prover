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
) where

-- import           Data.Binary
-- import           GHC.Generics                (Generic)
-- import           Control.Parallel.Strategies
-- import           Data.Foldable
import           Theory.Model.Fact
import           Theory.Model.Rule
import           Theory.Model.Formula
import           Theory.Sapic
-- import           Term.LTerm
import           Theory.Text.Pretty


rulePrinter :: [LNFact] -> [LNFact] -> [LNFact] -> [SyntacticLNFormula] -> String
rulePrinter l a r res = render $ prettyRuleRestr l a r res

-- | Instantiate printers with rulePrinter from Theory.Text.Pretty
prettySapicAction :: SapicAction -> String
prettySapicAction = prettySapicAction' rulePrinter

prettySapic :: AnProcess ann -> String
prettySapic = prettySapic' rulePrinter

prettySapicTopLevel :: AnProcess ann -> String
prettySapicTopLevel = prettySapicTopLevel' rulePrinter
