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
    , SapicAction(..)
    , SapicTerm
    , processAddAnnotation
    , pfoldMap
    , prettySapic
    , prettySapicAction
    , prettySapicComb
    , prettySapicTopLevel
    , ProcessPosition
    , prettyPosition
) where

import           Theory.Model.Fact
import           Theory.Model.Rule
import           Theory.Model.Formula
import           Theory.Sapic
import           Term.LTerm
import           Theory.Text.Pretty

-- | pretty-print rules using a generic fact pretty-printer (based on show)
-- rulePrinter :: Show a =>
--              [Fact (Term a)]
--              -> [Fact (Term a)] -> [Fact (Term a)] -> [b] -> String
rulePrinter :: Show a =>
               [Fact (Term a)]
               -> [Fact (Term a)]
               -> [Fact (Term a)]
               -> [SapicFormula]
               -> p
               -> String
-- TODO we should convert l into a Pattern using mv and print it out correctly
rulePrinter l a r res mv = render $ prettyRuleRestrGen ppFact ppRes l a r res 
    where
        ppFact = prettyFact $ prettyTerm $ text . show
        ppRes  = prettySyntacticLNFormula . toLFormula 

-- | Instantiate printers with rulePrinter from Theory.Text.Pretty
prettySapicAction :: LSapicAction -> String
prettySapicAction = prettySapicAction' rulePrinter

prettySapic :: (Document d) => LProcess ann -> d
prettySapic = prettySapic' rulePrinter

prettySapicTopLevel :: LProcess ann -> String
prettySapicTopLevel = prettySapicTopLevel' rulePrinter
