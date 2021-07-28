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
import           Theory.Sapic.Pattern 
import qualified Data.Set as S
import Theory.Model.Atom ( SyntacticSugar )

-- | pretty-print rules using a generic fact pretty-printer (based on show)
rulePrinter :: [Fact SapicTerm]
    -> [Fact SapicTerm]
    -> [Fact SapicTerm]
    -> [ProtoFormula SyntacticSugar (String, LSort) Name SapicLVar]
    -> S.Set SapicLVar
    -> String
rulePrinter l a r res mv = render $ prettyRuleRestrGen ppFact ppRes l' (toPat a) (toPat r) res 
    where
        ppFact = prettyFact $ prettyTerm $ text . show
        ppRes  = prettySyntacticLNFormula . toLFormula 
        l'     = fmap (fmap (unextractMatchingVariables mv)) l 
        toPat  = fmap (fmap (unextractMatchingVariables mempty))

-- | Instantiate printers with rulePrinter from Theory.Text.Pretty
prettySapicAction :: LSapicAction -> String
prettySapicAction = prettySapicAction' rulePrinter

prettySapic :: (Document d) => LProcess ann -> d
prettySapic = prettySapic' rulePrinter

prettySapicTopLevel :: LProcess ann -> String
prettySapicTopLevel = prettySapicTopLevel' rulePrinter
