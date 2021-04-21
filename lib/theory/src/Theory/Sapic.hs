{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Data types for SAPIC processes in theories
module Theory.Sapic (
    -- types
    Process(..)
    , ProcessCombinator(..)
    , ProcessParsedAnnotation(..)
    , SapicType
    , defaultSapicTypeS
    , defaultSapicType
    , defaultSapicNodeType
    , SapicAction(..)
    , SapicLVar(..)
    , SapicTerm
    , SapicNTerm
    , SapicLNFact
    , SapicFormula
    , SapicFunSym
    , LSapicAction
    , LProcessCombinator
    , LProcess
    , PlainProcess
    -- converters
    , toLVar
    , toLNTerm
    , toLNFact
    , toLFormula
    -- utitlities
    , freesSapicTerm
    , freesSapicFact
    , paddAnn
    , foldProcess
    , foldMProcess
    , traverseTermsAction
    , traverseTermsComb
    , applyProcess
    , pfoldMap
    , mapTerms
    , mapTermsAction
    , mapTermsComb
    , ProcessPosition
    , lhsP
    , rhsP
    , descendant
    -- pretty printing
    , prettySapic'
    , prettySapicAction'
    , prettySapicComb
    , prettySapicTopLevel'
    , prettyPosition
) where
import Theory.Sapic.Term
import Theory.Sapic.Process
import Theory.Sapic.Annotation
import Theory.Sapic.Position
