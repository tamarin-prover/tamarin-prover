{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Exceptions used during translation

module Sapic.Exceptions (
    WFLockTag(..),
    WFerror(..),
    SapicException(..)
, prettySapicException) where
import Data.Typeable
import Data.Set as S
import qualified Data.List as List
import Control.Exception
import Theory
import Theory.Sapic
import Data.Label
import qualified Data.Maybe
import Theory.Text.Pretty
import Sapic.Annotation (toAnProcess, toProcess)

-- two different kind of locking erros
data WFLockTag = WFRep | WFPar  deriving (Show)

prettyWFLockTag :: WFLockTag -> String
prettyWFLockTag WFRep = "replication"
prettyWFLockTag WFPar = "a parallel"

-- | Wellformedness errors, see instance of show below for explanation.
data WFerror = WFLock WFLockTag
                | WFUnbound (Set LVar)
                | WFReliable
                | WFBoundTwice SapicLVar
                | TypingErrorArgument SapicTerm [SapicType]
                | TypingError SapicTerm SapicType SapicType
                | TypingErrorFunctionMerge NoEqSym SapicFunType SapicFunType
                | FunctionNotDefined NoEqSym
    deriving (Typeable)

-- | SapicExceptions see instance of show below for explanation.
data SapicException p = NotImplementedError String
                    -- SomethingBad
                    -- | VerdictNotWellFormed String
                    -- | InternalRepresentationError String
                    -- | UnAnnotatedLock String
                    | ProcessNotWellformed WFerror (Maybe p)
                    | InvalidPosition ProcessPosition
                    | ImplementationError String
                    | MoreThanOneProcess
                    | RuleNameExists String
                    | LemmaNameExists String
                    | RestrictionNameExists String
                    | ReliableTransmissionButNoProcess
                    | CannotExpandPredicate FactTag SyntacticRestriction
    deriving (Typeable)

prettyVarSet :: S.Set LVar -> String
prettyVarSet = List.intercalate ", "  . List.map show . toList

instance (Show p) => Show (SapicException p) where
    -- show SomethingBad = "Something bad happened"

    show MoreThanOneProcess = "More than one top-level process is defined. This is not supported by the translation."
    show (RuleNameExists s) = "Rule name already exists:" ++ s
    show (LemmaNameExists s) = "Lemma name already exists:" ++ s
    show (RestrictionNameExists s) = "Restriction already exists:" ++ s
    show (InvalidPosition p) = "Invalid position:" ++ prettyPosition p
    show (NotImplementedError s) = "This feature is not implemented yet. Sorry! " ++ s
    show (ImplementationError s) = "You've encountered an error in the implementation: " ++ s
    show (ProcessNotWellformed e p) = "Process not well-formed: " ++ show e ++ maybe "" (\p' ->  "in " ++ show p') p
    show ReliableTransmissionButNoProcess = "The builtin support for reliable channels currently only affects the process calculus, but you have not specified a top-level process. Please remove \"builtins: reliable-channel\" to proceed."
    show (CannotExpandPredicate facttag rstr) = "Undefined predicate "
                              ++ showFactTagArity facttag
                              ++ " in definition of predicate: "
                              ++ get rstrName rstr
                              ++ "."

prettySapicException :: (Show an, HighlightDocument d, GoodAnnotation an) => SapicException (LProcess an) -> d
prettySapicException (ProcessNotWellformed e p) = text (show e) <-> maybe emptyDoc ppP p 
    where ppP = prettyProcess . toProcess
prettySapicException o = text (show o) 
        
instance Show WFerror where
    show (WFUnbound varset) =
                   "The variable(s) "
                   ++
                   prettyVarSet varset
                   ++
                   " are not bound."
    show WFReliable =
                   "If reliable channels are activated, processes should only contain in('r',m), out('r',m), in('c',m) or out('c',m) for communication."
    show (WFLock tag) =
                   "Process contains lock that extends over "
                   ++ prettyWFLockTag tag ++ " which is not allowed."
    show (WFBoundTwice v) =
                   "Variable bound twice: " ++ show v ++ "."
    show (TypingErrorArgument t types) = "Typing error: subterm "
                              ++ show t
                              ++ " should have input types "
                              ++ List.intercalate ", " (List.map (Data.Maybe.fromMaybe defaultSapicTypeS) types)
                              ++ "."
    show (TypingError t at tt) = "Typing error: expected term "
                              ++ show t
                              ++ " to have "
                              ++ show tt
                              ++ " but actual type is "
                              ++ show at
                              ++ "."
    show (TypingErrorFunctionMerge fs t1 t2) = "Typing error: function types for function"
                              ++ show fs
                              ++ " are compatible. Expected type "
                              ++ prettySapicFunType t1
                              ++ " but actual type is "
                              ++ prettySapicFunType t2
                              ++ "."
    show (FunctionNotDefined sym ) = "Function not defined " ++ show sym
        

instance Exception WFerror
instance (Typeable a, Show a) => Exception (SapicException a)
