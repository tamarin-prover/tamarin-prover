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
    SapicException(..),
    ExportException(..)) where
import Data.Typeable
import Data.Set as S
import qualified Data.List as List
import Control.Exception
import Theory
import Theory.Sapic
import Data.Label
import qualified Data.Maybe
import Theory.Text.Pretty
import Sapic.Annotation  --toAnProcess
import Theory.Sapic.Print (prettySapic)
import qualified Theory.Text.Pretty as Pretty

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
data SapicException an = NotImplementedError String
                    -- SomethingBad
                    -- | VerdictNotWellFormed String
                    -- | InternalRepresentationError String
                    -- | UnAnnotatedLock String
                    | ProcessNotWellformed WFerror (Maybe (LProcess an))
                    | InvalidPosition ProcessPosition
                    | ImplementationError String
                    | MoreThanOneProcess
                    | RuleNameExists String
                    | LemmaNameExists String
                    | RestrictionNameExists String
                    | ReliableTransmissionButNoProcess
                    | CannotExpandPredicate FactTag SyntacticRestriction
    deriving (Typeable)

data ExportException = UnsupportedBuiltinMS
                       | UnsupportedBuiltinBP
                       | UnsupportedTypes [String]

instance Show ExportException where
    
    show (UnsupportedTypes incorrectFunctionUsages) = do
        let functionsString = List.intercalate ", " incorrectFunctionUsages
        (case length functionsString of
          1 -> "The function " ++ functionsString ++ ", which is declared with a user-defined type, appears in a rewrite rule. "
          _ -> "The functions " ++ functionsString ++ ", which are declared with a user-defined type, appear in a rewrite rule. ")
        ++ "However, the translation of rules only works with bitstrings at the moment."
    show unsuppBuiltin = 
        "The builtins bilinear-pairing and multiset are not supported for export. However, your model uses " ++
        (case unsuppBuiltin of
            UnsupportedBuiltinBP -> "bilinear-pairing."
            UnsupportedBuiltinMS -> "multiset.")

prettyVarSet :: S.Set LVar -> String
prettyVarSet = List.intercalate ", "  . List.map show . toList

instance Show (SapicException an) where
    -- show SomethingBad = "Something bad happened"

    show MoreThanOneProcess = "More than one top-level process is defined. This is not supported by the translation."
    show (RuleNameExists s) = "Rule name already exists:" ++ s
    show (LemmaNameExists s) = "Lemma name already exists:" ++ s
    show (RestrictionNameExists s) = "Restriction already exists:" ++ s
    show (InvalidPosition p) = "Invalid position:" ++ prettyPosition p
    show (NotImplementedError s) = "This feature is not implemented yet. Sorry! " ++ s
    show (ImplementationError s) = "You've encountered an error in the implementation: " ++ s
    show a@(ProcessNotWellformed e p) = "Process not well-formed: " ++ Pretty.render (text (show e) $-$ nest 2 (maybe emptyDoc prettySapic p))
    show ReliableTransmissionButNoProcess = "The builtin support for reliable channels currently only affects the process calculus, but you have not specified a top-level process. Please remove \"builtins: reliable-channel\" to proceed."
    show (CannotExpandPredicate facttag rstr) = "Undefined predicate "
                              ++ showFactTagArity facttag
                              ++ " in definition of predicate: "
                              ++ get rstrName rstr
                              ++ "."

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
instance (Typeable an) => Exception (SapicException an)
instance Exception ExportException
