{-# LANGUAGE DeriveDataTypeable #-}
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
    WFerrror(..),
    SapicException(..)
) where
import Data.Typeable
import Data.Set
import qualified Data.List as List
import Control.Exception
import Theory
import Theory.Sapic
import Data.Label

-- two different kind of locking erros
data WFLockTag = WFRep | WFPar  deriving (Show)

prettyWFLockTag :: WFLockTag -> String
prettyWFLockTag WFRep = "replication"
prettyWFLockTag WFPar = "a parallel"

-- | Wellformedness errors, see instance of show below for explanation.
data WFerrror p = WFLock WFLockTag p
                | WFUnboundProto (Set LVar)
                | WFUnbound (Set LVar) p
                | WFReliable
                | WFBoundTwice SapicLVar
    deriving (Typeable, Show)

-- | SapicExceptions see instance of show below for explanation.
data SapicException p = NotImplementedError String
                    -- SomethingBad
                    -- | VerdictNotWellFormed String
                    -- | InternalRepresentationError String
                    -- | UnAnnotatedLock String
                    | ProcessNotWellformed (WFerrror p)
                    | InvalidPosition ProcessPosition
                    | ImplementationError String
                    | MoreThanOneProcess
                    | RuleNameExists String
                    | RestrictionNameExists String
                    | ReliableTransmissionButNoProcess
                    | CannotExpandPredicate FactTag SyntacticRestriction
                    | TypingErrorArgument SapicTerm [SapicType]
    deriving (Typeable)

prettyVarSet :: Set LVar -> String
prettyVarSet = List.intercalate ", "  . List.map show . toList

instance (Show a) => Show (SapicException a) where
    -- show SomethingBad = "Something bad happened"
    show MoreThanOneProcess = "More than one top-level process is defined. This is not supported by the translation."
    show (RuleNameExists s) = "Rule name already exists:" ++ s
    show (RestrictionNameExists s) = "Restriction already exists:" ++ s
    show (InvalidPosition p) = "Invalid position:" ++ prettyPosition p
    show (NotImplementedError s) = "This feature is not implemented yet. Sorry! " ++ s
    show (ImplementationError s) = "You've encountered an error in the implementation: " ++ s
    show (ProcessNotWellformed (WFUnboundProto varset)) =
                   "The variable or variables "
                   ++
                   prettyVarSet varset
                   ++
                   " are not bound."
    show (ProcessNotWellformed (WFUnbound varset pr)) =
                   "The variable or variables"
                   ++
                   prettyVarSet  varset
                   ++
                   " are not bound in the process:"
                   ++
                   show pr
    show (ProcessNotWellformed WFReliable) =
                   "If reliable channels are activated, processes should only contain in('r',m), out('r',m), in('c',m) or out('c',m) for communication."
    show (ProcessNotWellformed (WFLock tag pr)) =
                   "Process " ++ show pr ++ " contains lock that extends over " 
                   ++ prettyWFLockTag tag ++ " which is not allowed."
    show (ProcessNotWellformed (WFBoundTwice v)) =
                   "Variable bound twice: " ++ show v ++ "."
    show ReliableTransmissionButNoProcess = "The builtin support for reliable channels currently only affects the process calculus, but you have not specified a top-level process. Please remove \"builtins: reliable-channel\" to proceed."
    show (CannotExpandPredicate facttag rstr) = "Undefined predicate "
                              ++ showFactTagArity facttag
                              ++ " in definition of predicate: "
                              ++ get rstrName rstr
                              ++ "."
    show (TypingErrorArgument t types) = "Typing error: subterm "
                              ++ show t
                              ++ " should have input types "
                              ++ List.intercalate ", " (List.map (maybe defaultSapicTypeS id) types)
                              ++ "."


instance (Typeable a, Show a) => Exception (SapicException a)
