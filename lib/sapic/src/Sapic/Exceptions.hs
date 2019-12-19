{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TemplateHaskell #-}
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
import           Control.Exception
import           Data.Typeable
import qualified Data.Set as S
import           Data.List
import           Theory
import           Theory.Sapic
import           Theory.Sapic.Print
import           Data.Label

-- two different kind of locking erros
data WFLockTag = WFRep | WFPar  deriving (Show)

prettyWFLockTag :: WFLockTag -> String
prettyWFLockTag WFRep = "replication"
prettyWFLockTag WFPar = "a parallel"

-- | Wellformedness errors, see instance of show below for explanation.
data WFerrror a = WFLock WFLockTag (AnProcess a)
                | WFUnboundProto (S.Set LVar)
                | WFUnbound (S.Set LVar) (AnProcess a)
                | WFReliable
    deriving (Typeable, Show)

-- | SapicExceptions see instance of show below for explanation.
data SapicException a = NotImplementedError String
                    -- SomethingBad
                    -- | VerdictNotWellFormed String
                    -- | InternalRepresentationError String
                    -- | UnAnnotatedLock String
                    | CaseTestsUndefined [(String, [String])]
                    | ProcessNotWellformed (WFerrror a)
                    | InvalidPosition ProcessPosition
                    | ImplementationError String
                    | MoreThanOneProcess
                    | RuleNameExists String
                    | LemmaNameExists String
                    | RestrictionNameExists String
                    | ReliableTransmissionButNoProcess
                    | CannotExpandPredicate FactTag SyntacticRestriction
    -- deriving (Typeable, Show)
    deriving (Typeable)

prettyVarSet :: S.Set LVar -> [Char]
prettyVarSet = (intercalate ", " ) . (map show) . S.toList

instance Show (SapicException a) where
    -- show SomethingBad = "Something bad happened"
    show (CaseTestsUndefined el) =
        "The following case tests are undefined but are required in a lemma: \n" ++
        intercalate "\n" (map (\(a, c) -> "  " ++ (intercalate ", " c) ++ " required by the lemma '" ++ a ++ "'") el)

    show MoreThanOneProcess = "More than one top-level process is defined. This is not supported by the translation."
    show (RuleNameExists s) = "Rule name already exists:" ++ s
    show (LemmaNameExists s) = "Lemma name already exists:" ++ s
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
                   prettySapic pr
    show (ProcessNotWellformed WFReliable) =
                   "If reliable channels are activated, processes should only contain in('r',m), out('r',m), in('c',m) or out('c',m) for communication."
    show (ProcessNotWellformed (WFLock tag pr)) =
                   "Process " ++ prettySapic pr ++ " contains lock that extends over " 
                   ++ prettyWFLockTag tag ++ " which is not allowed."
    show ReliableTransmissionButNoProcess = "The builtin support for reliable channels currently only affects the process calculus, but you have not specified a top-level process. Please remove \"builtins: reliable-channel\" to proceed."
    show (CannotExpandPredicate facttag rstr) = "Undefined predicate "
                              ++ showFactTagArity facttag
                              ++ " in definition of predicate: "
                              ++ get rstrName rstr
                              ++ "."
instance (Typeable a, Show a) => Exception (SapicException a)
