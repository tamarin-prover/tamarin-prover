{-# LANGUAGE DeriveDataTypeable #-}
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
import Control.Exception
import Data.Typeable
import Data.Set
import qualified Data.List as List
import Theory
import Theory.Sapic
import Theory.Sapic.Print

-- two different kind of locking erros
data WFLockTag = WFRep | WFPar  deriving (Show)

-- | Wellformedness errors, see instance of show below for explanation.
data WFerrror a = WFLock WFLockTag (AnProcess a) 
                | WFUnboundProto (Set LVar) 
                | WFUnbound (Set LVar) (AnProcess a) 
                | WFReliable 
    deriving (Typeable, Show)

-- | SapicExceptions see instance of show below for explanation.
data SapicException a = SomethingBad
                    -- | VerdictNotWellFormed String
                    -- | InternalRepresentationError String
                    | NotImplementedError String
                    | TranslationError String
                    -- | UnAnnotatedLock String
                    | ProcessNotWellformed (WFerrror a) 
                    | NoNextState
                    | UnassignedTerm
                    | InvalidPosition ProcessPosition
                    | NotInRange String
                    | ImplementationError String
                    | MoreThanOneProcess
                    | RuleNameExists String
                    | RestrictionNameExists String
    -- deriving (Typeable, Show)
    deriving (Typeable)

prettyVarSet :: Set LVar -> [Char]
prettyVarSet = (List.intercalate ", " ) . (List.map show) . toList

-- TODO not complete yet, add nicer error messages later
instance Show (SapicException a) where 
    show SomethingBad = "Something bad happened"
    show MoreThanOneProcess = "More than one top-level process is defined. This is not supported by the translation."
    show (RuleNameExists s) = "Rule name already exists:" ++ s
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
    show (ProcessNotWellformed (WFReliable)) =
                   "If reliable channels are activated, processes should only contain in('r',m), out('r',m), in('c',m) or out('c',m) for communication."
instance (Typeable a, Show a) => Exception (SapicException a)