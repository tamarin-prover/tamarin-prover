{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann and Alexander Dax
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation from Theories with Processes to mrs

module Sapic.Exceptions (
    SapicException(..)
) where
-- import Data.Maybe
-- import Data.Foldable
import Control.Exception
import Data.Typeable
import Text.Parsec (ParseError)

data SapicException = SomethingBad | SapicParseError ParseError 
    deriving Typeable
instance Show SapicException where
    show SomethingBad = "something bad happened"
    show (SapicParseError err) = "Parser error:" ++ show err
-- instance Exception SapicException
instance Exception SapicException 

-- newtype SapicException = forall e . Exception e => SapicException e
-- instance Show SapicException where
--     show (SapicException e) = show e

-- instance Exception SapicException

-- SapicExceptionToException :: Exception e => e -> SomeException
-- SapicExceptionToException = toException . SapicException

-- SapicExceptionFromException :: Exception e => SomeException -> Maybe e
-- SapicExceptionFromException x = do
--     SapicException a <- fromException x
--     cast a


-- data SomethingBad = SomethingBad
--     deriving Typeable
-- instance Show SomethingBad where
--     show SomethingBad = "something bad happened"
-- -- instance Exception SomethingBad
-- instance Exception SomethingBad where
--     toException   = SapicExceptionToException
--     fromException = SapicExceptionFromException

-- TODO Lookup exceptions and see how we do this.

-- exception VerdictNotWellFormed of string

-- exception InternalRepresentationError of string
-- exception NotImplementedError of string

-- exception TranslationError of string
-- exception UnAnnotatedLock of string
-- exception ProcessNotWellformed of string
-- exception NoNextState
-- exception UnassignedTerm
-- exception InvalidPosition of string
-- exception NotInRange of string
-- exception ImplementationError of string

