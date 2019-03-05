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
    WFLockTag(..),
    WFerrror(..),
    SapicException(..)
) where
-- import Data.Maybe
-- import Data.Foldable
import Control.Exception
import Data.Typeable
import Data.Set
import Theory
import Theory.Sapic
import Theory.Model.Rule
-- import Text.Parsec (ParseError)

data WFLockTag = WFRep | WFPar  deriving (Show)

data WFerrror a = WFLock WFLockTag (AnProcess a) 
                | WFUnboundProto (Set LVar) 
                | WFUnbound (Set LVar) (AnProcess a) 
--                ("Condition contains unbound variables: "^(String.concat ", "
--                                                             ( List.map var2string (VarSet.elements (VarSet.diff cond_vars tildex))))
--                 ^" (the bound variables are: "
--                 ^ (String.concat ", " ( List.map var2string (VarSet.elements ( tildex))))^")" )
                | Other String

data SapicException a = SomethingBad
                    | VerdictNotWellFormed String
                    | InternalRepresentationError String
                    | NotImplementedError String
                    | TranslationError String
                    | UnAnnotatedLock String
                    | ProcessNotWellformed (WFerrror a) 
                    | NoNextState
                    | UnassignedTerm
                    | InvalidPosition Position
                    | NotInRange String
                    | ImplementationError String
    deriving (Typeable)
instance Show (SapicException a) where
    show SomethingBad = "something bad happened"
    -- show (SapicParseError err) = "Parser error:" ++ show err
-- instance Exception SapicException
instance Typeable a => Exception (SapicException a)

-- TODO notes: this is how to do hierarchical exceptions
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

