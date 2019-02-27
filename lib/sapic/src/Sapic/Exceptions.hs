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
    translate
) where
-- import Data.Maybe
-- import Data.Foldable
-- import Sapic.Exceptions

TODO Lookup exceptions and see how we do this.

exception VerdictNotWellFormed of string

exception InternalRepresentationError of string
exception NotImplementedError of string

exception TranslationError of string
exception UnAnnotatedLock of string
exception ProcessNotWellformed of string
exception NoNextState
exception UnassignedTerm
exception InvalidPosition of string
exception NotInRange of string
exception ImplementationError of string

