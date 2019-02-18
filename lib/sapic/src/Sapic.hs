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
module Sapic (
    translate
) where

translate (Left x) = x
translate (Right th) = 
    fold_left (addProtoRule th) th []
    where
        process = theoryProcesses th
        msrs =  []
-- translate x = Left (Parsec.ParseError "Lol")
