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
import Theory

translate (Left x) = x
translate (Right th) =
    foldr addProtoRule th msrs
    where
        processes = theoryProcesses th
        msrs =  map msrFromProcess processes

msrFromProcess process = []
