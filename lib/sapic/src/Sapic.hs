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
import Data.Maybe
import Data.Foldable

translate x = x
--translate (Left x) = (Left x)
--translate (Right th) = new_th
--    where
--        processes = theoryProcesses th
--        msrs = foldr (++) [] (map msrFromProcess processes)
--        new_th = foldrM addProtoRule th msrs


-- translate (Left x) = x
-- translate (Right th) =
--     foldr addProtoRule th msrs
--     where
--         processes = theoryProcesses th
--         msrs =  map msrFromProcess processes

--msrFromProcess process = []
