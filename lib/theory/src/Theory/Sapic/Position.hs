-- Copyright   : (c) 2021 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Positions within SAPIC processes
module Theory.Sapic.Position (
    -- types
    ProcessPosition
    -- utitlities
    , lhsP
    , rhsP
    , descendant
    -- pretty printing
    , prettyPosition
) where

import Data.List ( isPrefixOf )

type ProcessPosition = [Int]

-- | Positions are to be read left-to-right, 1 is left, 2 is right.
lhsP :: [Int] -> ProcessPosition
lhsP p = (p++[1]) :: ProcessPosition

rhsP :: [Int] -> ProcessPosition
rhsP p = (p++[2]) :: ProcessPosition
-- rhs :: ProcessPosition = 2

descendant :: Eq a => [a] -> [a] -> Bool
descendant child parent = parent `isPrefixOf` child

prettyPosition:: ProcessPosition -> String
prettyPosition = foldl (\ s n -> s ++ show n ) ""