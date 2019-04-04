{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveAnyClass     #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Common types for our constraint solver. They must be declared jointly
-- because there is a recursive dependency between goals, proof contexts, and
-- case distinctions.

-- Needed to move common types to System, now this modul is just passing them through.
module Theory.Constraint.Solver.Heuristics (
    GoalRanking(..)
  , Heuristic(..)

  , goalRankingIdentifiers
  , goalRankingIdentifiersDiff

  , charToGoalRankingMay
  , charToGoalRanking
  , charToGoalRankingDiffMay
  , charToGoalRankingDiff

  , listGoalRankings
  , listGoalRankingsDiff

  , goalRankingName
  , prettyGoalRankings
  , prettyGoalRanking
) where

import           GHC.Generics       (Generic)
import           Data.Binary
import           Control.DeepSeq
import           Data.Maybe         (fromMaybe)
import qualified Data.Map as M
import           Data.List          (find)

import           Theory.Text.Pretty

-- | The different available functions to rank goals with respect to their
-- order of solving in a constraint system.
data GoalRanking =
    GoalNrRanking
  | OracleRanking String
  | OracleSmartRanking String
  | SapicRanking
  | SapicPKCS11Ranking
  | UsefulGoalNrRanking
  | SmartRanking Bool
  | SmartDiffRanking
  | InjRanking Bool
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

newtype Heuristic = Heuristic [GoalRanking]
    deriving( Eq, Ord, Show, Generic, NFData, Binary )

goalRankingIdentifiers :: M.Map Char GoalRanking
goalRankingIdentifiers = M.fromList
                        [ ('s', SmartRanking False)
                        , ('S', SmartRanking True)
                        , ('o', OracleRanking "./oracle")
                        , ('O', OracleSmartRanking "./oracle")
                        , ('p', SapicRanking)
                        , ('P', SapicPKCS11Ranking)
                        , ('c', UsefulGoalNrRanking)
                        , ('C', GoalNrRanking)
                        , ('i', InjRanking False)
                        , ('I', InjRanking True)
                        ]

goalRankingIdentifiersDiff :: M.Map Char GoalRanking
goalRankingIdentifiersDiff  = M.fromList
                            [ ('s', SmartDiffRanking)
                            , ('o', OracleRanking "./oracle")
                            , ('O', OracleSmartRanking "./oracle")
                            , ('c', UsefulGoalNrRanking)
                            , ('C', GoalNrRanking)
                            ]

charToGoalRankingMay :: Char -> Maybe GoalRanking
charToGoalRankingMay c = M.lookup c goalRankingIdentifiers

charToGoalRanking :: Char -> GoalRanking
charToGoalRanking c = fromMaybe
    (error $ render $ sep $ map text $ lines $ "Unknown goal ranking '" ++ [c]
        ++ "'. Use one of the following:\n" ++ listGoalRankings)
    $ charToGoalRankingMay c

charToGoalRankingDiffMay :: Char -> Maybe GoalRanking
charToGoalRankingDiffMay c = M.lookup c goalRankingIdentifiersDiff

charToGoalRankingDiff :: Char -> GoalRanking
charToGoalRankingDiff c = fromMaybe
    (error $ render $ sep $ map text $ lines $ "Unknown goal ranking '" ++ [c]
        ++ "'. Use one of the following:\n" ++ listGoalRankingsDiff)
    $ charToGoalRankingDiffMay c

listGoalRankings :: String
listGoalRankings = M.foldMapWithKey
    (\k v -> "'"++[k]++"': " ++ goalRankingName v ++ "\n") goalRankingIdentifiers

listGoalRankingsDiff :: String
listGoalRankingsDiff = M.foldMapWithKey
    (\k v -> "'"++[k]++"': " ++ goalRankingName v ++ "\n") goalRankingIdentifiersDiff

-- | The name/explanation of a 'GoalRanking'.
goalRankingName :: GoalRanking -> String
goalRankingName ranking =
    "Goals sorted according to " ++ case ranking of
        GoalNrRanking                 -> "their order of creation"
        OracleRanking oracleName      -> "an oracle for ranking, located at " ++ oracleName
        OracleSmartRanking oracleName -> "an oracle for ranking based on 'smart' heuristic, located at " ++ oracleName
        UsefulGoalNrRanking           -> "their usefulness and order of creation"
        SapicRanking                  -> "heuristics adapted for processes"
        SapicPKCS11Ranking            -> "heuristics adapted to a specific model of PKCS#11 expressed using SAPIC. deprecated."
        SmartRanking useLoopBreakers  -> "the 'smart' heuristic" ++ loopStatus useLoopBreakers
        SmartDiffRanking              -> "the 'smart' heuristic (for diff proofs)"
        InjRanking useLoopBreakers    -> "heuristics adapted to stateful injective protocols" ++ loopStatus useLoopBreakers
   where
     loopStatus b = " (loop breakers " ++ (if b then "allowed" else "delayed") ++ ")"

prettyGoalRankings :: [GoalRanking] -> String
prettyGoalRankings rs = map prettyGoalRanking rs

prettyGoalRanking :: GoalRanking -> Char
prettyGoalRanking ranking = case find (\(_,v) -> v == ranking) $ combinedIdentifiers of
    Just (k,_) -> k
    Nothing    -> error "Goal ranking does not have a defined identifier"
  where
    -- Note because find works left first this will look at non-diff identifiers first. Thus,
    -- this assumes the diff rankings don't use a different character for the same goal ranking.
    combinedIdentifiers = (M.toList goalRankingIdentifiers) ++ (M.toList goalRankingIdentifiersDiff)
