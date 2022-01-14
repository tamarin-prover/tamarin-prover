{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE RecordWildCards    #-}
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
  , defaultRankings
  , defaultHeuristic

  , Oracle(..)
  , defaultOracle
  , oraclePath
  , maybeSetOracleWorkDir
  , maybeSetOracleRelPath
  , mapOracleRanking

  , Tactic(..)
  , defaultTactic
  , tacticPath
  , maybeSetTacticWorkDir
  , maybeSetTacticRelPath
  , mapTacticRanking

  , TacticI(..)
  , Prio(..)
  , Deprio(..)
  , defaultTacticI
  , tacticiName
  , tacticiPrio
  , tacticiDeprio
  , prioFunctions
  , deprioFunctions

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
import           System.FilePath

import           Theory.Text.Pretty

------------------------------------------------------------------------------
-- Tactics external
------------------------------------------------------------------------------

data Oracle = Oracle {
    oracleWorkDir :: !FilePath
  , oracleRelPath :: !FilePath
  }
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

data Tactic = Tactic {
    tacticWorkDir :: !FilePath
  , tacticRelPath :: !FilePath
  }
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

------------------------------------------------------------------------------
-- Tactics internal
------------------------------------------------------------------------------

data Prio = Prio {
      functionsPrio :: [(String,String)]  
    }
    deriving( Eq, Ord, Show, Generic, NFData, Binary )

data Deprio = Deprio {
      functionsDeprio :: [(String,String)]
    }
    deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | New type for Tactis inside the theory file
data TacticI = TacticI{
      _name :: String,
      _prios :: [Prio],
      _deprios :: [Deprio]
    }
    deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | The different available functions to rank goals with respect to their
-- order of solving in a constraint system.
data GoalRanking =
    GoalNrRanking
  | OracleRanking Oracle
  | OracleSmartRanking Oracle
  | TacticRanking Tactic
  | TacticSmartRanking Tactic
  | InternalTactic
  | SapicRanking
  | SapicPKCS11Ranking
  | UsefulGoalNrRanking
  | SmartRanking Bool
  | SmartDiffRanking
  | InjRanking Bool
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

newtype Heuristic = Heuristic [GoalRanking]
    deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- Default rankings for normal and diff mode.
defaultRankings :: Bool -> [GoalRanking]
defaultRankings False = [SmartRanking False]
defaultRankings True = [SmartDiffRanking]

-- Default heuristic for normal and diff mode.
defaultHeuristic :: Bool -> Heuristic
defaultHeuristic = Heuristic . defaultRankings

defaultTacticI :: TacticI
defaultTacticI = TacticI "default" [] []


-- Default to "./oracle" in the current working directory.
defaultOracle :: Oracle
defaultOracle = Oracle "." "oracle"

maybeSetOracleWorkDir :: Maybe FilePath -> Oracle -> Oracle
maybeSetOracleWorkDir p o = maybe o (\x -> o{ oracleWorkDir = x }) p

maybeSetOracleRelPath :: Maybe FilePath -> Oracle -> Oracle
maybeSetOracleRelPath p o = maybe o (\x -> o{ oracleRelPath = x }) p

mapOracleRanking :: (Oracle -> Oracle) -> GoalRanking -> GoalRanking
mapOracleRanking f (OracleRanking o) = OracleRanking (f o)
mapOracleRanking f (OracleSmartRanking o) = OracleSmartRanking (f o)
mapOracleRanking _ r = r

oraclePath :: Oracle -> FilePath
oraclePath Oracle{..} = oracleWorkDir </> normalise oracleRelPath

-- Default to "./oracle" in the current working directory.
defaultTactic :: Tactic
defaultTactic = Tactic "." "tactic"

maybeSetTacticWorkDir :: Maybe FilePath -> Tactic -> Tactic
maybeSetTacticWorkDir p t = maybe t (\x -> t{ tacticWorkDir = x }) p

maybeSetTacticRelPath :: Maybe FilePath -> Tactic -> Tactic
maybeSetTacticRelPath p t = maybe t (\x -> t{ tacticRelPath = x }) p

mapTacticRanking :: (Tactic -> Tactic) -> GoalRanking -> GoalRanking
mapTacticRanking f (TacticRanking t) = TacticRanking (f t)
mapTacticRanking f (TacticSmartRanking t) = TacticSmartRanking (f t)
mapTacticRanking _ r = r

tacticPath :: Tactic -> FilePath
tacticPath Tactic{..} = tacticWorkDir </> normalise tacticRelPath

tacticiName :: TacticI -> String
tacticiName TacticI{..} = _name

tacticiPrio :: TacticI -> [Prio]
tacticiPrio TacticI{..} = _prios

prioFunctions :: Prio -> [(String,String)] 
prioFunctions Prio{..} = functionsPrio

deprioFunctions :: Deprio -> [(String,String)] 
deprioFunctions Deprio{..} = functionsDeprio

tacticiDeprio :: TacticI -> [Deprio]
tacticiDeprio TacticI{..} = _deprios

goalRankingIdentifiers :: M.Map Char GoalRanking
goalRankingIdentifiers = M.fromList
                        [ ('s', SmartRanking False)
                        , ('S', SmartRanking True)
                        , ('o', OracleRanking defaultOracle)
                        , ('O', OracleSmartRanking defaultOracle)
                        , ('t', TacticRanking defaultTactic)
                        , ('T', TacticSmartRanking defaultTactic)
                        , ('p', SapicRanking)
                        , ('P', SapicPKCS11Ranking)
                        , ('c', UsefulGoalNrRanking)
                        , ('C', GoalNrRanking)
                        , ('i', InjRanking False)
                        , ('I', InjRanking True)
                        , ('k', InternalTactic)
                        ]

goalRankingIdentifiersDiff :: M.Map Char GoalRanking
goalRankingIdentifiersDiff  = M.fromList
                            [ ('s', SmartDiffRanking)
                            , ('o', OracleRanking defaultOracle)
                            , ('O', OracleSmartRanking defaultOracle)
                            , ('t', TacticRanking defaultTactic)
                            , ('T', TacticSmartRanking defaultTactic)
                            , ('c', UsefulGoalNrRanking)
                            , ('C', GoalNrRanking)
                            , ('k', InternalTactic)
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
        OracleRanking oracle          -> "an oracle for ranking, located at " ++ oraclePath oracle
        OracleSmartRanking oracle     -> "an oracle for ranking based on 'smart' heuristic, located at " ++ oraclePath oracle
        TacticRanking tactic          -> "an tactic for ranking, located at " ++ tacticPath tactic
        TacticSmartRanking tactic     -> "an tactic for ranking based on 'smart' heuristic, located at " ++ tacticPath tactic
        UsefulGoalNrRanking           -> "their usefulness and order of creation"
        SapicRanking                  -> "heuristics adapted for processes"
        SapicPKCS11Ranking            -> "heuristics adapted to a specific model of PKCS#11 expressed using SAPIC. deprecated."
        SmartRanking useLoopBreakers  -> "the 'smart' heuristic" ++ loopStatus useLoopBreakers
        SmartDiffRanking              -> "the 'smart' heuristic (for diff proofs)"
        InjRanking useLoopBreakers    -> "heuristics adapted to stateful injective protocols" ++ loopStatus useLoopBreakers
        InternalTactic                -> "the tactic written in the theory file"
   where
     loopStatus b = " (loop breakers " ++ (if b then "allowed" else "delayed") ++ ")"

prettyGoalRankings :: [GoalRanking] -> String
prettyGoalRankings rs = unwords (map prettyGoalRanking rs)

prettyGoalRanking :: GoalRanking -> String
prettyGoalRanking ranking = case ranking of
    OracleRanking oracle      -> findIdentifier ranking : " \"" ++ oracleRelPath oracle ++ "\""
    OracleSmartRanking oracle -> findIdentifier ranking : " \"" ++ oracleRelPath oracle ++ "\""
    TacticRanking tactic      -> findIdentifier ranking : " \"" ++ tacticRelPath tactic ++ "\""
    TacticSmartRanking tactic -> findIdentifier ranking : " \"" ++ tacticRelPath tactic ++ "\""
    _                         -> [findIdentifier ranking]
  where
    findIdentifier r = case find (compareRankings r . snd) combinedIdentifiers of
        Just (k,_) -> k
        Nothing    -> error "Goal ranking does not have a defined identifier"

    -- Note because find works left first this will look at non-diff identifiers first. Thus,
    -- this assumes the diff rankings don't use a different character for the same goal ranking.
    combinedIdentifiers = M.toList goalRankingIdentifiers ++ M.toList goalRankingIdentifiersDiff

    compareRankings (OracleRanking _) (OracleRanking _) = True
    compareRankings (OracleSmartRanking _) (OracleSmartRanking _) = True
    compareRankings r1 r2 = r1 == r2
