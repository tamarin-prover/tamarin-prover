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

  , TacticI(..)
  , Prio(..)
  , Deprio(..)
  , defaultTacticI
  , tacticiName
  , tacticiPresort
  , tacticiPrio
  , tacticiPrioString
  , tacticiDeprio
  , tacticiDeprioString
  , prioFunctions
  , deprioFunctions
  , mapInternalTacticRanking
  , maybeSetInternalTacticName

  , goalRankingIdentifiers
  , goalRankingIdentifiersDiff

  , stringToGoalRankingMay
  , stringToGoalRanking
  , stringToGoalRankingDiffMay
  , stringToGoalRankingDiff
  , filterHeuristic

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
import           Text.Show.Functions()

import           Theory.Text.Pretty
import           Theory.Constraint.Solver.AnnotatedGoals
import           Debug.Trace

------------------------------------------------------------------------------
-- Tactics external
------------------------------------------------------------------------------

data Oracle = Oracle {
    oracleWorkDir :: !FilePath
  , oracleRelPath :: !FilePath
  }
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

------------------------------------------------------------------------------
-- Tactics internal
------------------------------------------------------------------------------

data Prio = Prio {
      functionsPrio :: [AnnotatedGoal -> Bool]  
    }
    --deriving Show
    deriving( Show, Generic )

instance Eq Prio where
    (==) _ _ = True

instance Ord Prio where
    compare _ _ = EQ
    (<=) _ _ = True

instance NFData Prio where
    rnf _ = ()

instance Binary Prio where
    put p = put $ show p
    get = return Prio{..}

data Deprio = Deprio {
      functionsDeprio :: [AnnotatedGoal -> Bool]
    }
    deriving ( Show, Generic )
    --deriving( Eq, Ord, Show, Generic, NFData, Binary )

instance Eq Deprio where
    (==) _ _ = True

instance Ord Deprio where
    compare _ _ = EQ
    (<=) _ _ = True

instance NFData Deprio where
    rnf _ = ()

instance Binary Deprio where
    put d = put $ show d
    get = return Deprio{..}

-- | New type for Tactis inside the theory file
data TacticI = TacticI{
      _name :: String,
      _presort :: Char,
      _prios :: [Prio],
      _prioString :: [[String]],
      _deprios :: [Deprio],
      _deprioString :: [[String]]
    }
    deriving (Eq, Ord, Show, Generic, NFData, Binary )
    --deriving( Eq, Ord, Show, Generic, NFData, Binary )


-- | The different available functions to rank goals with respect to their
-- order of solving in a constraint system.
data GoalRanking =
    GoalNrRanking
  | OracleRanking Oracle
  | OracleSmartRanking Oracle
  | InternalTacticRanking TacticI
  | SapicRanking
  | SapicPKCS11Ranking
  | UsefulGoalNrRanking
  | SmartRanking Bool
  | SmartDiffRanking
  | InjRanking Bool
  deriving (Eq, Ord, Show, Generic, NFData, Binary  )
  --deriving( Eq, Ord, Show, Generic, NFData, Binary )

newtype Heuristic = Heuristic [GoalRanking]
    deriving (Eq, Ord, Show, Generic, NFData, Binary  )
    --deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- Default rankings for normal and diff mode.
defaultRankings :: Bool -> [GoalRanking]
defaultRankings False = [SmartRanking False]
defaultRankings True = [SmartDiffRanking]

-- Default heuristic for normal and diff mode.
defaultHeuristic :: Bool -> Heuristic
defaultHeuristic = Heuristic . defaultRankings

defaultTacticI :: TacticI
defaultTacticI = TacticI "default" 's' [] [] [] []


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

maybeSetInternalTacticName :: Maybe String -> TacticI -> TacticI
maybeSetInternalTacticName s t = maybe t (\x -> t{ _name = x }) s

mapInternalTacticRanking :: (TacticI -> TacticI) -> GoalRanking -> GoalRanking
mapInternalTacticRanking f (InternalTacticRanking t) = InternalTacticRanking (f t)
mapInternalTacticRanking _ r = r


tacticiName :: TacticI -> String
tacticiName TacticI{..} = _name

tacticiPresort :: TacticI -> Char
tacticiPresort TacticI{..} = _presort

tacticiPrio :: TacticI -> [Prio]
tacticiPrio TacticI{..} = _prios

tacticiPrioString :: TacticI -> [[String]]
tacticiPrioString TacticI{..} = _prioString

prioFunctions :: Prio -> [AnnotatedGoal -> Bool] 
prioFunctions Prio{..} = functionsPrio

deprioFunctions :: Deprio -> [AnnotatedGoal -> Bool] 
deprioFunctions Deprio{..} = functionsDeprio

tacticiDeprio :: TacticI -> [Deprio]
tacticiDeprio TacticI{..} = _deprios

tacticiDeprioString :: TacticI -> [[String]]
tacticiDeprioString TacticI{..} = _deprioString

--setTact

goalRankingIdentifiers :: M.Map String GoalRanking
goalRankingIdentifiers = M.fromList
                        [ ("s", SmartRanking False)
                        , ("S", SmartRanking True)
                        , ("o", OracleRanking defaultOracle)
                        , ("O", OracleSmartRanking defaultOracle)
                        , ("p", SapicRanking)
                        , ("P", SapicPKCS11Ranking)
                        , ("c", UsefulGoalNrRanking)
                        , ("C", GoalNrRanking)
                        , ("i", InjRanking False)
                        , ("I", InjRanking True)
                        , ("{.}", InternalTacticRanking defaultTacticI)
                        ]

goalRankingIdentifiersNoOracle :: M.Map String GoalRanking
goalRankingIdentifiersNoOracle = M.fromList
                        [ ("s", SmartRanking False)
                        , ("S", SmartRanking True)
                        , ("p", SapicRanking)
                        , ("P", SapicPKCS11Ranking)
                        , ("c", UsefulGoalNrRanking)
                        , ("C", GoalNrRanking)
                        , ("i", InjRanking False)
                        , ("I", InjRanking True)
                        ]

goalRankingIdentifiersDiff :: M.Map String GoalRanking
goalRankingIdentifiersDiff  = M.fromList
                            [ ("s", SmartDiffRanking)
                            , ("o", OracleRanking defaultOracle)
                            , ("O", OracleSmartRanking defaultOracle)
                            , ("c", UsefulGoalNrRanking)
                            , ("C", GoalNrRanking)
                            ]

stringToGoalRankingMay :: String -> String -> Maybe GoalRanking
stringToGoalRankingMay "noOracle" s = M.lookup s goalRankingIdentifiersNoOracle
stringToGoalRankingMay      _     s = M.lookup s goalRankingIdentifiers

stringToGoalRanking :: String -> String -> GoalRanking
stringToGoalRanking "noOracle" s = fromMaybe
    (error $ render $ sep $ map text $ lines $ "Unknown goal ranking '" ++ s
        ++ "'. Use one of the following:\n" ++ listGoalRankingsNoOracle)
    $ stringToGoalRankingMay "noOracle" s
stringToGoalRanking    _     s = fromMaybe
    (error $ render $ sep $ map text $ lines $ "Unknown goal ranking '" ++ s
        ++ "'. Use one of the following:\n" ++ listGoalRankings)
    $ stringToGoalRankingMay "" s

stringToGoalRankingDiffMay :: String -> Maybe GoalRanking
stringToGoalRankingDiffMay s = M.lookup s goalRankingIdentifiersDiff

stringToGoalRankingDiff :: String -> GoalRanking
stringToGoalRankingDiff s = fromMaybe
    (error $ render $ sep $ map text $ lines $ "Unknown goal ranking '" ++ s
        ++ "'. Use one of the following:\n" ++ listGoalRankingsDiff)
    $ stringToGoalRankingDiffMay s

listGoalRankings :: String
listGoalRankings = M.foldMapWithKey
    (\k v -> "'"++k++"': " ++ goalRankingName v ++ "\n") goalRankingIdentifiers

listGoalRankingsNoOracle :: String
listGoalRankingsNoOracle = M.foldMapWithKey
    (\k v -> "'"++k++"': " ++ goalRankingName v ++ "\n") goalRankingIdentifiersNoOracle

listGoalRankingsDiff :: String
listGoalRankingsDiff = M.foldMapWithKey
    (\k v -> "'"++k++"': " ++ goalRankingName v ++ "\n") goalRankingIdentifiersDiff

filterHeuristic :: String -> [GoalRanking]
filterHeuristic ('{':t) = InternalTacticRanking (TacticI (takeWhile (/= '}') t) ' ' [] [] [] []):(filterHeuristic $ tail $ dropWhile (/= '}') t)
filterHeuristic (c:t)   = (stringToGoalRanking "" [c]):(filterHeuristic t)
filterHeuristic ("")    = []

-- | The name/explanation of a 'GoalRanking'.
goalRankingName :: GoalRanking -> String
goalRankingName ranking =
    "Goals sorted according to " ++ case ranking of
        GoalNrRanking                 -> "their order of creation"
        OracleRanking oracle          -> "an oracle for ranking, located at " ++ oraclePath oracle
        OracleSmartRanking oracle     -> "an oracle for ranking based on 'smart' heuristic, located at " ++ oraclePath oracle
        UsefulGoalNrRanking           -> "their usefulness and order of creation"
        SapicRanking                  -> "heuristics adapted for processes"
        SapicPKCS11Ranking            -> "heuristics adapted to a specific model of PKCS#11 expressed using SAPIC. deprecated."
        SmartRanking useLoopBreakers  -> "the 'smart' heuristic" ++ loopStatus useLoopBreakers
        SmartDiffRanking              -> "the 'smart' heuristic (for diff proofs)"
        InjRanking useLoopBreakers    -> "heuristics adapted to stateful injective protocols" ++ loopStatus useLoopBreakers
        InternalTacticRanking tactic  -> "the tactic written in the theory file: "++tacticiName tactic
   where
     loopStatus b = " (loop breakers " ++ (if b then "allowed" else "delayed") ++ ")"

prettyGoalRankings :: [GoalRanking] -> String
prettyGoalRankings rs = unwords (map prettyGoalRanking rs)

prettyGoalRanking :: GoalRanking -> String
prettyGoalRanking ranking = case ranking of
    OracleRanking oracle            -> findIdentifier ranking ++ " \"" ++ oracleRelPath oracle ++ "\""
    OracleSmartRanking oracle       -> findIdentifier ranking ++ " \"" ++ oracleRelPath oracle ++ "\""
    InternalTacticRanking tactic    -> '{':tacticiName tactic++"}"
    _                         -> findIdentifier ranking
  where
    findIdentifier r = case find (compareRankings r . snd) combinedIdentifiers of
        Just (k,_) -> k
        Nothing    -> error "Goal ranking does not have a defined identifier"

    -- Note because find works left first this will look at non-diff identifiers first. Thus,
    -- this assumes the diff rankings don't use a different character for the same goal ranking.
    combinedIdentifiers = M.toList goalRankingIdentifiers ++ M.toList goalRankingIdentifiersDiff

    compareRankings (OracleRanking _) (OracleRanking _) = True
    compareRankings (OracleSmartRanking _) (OracleSmartRanking _) = True
    compareRankings (InternalTacticRanking _ ) (InternalTacticRanking _ ) = True
    -- compareRankings r1 r2 = r1 == r2
    compareRankings _ _ = True
