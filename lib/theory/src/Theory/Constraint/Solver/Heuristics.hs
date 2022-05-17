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
  , prioString
  , tacticiDeprio
  , deprioString
  , prioFunctions
  , deprioFunctions
  , mapInternalTacticRanking
  , maybeSetInternalTacticName

  , goalRankingIdentifiers
  , goalRankingIdentifiersDiff
  , goalRankingToChar

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
import           Data.List          (find,intercalate)
import           System.FilePath
import           Text.Show.Functions()

import           Theory.Text.Pretty
import           Theory.Constraint.Solver.AnnotatedGoals
--import           Theory.Constraint.SystemLight
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

data Prio a = Prio {
       functionsPrio :: [AnnotatedGoal -> a -> System -> Bool]  
     , stringsPrio :: [String]
    }
    --deriving Show
    deriving( Generic )

instance Show Prio where
    show p = intercalate ", " $ prioString p

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

data Deprio a = Deprio {
       functionsDeprio :: [AnnotatedGoal -> a -> System -> Bool]
     , stringsDeprio :: [String]
    }
    deriving ( Generic )

instance Show Deprio where
    show d = intercalate ", " $ deprioString d

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
      _presort :: GoalRanking,
      _prios :: [Prio],
      _deprios :: [Deprio]
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
defaultTacticI = TacticI "default" (SmartRanking False) [] []


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

tacticiPresort :: TacticI -> GoalRanking
tacticiPresort TacticI{..} = _presort

tacticiPrio :: TacticI -> [Prio]
tacticiPrio TacticI{..} = _prios

prioString :: Prio -> [String]
prioString Prio{..} = stringsPrio

prioFunctions :: Prio -> [AnnotatedGoal -> a -> System -> Bool] 
prioFunctions Prio{..} = functionsPrio


tacticiDeprio :: TacticI -> [Deprio]
tacticiDeprio TacticI{..} = _deprios

deprioFunctions :: Deprio -> [AnnotatedGoal -> a -> System -> Bool] 
deprioFunctions Deprio{..} = functionsDeprio

deprioString :: Deprio -> [String]
deprioString Deprio{..} = stringsDeprio

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

goalRankingToIdentifiersNoOracle :: M.Map GoalRanking Char
goalRankingToIdentifiersNoOracle = M.fromList
                        [ (SmartRanking False, 's')
                        , (SmartRanking True, 'S')
                        , (SapicRanking, 'p')
                        , (SapicPKCS11Ranking, 'P')
                        , (UsefulGoalNrRanking, 'c')
                        , (GoalNrRanking, 'C')
                        , (InjRanking False, 'i')
                        , (InjRanking True, 'I')
                        ]

goalRankingIdentifiersDiff :: M.Map String GoalRanking
goalRankingIdentifiersDiff  = M.fromList
                            [ ("s", SmartDiffRanking)
                            , ("o", OracleRanking defaultOracle)
                            , ("O", OracleSmartRanking defaultOracle)
                            , ("c", UsefulGoalNrRanking)
                            , ("C", GoalNrRanking)
                            ]

goalRankingIdentifiersDiffNoOracle :: M.Map String GoalRanking
goalRankingIdentifiersDiffNoOracle  = M.fromList
                            [ ("s", SmartDiffRanking)
                            , ("c", UsefulGoalNrRanking)
                            , ("C", GoalNrRanking)
                            ]

stringToGoalRankingMay :: Bool -> String -> Maybe GoalRanking
stringToGoalRankingMay noOracle s = if noOracle then M.lookup s goalRankingIdentifiersNoOracle else M.lookup s goalRankingIdentifiers

goalRankingToChar :: GoalRanking -> Char
goalRankingToChar g = fromMaybe (error $ render $ sep $ map text $ lines $ "Unknown goal ranking.")
    $ M.lookup g goalRankingToIdentifiersNoOracle

stringToGoalRanking :: Bool -> String -> GoalRanking
stringToGoalRanking noOracle s = fromMaybe
    (error $ render $ sep $ map text $ lines $ "Unknown goal ranking '" ++ s
        ++ "'. Use one of the following:\n" ++ listGoalRankings noOracle)
    $ stringToGoalRankingMay noOracle s


stringToGoalRankingDiffMay :: Bool -> String -> Maybe GoalRanking
stringToGoalRankingDiffMay noOracle s = if noOracle then M.lookup s goalRankingIdentifiersDiffNoOracle else M.lookup s goalRankingIdentifiersDiff

stringToGoalRankingDiff :: Bool -> String -> GoalRanking
stringToGoalRankingDiff noOracle s = fromMaybe
    (error $ render $ sep $ map text $ lines $ "Unknown goal ranking '" ++ s
        ++ "'. Use one of the following:\n" ++ listGoalRankings noOracle)
    $ stringToGoalRankingDiffMay noOracle s  

listGoalRankings :: Bool -> String
listGoalRankings noOracle = M.foldMapWithKey
    (\k v -> "'"++k++"': " ++ goalRankingName v ++ "\n") goalRankingIdentifiersList
    where
        goalRankingIdentifiersList = if noOracle then goalRankingIdentifiersNoOracle else goalRankingIdentifiers


listGoalRankingsDiff :: Bool -> String
listGoalRankingsDiff noOracle = M.foldMapWithKey
    (\k v -> "'"++k++"': " ++ goalRankingName v ++ "\n") goalRankingIdentifiersDiffList
    where
        goalRankingIdentifiersDiffList = if noOracle then goalRankingIdentifiersDiffNoOracle else goalRankingIdentifiersDiff


filterHeuristic :: String -> [GoalRanking]
filterHeuristic ('{':t) = InternalTacticRanking (TacticI (takeWhile (/= '}') t) (SmartRanking False) [] []):(filterHeuristic $ tail $ dropWhile (/= '}') t)
filterHeuristic (c:t)   = (stringToGoalRanking False [c]):(filterHeuristic t)
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
