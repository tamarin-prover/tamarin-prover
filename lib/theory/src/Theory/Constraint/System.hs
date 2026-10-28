{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE ViewPatterns       #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- This is the public interface for constructing and deconstructing constraint
-- systems. The interface for performing constraint solving provided by
-- "Theory.Constraint.Solver".
module Theory.Constraint.System (
  -- * Constraints
    module Theory.Constraint.System.Constraints
  -- Heuristics (had to be moved here because of circular definition)
  , GoalRanking(..)
  , Heuristic(..)
  , defaultRankings
  , defaultHeuristic

  , Oracle(..)
  , defaultOracle
  , defaultOracleNames
  , oraclePath
  , maybeSetOracleWorkDir
  , maybeSetOracleRelPath
  , mapOracleRanking

  , Tactic(..)
  , Prio(..)
  , Deprio(..)
  -- , Ranking(..)
  , defaultTactic
  , usesOracle
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

  -- * Proof contexts
  -- | The proof context captures all relevant information about the context
  -- in which we are using the constraint solver. These are things like the
  -- signature of the message theory, the multiset rewriting rules of the
  -- protocol, the available precomputed sources, whether induction should be
  -- applied or not, whether raw or refined sources are used, and whether we
  -- are looking for the existence of a trace or proving the absence of any
  -- trace satisfying the constraint system.
  , ProofContext(..)
  , DiffProofContext(..)
  , InductionHint(..)

  , pcSignature
  , pcRules
  , pcInjectiveFactInsts
  , pcSources
  , pcSourceKind
  , pcUseInduction
  , pcHeuristic
  , pcTactic
  , pcTraceQuantifier
  , pcLemmaName
  , pcHiddenLemmas
  , pcMaudeHandle
  , pcDiffContext
  , pcTrueSubterm
  , pcVerbose
  , pcConstantRHS
  , pcIsSapic
  , dpcPCLeft
  , dpcPCRight
  , dpcProtoRules
  , dpcDestrRules
  , dpcConstrRules
  , dpcRestrictions
  , dpcReuseLemmas
  , dpcPreservedActions
  , eitherProofContext

  -- ** Classified rules
  , ClassifiedRules(..)
  , emptyClassifiedRules
  , crConstruct
  , crDestruct
  , crProtocol
  , joinAllRules
  , nonSilentRules

  -- ** Precomputed case distinctions
  -- | For better speed, we precompute case distinctions. This is especially
  -- important for getting rid of all chain constraints before actually
  -- starting to verify security properties.
  , Source(..)

  , cdGoal
  , cdCases

  , Side(..)
  , opposite

  -- * Constraint systems
  , System(..)
  , DiffProofType(..)
  , DiffSystem(..)

  -- ** Construction
  , emptySystem
  , isInitialSystem
  , emptyDiffSystem

  , SystemTraceQuantifier(..)
  , formulaToSystem

  -- ** Diff proof system
  , dsProofType
  , dsProtoRules
  , dsConstrRules
  , dsDestrRules
  , dsCurrentRule
  , dsSide
  , dsSystem
  , dsProofContext

  -- ** Node constraints
  , sNodes
  , allKDConcs
  , allInPrems
  , allPrems

  , nodeRule
  , nodeRuleSafe
  , nodeConcNode
  , nodePremNode
  , nodePremFact
  , nodeConcFact
  , resolveNodePremFact
  , resolveNodeConcFact
  , goalRule

  -- ** Actions
  , allActions
  , allKUActions
  , unsolvedActionAtoms
  -- FIXME: The two functions below should also be prefixed with 'unsolved'
  , kuActionAtoms
  , standardActionAtoms
  , compareSystemsUpToNewVars

  -- ** Edge and chain constraints
  , sEdges
  , unsolvedChains

  , Trivalent(..)

  , isCorrectDG
  , getMirrorDG
  , getMirrorDGandEvaluateRestrictions
  , MirrorGoal(..)
  , MirrorAdmission(..)
  , evaluateRestrictions
  , evaluateRestrictionsFor
  , openGoalsAreAttackerInputs
  , doRestrictionsHold
  , filterRestrictions
  , diffPreservedActionTags
  , DiffRestrictionKind(..)
  , classifyDiffRestriction
  , unsupportedDiffRestrictions

  , checkIndependence

  , unsolvedPremises
  , unsolvedTrivialGoals
  , allFormulasAreSolved
  , dgIsNotEmpty
  , allOpenFactGoalsAreIndependent
  , allOpenGoalsAreSimpleFacts

  -- ** Temporal ordering
  , sLessAtoms

  , getLessAtoms
  , rawLessRel
  , rawEdgeRel

  , alwaysBefore
  , isInTrace

  -- ** The last node
  , sLastAtom
  , isLast

  -- ** Equations
  , module Theory.Tools.EquationStore
  , sEqStore
  , sSubst
  , sConjDisjEqs

  -- ** Subterms
  , module Theory.Tools.SubtermStore
  , sSubtermStore

  -- ** Formulas
  , sFormulas
  , sSolvedFormulas

  -- ** Lemmas
  , sLemmas
  , insertLemmas

  -- ** Keeping track of source assumptions
  , SourceKind(..)
  , sSourceKind

  -- ** Goals
  , GoalStatus(..)
  , gsSolved
  , gsLoopBreaker
  , gsNr

  , sGoals
  , sNextGoalNr

  , isDiffSystem
  , sDiffSystem

  -- * Formula simplification
  , impliedFormulas

  -- * Pretty-printing
  , prettySystem
  , prettyNonGraphSystem
  , prettyNonGraphSystemDiff
  , prettySource

  , nonEmptyGraph
  , nonEmptyGraphDiff

  ) where

-- import           Debug.Trace
-- import           Debug.Trace.Ignore

import           Prelude                              hiding (id, (.))

import           GHC.Generics                         (Generic)

import           Data.Binary
import qualified Data.ByteString.Char8                as BC
import qualified Data.DAG.Simple                      as D
import           Data.List                            (foldl', partition, intersect,find,intercalate)
import qualified Data.Map                             as M
import           Data.Maybe                           (fromMaybe,mapMaybe, isNothing)
-- import           Data.Monoid                          (Monoid(..))
import qualified Data.Monoid                             as Mono
import qualified Data.Set                             as S
import           Data.Either                          (partitionEithers, lefts)
import           Data.Tuple                           (swap)

import           Control.Basics
import           Control.Category
import           Control.DeepSeq
import           Control.Monad.Fresh
import           Control.Monad.Reader

import           Data.Label                           ((:->), mkLabels)
import qualified Extension.Data.Label                 as L

import           GHC.IO                               (unsafePerformIO)

import           Logic.Connectives
import           Theory.Constraint.Solver.AnnotatedGoals
import           Theory.Constraint.System.Constraints
--import           Theory.Constraint.Solver.Heuristics
import           Theory.Model
import           Theory.Text.Pretty
import           Theory.Tools.SubtermStore
import           Theory.Tools.EquationStore
import           Theory.Tools.InjectiveFactInstances

import           System.Directory                     (doesFileExist)
import           System.FilePath
import           Text.Show.Functions()

----------------------------------------------------------------------
-- ClassifiedRules
----------------------------------------------------------------------

data ClassifiedRules = ClassifiedRules
     { _crProtocol      :: [RuleAC] -- all protocol rules
     , _crDestruct      :: [RuleAC] -- destruction rules
     , _crConstruct     :: [RuleAC] -- construction rules
     }
     deriving( Eq, Ord, Show, Generic, NFData, Binary )

$(mkLabels [''ClassifiedRules])

-- | The empty proof rule set.
emptyClassifiedRules :: ClassifiedRules
emptyClassifiedRules = ClassifiedRules [] [] []

-- | @joinAllRules rules@ computes the union of all rules classified in
-- @rules@.
joinAllRules :: ClassifiedRules -> [RuleAC]
joinAllRules (ClassifiedRules a b c) = a ++ b ++ c

-- | Extract all non-silent rules.
nonSilentRules :: ClassifiedRules -> [RuleAC]
nonSilentRules = filter (not . null . L.get rActs) . joinAllRules

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

-- | In the diff type, we have either the Left Hand Side or the Right Hand Side
data Side = LHS | RHS deriving ( Show, Eq, Ord, Read, Generic, NFData, Binary )

opposite :: Side -> Side
opposite LHS = RHS
opposite RHS = LHS

-- | Whether we are checking for the existence of a trace satisfiying a the
-- current constraint system or whether we're checking that no traces
-- satisfies the current constraint system.
data SystemTraceQuantifier = ExistsSomeTrace | ExistsNoTrace
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | Source kind that are allowed. The order of the kinds
-- corresponds to the subkinding relation: raw < refined.
data SourceKind = RawSource | RefinedSource
       deriving( Eq, Generic, NFData, Binary )

instance Show SourceKind where
    show RawSource     = "raw"
    show RefinedSource = "refined"

-- Adapted from the output of 'derive'.
instance Read SourceKind where
        readsPrec p0 r
          = readParen (p0 > 10)
              (\ r0 ->
                 [(RawSource, r1) | ("untyped", r1) <- lex r0])
              r
              ++
              readParen (p0 > 10)
                (\ r0 -> [(RefinedSource, r1) | ("typed", r1) <- lex r0])
                r

instance Ord SourceKind where
    compare RawSource     RawSource     = EQ
    compare RawSource     RefinedSource = LT
    compare RefinedSource RawSource     = GT
    compare RefinedSource RefinedSource = EQ

-- | The status of a 'Goal'. Use its 'Semigroup' instance to combine the
-- status info of goals that collapse.
data GoalStatus = GoalStatus
    { _gsSolved :: Bool
       -- True if the goal has been solved already.
    , _gsNr :: Integer
       -- The number of the goal: we use it to track the creation order of
       -- goals.
    , _gsLoopBreaker :: Bool
       -- True if this goal should be solved with care because it may lead to
       -- non-termination.
    }
    deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A constraint system.
data System = System
    { _sNodes          :: M.Map NodeId RuleACInst
    , _sEdges          :: S.Set Edge
    , _sLessAtoms      :: S.Set LessAtom
    , _sLastAtom       :: Maybe NodeId
    , _sSubtermStore   :: SubtermStore
    , _sEqStore        :: EqStore
    , _sFormulas       :: S.Set LNGuarded
    , _sSolvedFormulas :: S.Set LNGuarded
    , _sLemmas         :: S.Set LNGuarded
    , _sGoals          :: M.Map Goal GoalStatus
    , _sNextGoalNr     :: Integer
    , _sSourceKind     :: SourceKind
    , _sDiffSystem     :: Bool
    }
    -- NOTE: Don't forget to update 'substSystem' in
    -- "Constraint.Solver.Reduction" when adding further fields to the
    -- constraint system.
    deriving( Eq, Ord, Generic, NFData, Binary )

$(mkLabels [''System, ''GoalStatus])

deriving instance Show System

-- Further accessors
--------------------

-- | Label to access the free substitution of the equation store.
sSubst :: System :-> LNSubst
sSubst = eqsSubst . sEqStore

-- | Label to access the conjunction of disjunctions of fresh substutitution in
-- the equation store.
sConjDisjEqs :: System :-> Conj (SplitId, S.Set (LNSubstVFresh))
sConjDisjEqs = eqsConj . sEqStore

------------------------------------------------------------------------------
-- Oracles
------------------------------------------------------------------------------

data Oracle = Oracle {
    oracleWorkDir :: !(Maybe FilePath)
  , oracleRelPath :: !(Maybe FilePath)
  }
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

------------------------------------------------------------------------------
-- Tactics
------------------------------------------------------------------------------


-- | Prio keeps a list of function that aim at recognizing some goals based on the state of the
-- | System, the ProofContext and the Annotated Goal considered. If one of the function returns
-- | True for a goal, it is considered recognized by the all priority. Prio also holds an other
-- | function that will order the recognized goals based on some arbitrary criteria such as size...
-- | The goals recognized by a Prio will be treated earlier than the others.
data Prio a = Prio {
       rankingPrio :: Maybe ([AnnotatedGoal] -> [AnnotatedGoal]) -- An optional function to order the recognized goals
     , stringRankingPrio :: String                               -- The name of the function for pretty printing
     , functionsPrio :: [(AnnotatedGoal, a, System) -> Bool]     -- The main list of function
     , stringsPrio :: [String]                                   -- The name of the function for pretty printing
    }
    --deriving Show
    deriving( Generic )

instance Show (Prio a) where
    show p = (stringRankingPrio p) ++ " _ " ++ intercalate ", " (stringsPrio p)

instance Eq (Prio a) where
    (==) _ _ = True

instance Ord (Prio a) where
    compare _ _ = EQ
    (<=) _ _ = True

instance NFData (Prio a) where
    rnf _ = ()

instance Binary (Prio a) where
    put p = put $ show p
    get = return (Prio Nothing "" [] [])

-- | Derio keeps a list of function that aim at recognizing some goals based on the state of the
-- | System, the ProofContext and the Annotated Goal considered. If one of the function returns
-- | True for a goal, it is considered recognized by the all priority. Prio also holds an other
-- | function that will order the recognized goals based on some arbitrary criteria such as size...
-- | Deprio works as Prio but the goals it recognizes will be treated later than the others.
data Deprio a = Deprio {
       rankingDeprio :: Maybe ([AnnotatedGoal] -> [AnnotatedGoal]) -- An optional function to order the recognized goals
     , stringRankingDeprio :: String                               -- The name of the function for pretty printing
     , functionsDeprio :: [(AnnotatedGoal, a, System) -> Bool]     -- The main list of function
     , stringsDeprio :: [String]                                        -- The name of the function for pretty printing
    }
    deriving ( Generic )

instance Show (Deprio a) where
    show d = (stringRankingDeprio d) ++ " _ " ++ intercalate ", " (map show $ stringsDeprio d)

instance Eq (Deprio a) where
    (==) _ _ = True

instance Ord (Deprio a) where
    compare _ _ = EQ
    (<=) _ _ = True

instance NFData (Deprio a) where
    rnf _ = ()

instance Binary (Deprio a) where
    put d = put $ show d
    get = return (Deprio Nothing "" [] [])


-- | The object that record a user written tactic.
data Tactic a = Tactic{
      _name :: String,                  -- The name of the tactic
      _presort :: GoalRanking a,        -- The default strategy to order recognized goals in a tactic
      _prios :: [Prio a],               -- The list of priorities, the higher in the list the priority, the earlier its recognized goals will be treated
      _deprios :: [Deprio a]            -- The list of depriorities, the higher in the list the priority, the earlier its recognized goals will be treated
                                        -- (but still after all the goals recognized by the priorities and not recognized has been treated).
    }
    deriving (Eq, Ord, Show, Generic, NFData, Binary )


-- | The different available functions to rank goals with respect to their
-- order of solving in a constraint system.
data GoalRanking a =
    GoalNrRanking
  | OracleRanking Bool Oracle
  | OracleSmartRanking Bool Oracle
  | InternalTacticRanking Bool (Tactic a)
  | SapicRanking
  | SapicPKCS11Ranking
  | UsefulGoalNrRanking
  | SmartRanking Bool
  | SmartDiffRanking
  | InjRanking Bool
  deriving (Eq, Ord, Show, Generic, NFData, Binary  )

newtype Heuristic a = Heuristic [GoalRanking a]
    deriving (Eq, Ord, Show, Generic, NFData, Binary  )

-- Default rankings for normal and diff mode.
defaultRankings :: Bool -> [GoalRanking ProofContext]
defaultRankings False = [SmartRanking False]
defaultRankings True = [SmartDiffRanking]

-- Default heuristic for normal and diff mode.
defaultHeuristic :: Bool -> (Heuristic ProofContext)
defaultHeuristic = Heuristic . defaultRankings

defaultTactic :: Tactic ProofContext
defaultTactic = Tactic "default" (SmartRanking False) [] []

usesOracle :: Heuristic a -> Bool
usesOracle (Heuristic rs) = all isOracleRanking rs
  where
    isOracleRanking :: GoalRanking a -> Bool
    isOracleRanking (OracleRanking _ _) = True
    isOracleRanking (OracleSmartRanking _ _) = True
    isOracleRanking (InternalTacticRanking _ _) = True
    isOracleRanking _ = False

-- Default to "./oracle" in the current working directory.
defaultOracle :: Oracle
defaultOracle = Oracle Nothing Nothing

-- | Set the oraclename to the default ./theory_filename.oracle for all oracles in a heuristic.
defaultOracleNames :: FilePath -> [GoalRanking ProofContext] ->[GoalRanking ProofContext]
defaultOracleNames srcThyInFileName = map (mapOracleRanking remapOracle)
  where
    remapOracle o@(Oracle workDir relPath) =
      if isNothing relPath
        then
          let oracleDir = fromMaybe (takeDirectory srcThyInFileName) workDir
              mkOracle = Oracle (Just oracleDir) . Just
          in if unsafePerformIO (doesFileExist (oracleDir </> inFileOracleName))
               then mkOracle inFileOracleName
               else mkOracle "oracle"
        else o
    inFileOracleName = takeBaseName srcThyInFileName <.> "oracle"

maybeSetOracleWorkDir :: Maybe FilePath -> Oracle -> Oracle
maybeSetOracleWorkDir p o = o{ oracleWorkDir = p }

maybeSetOracleRelPath :: Maybe FilePath -> Oracle -> Oracle
maybeSetOracleRelPath p o = o{ oracleRelPath = p }

mapOracleRanking :: (Oracle -> Oracle) -> GoalRanking ProofContext -> GoalRanking ProofContext
mapOracleRanking f (OracleRanking b o) = OracleRanking b (f o)
mapOracleRanking f (OracleSmartRanking b o) = OracleSmartRanking b (f o)
mapOracleRanking _ r = r

oraclePath :: Oracle -> FilePath
oraclePath (Oracle oracleWorkDir_ oracleRelPath_) = fromMaybe "." oracleWorkDir_ </> normalise (fromMaybe "" oracleRelPath_)

maybeSetInternalTacticName :: Maybe String -> Tactic ProofContext -> Tactic ProofContext
maybeSetInternalTacticName s t = maybe t (\x -> t{ _name = x }) s

mapInternalTacticRanking :: (Tactic ProofContext -> Tactic ProofContext) -> GoalRanking ProofContext -> GoalRanking ProofContext
mapInternalTacticRanking f (InternalTacticRanking q t) = InternalTacticRanking q (f t)
mapInternalTacticRanking _ r = r


goalRankingIdentifiers :: M.Map String (GoalRanking ProofContext)
goalRankingIdentifiers = M.fromList
                        [ ("s", SmartRanking False)
                        , ("S", SmartRanking True)
                        , ("o", OracleRanking False defaultOracle)
                        , ("O", OracleSmartRanking False defaultOracle)
                        , ("p", SapicRanking)
                        , ("P", SapicPKCS11Ranking)
                        , ("c", UsefulGoalNrRanking)
                        , ("C", GoalNrRanking)
                        , ("i", InjRanking False)
                        , ("I", InjRanking True)
                        , ("{.}", InternalTacticRanking False defaultTactic)
                        ]

goalRankingIdentifiersNoOracle :: M.Map String (GoalRanking ProofContext)
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

goalRankingToIdentifiersNoOracle :: M.Map (GoalRanking ProofContext) Char
goalRankingToIdentifiersNoOracle = M.fromList
                        [ (SmartRanking False, 's')
                        , (SmartDiffRanking, 's')
                        , (SmartRanking True, 'S')
                        , (SapicRanking, 'p')
                        , (SapicPKCS11Ranking, 'P')
                        , (UsefulGoalNrRanking, 'c')
                        , (GoalNrRanking, 'C')
                        , (InjRanking False, 'i')
                        , (InjRanking True, 'I')
                        ]

goalRankingIdentifiersDiff :: M.Map String (GoalRanking ProofContext)
goalRankingIdentifiersDiff  = M.fromList
                            [ ("s", SmartDiffRanking)
                            , ("S", SmartRanking True)
                            , ("o", OracleRanking False defaultOracle)
                            , ("O", OracleSmartRanking False defaultOracle)
                            , ("c", UsefulGoalNrRanking)
                            , ("C", GoalNrRanking)
                            , ("{.}", InternalTacticRanking False defaultTactic)
                            ]

goalRankingIdentifiersDiffNoOracle :: M.Map String (GoalRanking ProofContext)
goalRankingIdentifiersDiffNoOracle  = M.fromList
                            [ ("s", SmartDiffRanking)
                            , ("S", SmartRanking True)
                            , ("c", UsefulGoalNrRanking)
                            , ("C", GoalNrRanking)
                            ]

stringToGoalRankingMay :: Bool -> String -> Maybe (GoalRanking ProofContext)
stringToGoalRankingMay noOracle s = if noOracle then M.lookup s goalRankingIdentifiersNoOracle else M.lookup s goalRankingIdentifiers

goalRankingToChar :: GoalRanking ProofContext -> Char
goalRankingToChar g = fromMaybe (error $ render $ sep $ map text $ lines $ "Unknown proof method ranking."++ show g)
    $ M.lookup g goalRankingToIdentifiersNoOracle

stringToGoalRanking :: Bool -> String -> GoalRanking ProofContext
stringToGoalRanking noOracle s = fromMaybe
    (error $ render $ sep $ map text $ lines $ "Unknown proof method ranking '" ++ s
        ++ "'. Use one of the following:\n" ++ listGoalRankings noOracle)
    $ stringToGoalRankingMay noOracle s

stringToGoalRankingDiffMay :: Bool -> String -> Maybe (GoalRanking ProofContext)
stringToGoalRankingDiffMay noOracle s = if noOracle then M.lookup s goalRankingIdentifiersDiffNoOracle else M.lookup s goalRankingIdentifiersDiff

stringToGoalRankingDiff :: Bool -> String -> GoalRanking ProofContext
stringToGoalRankingDiff noOracle s = fromMaybe
    (error $ render $ sep $ map text $ lines $ "Unknown proof method ranking '" ++ s
        ++ "'. Use one of the following:\n" ++ listGoalRankingsDiff noOracle)
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


filterHeuristic :: Bool -> String -> [GoalRanking ProofContext]
filterHeuristic diff  ('{':t) = if '}' `elem` t then InternalTacticRanking False (Tactic (takeWhile (/= '}') t) (SmartRanking False) [] []):(filterHeuristic diff $ tail $ dropWhile (/= '}') t) else error "A call to a tactic is supposed to end by '}' "
filterHeuristic False (c:t)   = (stringToGoalRanking False [c]):(filterHeuristic False t)
filterHeuristic True  (c:t)   = (stringToGoalRankingDiff False [c]):(filterHeuristic True t)
filterHeuristic   _   ("")    = []

-- | The name/explanation of a 'GoalRanking'.
goalRankingName :: GoalRanking ProofContext -> String
goalRankingName ranking =
    "Goals sorted according to " ++ case ranking of
        GoalNrRanking                 -> "their order of creation"
        OracleRanking _ oracle        -> "an oracle for ranking, located at " ++ printOracle oracle
        OracleSmartRanking _ oracle   -> "an oracle for ranking based on 'smart' heuristic, located at " ++ printOracle oracle
        UsefulGoalNrRanking           -> "their usefulness and order of creation"
        SapicRanking                  -> "heuristics adapted for processes"
        SapicPKCS11Ranking            -> "heuristics adapted to a specific model of PKCS#11 expressed using SAPIC. deprecated."
        SmartRanking useLoopBreakers  -> "the 'smart' heuristic" ++ loopStatus useLoopBreakers
        SmartDiffRanking              -> "the 'smart' heuristic (for diff proofs)"
        InjRanking useLoopBreakers    -> "heuristics adapted to stateful injective protocols" ++ loopStatus useLoopBreakers
        InternalTacticRanking _ tactic -> "the tactic written in the theory file: "++ _name tactic
   where
     loopStatus b = " (loop breakers " ++ (if b then "allowed" else "delayed") ++ ")"
     printOracle o@(Oracle workDir relPath) =
      if isNothing relPath
        then fromMaybe "" workDir </> "theory_filename.oracle"
        else oraclePath o

prettyGoalRankings :: [GoalRanking ProofContext] -> String
prettyGoalRankings rs = unwords (map prettyGoalRanking rs)

prettyGoalRanking :: GoalRanking ProofContext -> String
prettyGoalRanking ranking = case ranking of
    OracleRanking _ oracle          -> findIdentifier ranking ++ " \"" ++ fromMaybe "" (oracleRelPath oracle) ++ "\""
    OracleSmartRanking _ oracle     -> findIdentifier ranking ++ " \"" ++ fromMaybe "" (oracleRelPath oracle) ++ "\""
    InternalTacticRanking _ tactic  -> '{':_name tactic++"}"
    _                         -> findIdentifier ranking
  where
    findIdentifier r = case find (compareRankings r . snd) combinedIdentifiers of
        Just (k,_) -> k
        Nothing    -> error " does not have a defined identifier"

    -- Note because find works left first this will look at non-diff identifiers first. Thus,
    -- this assumes the diff rankings don't use a different character for the same proof method ranking.
    combinedIdentifiers = M.toList goalRankingIdentifiers ++ M.toList goalRankingIdentifiersDiff

    compareRankings (OracleRanking _ _) (OracleRanking _ _) = True
    compareRankings (OracleSmartRanking _ _) (OracleSmartRanking _ _) = True
    compareRankings (InternalTacticRanking _ _) (InternalTacticRanking _ _) = True
    compareRankings r1 r2 = r1 == r2


------------------------------------------------------------------------------
-- Proof Context
------------------------------------------------------------------------------

-- | A big-step source. (Formerly known as case distinction.)
data Source = Source
     { _cdGoal     :: Goal   -- start goal of source
       -- disjunction of named sequents with premise being solved; each name
       -- being the path of proof steps required to arrive at these cases
     , _cdCases    :: Disj ([String], System)
     }
     deriving( Eq, Ord, Show, Generic, NFData, Binary )

data InductionHint = UseInduction | AvoidInduction
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A proof context contains the globally fresh facts, classified rewrite
-- rules and the corresponding precomputed premise source theorems.
data ProofContext = ProofContext
       { _pcSignature          :: SignatureWithMaude
       , _pcRules              :: ClassifiedRules
       , _pcInjectiveFactInsts :: S.Set (FactTag, [[MonotonicBehaviour]])
       , _pcSourceKind         :: SourceKind
       , _pcSources            :: [Source]
       , _pcUseInduction       :: InductionHint
       , _pcHeuristic          :: Maybe (Heuristic ProofContext)
       , _pcTactic             :: Maybe [Tactic ProofContext]
       , _pcTraceQuantifier    :: SystemTraceQuantifier
       , _pcLemmaName          :: String
       , _pcHiddenLemmas       :: [String]
       , _pcVerbose            :: Bool -- true if we want to show the achieved goal and formula
       , _pcDiffContext        :: Bool -- true if diff proof
       , _pcTrueSubterm        :: Bool -- true if in all rules the RHS is a subterm of the LHS
       , _pcConstantRHS        :: Bool -- true if there are rules with a constant RHS
       , _pcIsSapic            :: Bool -- true if the model was originally a sapic process
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A diff proof context contains the two proof contexts for either side
-- and all rules.
data DiffProofContext = DiffProofContext
       {
         _dpcPCLeft               :: ProofContext
       , _dpcPCRight              :: ProofContext
       , _dpcProtoRules           :: [ProtoRuleE]
       , _dpcConstrRules          :: [RuleAC]
       , _dpcDestrRules           :: [RuleAC]
       , _dpcRestrictions         :: [(Side, [LNGuarded])]
       , _dpcReuseLemmas          :: [(Side, LNGuarded)]
       , _dpcPreservedActions     :: S.Set FactTag
       }
       deriving( Eq, Ord, Show )


$(mkLabels [''ProofContext, ''DiffProofContext, ''Source])


-- | The 'MaudeHandle' of a proof-context.
pcMaudeHandle :: ProofContext :-> MaudeHandle
pcMaudeHandle = sigmMaudeHandle . pcSignature

-- | Returns the LHS or RHS proof-context of a diff proof context.
eitherProofContext :: DiffProofContext -> Side -> ProofContext
eitherProofContext ctxt s = if s==LHS then L.get dpcPCLeft ctxt else L.get dpcPCRight ctxt

-- Instances
------------

data DiffProofType = RuleEquivalence | None
    deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A system used in diff proofs.
data DiffSystem = DiffSystem
    { _dsProofType      :: Maybe DiffProofType              -- The diff proof technique used
    , _dsSide           :: Maybe Side                       -- The side for backward search, when doing rule equivalence
    , _dsProofContext   :: Maybe ProofContext               -- The proof context used
    , _dsSystem         :: Maybe System                     -- The constraint system used
    , _dsProtoRules     :: S.Set ProtoRuleE                 -- the rules of the protocol
    , _dsConstrRules    :: S.Set RuleAC                     -- the construction rules of the theory
    , _dsDestrRules     :: S.Set RuleAC                     -- the deconstruction rules of the theory
    , _dsCurrentRule    :: Maybe String                     -- the name of the rule under consideration
    }
    deriving( Eq, Ord, Generic, NFData, Binary )

$(mkLabels [''DiffSystem])

------------------------------------------------------------------------------
-- Constraint system construction
------------------------------------------------------------------------------

-- | The empty constraint system, which is logically equivalent to true.
emptySystem :: SourceKind -> Bool -> System
emptySystem d isdiff = System
    M.empty S.empty S.empty Nothing emptySubtermStore emptyEqStore
    S.empty S.empty S.empty
    M.empty 0 d isdiff

-- TODO: I do not like the second conjunct; this should be done cleaner
isInitialSystem :: System -> Bool
isInitialSystem sys = null (L.get sSolvedFormulas sys) && not (S.member bot (L.get sFormulas sys))
  where bot = GDisj (Disj [])

-- | The empty diff constraint system.
emptyDiffSystem :: DiffSystem
emptyDiffSystem = DiffSystem
    Nothing Nothing Nothing Nothing S.empty S.empty S.empty Nothing

-- | Returns the constraint system that has to be proven to show that given
-- formula holds in the context of the given theory.
formulaToSystem :: [LNGuarded]           -- ^ Restrictions to add
                -> SourceKind            -- ^ Source kind
                -> SystemTraceQuantifier -- ^ Trace quantifier
                -> Bool                  -- ^ In diff proofs, all action goals have to be resolved
                -> LNFormula
                -> System
formulaToSystem restrictions kind traceQuantifier isdiff fm =
      insertLemmas safetyRestrictions
    $ L.set sFormulas (S.singleton gf2)
    $ (emptySystem kind isdiff)
  where
    (safetyRestrictions, otherRestrictions) = partition isSafetyFormula restrictions
    gf0 = formulaToGuarded_ fm
    gf1 = case traceQuantifier of
      ExistsSomeTrace -> gf0
      ExistsNoTrace   -> gnot gf0
    -- Non-safety restrictions must be added to the formula, as they render the set
    -- of traces non-prefix-closed, which makes the use of induction unsound.
    gf2 = gconj $ gf1 : otherRestrictions

-- | Add a lemma / additional assumption to a constraint system.
insertLemma :: LNGuarded -> System -> System
insertLemma =
    go
  where
    go (GConj conj) = foldr (.) id $ map go $ getConj conj
    go fm           = L.modify sLemmas (S.insert fm)

-- | Add lemmas / additional assumptions to a constraint system.
insertLemmas :: [LNGuarded] -> System -> System
insertLemmas fms sys = foldl' (flip insertLemma) sys fms

------------------------------------------------------------------------------
-- Queries
------------------------------------------------------------------------------


-- Nodes
------------

-- | A list of all KD-conclusions in the 'System'.
allKDConcs :: System -> [(NodeId, RuleACInst, LNTerm)]
allKDConcs sys = do
    (i, ru)                         <- M.toList $ L.get sNodes sys
    (_, kFactView -> Just (DnK, m)) <- enumConcs ru
    return (i, ru, m)

-- | A list of all In-premises in the 'System'.
allInPrems :: System -> [(NodeId, PremIdx, LNTerm)]
allInPrems sys = do
    (i, ru)                   <- M.toList $ L.get sNodes sys
    (j, inFactView -> Just m) <- enumPrems ru
    return (i, j, m)

-- | A list of all In- and Protocol premises in the 'System'.
allPrems :: System -> [(NodeId, PremIdx, Int, LNTerm)]
allPrems sys = do
    (i, ru)                           <- M.toList $ L.get sNodes sys
    (j, protoOrInFactView -> Just m') <- enumPrems ru
    (k, m)                            <- zip [0..] m'
    return (i, j, k, m)


-- | @nodeRule v@ accesses the rule label of node @v@ under the assumption that
-- it is present in the sequent.
nodeRule :: NodeId -> System -> RuleACInst
nodeRule v se =
    fromMaybe errMsg $ M.lookup v $ L.get sNodes se
  where
    errMsg = error $
        "nodeRule: node '" ++ show v ++ "' does not exist in sequent\n" ++
        render (nest 2 $ prettySystem se)

-- | @nodeRuleSafe v@ accesses the rule label of node @v@.
nodeRuleSafe :: NodeId -> System -> Maybe RuleACInst
nodeRuleSafe v se = M.lookup v $ L.get sNodes se

-- | @nodePremFact prem se@ computes the fact associated to premise @prem@ in
-- sequent @se@ under the assumption that premise @prem@ is a a premise in
-- @se@.
nodePremFact :: NodePrem -> System -> LNFact
nodePremFact (v, i) se = L.get (rPrem i) $ nodeRule v se

-- | @nodePremNode prem@ is the node that this premise is referring to.
nodePremNode :: NodePrem -> NodeId
nodePremNode = fst

-- | All facts associated to this node premise.
resolveNodePremFact :: NodePrem -> System -> Maybe LNFact
resolveNodePremFact (v, i) se = lookupPrem i =<< M.lookup v (L.get sNodes se)

-- | The fact associated with this node conclusion, if there is one.
resolveNodeConcFact :: NodeConc -> System -> Maybe LNFact
resolveNodeConcFact (v, i) se = lookupConc i =<< M.lookup v (L.get sNodes se)

-- | @nodeConcFact (NodeConc (v, i))@ accesses the @i@-th conclusion of the
-- rule associated with node @v@ under the assumption that @v@ is labeled with
-- a rule that has an @i@-th conclusion.
nodeConcFact :: NodeConc -> System -> LNFact
nodeConcFact (v, i) = L.get (rConc i) . nodeRule v

-- | 'nodeConcNode' @c@ compute the node-id of the node conclusion @c@.
nodeConcNode :: NodeConc -> NodeId
nodeConcNode = fst

-- | Returns a node premise fact from a node map
nodePremFactMap :: NodePrem -> M.Map NodeId RuleACInst -> LNFact
nodePremFactMap (v, i) nodes = L.get (rPrem i) $ nodeRuleMap v nodes

-- | Returns a node conclusion fact from a node map
nodeConcFactMap :: NodeConc -> M.Map NodeId RuleACInst -> LNFact
nodeConcFactMap (v, i) nodes = L.get (rConc i) $ nodeRuleMap v nodes

-- | Returns a rule instance from a node map
nodeRuleMap :: NodeId -> M.Map NodeId RuleACInst -> RuleACInst
nodeRuleMap v nodes =
    fromMaybe errMsg $ M.lookup v $ nodes
  where
    errMsg = error $
        "nodeRuleMap: node '" ++ show v ++ "' does not exist in sequent\n"

-- | Given a system and a goal, find the source rule for the goal, if one
-- exists. Only works for premise and action goals.
goalRule :: System -> Goal -> Maybe RuleACInst
goalRule sys goal = case goalNodeId goal of
    Just i  -> nodeRuleSafe i sys
    Nothing -> Nothing
  where
    goalNodeId :: Goal -> Maybe NodeId
    goalNodeId (PremiseG (i, _) _) = Just i
    goalNodeId (ActionG  i _)      = Just i
    goalNodeId _                   = Nothing


-- | 'getMaudeHandle' @ctxt@ @side@ returns the maude handle on side @side@ in diff proof context @ctxt@.
getMaudeHandle :: DiffProofContext -> Side -> MaudeHandle
getMaudeHandle ctxt side = if side == RHS then L.get (pcMaudeHandle . dpcPCRight) ctxt else L.get (pcMaudeHandle . dpcPCLeft) ctxt

-- | 'getAllRulesOnOtherSide' @ctxt@ @side@ returns all rules in diff proof context @ctxt@ on the opposite side of side @side@.
getAllRulesOnOtherSide :: DiffProofContext -> Side -> [RuleAC]
getAllRulesOnOtherSide ctxt side = getAllRulesOnSide ctxt $ if side == LHS then RHS else LHS

-- | 'getAllRulesOnSide' @ctxt@ @side@ returns all rules in diff proof context @ctxt@ on the side @side@.
getAllRulesOnSide :: DiffProofContext -> Side -> [RuleAC]
getAllRulesOnSide ctxt side = joinAllRules $ L.get pcRules $ if side == RHS then L.get dpcPCRight ctxt else L.get dpcPCLeft ctxt

-- | Certify action predicates whose occurrences and arguments are identical
-- in every mirror. This checks compiled rule families, including explicit
-- sides and variants, rather than just the syntax of the original diff rule.
--
-- A protocol fact is preserved if every corresponding pair of producers
-- preserves its conclusion at the same position, assuming preserved premises.
-- Eliminate candidates until this condition is closed. Induction over a
-- finite dependency graph then establishes the remaining candidates: fresh
-- nodes are copied by mirroring, and each other node receives equal certified
-- premises from earlier nodes. This also handles recursive state rules.
--
-- Only bare variables in equal premise argument positions are identified.
-- We never invert a constructor (which need not be injective modulo E).
-- New public variables are identified by the vector already fixed by
-- getSubstitutionsFixingNewVars. Other inputs, notably attacker knowledge,
-- remain unknown. Syntactically equal expressions in these identified values
-- remain equal under all rule-variant substitutions and modulo E.
diffPreservedActionTags :: [RuleAC] -> [RuleAC] -> S.Set FactTag
diffPreservedActionTags leftRules rightRules = S.filter preservedAction actionCandidates
  where
    families = M.fromListWith (++) . map (\r -> (ruleName r, [r])) . filter isProtocolRule
    leftFamilies = families leftRules
    rightFamilies = families rightRules
    pairs = [(l,r) | (name, ls) <- M.toList leftFamilies,
                     l <- ls, r <- M.findWithDefault [] name rightFamilies]
    protocolTag (ProtoFact _ _ _) = True
    protocolTag _ = False
    candidates field = S.fromList
      [factTag f | r <- leftRules ++ rightRules, f <- L.get field r, protocolTag (factTag f)]
    intruderTags field = S.fromList
      [factTag f | r <- leftRules ++ rightRules, not (isProtocolRule r), f <- L.get field r]
    -- An unmatched producer cannot certify its tags. Removing its state tags
    -- also removes dependent certificates through the fixed point, without
    -- disabling certificates for unrelated matched families.
    unmatched = concat (M.elems (leftFamilies `M.difference` rightFamilies)) ++
                concat (M.elems (rightFamilies `M.difference` leftFamilies))
    unmatchedTags field = S.fromList [factTag f | r <- unmatched, f <- L.get field r]
    eligible field = candidates field `S.difference`
      (intruderTags field `S.union` unmatchedTags field)
    factCandidates = eligible rConcs
    actionCandidates = eligible rActs
    preservedFacts = fixedPoint factCandidates
    fixedPoint known =
      let next = S.filter (\tag -> all (preservesConclusion known tag) pairs) known
      in if next == known then known else fixedPoint next

    -- Each binding has a shared positional key. Repeated variables can make
    -- this approximation stricter, but cannot identify unequal inputs.
    bindings :: S.Set FactTag -> RuleAC -> RuleAC -> [((Int, Int, Int), LVar, LVar)]
    bindings known l r =
      [((0, i, j), x, y)
      | (i, (lf, rf)) <- zip [0..] (zip (L.get rPrems l) (L.get rPrems r))
      , factTag lf == factTag rf
      , factTag lf == FreshFact || factTag lf `S.member` known
      , (j, (lt, rt)) <- zip [0..] (zip (factTerms lf) (factTerms rf))
      , Just x <- [getVar lt], Just y <- [getVar rt]
      , lvarSort x == lvarSort y] ++
      [((1, i, 0), x, y)
      | (i, (lt, rt)) <- zip [0..] (zip (L.get rNewVars l) (L.get rNewVars r))
      , Just x <- [getVar lt], Just y <- [getVar rt]
      , lvarSort x == LSortPub, lvarSort y == LSortPub]

    canonical known l r =
      let bs = bindings known l r
          keys = M.fromList $ zip (S.toList $ S.fromList [key | (key, _, _) <- bs]) [0..]
          variable key = varTerm $ LVar "preserved" LSortMsg (keys M.! key)
          leftSubst = M.fromList [(x, variable key) | (key, x, _) <- bs]
          rightSubst = M.fromList [(y, variable key) | (key, _, y) <- bs]
          normalize :: M.Map LVar LNTerm -> [LNFact] -> Maybe [LNFact]
          normalize subst facts
            | all (`M.member` subst) (frees facts) = Just $ apply (Subst subst) facts
            | otherwise = Nothing
      in (normalize leftSubst, normalize rightSubst)

    preservesConclusion known tag (l,r) =
      let (normL, normR) = canonical known l r
          selected ru = [(i,f) | (i,f) <- zip [0 :: Int ..] (L.get rConcs ru), factTag f == tag]
          ls = selected l
          rs = selected r
      in map fst ls == map fst rs && case (normL (map snd ls), normR (map snd rs)) of
           (Just lfs, Just rfs) -> lfs == rfs
           _ -> False

    preservedAction tag = all (\(l,r) ->
      let (normL, normR) = canonical preservedFacts l r
          selected = filter ((== tag) . factTag) . L.get rActs
      in case (normL (selected l), normR (selected r)) of
           (Just ls, Just rs) -> S.fromList ls == S.fromList rs
           _ -> False) pairs

-- | How a restriction conjunct can hold on the mirrored trace. Local
-- conjuncts must be checked on each dependency graph; preserved conjuncts
-- follow from the original trace and may need witnesses outside that graph.
data DiffRestrictionKind = DiffLocal | DiffPreserved | DiffUnsupported
    deriving (Eq, Show)

classifyDiffRestriction :: DiffProofContext -> Side -> LNGuarded -> DiffRestrictionKind
classifyDiffRestriction ctxt side f
  | isDiffLocalRestriction f = DiffLocal
  | withoutNames f `elem` map withoutNames other
  , all (`S.member` L.get dpcPreservedActions ctxt) (actionFactTags f) =
      DiffPreserved
  | otherwise = DiffUnsupported
  where
    other = concat [guardedConjuncts formula
                   | (s, fs) <- L.get dpcRestrictions ctxt, s == opposite side
                   , formula <- fs]
    -- Bound-variable names are printing hints. Sorts and bound indices still
    -- determine whether two restrictions have the same structure.
    withoutNames (GAto atom) = GAto atom
    withoutNames (GConj formulas) = GConj (fmap withoutNames formulas)
    withoutNames (GDisj formulas) = GDisj (fmap withoutNames formulas)
    withoutNames (GGuarded q binders atoms body) =
      GGuarded q (map snd binders) atoms (withoutNames body)

-- | The conjuncts of a side's restrictions that rule equivalence cannot
-- establish on the mirrored trace.
unsupportedDiffRestrictions :: DiffProofContext -> Side -> [LNGuarded]
unsupportedDiffRestrictions ctxt side =
    [ f | (s, fs) <- L.get dpcRestrictions ctxt, s == side
        , f <- concatMap guardedConjuncts fs
        , classifyDiffRestriction ctxt side f == DiffUnsupported ]


-- | 'protocolRuleWithName' @rules@ @name@ returns all rules with protocol rule name @name@ in rules @rules@.
protocolRuleWithName :: [RuleAC] -> ProtoRuleName -> [RuleAC]
protocolRuleWithName rules name = filter (\(Rule x _ _ _ _) -> case x of
                                             ProtoInfo p -> (L.get pracName p) == name
                                             IntrInfo  _ -> False) rules

-- | 'intruderRuleWithName' @rules@ @name@ returns all rules with intruder rule name @name@ in rules @rules@.
--   This respects the number of remaining consecutive rule applications.
intruderRuleWithName :: [RuleAC] -> IntrRuleACInfo -> [RuleAC]
intruderRuleWithName rules name = filter (\(Rule x _ _ _ _) -> case x of
                                             IntrInfo  (DestrRule i _ _ _ _) -> case name of
                                                                                 (DestrRule j _ _ _ _) -> i == j
                                                                                 _                   -> False
                                             IntrInfo  i -> i == name
                                             ProtoInfo _ -> False) rules

-- | 'getOppositeRules' @ctxt@ @side@ @rule@ returns all rules with the same name as @rule@ in diff proof context @ctxt@ on the opposite side of side @side@.
getOppositeRules :: DiffProofContext -> Side -> RuleACInst -> [RuleAC]
getOppositeRules ctxt side (Rule rule prem _ _ _) = case rule of
    ProtoInfo p -> case protocolRuleWithName (getAllRulesOnOtherSide ctxt side) (L.get praciName p) of
        [] -> error $ "No other rule found for protocol rule " ++ show (L.get praciName p) ++ show (getAllRulesOnOtherSide ctxt side)
        x  -> x
    IntrInfo  i -> case i of
        (ConstrRule _ x) | x == AC Mult     -> [(multRuleInstance (length prem))]
        (ConstrRule _ x) | x == AC Union    -> [(unionRuleInstance (length prem))]
        (ConstrRule n x) | x == AC Xor      -> (xorRuleInstance (length prem)):
                                                            (concat $ map (destrRuleToConstrRule (AC Xor) (length prem)) (intruderRuleWithName (getAllRulesOnOtherSide ctxt side) (DestrRule n 0 False False [x])))
        (DestrRule n l s c (x:_)) | x == AC Xor -> (constrRuleToDestrRule (xorRuleInstance (length prem)) l s c)++(concat $ map destrRuleToDestrRule (intruderRuleWithName (getAllRulesOnOtherSide ctxt side) i))
        _                                         -> case intruderRuleWithName (getAllRulesOnOtherSide ctxt side) i of
                                                            [] -> error $ "No other rule found for intruder rule " ++ show i ++ show (getAllRulesOnOtherSide ctxt side)
                                                            x  -> x

-- | 'getOriginalRule' @ctxt@ @side@ @rule@ returns the original rule of protocol rule @rule@ in diff proof context @ctxt@ on side @side@.
getOriginalRule :: DiffProofContext -> Side -> RuleACInst -> RuleAC
getOriginalRule ctxt side (Rule rule _ _ _ _) = case rule of
               ProtoInfo p -> case protocolRuleWithName (getAllRulesOnSide ctxt side) (L.get praciName p) of
                                   [x]  -> x
                                   _    -> error $ "getOriginalRule: No or more than one other rule found for protocol rule " ++ show (L.get praciName p) ++ show (getAllRulesOnSide ctxt side)
               IntrInfo  _ -> error $ "getOriginalRule: This should be a protocol rule: " ++ show rule


-- | Returns true if the graph is correct, i.e. complete and conclusions and premises match
-- | Note that this does not check if all goals are solved, nor if any restrictions are violated!
-- FIXME: consider implicit deduction
isCorrectDG :: System -> Bool
isCorrectDG sys = M.foldrWithKey (\k x y -> y && (checkRuleInstance sys k x)) True (L.get sNodes sys)
  where
    checkRuleInstance :: System -> NodeId -> RuleACInst -> Bool
    checkRuleInstance sys' idx rule = foldr (\x y -> y && (checkPrems sys' idx x)) True (enumPrems rule)

    checkPrems :: System -> NodeId -> (PremIdx, LNFact) -> Bool
    checkPrems sys' idx (premidx, fact) = case S.toList (S.filter (\(Edge _ y) -> y == (idx, premidx)) (L.get sEdges sys')) of
                                               [(Edge x _)] -> fact == nodeConcFact x sys'
                                               _            -> False

-- | A partial valuation for atoms. The return value of this function is
-- interpreted as follows.
--
-- @partialAtomValuation ctxt sys ato == Just True@ if for every valuation
-- @theta@ satisfying the graph constraints and all atoms in the constraint
-- system @sys@, the atom @ato@ is also satisfied by @theta@.
--
-- The interpretation for @Just False@ is analogous. @Nothing@ is used to
-- represent *unknown*.
--
safePartialAtomValuation :: ProofContext -> System -> LNAtom -> Maybe Bool
safePartialAtomValuation ctxt sys =
    eval
  where
    runMaude   = (`runReader` L.get pcMaudeHandle ctxt)
    before     = alwaysBefore sys
    lessRel    = rawLessRel sys
    nodesAfter = \i -> filter (i /=) $ S.toList $ D.reachableSet [i] lessRel
    reducible  = reducibleFunSyms $ mhMaudeSig $ L.get pcMaudeHandle ctxt
    sst        = L.get sSubtermStore sys

    -- | 'True' iff there in every solution to the system the two node-ids are
    -- instantiated to a different index *in* the trace.
    nonUnifiableNodes :: NodeId -> NodeId -> Bool
    nonUnifiableNodes i j = maybe False (not . runMaude) $
        (unifiableRuleACInsts) <$> M.lookup i (L.get sNodes sys)
                               <*> M.lookup j (L.get sNodes sys)

    -- | Try to evaluate the truth value of this atom in all models of the
    -- constraint system 'sys'.
    eval ato = case ato of
          Action (ltermNodeId' -> i) fa
            | otherwise ->
                case M.lookup i (L.get sNodes sys) of
                  Just ru
                    | any (fa ==) (L.get rActs ru)                                -> Just True
                    | all (not . runMaude . unifiableLNFacts fa) (L.get rActs ru) -> Just False
                  _                                                               -> Nothing

          Less (ltermNodeId' -> i) (ltermNodeId' -> j)
            | i == j || j `before` i             -> Just False
            | i `before` j                       -> Just True
            | isLast sys i && isInTrace sys j    -> Just False
            | isLast sys j && isInTrace sys i &&
              nonUnifiableNodes i j              -> Just True
            | otherwise                          -> Nothing

          EqE x y
            | x == y                                -> Just True
            | not (runMaude (unifiableLNTerms x y)) -> Just False
            | otherwise                             ->
                case (,) <$> ltermNodeId x <*> ltermNodeId y of
                  Just (i, j)
                    | i `before` j || j `before` i  -> Just False
                    | nonUnifiableNodes i j         -> Just False
                  _                                 -> Nothing

          Subterm small big                      -> isTrueFalse reducible (Just sst) (small, big)

          Last (ltermNodeId' -> i)
            | isLast sys i                       -> Just True
            | any (isInTrace sys) (nodesAfter i) -> Just False
            | otherwise ->
                case L.get sLastAtom sys of
                  Just j | nonUnifiableNodes i j -> Just False
                  _                              -> Nothing

          Syntactic _                            -> Nothing

-- | @impliedFormulas se imp@ returns the list of guarded formulas that are
-- implied by @se@.
impliedFormulas :: MaudeHandle -> System -> LNGuarded -> [LNGuarded]
impliedFormulas hnd sys gf0 = res
  where
    res = case (openGuarded gf `evalFresh` avoid gf) of
      Just (All, _vs, antecedent, succedent) -> do
        let (actionsEqs, otherAtoms) = first sortGAtoms . partitionEithers $
                                        map prepare antecedent
            succedent'               = gall [] otherAtoms succedent
        subst <- candidateSubsts emptySubst actionsEqs
        return $ unskolemizeLNGuarded $ applySkGuarded subst succedent'
      -- Non-universal safety assumptions still need ordinary formula
      -- reduction (including F, ground atoms, and Boolean combinations).
      -- Do not force existential reusable lemmas into every proof state.
      _ -> [gf0 | isSafetyFormula gf0]
    gf = skolemizeGuarded gf0

    prepare (Action i fa) = Left  (GAction i fa)
    prepare (EqE s t)     = Left  (GEqE s t)
    prepare ato           = Right (fmap (fmapTerm (fmap Free)) ato)

    sysActions = do (i, fa) <- allActions sys
                    return (skolemizeTerm (varTerm i), skolemizeFact fa)

    candidateSubsts subst []               = return subst
    candidateSubsts subst ((GAction a fa):as) = do
        sysAct <- sysActions
        subst' <- (`runReader` hnd) $ matchAction sysAct (applySkAction subst (a, fa))
        candidateSubsts (compose subst' subst) as
    candidateSubsts subst ((GEqE s' t'):as)   = do
        let s = applySkTerm subst s'
            t = applySkTerm subst t'
            (term, pat) | null $ frees s = (s,t)
                        | null $ frees t = (t,s)
                        | otherwise      = error $ "impliedFormulas: impossible, "
                                           ++ "equality not guarded as checked"
                                           ++"by 'Guarded.formulaToGuarded'."
        subst' <- (`runReader` hnd) $ matchTerm term pat
        candidateSubsts (compose subst' subst) as

-- | @impliedFormulasAndSystems se imp@ returns the list of guarded formulas that are
-- *potentially* implied by @se@, together with the updated system. The Boolean
-- records whether the instance leaves the system's variables unconstrained
-- (up to renaming). A violation after a proper specialization does not imply
-- that every instance of the original system violates the restriction.
impliedFormulasAndSystems :: MaudeHandle -> RestrictionInstance
                          -> [RestrictionInstance]
impliedFormulasAndSystems hnd instance0@(RestrictionInstance gf sys frame _) = res
  where
    companions = failureFrameFrees frame
    res = case (openGuarded gf `evalFresh` avoid (gf, companions, sys)) of
      Just (All, _vs, antecedent, succedent) -> map instantiate subst'
        where
          instantiate subst =
            let freeSubst = freshToFreeAvoiding subst
                              ((gf, subst), companions, sys)
            in specializeRestriction freeSubst
                 (isRenaming (restrictVFresh (frees sys) subst))
                 instance0 { restrictionFormula = succedent' }
          (actionsEqs, otherAtoms) = first sortGAtoms . partitionEithers $ map prepare antecedent
          succedent'               = gall [] otherAtoms succedent
          subst' = concat $ map (\(x, y) ->
            if null ((`runReader` hnd) (unifyLNTerm x))
               then []
               else (`runReader` hnd) (unifyLNTerm y)) (equalities actionsEqs)
      _ -> []

    prepare (Action i fa) = Left  (GAction i fa)
    prepare (EqE s t)     = Left  (GEqE s t)
    prepare ato           = Right (fmap (fmapTerm (fmap Free)) ato)

    sysActions = allActions sys

    equalities :: [GAtom (Term (Lit Name LVar))] -> [([Equal LNTerm], [Equal LNTerm])]
    equalities []                  = [([], [])]
    equalities ((GAction a fa):as) = go sysActions
      where
        go :: [(NodeId, LNFact)] -> [([Equal LNTerm], [Equal LNTerm])]
        go []                                                  = []
        go ((nid, sysAct):acts) | factTag sysAct == factTag fa =
            (map (\(x, y) -> ((((Equal (variableToConst nid) a):(zipWith Equal sysTerms formulaTerms)) ++ x),
                              (((Equal (varTerm nid) a):(zipWith Equal sysTerms formulaTerms)) ++ y))) $ equalities as)
                                  ++ (go acts)
            where
                sysTerms = map freshToConst (factTerms sysAct)
                formulaTerms = factTerms fa

        go ((_  , _     ):acts) | otherwise                    = go acts
    equalities ((GEqE s t):as)     = map (\(x, y) -> ((Equal s t):x, (Equal s t):y)) $ equalities as

-- | Remove safety restrictions whose action guards cannot match the system.
-- Action-free and non-safety restrictions cannot be discarded this way.
filterRestrictions :: ProofContext -> System -> [LNGuarded] -> [LNGuarded]
filterRestrictions ctxt sys formulas = filter relevant formulas
  where
    runMaude   = (`runReader` L.get pcMaudeHandle ctxt)

    relevant fm = not (isSafetyFormula fm)
               || hasActionFreeCase fm
               || unifiableNodes fm

    -- Boolean combinations can contain action-free obligations even when
    -- guardFactTags reports an action elsewhere in the formula. Such a case
    -- must retain the complete restriction. The body of an action-guarded
    -- universal need not count: if its guard cannot match, that implication
    -- is vacuously true; if it can match, unifiableNodes retains it.
    hasActionFreeCase :: LNGuarded -> Bool
    hasActionFreeCase (GAto (Action _ _)) = False
    hasActionFreeCase (GAto _)            = True
    hasActionFreeCase (GDisj fms)         =
      null (getDisj fms) || any hasActionFreeCase (getDisj fms)
    hasActionFreeCase (GConj fms)         = any hasActionFreeCase $ getConj fms
    hasActionFreeCase (GGuarded _ _ atos _) =
      not (any isActionAtom atos)

    unifiableNodes :: LNGuarded -> Bool
    unifiableNodes fm = case fm of
         GAto ato  -> unifiableAtoms [bvarToLVar ato]
         GDisj fms -> any unifiableNodes $ getDisj fms
         GConj fms -> any unifiableNodes $ getConj fms
         gg@(GGuarded _ _ _ _) ->
           case evalFreshAvoiding (openGuarded gg) (L.get sNodes sys) of
             Nothing -> error "Bug in filterRestrictions, please report."
             Just (_, _, atos, gf) -> unifiableNodes gf || unifiableAtoms atos

    unifiableAtoms :: [Atom (VTerm Name LVar)] -> Bool
    unifiableAtoms []                   = False
    unifiableAtoms ((Action _ fact):fs) = unifiableFact fact || unifiableAtoms fs
    unifiableAtoms (_:fs)               = unifiableAtoms fs

    unifiableFact :: LNFact -> Bool
    unifiableFact fact = mapper fact

    mapper fact = any (runMaude . unifiableLNFacts fact) $ concat $ map (L.get rActs . snd) $ M.toList (L.get sNodes sys)

-- | Data type for a trivalent logic used to return whether restrictions on mirrors are valid, invalid or unknown
data Trivalent = TTrue | TFalse | TUnknown deriving (Show, Eq)

-- | Computes the mirror dependency graph and evaluates whether the restrictions hold.
-- Returns Just True and a list of mirrors if all hold, Just False and a list of attacks (if found) if at least one does not hold and Nothing otherwise.
getMirrorDGandEvaluateRestrictions :: DiffProofContext -> DiffSystem -> Bool -> (Trivalent, [System])
getMirrorDGandEvaluateRestrictions dctxt dsys isSolved =
    case (L.get dsSide dsys, L.get dsSystem dsys) of
          (Nothing,   _       ) -> (TFalse, [])
          (Just _ , Nothing   ) -> (TFalse, [])
          (Just side, Just sys) -> evaluateRestrictions dctxt dsys (getMirrorDG dctxt side sys) isSolved

-- | The answer a caller of 'evaluateRestrictionsFor' needs.
data MirrorGoal
    = MirrorCoverage
      -- ^ Only whether the result is 'TTrue'. Evaluation stops at the first
      -- failure case that is not covered, and any other result is 'TUnknown'.
    | MirrorAttack
      -- ^ Only whether the result is 'TFalse'. Failure cases that cannot
      -- certify an attack are not refined further.
    | MirrorFull
      -- ^ The complete trivalent answer.
    deriving (Eq, Show)

-- | Solver admission of a candidate original. Simplification may reject it,
-- leave obligations unresolved, or produce one or more completed branches.
data MirrorAdmission = MirrorRejected | MirrorUnresolved | MirrorAdmitted System

-- | Evaluates whether the restrictions hold. Assumes that the mirrors have been correctly computed.
-- Returns TTrue when the alternatives cover all admitted original assignments,
-- TFalse when they share a failing assignment, and TUnknown otherwise.
evaluateRestrictions :: DiffProofContext -> DiffSystem -> [System] -> Bool -> (Trivalent, [System])
evaluateRestrictions = evaluateRestrictionsFor MirrorFull (\sys -> [MirrorAdmitted sys])

-- | 'evaluateRestrictions' for the answer a caller needs. 'MirrorCoverage'
-- returns 'TTrue' exactly when the full evaluation does. For solved originals,
-- 'MirrorAttack' likewise preserves 'TFalse' answers, given the same
-- admission callback. For unsolved originals it checks only the generic
-- completed instance: conditional failures requiring further specialization
-- remain unknown. Joint failure intersection is exponential in the number of
-- mirrors in general; these goals avoid work that cannot establish the
-- requested result.
--
-- The callback simplifies a candidate under the caller's complete solver
-- context, including newly activated reusable assumptions. Its branches must
-- cover the candidate; an empty list rejects it. Only admitted completed
-- branches can certify an attack, and unresolved branches prevent coverage.
evaluateRestrictionsFor :: MirrorGoal -> (System -> [MirrorAdmission]) -> DiffProofContext -> DiffSystem -> [System] -> Bool
                        -> (Trivalent, [System])
evaluateRestrictionsFor goal certify dctxt dsys mirrors isSolved =
    case (L.get dsSide dsys, L.get dsSystem dsys) of
        (Nothing,   _       ) -> (TFalse, [])
        (Just _ , Nothing   ) -> (TFalse, [])
        (Just side, Just sys)
          | not (null successful) -> (TTrue, concatMap snd successful)
          | goal /= MirrorCoverage, Just witnesses <- genericAttack -> (TFalse, witnesses)
          -- Only the generic instance completes an unsolved original.
          | goal == MirrorAttack && not isSolved -> (TUnknown, [])
          | otherwise -> case jointFailures sys independentMirrors [] of
              (TTrue, _) -> (TTrue, mirrors)
              (_, witnesses) | goal == MirrorCoverage -> (TUnknown, witnesses)
              result     -> result
            where
                oppositeCtxt = eitherProofContext dctxt (opposite side)
                successful = filter ((== TTrue) . fst) $ map evaluateMirror distinctMirrors
                distinctMirrors = distinctMirrorsByNodes mirrors
                evaluateMirror mirror =
                    doRestrictionsHold oppositeCtxt mirror
                      (relevantRestrictions mirror) isSolved
                -- A solved original describes a trace for its instance with
                -- every variable replaced by a distinct fresh constant. So
                -- does an original whose only open goals are attacker inputs
                -- K(x) for distinct message variables, once each x is a fresh
                -- public name that the pub rule provides. If every mirror of
                -- that complete instance fails outright, the instance is an
                -- attack. This certifies failures that are disequalities
                -- between original variables, which no common failing
                -- substitution below can express. Natural-number variables and
                -- subterm constraints are left to the joint search.
                genericAttack
                  | not (isSolved || openGoalsAreAttackerInputs sys) = Nothing
                  | any ((== LSortNat) . lvarSort) termVars = Nothing
                  | not (null (L.get posSubterms store) && null (L.get negSubterms store)) = Nothing
                  | otherwise = case certifyCandidate True generic Nothing of
                      (TFalse, witnesses) -> Just witnesses
                      _                   -> Nothing
                  where
                    store = L.get sSubtermStore sys
                    termVars = filter ((/= LSortNode) . lvarSort) (frees sys)
                    genericName v = constTerm $ Name
                      (if lvarSort v == LSortFresh then FreshName else PubName)
                      (NameId ("genericInstance_" ++ show (lvarSort v) ++ "_"
                               ++ show (lvarIdx v) ++ "_" ++ lvarName v))
                    genericSubst = Subst $ M.fromList [(v, genericName v) | v <- termVars]
                    generic = completeAttackerInputs genericSubst $
                      applySystemSubst genericSubst sys

                -- Only variables from the original graph are shared between
                -- alternatives. Equal names for mirror-local variables must
                -- not create dependencies between their failure conditions.
                independentMirrors = evalFreshAvoiding
                  (mapM (renameIgnoring (frees sys)) distinctMirrors) (sys, distinctMirrors)

                -- Intersect the failure cases by applying every specialization
                -- to the original graph, remaining mirrors, and earlier failed
                -- mirrors together. An empty intersection establishes coverage;
                -- a common failure must also satisfy the original restrictions.
                -- This also handles an initially empty mirror family: no
                -- alternative is an attack only for an admitted original.
                jointFailures original [] failed = certifyCandidate isSolved original (Just failed)
                jointFailures original (candidate:remaining) failed =
                  combineFailures $ map checkInstance instances
                  where
                    mirror = normDG oppositeCtxt candidate
                    frame = beginAlternative original mirror remaining failed
                    instances = restrictionInstances oppositeCtxt mirror
                      (relevantRestrictions mirror) isSolved (Just frame)

                    checkInstance (RestrictionInstance f _ _ _) | f == gtrue = (TTrue, [])
                    -- A branch below a conditional or local-constrained
                    -- failure is reported as TUnknown even if it fails
                    -- jointly (see below), so it cannot certify an attack.
                    checkInstance (RestrictionInstance f m (Just current) _)
                      | goal == MirrorAttack
                        && (f /= gfalse || not (localsUnconstrained current)) = (TUnknown, [m])
                    checkInstance (RestrictionInstance f m (Just current) _) =
                      case finishAlternative m current of
                        (o, rest, previous) -> case jointFailures o rest previous of
                          (TFalse, witnesses)
                            | f /= gfalse || not (localsUnconstrained current) ->
                                (TUnknown, witnesses)
                          result -> result
                    checkInstance _ = error "jointFailures: missing failure frame"

                -- Generic completions and joint specializations share admission
                -- policy. Rejected branches cover no original assignments;
                -- one admitted failing branch suffices for an attack.
                certifyCandidate completed original knownFailures
                  -- A specialization must still describe normal rule instances.
                  | not (normal original) = (TUnknown, failed)
                  | otherwise = combineFailures $ map checkAdmission (certify original)
                  where
                    failed = fromMaybe [] knownFailures
                    checkAdmission MirrorRejected = (TTrue, [])
                    checkAdmission MirrorUnresolved = (TUnknown, failed)
                    checkAdmission (MirrorAdmitted admitted)
                      | not (normal admitted) = (TUnknown, failed)
                      | otherwise = case fst $ doRestrictionsHold originalCtxt
                            (normDG originalCtxt admitted)
                            (originalRestrictions ++ S.toList (L.get sFormulas admitted)) True of
                          TFalse   -> (TTrue, [])
                          TUnknown -> (TUnknown, failed)
                          TTrue    -> recheckMirrors completed admitted knownFailures
                    normal = all ((`runReader` L.get pcMaudeHandle originalCtxt) . nfRule)
                             . M.elems . L.get sNodes

                recheckMirrors completed original knownFailures
                  | Just failed <- knownFailures
                  , eqModuloFreshnessNoAC original sys = (TFalse, failed)
                  | any ((== TTrue) . fst) rechecked = (TTrue, [])
                  | all ((== TFalse) . fst) rechecked = (TFalse, concatMap snd rechecked)
                  | otherwise = (TUnknown, refinedMirrors)
                  where
                    -- Fixing original variables can enable mirrors that did
                    -- not unify with the original symbolic graph. Before
                    -- reporting an attack, enumerate again and require their
                    -- failures without another independent specialization.
                    refinedMirrors = distinctMirrorsByNodes (getMirrorDG dctxt side original)
                    rechecked = [doRestrictionsHold oppositeCtxt m
                                   (relevantRestrictions m) completed
                                | m <- refinedMirrors]

                combineFailures results
                  -- Results are computed lazily: coverage fails at the first
                  -- failure case that is not covered.
                  | goal == MirrorCoverage = case dropWhile ((== TTrue) . fst) results of
                      []      -> (TTrue, [])
                      (r : _) -> (TUnknown, snd r)
                  | not (null attacks) = (TFalse, concatMap snd attacks)
                  | not (null unknown) = (TUnknown, concatMap snd unknown)
                  | otherwise          = (TTrue, [])
                  where
                    attacks = filter ((== TFalse) . fst) results
                    unknown = filter ((== TUnknown) . fst) results
                restrictions = restrictions' (opposite side) $ L.get dpcRestrictions dctxt
                originalCtxt = eitherProofContext dctxt side
                originalRestrictions = restrictions' side $ L.get dpcRestrictions dctxt
                relevantRestrictions mirror = filterRestrictions oppositeCtxt mirror restrictions

                restrictions' _  []               = []
                restrictions' s' ((s'', form):xs) = if s' == s'' then form ++ (restrictions' s' xs) else (restrictions' s' xs)


-- | Mirrors share the original constraints, but their rule instances differ.
-- Keep every distinct node map: restrictions inspect actions and also compare
-- complete rules to establish node inequality and last-node ordering.
distinctMirrorsByNodes :: [System] -> [System]
distinctMirrorsByNodes = go S.empty
  where
    go _ [] = []
    go seen (m:ms)
      | key `S.member` seen = go seen ms
      | otherwise           = m : go (S.insert key seen) ms
      where key = L.get sNodes m

-- | The unsolved goals of a system that are attacker inputs @K(x)@ for a
-- message or public variable @x@.
openAttackerInputs :: System -> [(NodeId, LVar)]
openAttackerInputs sys =
    [ (i, v) | (ActionG i (Fact KUFact _ [t]), status) <- M.toList (L.get sGoals sys)
             , not (L.get gsSolved status)
             , Just v <- [getVar t]
             , lvarSort v `elem` [LSortMsg, LSortPub] ]

-- | Whether every unsolved goal is an attacker input for a distinct variable
-- at distinct uninstantiated nodes, so that replacing each variable by a
-- fresh public name and deducing it with the pub rule completes the system.
openGoalsAreAttackerInputs :: System -> Bool
openGoalsAreAttackerInputs sys =
       not (null inputs)
    && length inputs == length [ () | (_, status) <- M.toList (L.get sGoals sys)
                                   , not (L.get gsSolved status) ]
    && S.size (S.fromList (map snd inputs)) == length inputs
    && S.size (S.fromList (map fst inputs)) == length inputs
    && all ((`M.notMember` L.get sNodes sys) . fst) inputs
  where
    inputs = openAttackerInputs sys

-- | Complete open attacker inputs with pub rule nodes after grounding.
-- Applying a substitution to System deliberately leaves goal keys unchanged.
-- Ground each completed input goal as well as its node, retaining its age and
-- loop-breaker status. Otherwise ordinary simplification substitutes the old
-- variable goal and reopens it, despite its existing public-constructor node.
completeAttackerInputs :: LNSubst -> System -> System
completeAttackerInputs subst sys =
    L.modify sGoals (M.fromListWith combineStatus . map solveInput . M.toList) $
    L.modify sNodes (M.union pubNodes) sys
  where
    pubNodes = M.fromList [ (i, Rule (IntrInfo PubConstrRule) [] [kuFact t] [kuFact t] [t])
               | (ActionG i (Fact KUFact _ [input]), status) <- M.toList (L.get sGoals sys)
               , not (L.get gsSolved status)
               , let t = apply subst input, isPubConstant t ]
    isPubConstant t = case viewTerm t of
      Lit (Con (Name PubName _)) -> True
      _                          -> False
    solveInput (goal@(ActionG i (Fact KUFact _ [_])), status)
      | not (L.get gsSolved status), i `M.member` pubNodes =
          (apply subst goal, L.set gsSolved True status)
    solveInput entry = entry
    -- As in ordinary goal substitution, colliding keys keep the oldest age
    -- and both solved/loop-breaker flags. Unrelated goal keys stay unchanged.
    combineStatus (GoalStatus solved1 age1 loops1) (GoalStatus solved2 age2 loops2) =
      GoalStatus (solved1 || solved2) (min age1 age2) (loops1 || loops2)

-- | Evaluates whether the formulas hold using safePartialAtomValuation and impliedFormulas.
-- Returns TFalse for an unconditional violation, TUnknown for a conditional
-- violation or unresolved formula, and TTrue otherwise. Original-side admission
-- and intersections of alternative failures belong to jointFailures above.
doRestrictionsHold :: ProofContext -> System -> [LNGuarded] -> Bool -> (Trivalent, [System])
doRestrictionsHold _ sys [] _ = (TTrue, [sys])
doRestrictionsHold ctxt sys formulas isSolved
  | not (null definiteViolations) = (TFalse, definiteViolations)
  | hasUnresolved                 = (TUnknown, [sys])
  | otherwise                     = (TTrue, map restrictionSystem simplifiedForms)
  where
    simplifiedForms = restrictionInstances ctxt sys formulas isSolved Nothing
    definiteViolations = [s | RestrictionInstance f s _ True <- simplifiedForms, f == gfalse]
    hasUnresolved = any (\(RestrictionInstance f _ _ unconditional) ->
      f /= gtrue && (f /= gfalse || not unconditional)) simplifiedForms

-- Private assignment-transport state. A standalone restriction has no failure
-- frame; a joint alternative carries all companion graphs and its current
-- local basis. The basis is captured only after normalizing that alternative.
data FailureFrame = FailureFrame
    { failureOriginal :: System
    , failureRemaining :: [System]
    , failurePrevious :: [System]
    , failureLocalSorts :: [LSort]
    , failureLocalImages :: [LNTerm]
    } deriving (Eq)

data RestrictionInstance = RestrictionInstance
    { restrictionFormula :: LNGuarded
    , restrictionSystem :: System
    , restrictionFrame :: Maybe FailureFrame
    , restrictionUnconditional :: Bool
    } deriving (Eq)

beginAlternative :: System -> System -> [System] -> [System] -> FailureFrame
beginAlternative original mirror remaining failed =
    FailureFrame original remaining failed (map lvarSort locals) (map varTerm locals)
  where
    locals = S.toList $ S.fromList (frees mirror)
               `S.difference` S.fromList (frees original)

finishAlternative :: System -> FailureFrame -> (System, [System], [System])
finishAlternative mirror frame =
    (failureOriginal frame, failureRemaining frame, mirror : failurePrevious frame)

-- Fresh guard variables avoid every graph and every transported local image.
-- Sorts are immutable evidence about the basis, not variable occurrences.
failureFrameFrees :: Maybe FailureFrame -> [LVar]
failureFrameFrees Nothing = []
failureFrameFrees (Just frame) = frees
    (failureOriginal frame, failureRemaining frame,
     failurePrevious frame, failureLocalImages frame)

-- This is the only guard-specialization operation: the selected formula,
-- selected graph, all companions and local images move together. Restrict each
-- graph's domain independently so its EqStore cannot acquire absent locals.
specializeRestriction :: LNSubst -> Bool -> RestrictionInstance -> RestrictionInstance
specializeRestriction subst unchanged instance' = instance'
    { restrictionFormula = apply subst (restrictionFormula instance')
    , restrictionSystem = applySystemSubst subst (restrictionSystem instance')
    , restrictionFrame = fmap transport (restrictionFrame instance')
    , restrictionUnconditional = restrictionUnconditional instance' && unchanged
    }
  where
    transport current = current
      { failureOriginal = applySystemSubst subst (failureOriginal current)
      , failureRemaining = map (applySystemSubst subst) (failureRemaining current)
      , failurePrevious = map (applySystemSubst subst) (failurePrevious current)
      , failureLocalImages = apply subst (failureLocalImages current)
      }

-- Conditions on locals describe possible failures, but cannot certify attacks.
-- Recheck after all nested guard substitutions; never cache this Boolean.
localsUnconstrained :: FailureFrame -> Bool
localsUnconstrained frame = case traverse getVar (failureLocalImages frame) of
    Nothing -> False
    Just vs -> length vs == S.size (S.fromList vs)
      && map lvarSort vs == failureLocalSorts frame
      && S.null (S.fromList vs `S.intersection` S.fromList (frees (failureOriginal frame)))

restrictionInstances :: ProofContext -> System -> [LNGuarded] -> Bool
                     -> Maybe FailureFrame -> [RestrictionInstance]
restrictionInstances ctxt sys formulas isSolved frame =
    simplify [RestrictionInstance f sys frame True | f <- formulas]
  where
    simplify forms =
        if next == forms then forms else simplify next
      where
        next = map simpGuard $ concatMap impliedOrInitial $ concatMap splitConjunction forms

    splitConjunction instance'@(RestrictionInstance f _ _ _)
      | f == gtrue = [instance']
      | otherwise = [instance' { restrictionFormula = part } | part <- guardedConjuncts f]

    simpGuard instance' = instance'
      { restrictionFormula = simplifyGuardedOrReturn
          (safePartialAtomValuation ctxt (restrictionSystem instance'))
          (restrictionFormula instance') }

    impliedOrInitial instance'
      | isAllGuarded (restrictionFormula instance') && (isSolved || not (null imps)) = imps
      | otherwise = [instance']
      where
        -- specializeRestriction composes the unconditional flag with each
        -- nested guard; a later renaming cannot erase an outer constraint.
        imps = [next { restrictionSystem = normDG ctxt (restrictionSystem next) }
               | next <- impliedFormulasAndSystems (L.get pcMaudeHandle ctxt) instance']

-- EqStore records substitutions, including bindings for variables absent from
-- the graph. Do not import another mirror's local variables into this system.
applySystemSubst :: LNSubst -> System -> System
applySystemSubst subst sys = apply (restrict (frees sys) subst) sys

-- | Normalizes all terms in the dependency graph.
normDG :: ProofContext -> System -> System
normDG ctxt sys = L.set sNodes normalizedNodes sys
  where
    normalizedNodes = M.map (\r -> runReader (normRule r) (L.get pcMaudeHandle ctxt)) (L.get sNodes sys)

-- | Returns the mirrored DGs, if they exist.
getMirrorDG :: DiffProofContext -> Side -> System -> [System]
getMirrorDG ctxt side sys = {-trace (show (evalFreshAvoiding newNodes (freshNatAndPubConstrRules, sys))) $-} fmap (normDG $ eitherProofContext ctxt side) $ unifyInstances $ evalFreshAvoiding newNodes (freshNatAndPubConstrRules, sys)
  where
    (freshNatAndPubConstrRules, notFreshNorPub) = (M.partition (\rule -> (isFreshRule rule) || (isPubConstrRule rule) || (isNatConstrRule rule)) (L.get sNodes sys))
    (newProtoRules, otherRules) = (M.partition (\rule -> (containsNewVars rule) && (isProtocolRule rule)) notFreshNorPub)
    newNodes = (M.foldrWithKey (transformRuleInstance) (M.foldrWithKey (transformRuleInstance) (return [freshNatAndPubConstrRules]) newProtoRules) otherRules)

    -- We keep instantiations of fresh and public variables. Currently new public variables in protocol rule instances
    -- are instantiated correctly in someRuleACInstAvoiding, but if this is changed we need to fix this part.
    transformRuleInstance :: MonadFresh m => NodeId -> RuleACInst -> m ([M.Map NodeId RuleACInst]) -> m ([M.Map NodeId RuleACInst])
    transformRuleInstance idx rule nodes = genNodeMapsForAllRuleVariants <$> nodes <*> (getOtherRulesAndVariants rule)
      where
        genNodeMapsForAllRuleVariants :: [M.Map NodeId RuleACInst] -> [RuleACInst] -> [M.Map NodeId RuleACInst]
        genNodeMapsForAllRuleVariants nodes' rules = (\x y -> M.insert idx y x) <$> nodes' <*> rules

        getOtherRulesAndVariants :: MonadFresh m => RuleACInst -> m ([RuleACInst])
        getOtherRulesAndVariants original =
            concat <$> traverse instantiate (getOppositeRules ctxt side original)
          where
            instantiate oppositeRule = do
              variants <- someRuleACInst oppositeRule >>= getVariants
              pure $ if isProtocolRule original
                then mapMaybe (\variant -> (`apply` variant) <$>
                       getSubstitutionsFixingNewVars original variant) variants
                else variants

        getVariants :: MonadFresh m => (RuleACInst, Maybe RuleACConstrs) -> m ([RuleACInst])
        getVariants (r, Nothing)       = return [r]
        getVariants (r, Just (Disj variants)) = traverse instantiate variants
          where
            instantiate :: MonadFresh m => LNSubstVFresh -> m RuleACInst
            instantiate variant = do
              subst <- freshToFree variant
              rename (apply subst r)

    unifyInstances :: [M.Map NodeId RuleACInst] -> [System]
    -- Preserve the existing candidate order, with each candidate contributing
    -- one independent mirror for every solution of its graph equalities.
    unifyInstances = concatMap instantiate . reverse
        where
          instantiate nodes =
              [L.set sNodes (apply subst nodes) sys | subst <- freeUnifiers nodes]
            where
              (foundUnifiers, constSubsts) = unifiers $ equalities True nodes

              finalSubst :: [LNSubst] -> [LNSubst]
              finalSubst subst = map replaceConstants subst
                where
                  replaceConstants :: LNSubst -> LNSubst
                  replaceConstants s = mapRange applyInverseSubst s
                    where
                      applyInverseSubst :: LNTerm -> LNTerm
                      applyInverseSubst t = case viewTerm t of
                              (Lit _) | t `M.member` inversSubst -> varTerm $ inversSubst M.! t
                                      | otherwise                -> t
                              (FApp s' ts)                       -> fApp s' $ map applyInverseSubst ts

                      inversSubst = M.fromList $ map swap constSubsts

              freeUnifiers :: M.Map NodeId RuleACInst -> [LNSubst]
              freeUnifiers newnodes = finalSubst $ map (\y -> freshToFreeAvoiding y (newnodes, sys)) foundUnifiers

    unifiers :: (Maybe [(Equal LNFact, (LVar, LNTerm))],[Equal LNFact]) -> ([SubstVFresh Name LVar], [(LVar, LNTerm)])
    unifiers (Nothing, _)                  = ([], [])
    unifiers (Just equalfacts, equaledges) = (runReader (unifyLNFactEqs $ (map fst equalfacts) ++ equaledges) (getMaudeHandle ctxt side), map snd equalfacts)

    equalities :: Bool -> M.Map NodeId RuleACInst -> (Maybe [(Equal LNFact, (LVar, LNTerm))],[Equal LNFact])
    equalities fixNewPublicVars newrules = (getNewVarEqualities fixNewPublicVars newrules, (getGraphEqualities newrules) ++ (getKUGraphEqualities newrules))

    getGraphEqualities :: M.Map NodeId RuleACInst -> [Equal LNFact]
    getGraphEqualities nodes = map (\(Edge x y) -> Equal (nodePremFactMap y nodes) (nodeConcFactMap x nodes)) $ S.toList (L.get sEdges sys)

    getKUGraphEqualities :: M.Map NodeId RuleACInst -> [Equal LNFact]
    getKUGraphEqualities nodes = toEquality [] $ getEdgesFromLessRelation sys
      where
        toEquality _     []                       = []
        toEquality goals ((Left  (Edge y x)):xs)  = (Equal (nodePremFactMap x nodes) (nodeConcFactMap y nodes)):(toEquality goals xs)
        toEquality goals ((Right (prem, nid)):xs) = eqs ++ (toEquality ((prem, nid):goals) xs)
          where
            eqs = map (\(x, _) -> (Equal (nodePremFactMap prem nodes) (nodePremFactMap x nodes))) $ filter (\(_, y) -> nid == y) goals

    getNewVarEqualities :: Bool -> M.Map NodeId RuleACInst -> Maybe ([(Equal LNFact, (LVar, LNTerm))])
    getNewVarEqualities fixNewPublicVars nodes = (++) <$> genTrivialEqualities <*> (Just (concat $ map (\(_, r) -> genEqualities $ map (\x -> (kuFact (varTerm x), x, x)) $ getNewVariables fixNewPublicVars r) $ M.toList nodes))
      where
        genEqualities :: [(LNFact, LVar, LVar)] -> [(Equal LNFact, (LVar, LNTerm))]
        genEqualities = map (\(x, y, z) -> (Equal x (replaceNewVarWithConstant x y z), (y, constant y z)))

        genTrivialEqualities :: Maybe ([(Equal LNFact, (LVar, LNTerm))])
        genTrivialEqualities = genEqualities <$> getTrivialFacts nodes sys

        replaceNewVarWithConstant :: LNFact -> LVar -> LVar -> LNFact
        replaceNewVarWithConstant fact v cvar = apply subst fact
          where
            subst = Subst (M.fromList [(v, constant v cvar)])

        constant :: LVar -> LVar -> LNTerm
        constant v cvar = constTerm (Name (pubOrFresh v) (NameId ("constVar_" ++ toConstName cvar)))
          where
            toConstName (LVar name vsort idx) = (show vsort) ++ "_" ++ (show idx) ++ "_" ++ name

            pubOrFresh (LVar _ LSortFresh _) = FreshName
            pubOrFresh (LVar _ _          _) = PubName

-- | Returns the set of edges of a system saturated with all edges deducible from the nodes and the less relation
--   This does not cover edges to open goals.
saturateEdgesWithLessRelation :: System -> S.Set Edge
saturateEdgesWithLessRelation sys = S.union (S.fromList $ lefts $ getEdgesFromLessRelation sys) (L.get sEdges sys)

-- | Returns the set of implicit edges of a system, which are implied by the nodes and the less relation
--   If the edge references an open goal, the corresponding fact is returned.
getEdgesFromLessRelation :: System -> [Either Edge (NodePrem, NodeId)]
getEdgesFromLessRelation sys = map toEdge $ concat $ map (\x -> getAllMatchingConcs sys x $ getAllLessPreds sys $ fst x) (getOpenNodePrems sys)
  where
    toEdge (x, Left y)  = Left (Edge y x)
    toEdge (x, Right y) = Right (x, y)

-- | Given a system, a node premise, and a set of node ids from the less relation returns:
--   a list of implicit edges for this premise, if the rule instances exist, or the corresponding LNFact otherwise
getAllMatchingConcs :: System -> NodePrem -> [NodeId] -> [(NodePrem, Either NodeConc NodeId)]
getAllMatchingConcs sys premid (x:xs) = case (nodeRuleSafe x sys) of
    Nothing   -> (if M.member (ActionG x (nodePremFact premid sys)) goals
                     then [(premid, Right x)]
                     else [])
                  ++ (getAllMatchingConcs sys premid xs)
                    where
                      goals = L.get sGoals sys
    Just rule -> (map (\(cid, _) -> (premid, Left (x, cid))) (filter (\(_, cf) -> nodePremFact premid sys == cf) $ enumConcs rule))
        ++ (getAllMatchingConcs sys premid xs)
getAllMatchingConcs _    _     []     = []

-- | Given a system, a fact, and a set of node ids from the less relation returns the set of matching premises, if the rule instances exist
getAllMatchingPrems :: System -> LNFact -> [NodeId] -> [NodePrem]
getAllMatchingPrems sys fa (x:xs) = case (nodeRuleSafe x sys) of
    Nothing   -> getAllMatchingPrems sys fa xs
    Just rule -> (map (\(pid, _) -> (x, pid)) (filter (\(_, pf) -> fa == pf) $ enumPrems rule))
        ++ (getAllMatchingPrems sys fa xs)
getAllMatchingPrems _   _     []  = []

-- | Given a system and a node, gives the list of all nodes that have a "less" edge to this node
getAllLessPreds :: System -> NodeId -> [NodeId]
getAllLessPreds sys nid = map (L.get laSmaller) $ filter ((nid ==) . L.get laLarger) (S.toList (L.get sLessAtoms sys))

-- | Given a system and a node, gives the list of all nodes that have a "less" edge to this node
getAllLessSucs :: System -> NodeId -> [NodeId]
getAllLessSucs sys nid = map (L.get laLarger) $ filter ((nid ==) . L.get laSmaller) (S.toList (L.get sLessAtoms sys))

-- | Given a system, returns all node premises that have no incoming edge
getOpenNodePrems :: System -> [NodePrem]
getOpenNodePrems sys = getOpenIncoming (M.toList $ L.get sNodes sys)
  where
    getOpenIncoming :: [(NodeId, RuleACInst)] -> [NodePrem]
    getOpenIncoming []          = []
    getOpenIncoming ((k, r):xs) = (filter hasNoIncomingEdge $ map (\(x, _) -> (k, x)) (enumPrems r)) ++ (getOpenIncoming xs)

    hasNoIncomingEdge np = S.null (S.filter (\(Edge _ y) -> y == np) (L.get sEdges sys))

-- | Returns a list of all open trivial facts of nodes in the current system, and the variable they need to be unified with
getTrivialFacts :: M.Map NodeId RuleACInst -> System -> Maybe ([(LNFact, LVar, LVar)])
getTrivialFacts nodes sys = case (unsolvedTrivialGoals sys) of
                                 []     -> Just []
                                 (x:xs) -> foldl foldTreatGoal (treatGoal nodes x) xs
  where
    foldTreatGoal :: Maybe [(LNFact, LVar, LVar)] -> (Either NodePrem LVar, LNFact) -> Maybe [(LNFact, LVar, LVar)]
    foldTreatGoal eqdata goal = (++) <$> (treatGoal eqdata goal) <*> eqdata

    treatGoal :: HasFrees t => t -> (Either NodePrem LVar, LNFact) -> Maybe [(LNFact, LVar, LVar)]
    treatGoal _ (Left pidx, _ ) = (map (\(x, y) -> (x, y, y))) <$> getFactAndVars nodes pidx
    treatGoal a (Right var, fa) = premiseFacts (nodes, a) var fa

    premisesForKUAction :: LVar -> LNFact -> [NodePrem]
    premisesForKUAction var fa = getAllMatchingPrems sys fa $ getAllLessSucs sys var

    premiseFacts :: HasFrees t => t -> LVar -> LNFact -> Maybe ([(LNFact, LVar, LVar)])
    premiseFacts av var fa = fmap concat $ sequence $ map (getAllEqData (renameAvoiding fa av)) (premisesForKUAction var fa)

    getAllEqData :: LNFact -> NodePrem -> Maybe ([(LNFact, LVar, LVar)])
    getAllEqData fact p = zipWith (\(x, y) z -> (x, y, z)) <$> getFactAndVars nodes p <*> (isTrivialFact fact)

-- | If the fact at premid in nodes is trivial, returns the fact and its (trivial) variables. Otherwise returns nothing
getFactAndVars :: M.Map NodeId RuleACInst -> NodePrem -> Maybe ([(LNFact, LVar)])
getFactAndVars nodes premid = (map (\x -> (fact, x))) <$> (isTrivialFact fact)
  where
    fact = (nodePremFactMap premid nodes)

-- | Assumption: the goal is trivial. Returns true if it is independent wrt the rest of the system.
checkIndependence :: System -> (Either NodePrem LVar, LNFact) -> Bool
checkIndependence sys (eith, fact) = not (D.cyclic (rawLessRel sys))
    && (checkNodes $ case eith of
                         (Left premidx) -> checkIndependenceRec (L.get sNodes sys) premidx
                         (Right lvar)   -> foldl checkIndependenceRec (L.get sNodes sys) $ identifyPremises lvar fact)
  where
    edges = S.toList $ saturateEdgesWithLessRelation sys
    variables = fromMaybe (error $ "checkIndependence: This fact " ++ show fact ++ " should be trivial! System: " ++ show sys) (isTrivialFact fact)

    identifyPremises :: LVar -> LNFact -> [NodePrem]
    identifyPremises var' fact' = getAllMatchingPrems sys fact' (getAllLessSucs sys var')

    checkIndependenceRec :: M.Map NodeId RuleACInst -> NodePrem -> M.Map NodeId RuleACInst
    checkIndependenceRec nodes (nid, _) = foldl checkIndependenceRec (M.delete nid nodes)
        $ map (\(Edge _ tgt) -> tgt) $ filter (\(Edge (srcn, _) _) -> srcn == nid) edges

    checkNodes :: M.Map NodeId RuleACInst -> Bool
    checkNodes nodes = all (\(_, r) -> null $ filter (\f -> not $ null $ intersect variables (getFactVariables f)) (facts r)) $ M.toList nodes
      where
        facts ru = (map snd (enumPrems ru)) ++ (map snd (enumConcs ru))


-- | All premises that still need to be solved.
unsolvedPremises :: System -> [(NodePrem, LNFact)]
unsolvedPremises sys =
      do (PremiseG premidx fa, status) <- M.toList (L.get sGoals sys)
         guard (not $ L.get gsSolved status)
         return (premidx, fa)

-- | All trivial goals that still need to be solved.
unsolvedTrivialGoals :: System -> [(Either NodePrem LVar, LNFact)]
unsolvedTrivialGoals sys = foldl f [] $ M.toList (L.get sGoals sys)
  where
    f l (PremiseG premidx fa, status) = if ((isTrivialFact fa /= Nothing) && (not $ L.get gsSolved status)) then (Left premidx, fa):l else l
    f l (ActionG var fa, status)      = if ((isTrivialFact fa /= Nothing) && (isKUFact fa) && (not $ L.get gsSolved status)) then (Right var, fa):l else l
    f l (ChainG _ _, _)               = l
    f l (SplitG _, _)                 = l
    f l (DisjG _, _)                  = l
    f l (SubtermG _, _)               = l

-- | Tests whether there are common Variables in the Facts
noCommonVarsInGoals :: [(Either NodePrem LVar, LNFact)] -> Bool
noCommonVarsInGoals goals =
    noCommonVars $ map (getFactVariables . snd) goals
  where
    noCommonVars :: [[LVar]] -> Bool
    noCommonVars []     = True
    noCommonVars (x:xs) = (all (\y -> null $ intersect x y) xs) && (noCommonVars xs)


-- | Returns true if all formulas in the system are solved.
allFormulasAreSolved :: System -> Bool
allFormulasAreSolved sys = S.null $ L.get sFormulas sys

-- | Returns true if all the depedency graph is not empty.
dgIsNotEmpty :: System -> Bool
dgIsNotEmpty sys = not $ M.null $ L.get sNodes sys

-- | Assumption: all open goals in the system are "trivial" fact goals. Returns true if these goals are independent from each other and the rest of the system.
allOpenFactGoalsAreIndependent :: System -> Bool
allOpenFactGoalsAreIndependent sys = (noCommonVarsInGoals unsolvedGoals) && (all (checkIndependence sys) unsolvedGoals)
  where
    unsolvedGoals = unsolvedTrivialGoals sys

-- | Returns true if all open goals in the system are "trivial" fact goals.
allOpenGoalsAreSimpleFacts :: DiffProofContext -> System -> Bool
allOpenGoalsAreSimpleFacts ctxt sys = M.foldlWithKey goalIsSimpleFact True (L.get sGoals sys)
  where
    goalIsSimpleFact :: Bool -> Goal -> GoalStatus -> Bool
    goalIsSimpleFact ret (ActionG _ fact)         (GoalStatus solved _ _) = ret && (solved || ((isTrivialFact fact /= Nothing) && (isKUFact fact)))
    goalIsSimpleFact ret (ChainG _ _)             (GoalStatus solved _ _) = ret && solved
    goalIsSimpleFact ret (PremiseG (nid, _) fact) (GoalStatus solved _ _) = ret && (solved || (isTrivialFact fact /= Nothing) && (not (isProtocolRule r) || (getOriginalRule ctxt LHS r == getOriginalRule ctxt RHS r)))
      where
        r = nodeRule nid sys
    goalIsSimpleFact ret (SplitG _)               (GoalStatus solved _ _) = ret && solved
    goalIsSimpleFact ret (DisjG _)                (GoalStatus solved _ _) = ret && solved
    goalIsSimpleFact ret (SubtermG _)             (GoalStatus solved _ _) = ret && solved

-- | Returns true if the current system is a diff system
isDiffSystem :: System -> Bool
isDiffSystem = L.get sDiffSystem

-- Actions
----------

-- | All actions that hold in a sequent.
unsolvedActionAtoms :: System -> [(NodeId, LNFact)]
unsolvedActionAtoms sys =
      do (ActionG i fa, status) <- M.toList (L.get sGoals sys)
         guard (not $ L.get gsSolved status)
         return (i, fa)

-- | All actions that hold in a sequent.
allActions :: System -> [(NodeId, LNFact)]
allActions sys =
      unsolvedActionAtoms sys
  <|> do (i, ru) <- M.toList $ L.get sNodes sys
         (,) i <$> L.get rActs ru

-- | All actions that hold in a sequent.
allKUActions :: System -> [(NodeId, LNFact, LNTerm)]
allKUActions sys = do
    (i, fa@(kFactView -> Just (UpK, m))) <- allActions sys
    return (i, fa, m)

-- | The standard actions, i.e., non-KU-actions.
standardActionAtoms :: System -> [(NodeId, LNFact)]
standardActionAtoms = filter (not . isKUFact . snd) . unsolvedActionAtoms

-- | All KU-actions.
kuActionAtoms :: System -> [(NodeId, LNFact, LNTerm)]
kuActionAtoms sys = do
    (i, fa@(kFactView -> Just (UpK, m))) <- unsolvedActionAtoms sys
    return (i, fa, m)

-- Destruction chains
---------------------

-- | All unsolved destruction chains in the constraint system.
unsolvedChains :: System -> [(NodeConc, NodePrem)]
unsolvedChains sys = do
    (ChainG from to, status) <- M.toList $ L.get sGoals sys
    guard (not $ L.get gsSolved status)
    return (from, to)


-- The temporal order
---------------------

-- | @(from,to)@ is in @rawEdgeRel se@ iff we can prove that there is an
-- edge-path from @from@ to @to@ in @se@ without appealing to transitivity.
rawEdgeRel :: System -> [(NodeId, NodeId)]
rawEdgeRel sys = map (nodeConcNode *** nodePremNode) $
     [(from, to) | Edge from to <- S.toList $ L.get sEdges sys]
  ++ unsolvedChains sys

-- | @(from,to)@ is in @rawLessRel se@ iff we can prove that there is a path
-- (possibly using the 'Less' relation) from @from@ to @to@ in @se@ without
-- appealing to transitivity.
rawLessRel :: System -> [(NodeId,NodeId)]
rawLessRel se = (getLessRel $ S.toList (L.get sLessAtoms se)) ++ rawEdgeRel se

getLessAtoms :: System -> S.Set (NodeId, NodeId)
getLessAtoms = S.fromList . getLessRel . S.toList . L.get sLessAtoms

-- | Returns a predicate that is 'True' iff the first argument happens before
-- the second argument in all models of the sequent.
alwaysBefore :: System -> (NodeId -> NodeId -> Bool)
alwaysBefore sys =
    check -- lessRel is cached for partial applications
  where
    lessRel   = rawLessRel sys
    check i j =
         -- speed-up check by first checking less-atoms
         ((i, j) `S.member` getLessAtoms sys)
      || (j `S.member` D.reachableSet [i] lessRel)

-- | 'True' iff the given node id is guaranteed to be instantiated to an
-- index in the trace.
isInTrace :: System -> NodeId -> Bool
isInTrace sys i =
     i `M.member` L.get sNodes sys
  || isLast sys i
  || any ((i ==) . fst) (unsolvedActionAtoms sys)

-- | 'True' iff the given node id is guaranteed to be instantiated to the last
-- index of the trace.
isLast :: System -> NodeId -> Bool
isLast sys i = Just i == L.get sLastAtom sys

------------------------------------------------------------------------------
-- Pretty printing                                                          --
------------------------------------------------------------------------------

-- | Pretty print a sequent
prettySystem :: HighlightDocument d => System -> d
prettySystem se = vcat $
    map combine_
      [ ("nodes",          vcat $ map prettyNode $ M.toList $ L.get sNodes se)
      , ("actions",        fsepList ppActionAtom $ unsolvedActionAtoms se)
      , ("edges",          fsepList prettyEdge   $ S.toList $ L.get sEdges se)
      , ("less",           fsepList prettyLess   $ S.toList $ L.get sLessAtoms se)
      , ("unsolved constraints", prettyGoals False se)
      ]
    ++ [prettyNonGraphSystem se]
  where
    combine_ (header, d) = fsep [keyword_ header <> colon, nest 2 d]
    ppActionAtom (i, fa) = prettyNAtom (Action (varTerm i) fa)

-- | Pretty print the non-graph part of the sequent; i.e. equation store and
-- clauses.
prettyNonGraphSystem :: HighlightDocument d => System -> d
prettyNonGraphSystem se = vsep $ map combine_ -- text $ show se
  [ ("last",            maybe (text "none") prettyNodeId $ L.get sLastAtom se)
  , ("formulas",        vsep $ map prettyGuarded {-(text . show)-} $ S.toList $ L.get sFormulas se)
  , ("subterms",        prettySubtermStore $ L.get sSubtermStore se)
  , ("equations",       prettyEqStore $ L.get sEqStore se)
  , ("lemmas",          vsep $ map prettyGuarded $ S.toList $ L.get sLemmas se)
  , ("allowed cases",   text $ show $ L.get sSourceKind se)
  , ("solved formulas", vsep $ map prettyGuarded $ S.toList $ L.get sSolvedFormulas se)
  , ("unsolved constraints", prettyGoals False se)
  , ("solved constraints", prettyGoals True se)
  ]
  where
    combine_ (header, d)  = fsep [keyword_ header <> colon, nest 2 d]

-- | Pretty print the non-graph part of the sequent; i.e. equation store and
-- clauses.
prettyNonGraphSystemDiff :: HighlightDocument d => DiffSystem -> d
prettyNonGraphSystemDiff se = vsep $ map combine_
  [ ("proof type",          prettyProofType $ L.get dsProofType se)
  , ("current rule",        maybe (text "none") text $ L.get dsCurrentRule se)
  , ("system",              maybe (text "none") prettyNonGraphSystem $ L.get dsSystem se)
  , ("protocol rules",      vsep $ map prettyProtoRuleE $ S.toList $ L.get dsProtoRules se)
  , ("construction rules",  vsep $ map prettyRuleAC $ S.toList $ L.get dsConstrRules se)
  , ("destruction rules",   vsep $ map prettyRuleAC $ S.toList $ L.get dsDestrRules se)
  ]
  where
    combine_ (header, d)  = fsep [keyword_ header <> colon, nest 2 d]

-- | Pretty print the proof type.
prettyProofType :: HighlightDocument d => Maybe DiffProofType -> d
prettyProofType Nothing  = text "none"
prettyProofType (Just p) = text $ show p

-- | Pretty print solved or un.
prettyGoals :: HighlightDocument d => Bool -> System -> d
prettyGoals solved sys = vsep $ do
    (goal, status) <- M.toList $ L.get sGoals sys
    guard (solved == L.get gsSolved status)
    let nr  = L.get gsNr status
        sourceRule = case goalRule sys goal of
            Just ru -> " (from rule " ++ getRuleName ru ++ ")"
            Nothing -> ""
        loopBreaker | L.get gsLoopBreaker status = " (loop breaker)"
                    | otherwise                  = ""
        useful = case goal of
          _ | L.get gsLoopBreaker status              -> " (loop breaker)"
          ActionG i (kFactView -> Just (UpK, m))
              -- if there are KU-guards then all knowledge goals are useful
            | hasKUGuards             -> " (useful1)"
            | currentlyDeducible i m  -> " (currently deducible)"
            | probablyConstructible m -> " (probably constructible)"
          _                           -> " (useful2)"
    return $ prettyGoal goal <-> lineComment_ ("nr: " ++ show nr ++ sourceRule ++ loopBreaker ++ show useful)
  where
    existingDeps = rawLessRel sys
    hasKUGuards  =
        any ((KUFact `elem`) . guardFactTags) $ S.toList $ L.get sFormulas sys

    checkTermLits :: (LSort -> Bool) -> LNTerm -> Bool
    checkTermLits p =
        Mono.getAll . foldMap (Mono.All . p . sortOfLit)

    -- KU goals of messages that are likely to be constructible by the
    -- adversary. These are terms that do not contain a fresh name or a fresh
    -- name variable. For protocols without loops they are very likely to be
    -- constructible. For protocols with loops, such terms have to be given
    -- similar priority as loop-breakers.
    probablyConstructible  m = checkTermLits (LSortFresh /=) m
                               && not (containsPrivate m)

    -- KU goals of messages that are currently deducible. Either because they
    -- are composed of public names only and do not contain private function
    -- symbols or because they can be extracted from a sent message using
    -- unpairing or inversion only.
    currentlyDeducible i m = (checkTermLits (`elem` [LSortPub, LSortNat]) m
                              && not (containsPrivate m))
                          || extractible i m

    extractible i m = or $ do
        (j, ru) <- M.toList $ L.get sNodes sys
        -- We cannot deduce a message from a last node.
        guard (not $ isLast sys j)
        let derivedMsgs = concatMap toplevelTerms $
                [ t | Fact OutFact _ [t] <- L.get rConcs ru] <|>
                [ t | Just (DnK, t)    <- kFactView <$> L.get rConcs ru]
        -- m is deducible from j without an immediate contradiction
        -- if it is a derived message of 'ru' and the dependency does
        -- not make the graph cyclic.
        return $ m `elem` derivedMsgs &&
                 not (j `S.member` D.reachableSet [i] existingDeps)

    toplevelTerms t@(viewTerm2 -> FPair t1 t2) =
        t : toplevelTerms t1 ++ toplevelTerms t2
    toplevelTerms t@(viewTerm2 -> FInv t1) = t : toplevelTerms t1
    toplevelTerms t = [t]

-- | Pretty print a case distinction
prettySource :: HighlightDocument d => Source -> d
prettySource th = vcat $
   [ prettyGoal $ L.get cdGoal th ]
   ++ map combine_ (zip [(1::Int)..] $ map snd . getDisj $ (L.get cdCases th))
  where
    combine_ (i, sys) = fsep [keyword_ ("Case " ++ show i) <> colon, nest 2 (prettySystem sys)]


-- Additional instances
-----------------------

deriving instance Show DiffSystem

instance Apply LNSubst SourceKind where
    apply = const id

instance Apply LNSubst System where
    apply subst (System a b c d e f g h i j k l m) =
        System (apply subst a)
        -- we do not apply substitutions to node variables, so we do not apply them to the edges either
        b
        (apply subst c) (apply subst d)
        (apply subst e) (apply subst f) (apply subst g) (apply subst h) (apply subst i)
        j k (apply subst l) (apply subst m)

instance HasFrees SourceKind where
    foldFrees = const mempty
    foldFreesOcc  _ _ = const mempty
    mapFrees  = const pure

instance HasFrees GoalStatus where
    foldFrees = const mempty
    foldFreesOcc  _ _ = const mempty
    mapFrees  = const pure

instance HasFrees System where
    {-# INLINABLE foldFrees #-}
    foldFrees fun (System a b c d e f g h i j k l m) =
        foldFrees fun a `mappend`
        foldFrees fun b `mappend`
        foldFrees fun c `mappend`
        foldFrees fun d `mappend`
        foldFrees fun e `mappend`
        foldFrees fun f `mappend`
        foldFrees fun g `mappend`
        foldFrees fun h `mappend`
        foldFrees fun i `mappend`
        foldFrees fun j `mappend`
        foldFrees fun k `mappend`
        foldFrees fun l `mappend`
        foldFrees fun m

    foldFreesOcc fun ctx (System a _b _c _d _e _f _g _h _i _j _k _l _m) =
        foldFreesOcc fun ("a":ctx') a {- `mappend`
        foldFreesCtx fun ("b":ctx') b `mappend`
        foldFreesCtx fun ("c":ctx') c `mappend`
        foldFreesCtx fun ("d":ctx') d `mappend`
        foldFreesCtx fun ("e":ctx') e `mappend`
        foldFreesCtx fun ("f":ctx') f `mappend`
        foldFreesCtx fun ("g":ctx') g `mappend`
        foldFreesCtx fun ("h":ctx') h `mappend`
        foldFreesCtx fun ("i":ctx') i `mappend`
        foldFreesCtx fun ("j":ctx') j `mappend`
        foldFreesCtx fun ("k":ctx') k -}
      where ctx' = "system":ctx

    {-# INLINABLE mapFrees #-}
    mapFrees fun (System a b c d e f g h i j k l m) =
        System <$> mapFrees fun a
               <*> mapFrees fun b
               <*> mapFrees fun c
               <*> mapFrees fun d
               <*> mapFrees fun e
               <*> mapFrees fun f
               <*> mapFrees fun g
               <*> mapFrees fun h
               <*> mapFrees fun i
               <*> mapFrees fun j
               <*> mapFrees fun k
               <*> mapFrees fun l
               <*> mapFrees fun m

instance HasFrees Source where
    {-# INLINABLE foldFrees #-}
    foldFrees f th =
        foldFrees f (L.get cdGoal th)   `mappend`
        foldFrees f (L.get cdCases th)

    foldFreesOcc  _ _ = const mempty

    {-# INLINABLE mapFrees #-}
    mapFrees f th = Source <$> mapFrees f (L.get cdGoal th)
                                    <*> mapFrees f (L.get cdCases th)

-- Special comparison functions to ignore new var instantiations
----------------------------------------------------------------

compareListsUpToNewVars :: [(NodeId, RuleACInst)] -> [(NodeId, RuleACInst)] -> Ordering
compareListsUpToNewVars []           []           = EQ
compareListsUpToNewVars []           _            = LT
compareListsUpToNewVars (_:_)        []           = GT
compareListsUpToNewVars ((x1,x2):xs) ((y1,y2):ys) = case compare x1 y1 of
                                                         EQ -> case compareRulesUpToNewVars x2 y2 of
                                                                EQ -> compareListsUpToNewVars xs ys
                                                                LT -> LT
                                                                GT -> GT
                                                         LT -> LT
                                                         GT -> GT

compareNodesUpToNewVars :: M.Map NodeId RuleACInst -> M.Map NodeId RuleACInst -> Ordering
compareNodesUpToNewVars n1 n2 = compareListsUpToNewVars (M.toAscList n1) (M.toAscList n2)

compareSystemsUpToNewVars :: System -> System -> Ordering
-- when we have trace systems, we can ignore new variable instantiations
compareSystemsUpToNewVars
   (System a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 False)
   (System a2 b2 c2 d2 e2 f2 g2 h2 i2 j2 k2 l2 False)
       = if compareNodes == EQ then
            compare (System M.empty b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 False)
                (System M.empty b2 c2 d2 e2 f2 g2 h2 i2 j2 k2 l2 False)
         else
            compareNodes
        where
            compareNodes = compareNodesUpToNewVars a1 a2
-- in case of diff systems, we remain prudent
compareSystemsUpToNewVars s1 s2 = compare s1 s2


-- | 'True' iff the dotted system will be a non-empty graph.
nonEmptyGraph :: System -> Bool
nonEmptyGraph sys = not $
    M.null (L.get sNodes sys) && null (unsolvedActionAtoms sys) &&
    null (unsolvedChains sys) &&
    S.null (L.get sEdges sys) && S.null (L.get sLessAtoms sys)

-- | 'True' iff the dotted system will be a non-empty graph.
nonEmptyGraphDiff :: DiffSystem -> Bool
nonEmptyGraphDiff diffSys = not $
     case (L.get dsSystem diffSys) of
          Nothing    -> True
          (Just sys) -> M.null (L.get sNodes sys) && null (unsolvedActionAtoms sys) &&
                        null (unsolvedChains sys) &&
                        S.null (L.get sEdges sys) && S.null (L.get sLessAtoms sys)
