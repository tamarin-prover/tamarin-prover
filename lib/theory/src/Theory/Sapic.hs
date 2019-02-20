{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveAnyClass       #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann and Alexander Dax
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Data types for SAPIC processes in theories
module Theory.Sapic (
    Process(..)
    , ProcessCombinator(..)
    , AnProcess(..)
    , SapicAction(..)
    , paddAnn
    , prettySapic
    , prettySapicAction
) where

import           Data.Binary
import           Data.List
import           Data.Maybe
import           Data.Monoid                         (Sum(..))
import qualified Data.Set                            as S
import           GHC.Generics                        (Generic)
import           Extension.Data.Label                hiding (get)
import qualified Extension.Data.Label                as L
import           Control.Parallel.Strategies

import           Theory.Model
import           Term.LTerm

-- | A process data structure
data IfCondition = CondIdentifier                   
    deriving( Show, Eq, Ord, Generic, NFData, Binary )

type Id = String
type SapicVar = LNTerm
type SapicTerm = LNTerm

data SapicAction = 
                   Null 
                 | Par
                 | Rep
                 | New Name
                 | Ch_In_Pattern (Maybe SapicTerm) SapicTerm
                 | Ch_In (Maybe SapicTerm) SapicTerm
                 | Ch_Out (Maybe SapicTerm) SapicTerm
                 | Insert SapicTerm SapicTerm
                 | Delete SapicTerm 
                 | Lock SapicTerm 
                 | Unlock SapicTerm 
                 | Lookup SapicTerm SapicTerm
                 -- | Event of action
                 -- | Cond of action
                 -- | MSR of msr 
                 -- | Let of string
    -- |   ...   TODO parser: extend
        deriving( Show, Eq, Ord, Generic, NFData, Binary )
     
data ProcessCombinator = Parallel | NDC | Cond deriving (Generic, NFData, Binary)
-- data ProcessTag = NullP | Comb | SAction

data AnProcess ann =  
        ProcessNull ann
    |   ProcessComb ProcessCombinator ann (AnProcess ann) (AnProcess ann)
    -- |   ProcessIdentifier String ann 
    |   ProcessAction SapicAction ann (AnProcess ann)
     deriving(Generic )
     -- deriving (Generic, Binary, NFData, Ord, Eq, Show)
-- deriving instance Generic (AnProcess ann)
-- deriving instance Binary ann => Binary (AnProcess ann)
-- deriving instance NFData ann => NFData (AnProcess ann)
-- deriving instance Ord ann => Ord (AnProcess ann)
-- deriving instance Eq ann => Eq (AnProcess ann)
-- deriving instance Show ann => Show (AnProcess ann)
instance (Ord ann) => Ord (AnProcess ann)
deriving instance (NFData ann) => NFData (AnProcess ann)
instance (Binary ann) => Binary (AnProcess ann)
instance (Eq ann) => Eq (AnProcess ann)
instance (Show ann) => Show (AnProcess ann)

type ProcessName = String -- String used in annotation to identify processes
type ProcessAnnotation = [String]
type Process = AnProcess (Maybe ProcessAnnotation)

-- TODO make compatible with maybe type
paddAnn :: Process -> ProcessAnnotation -> Process
paddAnn (ProcessNull Nothing) ann' = ProcessNull (Just ann')
paddAnn (ProcessComb c Nothing pl pr ) ann' = ProcessComb c (Just ann')  pl pr 
paddAnn (ProcessAction a Nothing p ) ann' = ProcessAction a (Just ann')  p
paddAnn (ProcessNull (Just ann)) ann' = ProcessNull $ Just $ ann `mappend` ann'
paddAnn (ProcessComb c (Just ann) pl pr ) ann' = ProcessComb c (Just $ ann `mappend` ann')  pl pr 
paddAnn (ProcessAction a (Just ann) p ) ann' = ProcessAction a (Just $ ann `mappend` ann')  p

pfoldMap :: Monoid a => (AnProcess ann -> a) -> AnProcess ann -> a
pfoldMap f (ProcessNull an) = f (ProcessNull an)
pfoldMap f (ProcessComb c an pl pr)  = 
        pfoldMap f pl
        `mappend` 
        f (ProcessComb c an pl pr)
        `mappend` 
        pfoldMap f pr
pfoldMap f (ProcessAction a an p)   = 
        pfoldMap f p
        `mappend` 
        f (ProcessAction a an p)
     
prettySapicAction :: SapicAction  -> String                                     -- TODO parser: extend if changes on SapicAction data structure
prettySapicAction action = case action of 
        New n -> "new "++ (show n)
                         

-- help function to generate output string 
prettySapic :: (AnProcess ann) -> String
prettySapic = pfoldMap f 
    where f (ProcessNull _) = "0"
          f _  = "0" -- TODO complete

-- case p of                                                     -- TODO parser: extend if changes on process data structure
--         ProcessParallel p1 p2 -> "(" ++ (prettySapic p1) ++ " || "  ++ (prettySapic p2) ++ ")"
--         ProcessAlternative p1 p2 -> "(" ++ (prettySapic p1) ++ " + "  ++ (prettySapic p2) ++ ")"
--         ProcessNull -> "0"
--         ProcessIdentifier i-> i
--         ProcessRep pr -> "!" ++ (prettySapic pr)
--         PAction s -> prettySapicAction s
--         ProcessOpt s pr -> (prettySapicAction s) ++ "," ++ (prettySapic pr)
     
