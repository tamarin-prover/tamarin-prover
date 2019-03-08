{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveTraversable       #-}
{-# LANGUAGE DeriveAnyClass       #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Data types for SAPIC processes in theories
module Theory.Sapic (
    Process
    , ProcessCombinator(..)
    , AnProcess(..)
    , SapicAction(..)
    , SapicTerm
    , paddAnn
    , pfoldMap
    , prettySapic
    , prettySapicAction
    , prettySapicComb
    , prettySapicTopLevel
    , ProcessPosition
    , prettyPosition
    , lhs
    , rhs
) where

import           Data.Binary
-- import           Data.Monoid                         (Sum(..))
-- import qualified Data.Set                            as S
import           GHC.Generics                        (Generic)
-- import           Extension.Data.Label                
-- import qualified Extension.Data.Label                as L
import           Control.Parallel.Strategies
import Data.Foldable

import           Theory.Model
-- import           Term.LTerm
import           Theory.Text.Pretty

-- | A process data structure

-- | In general, terms we use in the translation have logical veriables
type SapicTerm = LNTerm

-- | Actions are parts of the process that maybe connected with ";"
data SapicAction = 
                   Rep
                 | New LVar
                 | ChIn (Maybe SapicTerm) SapicTerm
                 | ChOut (Maybe SapicTerm) SapicTerm
                 | Insert SapicTerm SapicTerm
                 | Delete SapicTerm 
                 | Lock SapicTerm 
                 | Unlock SapicTerm 
                 | Event LNFact 
                 | MSR ([LNFact], [LNFact], [LNFact])
        deriving( Show, Eq, Ord, Generic, NFData, Binary )

-- | When the process tree splits, it is connected with one of these connectives
data ProcessCombinator = Parallel | NDC | Cond LNFact 
        | CondEq SapicTerm SapicTerm | Lookup SapicTerm LVar
    deriving (Generic, NFData, Binary, Show, Eq)

-- | The process tree is terminated with null processes, and either splits
-- (parallel and other combinators) or describes a sequence of actions with
-- only one daughter
data AnProcess ann =  
        ProcessNull ann
    |   ProcessComb ProcessCombinator ann (AnProcess ann) (AnProcess ann)
    -- |   ProcessIdentifier String ann 
    |   ProcessAction SapicAction ann (AnProcess ann)
     deriving(Generic )
instance (Ord ann) => Ord (AnProcess ann)
deriving instance (NFData ann) => NFData (AnProcess ann)
deriving instance (Binary ann) => Binary (AnProcess ann)
deriving instance (Eq ann) => Eq (AnProcess ann)
deriving instance (Show ann) => Show (AnProcess ann)
deriving instance (Semigroup ann) => Semigroup (AnProcess ann)
deriving instance (Monoid ann) => Monoid (AnProcess ann)
deriving instance Foldable (AnProcess)
deriving instance Traversable (AnProcess)
instance Functor AnProcess where
    fmap f (ProcessNull an) = ProcessNull (f an)
    fmap f (ProcessComb c an pl pr)  = ProcessComb c (f an) (fmap f pl) (fmap f pr)
    fmap f (ProcessAction a an p)   =  ProcessAction a (f an) (fmap f p)


-- | After parsing, the process is already annotated wth a list of process
-- identifiers, describing the sequence of let P = ... constructs that were
-- used to describe this. This will be helpful to recognise protocols roles and
-- visualise them.
type ProcessName = String -- String used in annotation to identify processes
type ProcessAnnotation = [ProcessName]
type Process = AnProcess ProcessAnnotation
type ProcessPosition = [Int]

lhs  = [1] :: ProcessPosition
rhs  = [2] :: ProcessPosition
-- rhs :: ProcessPosition = 2

prettyPosition:: ProcessPosition -> String
prettyPosition = foldl (\ s n -> s ++ show n ) ""

-- | Add another element to the existing annotations, e.g., yet another identifier.
paddAnn :: Process -> ProcessAnnotation -> Process
paddAnn (ProcessNull ann) ann' = ProcessNull $ ann `mappend` ann'
paddAnn (ProcessComb c ann pl pr ) ann' = ProcessComb c (ann `mappend` ann')  pl pr 
paddAnn (ProcessAction a ann p ) ann' = ProcessAction a (ann `mappend` ann')  p

-- | folding on the process tree, used, e.g., for printing
pfoldMap :: Monoid a => (AnProcess ann -> a) -> AnProcess ann -> a
pfoldMap f (ProcessNull an) = f (ProcessNull an)
pfoldMap f (ProcessComb c an pl pr)  = 
        pfoldMap f pl
        `mappend` 
        f (ProcessComb c an pl pr)
        `mappend` 
        pfoldMap f pr
pfoldMap f (ProcessAction a an p)   = 
        f (ProcessAction a an p)
        `mappend` 
        pfoldMap f p

     
prettySapicAction :: SapicAction  -> String
prettySapicAction (New n) = "new "++ show n
prettySapicAction Rep  = "!"
prettySapicAction (ChIn (Just t1) t2 )  = "in(" ++ render (prettyLNTerm t1) ++ "," ++ render ( prettyLNTerm t2) ++ ")"
prettySapicAction (ChIn Nothing t2 )  = "in(" ++ render (prettyLNTerm t2) ++ ")"
prettySapicAction (ChOut (Just t1) t2 )  = "out(" ++ render (prettyLNTerm t1) ++ "," ++ render (prettyLNTerm t2) ++ ")"
prettySapicAction (ChOut Nothing t2 )  = "out(" ++ render (prettyLNTerm t2) ++ ")"
prettySapicAction (Insert t1 t2)  = "insert " ++ render (prettyLNTerm t1) ++ "," ++ render (prettyLNTerm t2)
prettySapicAction (Delete t )  = "delete " ++ render (prettyLNTerm t)
prettySapicAction (Lock t )  = "lock " ++ render (prettyLNTerm t)
prettySapicAction (Unlock t )  = "unlock " ++ render (prettyLNTerm t)
prettySapicAction (Event a )  = "unlock " ++ render (prettyLNFact a)
prettySapicAction (MSR (p,a,c)) = render $ prettyRule p a c

prettySapicComb :: ProcessCombinator -> [Char]
prettySapicComb Parallel = "|"
prettySapicComb NDC = "+"
prettySapicComb (Cond a) = "if "++ render (prettyLNFact a)
prettySapicComb (CondEq t t') = "if "++ p t ++ "=" ++ p t'
                                    where p = render . prettyLNTerm
prettySapicComb (Lookup t v) = "lookup "++ p t ++ "as" ++ show v
                                    where p = render . prettyLNTerm

-- helper function to generate output string 
-- TODO At the moment, the process structure is not used to properly print parenthesis. Should do it, but then we cannot use pfoldMap anymore.
prettySapic :: AnProcess ann -> String
prettySapic = pfoldMap f 
    where f (ProcessNull _) = "0"
          f (ProcessComb c _ _ _)  = prettySapicComb c 
          f (ProcessAction Rep _ _)  = prettySapicAction Rep 
          f (ProcessAction a _ _)  = prettySapicAction a ++ ";"

prettySapicTopLevel :: AnProcess ann -> String
prettySapicTopLevel (ProcessNull _) = "0"
prettySapicTopLevel (ProcessComb c _ _ _)  = prettySapicComb c 
prettySapicTopLevel (ProcessAction Rep _ _)  = prettySapicAction Rep 
prettySapicTopLevel (ProcessAction a _ _)  = prettySapicAction a ++ ";"

