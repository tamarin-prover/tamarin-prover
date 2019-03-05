-- |
-- Copyright   : (c) 2019 Robert Künnemann and Alexander Dax
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- TODO
module Sapic.Facts (
     TransAction(..)
   , TransFact(..)
   , AnnotatedRule(..)
   , StateKind(..)
) where
-- import Data.Maybe
-- import Data.Foldable
-- import Control.Exception
-- import Control.Monad.Fresh
-- import Control.Monad.Catch
-- import Sapic.Exceptions
import Theory
import Theory.Sapic
import Sapic.Annotation
import Theory.Model.Rule
-- import Theory.Model.Rule
-- import Data.Typeable
import Data.Set
-- import Control.Monad.Trans.FastFresh

data TransAction =  InitEmpty
  | InitId
  | StopId
  | EventEmpty
  | EventId
  | Predicate LNFact
  | NegPredicate LNFact
  | ProgressFrom Position 
  | ProgressTo Position Position
  | Listen Position LVar 
  | Receive Position SapicTerm
  | Send Position SapicTerm
  | TamarinAct LNFact

data StateKind  = LState | PState | LSemiState | PSemiState

data TransFact = K SapicTerm | Fr LVar | In SapicTerm 
            | Out SapicTerm
            | Message SapicTerm SapicTerm
            | Ack SapicTerm SapicTerm
            | State StateKind Position (Set LVar)
            | MessageIDSender Position
            | MessageIDReceiver Position
            | TamarinFact LNFact

data AnnotatedRule ann = AnnotatedRule { 
      processName  :: Maybe String
    , process      :: AnProcess ann
    , position     :: Position
    , prems        :: [LNFact]
    , acts         :: [LNFact]  
    , concs        :: [LNFact]
}

