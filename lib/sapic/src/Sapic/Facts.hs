{-# LANGUAGE RecordWildCards #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation specific fact types that are translated into LNFacts
module Sapic.Facts (
     TransAction(..)
   , TransFact(..)
   , SpecialPosition(..)
   , AnnotatedRule(..)
   , StateKind(..)
   , isSemiState
   , isNonSemiState
   , addVarToState
   , factToFact
   , actionToFact
   , actionToFactFormula
   , toRule
   , varMID
   , varProgress
   , msgVarProgress
) where
-- import Data.Maybe
-- import Data.Foldable
-- import Control.Exception
-- import Control.Monad.Fresh
-- import Control.Monad.Catch
-- import Sapic.Exceptions
import Theory
import Theory.Text.Parser
import Theory.Sapic
import Theory.Sapic.Print
import Sapic.Annotation
-- import Theory.Model.Rule
-- import Theory.Model.Rule
-- import Data.Typeable
-- import Data.Text
import Data.Char
import qualified Data.Set as S
import Data.Color
-- import Control.Monad.Trans.FastFresh

-- | Facts that are used as actions
data TransAction =  InitEmpty
  | InitId
  | StopId
  | EventEmpty
  | EventId
  | PredicateA LNFact
  | NegPredicateA LNFact
  | ProgressFrom ProcessPosition
  | ProgressTo ProcessPosition ProcessPosition
  | Listen ProcessPosition LVar
  | Receive ProcessPosition SapicTerm
  | IsIn SapicTerm LVar
  | IsNotSet SapicTerm
  | InsertA SapicTerm SapicTerm
  | DeleteA SapicTerm
  | ChannelIn SapicTerm
  | Send ProcessPosition SapicTerm
  | LockUnnamed SapicTerm LVar
  | LockNamed SapicTerm LVar
  | UnlockUnnamed SapicTerm LVar
  | UnlockNamed SapicTerm LVar
  | TamarinAct LNFact

-- | Facts that are used as premises and conclusions.
-- Most important one is the state, containing the variables currently
-- bound. Persistant variant for replication, and linear for all other
-- actions. Semistates are used in rules where a SAPIC step might take more
-- than one MSR step, i.e., messages over private channels.
data StateKind  = LState | PState | LSemiState | PSemiState
data TransFact =  Fr LVar | In SapicTerm
            | Out SapicTerm
            | Message SapicTerm SapicTerm
            | Ack SapicTerm SapicTerm
            | State StateKind ProcessPosition (S.Set LVar)
            | MessageIDSender ProcessPosition
            | MessageIDReceiver ProcessPosition
            | TamarinFact LNFact

data SpecialPosition = InitPosition -- initial position, is logically the predecessor of []
                     | NoPosition -- no real position, e.g., message id rule

-- | annotated rules know:
data AnnotatedRule ann = AnnotatedRule {
      processName  :: Maybe String    -- optional name for rules that are not bound to a process, e.g., Init
    , process      :: AnProcess ann   -- process this rules was generated for
    , position     :: Either ProcessPosition SpecialPosition -- position of this process in top-level process
    , prems        :: [TransFact]     -- Facts/actions to be translated
    , acts         :: [TransAction]
    , concs        :: [TransFact]
    , index        :: Int             -- Index to distinguish multiple rules originating from the same process
}

isSemiState :: StateKind -> Bool
isSemiState LState = False
isSemiState PState = False
isSemiState LSemiState = True
isSemiState PSemiState = True

isNonSemiState :: TransFact -> Bool
isNonSemiState (State kind _ _) = not $ isSemiState kind
isNonSemiState _ = False

addVarToState :: LVar -> TransFact -> TransFact
addVarToState v' (State kind pos vs)  = State kind pos (v' `S.insert` vs)
addVarToState _ x = x

multiplicity :: StateKind -> Multiplicity
multiplicity LState = Linear
multiplicity LSemiState = Linear
multiplicity PState = Persistent
multiplicity PSemiState = Persistent

-- | map f to the name of a fact
mapFactName :: (String -> String) -> Fact t -> Fact t
mapFactName f fact =  fact { factTag = f' (factTag fact) }
    where f' (ProtoFact m s i) = ProtoFact m (f s) i
          f' ft = ft

-- Optimisation: have a diffent fact name for every (unique) locking variable
lockFactName :: LVar -> String
lockFactName v = "Lock_"++ show (lvarIdx v)

unlockFactName :: LVar -> String
unlockFactName v = "Unlock_" ++ show (lvarIdx v)

lockPubTerm :: LVar -> NTerm v
lockPubTerm = pubTerm . show . lvarIdx

varNameProgress :: ProcessPosition -> String
varNameProgress p = "prog_" ++ prettyPosition p

varProgress :: ProcessPosition -> LVar
varProgress p = LVar n s i
    where n = varNameProgress p
          s = LSortFresh
          i = 0

msgVarProgress :: ProcessPosition -> LVar
msgVarProgress p = LVar n s i
    where n = varNameProgress p
          s = LSortMsg
          i = 0

varMsgId :: ProcessPosition -> LVar
varMsgId p = LVar n s i
    where n = "mid_" ++ prettyPosition p
          s = LSortFresh
          i = 0

-- actionToFact :: TransAction -> Fact t
actionToFact :: TransAction -> Fact (VTerm Name LVar)
actionToFact InitEmpty = protoFact Linear "Init" []
  -- | Not implemented yet: progress
  -- | StopId
  -- | EventEmpty
  -- | EventId
  -- | ProgressFrom ProcessPosition
  -- | ProgressTo ProcessPosition ProcessPosition
  -- | Listen ProcessPosition LVar
  -- | Receive ProcessPosition SapicTerm
actionToFact (Send p t) = protoFact Linear "Send" [varTerm $ varMsgId p ,t]
actionToFact (Receive p t) = protoFact Linear "Receive" [varTerm $ varMsgId p ,t]
actionToFact (IsIn t v)   =  protoFact Linear "IsIn" [t,varTerm v]
actionToFact (IsNotSet t )   =  protoFact Linear "IsNotSet" [t]
actionToFact (InsertA t1 t2)   =  protoFact Linear "Insert" [t1,t2]
actionToFact (DeleteA t )   =  protoFact Linear "Delete" [t]
actionToFact (ChannelIn t)   =  protoFact Linear "ChannelIn" [t]
actionToFact (PredicateA f)   =  mapFactName (\s -> "Pred_" ++ s) f
actionToFact (NegPredicateA f)   =  mapFactName (\s -> "Pred_Not_" ++ s) f
actionToFact (LockNamed t v)   = protoFact Linear (lockFactName v) [lockPubTerm v,varTerm v, t ]
actionToFact (LockUnnamed t v)   = protoFact Linear "Lock" [lockPubTerm v, varTerm v, t ]
actionToFact (UnlockNamed t v) = protoFact Linear (unlockFactName v) [lockPubTerm v,varTerm v,t]
actionToFact (UnlockUnnamed t v) = protoFact Linear "Unlock" [lockPubTerm v,t,varTerm v]
actionToFact (ProgressFrom p) = protoFact Linear ("ProgressFrom_"++prettyPosition p) [varTerm $ varProgress p]
actionToFact (ProgressTo p pf) = protoFact Linear ("ProgressTo_"++prettyPosition p) $ [varTerm $ varProgress pf]
actionToFact (TamarinAct f) = f

toFreeMsgVariable :: LVar -> BVar LVar
toFreeMsgVariable (LVar name LSortFresh id') = Free $ LVar name LSortMsg id'
toFreeMsgVariable v = Free $ v

actionToFactFormula :: TransAction -> Fact (Term (Lit Name (BVar LVar)))
actionToFactFormula = fmap (fmap $ fmap toFreeMsgVariable) . actionToFact 

-- | Term with variable for message id. Uniqueness ensured by process position.
varMID :: ProcessPosition -> LVar
varMID p = LVar n s i
    where n = "mid_" ++ prettyPosition p
          s = LSortFresh
          i = 0 -- This is the message index.
                -- We could also compute it from the position as before,
                -- but I don't see an advantage (yet)

factToFact :: TransFact -> Fact SapicTerm
factToFact (Fr v) = freshFact $ varTerm (v)
factToFact (In t) = inFact t
factToFact (Out t) = outFact t
factToFact (Message t t') = protoFact Linear "Message" [t, t']
factToFact (Ack t t') = protoFact Linear "Ack" [t, t']
factToFact (MessageIDSender p) = protoFact Linear "MID_Sender" [ varTerm $ varMID p ]
factToFact (MessageIDReceiver p) = protoFact Linear "MID_Receiver" [ varTerm$ varMID p ]
factToFact (State kind p vars) = protoFact (multiplicity kind) (name kind ++ "_" ++ prettyPosition p) ts
    where
        name k = if isSemiState k then "semistate" else "state"
        ts = map varTerm (S.toList vars)
factToFact (TamarinFact f) = f

prettyEitherPositionOrSpecial:: Either ProcessPosition SpecialPosition -> String
prettyEitherPositionOrSpecial (Left pos) = prettyPosition pos
prettyEitherPositionOrSpecial (Right InitPosition) = "Init"
prettyEitherPositionOrSpecial (Right NoPosition) = ""


toRule :: GoodAnnotation ann => AnnotatedRule ann -> Rule ProtoRuleEInfo
toRule AnnotatedRule{..} = -- this is a Record Wildcard
          Rule (ProtoRuleEInfo (StandRule name) attr) l r a (newVariables l r)
          where
            name = case processName of
                Just s -> s
                Nothing -> stripNonAlphanumerical (prettySapicTopLevel process)
                         ++ "_" ++ show index ++ "_"
                         ++ prettyEitherPositionOrSpecial position
            attr = [ RuleColor $ RGB 0.3 0.3 0.3 -- TODO compute color from processnames
                   , Process $ toProcess process]
            l = map factToFact prems
            a = map actionToFact acts
            r = map factToFact concs
            stripNonAlphanumerical = filter (\x -> isAlpha x)
