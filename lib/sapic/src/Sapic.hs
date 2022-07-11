{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DoAndIfThenElse #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann and Alexander Dax
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation from Theories with Processes to multiset rewrite rules

module Sapic (
translate
, module Sapic.Typing
, module Sapic.Warnings
, ) where

import Prelude hiding ((.),id)
import Control.Category ( Category(id, (.)) )
import Control.Exception hiding (catch)
import Control.Monad.Fresh
import Control.Monad.Catch
import Theory
import Theory.Sapic
import Data.Typeable
import Data.Maybe
import qualified Data.Set as S
import Extension.Data.Label
import Control.Monad.Trans.FastFresh   ()
import Sapic.Exceptions
import Sapic.Annotation
import Sapic.SecretChannels
import Sapic.Compression
import Sapic.Report
import Sapic.Facts
import Sapic.Locks
import Sapic.ProcessUtils
import Sapic.LetDestructors
import Sapic.Typing
import Sapic.States
import qualified Sapic.Basetranslation as BT
import qualified Sapic.ProgressTranslation as PT
import qualified Sapic.ReliableChannelTranslation as RCT
import Theory.Text.Parser
import Sapic.Warnings

-- | Translates the process (singular) into a set of rules and adds them to the theory
translate :: (Monad m, MonadThrow m, MonadCatch m) =>
             OpenTheory -> m OpenTheory
translate th = case theoryProcesses th of
      []  -> if get transReliable ops then
               throwM (ReliableTransmissionButNoProcess :: SapicException AnnotatedProcess)
             else
               return th
      [p] -> do
                -- annotate
                an_proc_pre <- translateLetDestr sigRules
                  $ checkOps' transReport translateTermsReport
                  $ checkOps' stateChannelOpt annotatePureStates
                  $ annotateSecretChannels
                  $ propagateNames
                  $ toAnProcess p
                an_proc <- evalFreshT (annotateLocks an_proc_pre) 0
                -- compute initial rules
                (initRules,initTx) <- 
                             checkOps transReport (reportInit an_proc)
                        =<<  checkOps transReliable (RCT.reliableChannelInit an_proc)
                        =<<  checkOps transProgress (PT.progressInit an_proc)
                             (BT.baseInit an_proc)
                -- generate protocol rules, starting from variables in initial tilde x
                protoRule <-  gen (trans an_proc) an_proc [] initTx
                -- apply path compression
                eProtoRule <- pathComp $ map toRule (initRules ++ protoRule)
                -- add these rules
                th1 <- foldM liftedAddProtoRule th $ map (`OpenProtoRule` []) eProtoRule
                -- add restrictions
                rest<- checkOps transReliable (RCT.reliableChannelRestr an_proc)
                     =<<  checkOps transProgress (PT.progressRestr an_proc)
                     =<<  BT.baseRestr an_proc needsInEvRes True []
                th2 <- foldM liftedAddRestriction th1 rest
                -- add heuristic, if not already defined by user
                let th3 = fromMaybe th2 (addHeuristic [SapicRanking] th2)
                -- for state optimisation: force special facts  to be injective
                let th4 = checkOps' stateChannelOpt (setforcedInjectiveFacts (S.fromList [pureStateFactTag, pureStateLockFactTag])) th3
                return th4
      _   -> throw (MoreThanOneProcess :: SapicException AnnotatedProcess)
  where
    ops = get thyOptions th
    checkOps l x
        | get l ops = x
        | otherwise = return
    checkOps' l x
        | get l ops = x
        | otherwise = id
    pathComp r =
      if get transProgress ops then return r
      else pathCompression (get compressEvents ops) r
    sigRules =  stRules (get (sigpMaudeSig . thySignature) th)
    trans anP = checkOps' transProgress (PT.progressTrans anP)
              $ checkOps' transReliable RCT.reliableChannelTrans
              $ BT.baseTrans (get asynchronousChannels ops) needsInEvRes
    needsInEvRes = any lemmaNeedsInEvRes (theoryLemmas th)

-- | Processes through an annotated process and translates every single action
-- | according to trans. It substitutes states by pstates for replication and
-- | makes sure that tildex, list of variables in state is updated for the next
-- | call. It also performs the substituion necessary for NDC
-- | Input:
-- |      - three-tuple of algoriths for translation of null processes, actions and combinators
-- |      - annotated process
-- |      - current position in this process
-- |      - tildex, the set of variables in the state
gen :: (MonadCatch m) =>
        (BT.TransFNull (m BT.TranslationResultNull),
         BT.TransFAct (m BT.TranslationResultAct),
         BT.TransFComb (m BT.TranslationResultComb))
       -> LProcess (ProcessAnnotation LVar) -> ProcessPosition -> S.Set LVar -> m [AnnotatedRule (ProcessAnnotation LVar)]
gen (trans_null, trans_action, trans_comb) anP p tildex  =
    do
        proc' <- processAt anP p
        case proc' of
            ProcessNull ann -> do
                msrs <- catch (trans_null ann p tildex) (handler proc')
                return $ mapToAnnotatedRule proc' msrs
            (ProcessComb NDC _ _ _) ->
               let  subst p_old = map_prems (substStatePos p_old p) in
               do
                   l <- gen trans anP ( p++[1] ) tildex
                   r <- gen trans anP (p++[2]) tildex
                   return $ subst (p++[1]) l ++ subst (p++[2]) r
            (ProcessComb c ann _ _) ->
                do
                (msrs, tildex'1, tildex'2) <- catch (trans_comb c ann p tildex) (handler proc')
                msrs_l <- gen trans anP (p++[1]) tildex'1
                msrs_r <- gen trans anP (p++[2]) tildex'2
                return  $
                    mapToAnnotatedRule proc' msrs ++ msrs_l ++ msrs_r
            (ProcessAction  ac ann _) ->
                do
                    (msrs, tildex') <- catch (trans_action ac ann p tildex) (handler proc')
                    msr' <-  gen trans anP (p++[1]) tildex'
                    return $ mapToAnnotatedRule proc' msrs ++ msr'
    where
        map_prems f = map (\r -> r { prems = map f (prems r) })
        --  Substitute every occurence of  State(p_old,v) with State(p_new,v)
        substStatePos p_old p_new fact
             | (State s p' vs) <- fact, p'==p_old, not $ isSemiState s = State LState p_new vs
             | otherwise = fact
        trans = (trans_null, trans_action, trans_comb)
        -- convert prems, acts and concls generated for current process
        -- into annotated rule
        toAnnotatedRule proc (l,a,r,res) = AnnotatedRule Nothing proc (Left p) l a r res
        mapToAnnotatedRule proc l = -- distinguishes rules by  adding the index of each element to it
            snd $ foldl (\(i,l') r -> (i+1,l' ++ [toAnnotatedRule proc r i] )) (0,[]) l
        handler:: (Typeable ann, Show ann) => LProcess ann ->  WFerror -> a
        handler anp (WFUnbound vs) = throw $ ProcessNotWellformed (WFUnbound vs) (Just anp)
        handler _ e = throw e


isPosNegFormula :: LNFormula -> (Bool, Bool)
isPosNegFormula fm = case fm of
    TF  _            -> (True, True)
    Ato (Action _ f) -> isActualKFact $ factTag f
    Ato _            -> (True, True)
    Not p            -> swap $ isPosNegFormula p
    Conn And p q     -> isPosNegFormula p `and2` isPosNegFormula q
    Conn Or  p q     -> isPosNegFormula p `and2` isPosNegFormula q
    Conn Imp p q     -> isPosNegFormula $ Not p .||. q
    Conn Iff p q     -> isPosNegFormula $ p .==>. q .&&. q .==>. p
    Qua  _   _ p     -> isPosNegFormula p
    where
      isActualKFact (ProtoFact _ "K" _) = (True, False)
      isActualKFact _ = (True, True)

      and2 (x, y) (p, q) = (x && p, y && q)
      swap (x, y) = (y, x)

-- Checks if the lemma is in the fragment of formulas for which the resInEv restriction is needed.
lemmaNeedsInEvRes :: Lemma p -> Bool
lemmaNeedsInEvRes lem = case (get lTraceQuantifier lem, isPosNegFormula $ get lFormula lem) of
  (AllTraces,   (_, True))     -> False -- L- for all-traces
  (ExistsTrace, (True, _))     -> False -- L+ for exists-trace
  (ExistsTrace, (False, True)) -> True  -- L- for exists-trace
  (AllTraces,   (True, False)) -> True  -- L+ for all-traces
  _                            -> True  -- not in L- and L+
