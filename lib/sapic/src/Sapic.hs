{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PatternGuards #-}
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
) where
import Control.Exception hiding (catch)
import Control.Monad.Fresh
import Control.Monad.Catch
import Sapic.Exceptions
import Theory
import Theory.Sapic
import Data.Typeable
import Data.Maybe
import qualified Extension.Data.Label                as L
import Control.Monad.Trans.FastFresh   ()
import Sapic.Annotation
import Sapic.SecretChannels
import Sapic.Facts
import Sapic.Locks
import Sapic.ProcessUtils
import qualified Sapic.Basetranslation as BT
import qualified Sapic.ProgressTranslation as PT
import qualified Sapic.ReliableChannelTranslation as RCT
import Sapic.Restrictions
import Theory.Text.Pretty


-- | Translates the process (singular) into a set of rules and adds them to the theory
translate :: (Monad m, MonadThrow m, MonadCatch m) =>
             Monoid (m (AnProcess ProcessAnnotation)) =>
             OpenTheory
             -> m OpenTranslatedTheory
translate th = case theoryProcesses th of
      []  -> if L.get transReliable ops then
                    throwM (ReliableTransmissionButNoProcess :: SapicException AnnotatedProcess)
             else 
                    return (removeSapicItems th)
      [p] -> do
                -- annotate
                an_proc <- evalFreshT (annotateLocks (annotateSecretChannels (propagateNames $ toAnProcess p))) 0
                -- compute initial rules
                (initRule,initTx) <- initialRules an_proc
                -- generate protocol rules, starting from variables in initial tilde x
                protoRule <-  gen (trans an_proc) an_proc [] initTx
                -- add these rules
                th1 <- foldM liftedAddProtoRule th $ map toRule $ initRule ++ protoRule
                -- add restrictions
                sapic_restrictions <- generateSapicRestrictions restr_option an_proc
                th2 <- foldM liftedAddRestriction th1 sapic_restrictions
                -- add heuristic, if not already defined:
                th3 <- return $ fromMaybe th2 (addHeuristic heuristics th2) -- does not overwrite user defined heuristic
                return (removeSapicItems th3)
      _   -> throw (MoreThanOneProcess :: SapicException AnnotatedProcess)
  where
    liftedAddProtoRule thy ru = case addProtoRule ru thy of
        Just thy' -> return thy'
        Nothing   -> throwM (RuleNameExists (render (prettyRuleName ru))  :: SapicException AnnotatedProcess)
    liftedAddRestriction thy rest = case addRestriction rest thy of
        Just thy' -> return thy'
        Nothing   -> throwM (RestrictionNameExists (render (prettyRestriction rest))  :: SapicException AnnotatedProcess)
    ops = L.get thyOptions th
    checkOps (lens,x) 
        | L.get lens ops = Just x
        | otherwise = Nothing
    initialRules anP = foldM (flip ($))  (BT.baseInit anP) --- fold from right to left 
                        $ mapMaybe checkOps [ --- remove if fst element does not point to option that is set
                        (transProgress, PT.progressInit anP)
                      , (transReliable, RCT.reliableChannelInit anP) 
                      ] 
    trans anP = foldr ($) BT.baseTrans 
                        $ mapMaybe checkOps [--- fold from right to left, foldr applies ($) the other way around
                        (transProgress, PT.progressTrans anP)
                      , (transReliable, RCT.reliableChannelTrans )
                      ] 
    -- TODO: in the future, restrictions can also be pushed to the modules of
    -- their respective translations
    restr_option = RestrictionOptions { hasAccountabilityLemmaWithControl = False -- TODO need to compute this, once we have accountability lemmas
                                      , hasProgress = L.get transProgress ops
                                      , hasReliableChannels = L.get transReliable ops }
    heuristics = [SapicRanking]

  -- TODO This function is not yet complete. This is what the ocaml code
  -- was doing:
  -- and predicate_restrictions = print_predicates input.pred
  -- and sapic_restrictions = print_lemmas (generate_sapic_restrictions input.op annotated_process)
  -- in
  -- let msr' = if Lemma.contains_control input.lem (* equivalent to op.accountability *)
  --            then annotate_eventId msr
  --            else msr
  -- in
  -- input.sign ^ ( print_msr msr' ) ^ sapic_restrictions ^
  -- predicate_restrictions ^ lemmas_tamarin
  -- ^ "end"

-- | Processes through an annotated process and translates every single action
-- | according to trans. It substitutes states by pstates for replication and
-- | makes sure that tildex, list of variables in state is updated for the next
-- | call. It also performs the substituion necessary for NDC
-- | Input:
-- |      - three-tuple of algoriths for translation of null processes, actions and combinators
-- |      - annotated process
-- |      - current position in this process
-- |      - tildex, the set of variables in the state
gen :: (Show ann, MonadCatch m, Typeable ann, Foldable t1,
        Foldable t2, Foldable t3) =>
       (ann
        -> ProcessPosition
        -> t4
        -> m (t1 ([TransFact], [TransAction], [TransFact])),
        SapicAction
        -> ann
        -> ProcessPosition
        -> t4
        -> m (t3 ([TransFact], [TransAction], [TransFact]), t4),
        ProcessCombinator
        -> ann
        -> ProcessPosition
        -> t4
        -> m (t2 ([TransFact], [TransAction], [TransFact]), t4, t4))
       -> AnProcess ann -> [Int] -> t4 -> m [AnnotatedRule ann]
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
        toAnnotatedRule proc (l,a,r) = AnnotatedRule Nothing proc (Left p) l a r
        mapToAnnotatedRule proc l = -- distinguishes rules by  adding the index of each element to it
            snd $ foldl (\(i,l') r -> (i+1,l' ++ [toAnnotatedRule proc r i] )) (0,[]) l
        handler:: (Typeable ann, Show ann) => AnProcess ann ->  SapicException ann -> a
        handler anp (ProcessNotWellformed (WFUnboundProto vs)) = throw $ ProcessNotWellformed $ WFUnbound vs anp 
        handler _ e = throw e
