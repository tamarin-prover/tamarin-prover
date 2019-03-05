{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann and Alexander Dax
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation from Theories with Processes to mrs

module Sapic (
    translate
) where
import Data.Maybe
import Data.Foldable
import Control.Exception
import Control.Monad.Fresh
import Control.Monad.Catch
import Sapic.Exceptions
import Theory
import Theory.Sapic
import Theory.Model.Rule
import Data.Typeable
import qualified Data.Set                   as S
import Control.Monad.Trans.FastFresh
import Sapic.Annotation
import Sapic.Facts
import Sapic.Locks
import Sapic.Exceptions

translate :: (Monad m, MonadThrow m) =>
             Monoid (m (AnProcess ProcessAnnotation)) => 
             OpenTheory
             -> m (OpenTheory)
translate th = case theoryProcesses th of
      [] -> return th
      [p] -> do 
            an_proc <- evalFreshT (annotateLocks (toAnProcess p)) 0
            msr <- noprogresstrans an_proc -- TODO check options to chose progress translation
            th' <- liftedAddProtoRule th testrule
            return th'
      _ -> throw (SomethingBad :: SapicException AnnotatedProcess)
  where
    liftedAddProtoRule thy ru = case addProtoRule ru thy of
        Just thy' -> return thy'
        Nothing   -> throwM (SomethingBad :: SapicException AnnotatedProcess)
        -- fail $ "duplicate rule: " -- ++ render (prettyRuleName ru)
    testrule = Rule (ProtoRuleEInfo (StandRule "lol") [])  [] [] [] []
  -- let msr =  
  --     if input.op.progress 
  --     then progresstrans annotated_process
  --     else noprogresstrans annotated_process 
  -- and lemmas_tamarin = print_lemmas input.lem
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

noprogresstrans anP = 
    initrule : 
    initrule::(gen basetrans anP [] empty)
    where 
          initrule = Rule (ProtoRuleEInfo (StandRule "Init") []) l a r
          l = []
          a = [toFact InitEmpty ] 
          r = [toFact State([],empty)]

gen (trans_null, trans_action, trans_comb) process p tildex  = 
-- Processes through an annotated process and translates every single action
-- according to trans. It substitutes states by pstates for replication and
-- makes sure that tildex, list of variables in state is updated for the next
-- call. It also performs the substituion necessary for NDC 
-- Input: 
    case process_at tree p of
    ProcessNull ann -> trans_null ann 
    (ProcessComb NDC ann pl pr) -> 
       let  l = gen trans tree (1::p) tildex in
       let  r = gen trans tree (2::p) tildex in
       let  subst p_new = map_prems (subststatepos p p_new) in
            subst (1:p) l ++ subst (2:p) r
    (ProcessComb c ann pl pr) -> 
        let (msrs, tildex'1, tildex'2) = trans_comb c ann p tildex in
        msrs 
        ++ gen trans tree (1::p) tildex'1
        ++ gen trans tree (2::p) tildex'2
    (ProcessAction  ac ann pr') ->
        let (msrs, tildex') = trans_action ac ann p tildex in
        msrs 
        ++ gen trans tree (1::p) tildex'
    where
        map_prems f = map (\r -> r { prems = f (prems r) })
        --  Substitute every occurence of  State(p_old,v) with State(p_new,v)
        substStatePos p_old p_new fact
                | (State p_old vs) <- fact = State p_new vs
                | otherwise = fact
        -- substStatePos p_old p_new (x) = x
