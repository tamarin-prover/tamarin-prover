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
import Control.Exception
import Control.Monad.Fresh
import Control.Monad.Catch
import Sapic.Exceptions
import Theory
import Theory.Sapic
import Data.Typeable
import qualified Data.Set              as S
import qualified Extension.Data.Label                as L
import Control.Monad.Trans.FastFresh   ()
import Sapic.Annotation
import Sapic.Facts
import Sapic.Locks
import Sapic.ProcessUtils
import qualified Sapic.Basetranslation as BT
import Sapic.Restrictions
import Sapic.ProgressFunction
import Theory.Text.Pretty


-- Translates the process (singular) into a set of rules and adds them to the theory
translate :: (Monad m, MonadThrow m, MonadCatch m) =>
             Monoid (m (AnProcess ProcessAnnotation)) =>
             OpenTheory
             -> m OpenTheory
translate th = case theoryProcesses th of
      []  -> return th
      [p] -> do
                an_proc <- evalFreshT (annotateLocks (toAnProcess p)) 0
                msr <- trans basetrans an_proc
                th' <- foldM liftedAddProtoRule th msr
                sapic_restrictions <- generateSapicRestrictions restr_option an_proc
                th'' <- foldM liftedAddRestriction th' sapic_restrictions
                return th''
      _   -> throw (MoreThanOneProcess :: SapicException AnnotatedProcess)
  where
    liftedAddProtoRule thy ru = case addProtoRule ru thy of
        Just thy' -> return thy'
        Nothing   -> throwM ((RuleNameExists (render (prettyRuleName ru) ) )  :: SapicException AnnotatedProcess)
    liftedAddRestriction thy rest = case addRestriction rest thy of
        Just thy' -> return thy'
        Nothing   -> throwM ((RestrictionNameExists (render (prettyRestriction rest)))  :: SapicException AnnotatedProcess)
    ops = L.get thyOptions th
    reliChannels = L.get transReliable ops
    trans = if L.get transProgress ops then
                progresstrans (reliChannels)
            else
                noprogresstrans (reliChannels)
    basetrans = if reliChannels then
                    BT.reliableChannelTrans (BT.baseTrans)
                  else
                    BT.baseTrans
    restr_option = RestrictionOptions { hasAccountabilityLemmaWithControl = False -- TODO need to compute this, once we have accountability lemmas
                                      , hasProgress = L.get transProgress ops
                                      , hasReliableChannels = L.get transReliable ops }

  -- TODO This function is not yet complete. This is what the ocaml code
  -- was doing:
  -- let msr =
  --     if input.op.progress
  --     then progresstrans annotated_process
  --     else noprogresstrans annotated_process
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
getInitRule:: AnProcess ann -> AnnotatedRule ann
getInitRule anP = initrule
  where
        initrule = AnnotatedRule (Just "Init") anP [] l a r 0
        l = []
        a = [InitEmpty ]
        r = [State LState [] S.empty]

getMsgId :: AnProcess ann -> AnnotatedRule ann
getMsgId anP = messageidrule
  where
        messageidrule = AnnotatedRule (Just "MessageID-rule") anP []
                    [ Fr  $ varMID [] ] -- prem
                    []                -- act
                    [ MessageIDReceiver [], MessageIDSender [] ]
                    0
-- | Standard translation without progress:
-- | use gen and basetranslation and add a simple Init rule.
noprogresstrans :: (Show ann, MonadCatch m, Typeable ann,
                    Foldable t1, Foldable t2, Foldable t3, GoodAnnotation ann) =>
                    Bool
                    ->(ann
                    -> ProcessPosition
                    -> S.Set a
                    -> m (t1 ([TransFact], [TransAction], [TransFact])),
                    SapicAction
                    -> ann
                    -> ProcessPosition
                    -> S.Set a
                    -> m (t3 ([TransFact], [TransAction], [TransFact]), S.Set a),
                    ProcessCombinator
                    -> ann
                    -> ProcessPosition
                    -> S.Set a
                    -> m (t2 ([TransFact], [TransAction], [TransFact]), S.Set a,
                          S.Set a))
                   -> AnProcess ann -> m [Rule ProtoRuleEInfo]
noprogresstrans msgIDbool basetrans anP = do
    msrs <- gen basetrans anP [] S.empty
    return $ case msgIDbool of
      True -> map (toRule) (initrule:messageidrule:msrs)
      _ -> map (toRule) (initrule:msrs)
    where
          initrule = getInitRule anP
          messageidrule = getMsgId anP

-- | translation with progress:
-- | use gen and basetranslation, but
-- | adds ProgressTo actions where a state-fact is in the premise
-- | adds ProgressFrom actions where a state-fact is in the conclusion
-- | also adds a message id rule
progresstrans :: (Show ann, MonadCatch m, Typeable ann,
                  Foldable t1, Foldable t2, Foldable t3, GoodAnnotation ann) =>
                  Bool
                  ->(ann
                  -> ProcessPosition
                  -> S.Set a
                  -> m (t1 ([TransFact], [TransAction], [TransFact])),
                  SapicAction
                  -> ann
                  -> ProcessPosition
                  -> S.Set a
                  -> m (t3 ([TransFact], [TransAction], [TransFact]), S.Set a),
                  ProcessCombinator
                  -> ann
                  -> ProcessPosition
                  -> S.Set a
                  -> m (t2 ([TransFact], [TransAction], [TransFact]), S.Set a,
                        S.Set a))
                 -> AnProcess ann -> m [Rule ProtoRuleEInfo]
progresstrans msgIDbool basetrans anP = do
    -- pf <- .. generate progress function
    msrs <- gen basetrans anP [] S.empty
    return $ case msgIDbool of
      True -> map (toRule . addProgressFrom . addProgressTo) (initrule:messageidrule:msrs)
      _ -> map (toRule . addProgressFrom . addProgressTo) (initrule:msrs)
      --return $ map (toRule . addProgressFrom . addProgressTo) (initrule:messageidrule:msrs)
    where
          initrule = getInitRule anP
          messageidrule = getMsgId anP
          x =  LVar "x" LSortFresh 0
          map_act_cond p f anrule = -- applys f to (l,a,r) if p prems concls holds
                if p (prems anrule) (concs anrule) then
                    let (l',a',r') = f (position anrule) (prems anrule) (acts anrule) (concs anrule) in
                    anrule { prems = l', acts = a', concs = r'  }
                else
                    anrule
          stateInPrems prems _ = any isNonSemiState prems  --- TODO need to incorporate progress function
          stateInConcls _ concls = any isNonSemiState concls --- TODO need to incorporate progress function, look at children of positon
          addProgressTo = map_act_cond stateInPrems  -- corresponds to step2 (child[12] p) in Firsttranslation.ml
                            (\p l a r ->
                            let q' = p -- TODO q' should be find_from pf p' for p' direct child of p
                            in
                            ( l
                            , ProgressTo p q':a
                            , r
                            ))
          addProgressFrom = map_act_cond stateInConcls  -- corresponds to step3 p in Firsttranslation.ml
                            (\p l a r ->
                            ( Fr(varProgress p):l
                            , ProgressFrom p:a
                            , map (addVarToState $ varProgress p) r
                            ))

-- | Processes through an annotated process and translates every single action
-- | according to trans. It substitutes states by pstates for replication and
-- | makes sure that tildex, list of variables in state is updated for the next
-- | call. It also performs the substituion necessary for NDC
-- | Input:
-- |      three-tuple of algoriths for translation of null processes, actions and combinators
-- |      annotated process
-- |      current position in this process
-- |      tildex, the set of variables in the state
-- gen :: (Typeable ann, Show ann, MonadCatch m ) =>
--         (ann
--          -> ProcessPosition -> t -> [([TransFact], [TransAction], [TransFact])],
--          SapicAction
--          -> ann
--          -> ProcessPosition
--          -> t
--          -> ([([TransFact], [TransAction], [TransFact])], t),
--          ProcessCombinator
--          -> ann
--          -> ProcessPosition
--          -> t
--          -> ([([TransFact], [TransAction], [TransFact])], t, t))
--         -> AnProcess ann -> ProcessPosition -> t -> m ( [AnnotatedRule ann])
gen (trans_null, trans_action, trans_comb) anP p tildex  =
    do
        proc' <- processAt anP p
        case proc' of
            ProcessNull ann -> do
                msrs <- trans_null ann p tildex
                return $ mapToAnnotatedRule proc' msrs
            (ProcessComb NDC _ _ _) ->
               let  subst p_new = map_prems (substStatePos p p_new) in
               do
                   l <- gen trans anP ( p++[1] ) tildex
                   r <- gen trans anP (p++[2]) tildex
                   return $ subst (p++[1]) l ++ subst (p++[2]) r
            (ProcessComb c ann _ _) ->
                do
                (msrs, tildex'1, tildex'2) <- trans_comb c ann p tildex
                msrs_l <- gen trans anP (p++[1]) tildex'1
                msrs_r <- gen trans anP (p++[2]) tildex'2
                return  $
                    mapToAnnotatedRule proc' msrs ++ msrs_l ++ msrs_r
            (ProcessAction  ac ann _) ->
                do
                    (msrs, tildex') <- trans_action ac ann p tildex
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
        toAnnotatedRule proc (l,a,r) = AnnotatedRule Nothing proc p l a r
        mapToAnnotatedRule proc l = -- distinguishes rules by  adding the index of each element to it
            snd $ foldl (\(i,l') r -> (i+1,l' ++ [toAnnotatedRule proc r i] )) (0,[]) l
