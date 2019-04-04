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
import Data.Maybe
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
             -> m OpenTranslatedTheory
translate th = case theoryProcesses th of
      []  -> return (removeSapicItems th)
      [p] -> do
                an_proc <- evalFreshT (annotateLocks (toAnProcess p)) 0
                -- add rules
                msr <- trans basetrans an_proc
                th1 <- foldM liftedAddProtoRule th (initialRules an_proc ++  msr)
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
    addIf True l  = l
    addIf False _ = []
    initialRules anP  =  map toRule $ 
                         getInitRule anP : addIf (L.get transReliable ops) [getMsgId anP]
    trans = if L.get transProgress ops then
                progresstrans 
            else
                noprogresstrans 
    basetrans = if L.get transReliable ops then
                    BT.reliableChannelTrans BT.baseTrans
                  else
                    BT.baseTrans
    restr_option = RestrictionOptions { hasAccountabilityLemmaWithControl = False -- TODO need to compute this, once we have accountability lemmas
                                      , hasProgress = L.get transProgress ops
                                      , hasReliableChannels = L.get transReliable ops }
    heuristics = [SapicRanking]


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
                    (ann
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
noprogresstrans basetrans anP = do
    msrs <- gen basetrans anP [] S.empty
    return $ map toRule msrs

-- | translation with progress:
-- | use gen and basetranslation, but
-- | adds ProgressTo actions where a state-fact is in the premise
-- | adds ProgressFrom actions where a state-fact is in the conclusion
-- | also adds a message id rule
progresstrans :: (Show ann, MonadCatch m, Typeable ann,
                  Foldable t1, Foldable t2, Foldable t3, GoodAnnotation ann) =>
                  (ann
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
progresstrans basetrans anP = do
    msrs <- gen basetrans anP [] S.empty
    dom_pf <- pfFrom anP
    inv_pf <- pfInv anP
    return $ map (toRule . (addProgressFrom dom_pf) . (addProgressTo inv_pf)) msrs
    where
          -- x =  LVar "x" LSortFresh 0
          map_act f anrule = let (l',a',r') = f (position anrule) (prems anrule) (acts anrule) (concs anrule) in
                    anrule { prems = l', acts = a', concs = r'  }
          stateInPrems  = any isNonSemiState . prems
          addProgressTo' q p l a r  =
                            ( l
                            , ProgressTo p q:a
                            , r)
          addProgressTo inv anrule -- corresponds to step2 (child[12] p) in Firsttranslation.ml
                                   -- if one of the direct childen of anrule is in the range of the pf
                                   --  it has an inverse. We thus add ProgressTo to each such rule
                                   --  that has the *old* state in the premise (we
                                   --  don't want to move into Semistates too
                                   --  early). ProgressTo is annotated with the
                                   --  inverse of the child's position, for
                                   --  verification speedup.
            | stateInPrems anrule, Just q <- inv (rhsP (position anrule)) = map_act (addProgressTo' q) anrule
            | stateInPrems anrule, Just q <- inv (lhsP (position anrule)) = map_act (addProgressTo' q) anrule
            | otherwise                                                  = anrule
          stateInConcls = any isNonSemiState . prems
          addProgressFrom dom' anrule
            | stateInConcls anrule,  (position anrule) `S.member` dom' =
                    map_act (\p l a r ->
                            ( Fr(varProgress p):l
                            , ProgressFrom p:a
                            , map (addVarToState $ varProgress p) r
                            )) anrule
            | otherwise  = anrule

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
                msrs <- trans_null ann p tildex
                return $ mapToAnnotatedRule proc' msrs
            (ProcessComb NDC _ _ _) ->
               let  subst p_old = map_prems (substStatePos p_old p) in
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
