{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
    typeTheory
  , translate
) where
import Control.Exception hiding (catch)
import Control.Monad.Fresh
import Control.Monad.Catch
import Sapic.Exceptions
import Theory
import Theory.Sapic
import Data.Typeable
import Data.Maybe
import qualified Data.Map.Strict as Map
import qualified Data.Set as S
import qualified Data.List as List
import qualified Extension.Data.Label                as L
import Control.Monad.Trans.FastFresh   ()
import Sapic.Annotation
import Sapic.SecretChannels
import Sapic.Facts
import Sapic.Locks
import Sapic.ProcessUtils
import qualified Sapic.Basetranslation as BT
-- import qualified Sapic.ProgressTranslation as PT -- TODO commented out for now
-- import qualified Sapic.ReliableChannelTranslation as RCT
import Theory.Text.Parser

typeProcess :: MonadThrow m => Theory sig c r p1 SapicElement
                        -> Process p2 SapicLVar -> m (Process p2 SapicLVar)
typeProcess th = foldMProcess fNull (lift3 fAct) (lift3 fComb) gAct gComb Map.empty
    where
        lift3 f a b c = return $ f a b c -- compose ternary function with return
        fNull _  = return . ProcessNull
        fAct  a _ (New v)       = insertVar v a
        fAct  a _ (ChIn _ t)    = foldr insertVar a (freesSapicTerm t)
        fAct  a _ (MSR (l,_,r,_)) =  foldr insertVar a (freesSapicFact r List.\\ freesSapicFact l)
        fAct  a _ _             =  a 
        fComb a _ (Lookup _ v) = insertVar v a
        fComb a _ _ = a 
        gAct a' ac ann r = do
                       -- a' is map variables to types
                       -- r is typed subprocess 
                       -- type terms with variables and reconstruct process
            ac' <- traverseTermsAction (typeWith  a') typeWithFact typeWithVar ac
            return $ ProcessAction ac' ann r
        gComb a' c ann rl rr = do
            c' <- traverseTermsComb (typeWith a') typeWithFact typeWithVar c
            return $ ProcessComb c' ann rl rr
        typeWith a' t = do
            (t',_) <- typeWith' a' t
            return t'
        typeWith' a' t 
            | Lit (Var v) <- viewTerm t
            , lvar' <- slvar v
            , Just stype' <- Map.lookup lvar' a' = 
                        return (termViewToTerm $ Lit (Var (SapicLVar lvar' stype')), stype')
            | FApp (NoEq fs) ts   <- viewTerm t 
            , Just (_,intypes,outtype) <- lookupFunctionTypingInfo fs th
            = do 
                ts' <- mapM (typeWith' a') ts
                let interms  = map fst ts'
                let intypes' = map snd ts'
                if intypes' == intypes 
                    then
                        return (termViewToTerm $ FApp (NoEq fs) interms, outtype)
                    else
                        throwM (ProcessNotWellformed (TypingErrorArgument t intypes') :: SapicException AnnotatedProcess)
            | FApp fs ts <- viewTerm t = do  -- list, AC or C symbol: ignore, i.e., assume polymorphic
                ts' <- mapM (typeWith a') ts
                return (termViewToTerm $ FApp fs ts', defaultSapicType) 
                        -- NOTE: this means list,ac,c-symols are polymorphic in input types but not output
            | otherwise = return (t, defaultSapicType) -- TODO no idea how to type here...
        typeWithVar  v -- variables are correctly typed, as we just inserted them 
            | Nothing <- stype v = return $ SapicLVar (slvar v) defaultSapicType
            | otherwise = return v  
        typeWithFact = return -- typing facts is hard because of quantified variables. We skip for now.
        insertVar v a 
               | Nothing <- stype v =  Map.insert (slvar v) defaultSapicType a
               | otherwise          =  Map.insert (slvar v) (stype v) a
        freesSapicTerm = foldMap $ foldMap (: []) -- frees from HasFrees only returns LVars
        freesSapicFact = foldMap $ foldMap freesSapicTerm -- fold over terms in fact and use freesSapicTerm to get list monoid 

typeTheory :: MonadThrow m => Theory sig c r p SapicElement -> m (Theory sig c r p SapicElement)
typeTheory th = mapMProcesses (typeProcess th) th

-- | Translates the process (singular) into a set of rules and adds them to the theory
translate :: (Monad m, MonadThrow m, MonadCatch m) =>
             OpenTheory
             -> m OpenTranslatedTheory
translate th = case theoryProcesses th of
      []  -> if L.get transReliable ops then
                    throwM (ReliableTransmissionButNoProcess :: SapicException AnnotatedProcess)
             else 
                    return (removeSapicItems th)
      [p] -> if allUnique $ pfoldMap bindings p then do
                    -- annotate
                    an_proc <- evalFreshT (annotateLocks (annotateSecretChannels (propagateNames $ toAnProcess p))) 0
                    -- compute initial rules
                    (initRules,initTx) <- initialRules an_proc
                    -- generate protocol rules, starting from variables in initial tilde x
                    protoRule <-  gen (trans an_proc) an_proc [] initTx
                    -- add these rules
                    th1 <- foldM liftedAddProtoRule th $ map toRule $ initRules ++ protoRule
                    -- add restrictions
                    rest<- restrictions an_proc
                    th2 <- foldM liftedAddRestriction th1 rest
                    -- add heuristic, if not already defined:
                    let th3 = fromMaybe th2 (addHeuristic heuristics th2) -- does not overwrite user defined heuristic
                    return (removeSapicItems th3)
                else
                    throw ( ProcessNotWellformed ( WFBoundTwice $ repeater $ pfoldMap bindings p)
                            :: SapicException AnnotatedProcess)
      _   -> throw (MoreThanOneProcess :: SapicException AnnotatedProcess)
  where
    bindings (ProcessComb (Lookup _ v) _ _ _) = [v]
    bindings (ProcessAction (New v) _ _) = [v]
    bindings _ = []

    allUnique = all ( (==) 1 . length) . List.group . List.sort
    repeater  = head . head . filter ((/=) 1 . length) . List.group . List.sort

    ops = L.get thyOptions th
    checkOps lens x   
        | L.get lens ops = Just x
        | otherwise = Nothing

    initialRules anP = foldM (flip ($))  (BT.baseInit anP) --- fold from left to right
                        $ catMaybes [ 
                        -- checkOps transProgress (PT.progressInit anP) -- TODO uncomment
                      -- , checkOps transReliable (RCT.reliableChannelInit anP)
                      ] 
    trans anP = foldr ($) BT.baseTrans  --- fold from right to left, not that foldr applies ($) the other way around compared to foldM
                        $ mapMaybe (uncurry checkOps) [ --- remove if fst element does not point to option that is set
                        -- (transProgress, PT.progressTrans anP) -- TODO uncomment
                      -- , (transReliable, RCT.reliableChannelTrans )
                      ] 
    restrictions:: (MonadThrow m1, MonadCatch m1) => LProcess (ProcessAnnotation LVar) -> m1 [SyntacticRestriction] 
    restrictions anP = foldM (flip ($)) []  --- fold from left to right
                                                                 --- TODO once accountability is supported, substitute True
                                                                 -- with predicate saying whether we need single_session lemma
                                                                 -- need to incorporate lemma2string_noacc once we handle accountability
                                                                -- if op.accountability then
                                                                  --   (* if an accountability lemma with control needs to be shown, we use a 
                                                                  --    * more complex variant of the restritions, that applies them to only one execution *)
                                                                  --   (List.map (bind_lemma_to_session (Msg id_ExecId)) restrs)
                                                                  --   @ (if op.progress then [progress_init_lemma_acc] else [])
                                                                -- else 
                                                                  --   restrs
                                                                  --    @ (if op.progress then [progress_init_lemma] else [])
                        $ [BT.baseRestr anP True] ++
                           mapMaybe (uncurry checkOps) [
                            -- (transProgress, PT.progressRestr anP) -- TODO uncomment
                          -- , (transReliable, RCT.reliableChannelRestr anP) 
                           ]
    heuristics = [SapicRanking]

  -- TODO This function is not yet complete. This is what the ocaml code
  -- was doing:
  -- NOTE: Kevin Morio is working on accountability
  --
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
        handler:: (Typeable ann, Show ann) => LProcess ann ->  SapicException ann -> a
        handler anp (ProcessNotWellformed (WFUnboundProto vs)) = throw $ ProcessNotWellformed $ WFUnbound vs anp 
        handler _ e = throw e
