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
import Theory.Sapic.Process
import Data.Typeable
import Data.Maybe
import qualified Data.Map.Strict as Map
import qualified Data.Set as S
import qualified Data.Foldable as F
import qualified Extension.Data.Label                as L
import Control.Monad.Trans.FastFresh   ()
import Sapic.Annotation
import Sapic.SecretChannels
import Sapic.Compression
import Sapic.Report
import Sapic.Facts
import Sapic.Locks
import Sapic.ProcessUtils
import Sapic.LetDestructors
import Sapic.Bindings
-- import Sapic.States (state optimisation disabled currently)
import qualified Sapic.Basetranslation as BT
import qualified Sapic.ProgressTranslation as PT
import qualified Sapic.ReliableChannelTranslation as RCT
import Theory.Text.Parser
import Control.Monad.Trans.State.Lazy


data TypingEnvironment = TypingEnvironment {
        vars :: Map.Map LVar SapicType
    ,   funs :: ()
}

-- typeProcess :: (MonadThrow m, Monoid ann, GoodAnnotation ann) => Theory sig c r p1 SapicElement
--                         -> Process ann SapicLVar -> m (Process ann SapicLVar)
typeProcess :: (GoodAnnotation a, MonadThrow m) => Theory sig c r p SapicElement -> Process a SapicLVar -> m (Process a SapicLVar)
typeProcess th p = evalStateT (foldMProcess fNull fAct fComb gAct gComb p) initstate
    where
        -- initial state
        initstate = TypingEnvironment{ vars = Map.empty, funs = () }
        -- fNull/fAcc/fComb collect variables that are bound when going downwards
        fNull ann  = return (ProcessNull ann)
        fAct  ann ac       = F.traverse_ insertVar (bindingsAct ann ac)
        fComb ann c        = F.traverse_ insertVar (bindingsComb ann c)
        -- gAct/gComb reconstruct process tree assigning types to the terms
        gAct ac ann r = do -- r is typed subprocess
            ac' <- traverseTermsAction typeWith typeWithFact typeWithVar ac
            return (ProcessAction ac' ann r)
        gComb c ann rl rr = do
            c' <- traverseTermsComb typeWith typeWithFact typeWithVar c
            return $ ProcessComb c' ann rl rr
        typeWith t = do
            a' <- gets vars
            (t',_) <- typeWith' a' t
            return t'
        typeWith' a' t
            | Lit (Var v) <- viewTerm t
            , lvar' <- slvar v
            , Just stype' <- Map.lookup lvar' a'
          =
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
                ts' <- mapM typeWith ts
                return (termViewToTerm $ FApp fs ts', defaultSapicType)
                        -- NOTE: this means list,ac,c-symols are polymorphic in input types but not output
            | otherwise = return (t, defaultSapicType) -- TODO no idea how to type here...
        typeWithVar  v -- variables are correctly typed, as we just inserted them
            | Nothing <- stype v = return $ SapicLVar (slvar v) defaultSapicType
            | otherwise = return v
        typeWithFact = return -- typing facts is hard because of quantified variables. We skip for now.
        insertVar v = do
            te <- get
            case Map.lookup (slvar v) (vars te) of
                Just _ -> throwM (ProcessNotWellformed ( WFBoundTwice v ) :: SapicException AnnotatedProcess)
                Nothing -> put $te { vars = Map.insert (slvar v) (maybeToDefault $ stype v) (vars te)}
        maybeToDefault Nothing   = defaultSapicType -- not quite the same as maybe, different type
        maybeToDefault something = something

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

      [p] -> do -- annotate
                typedP <- typeProcess th p
                an_proc_pre <- translateLetDestr sigRules
                  $ translateReport
--                  $ annotatePureStates
                  $ annotateSecretChannels
                  $ propagateNames
                  $ toAnProcess typedP
                an_proc <- evalFreshT (annotateLocks an_proc_pre) 0
                -- compute initial rules
                (initRules,initTx) <- initialRules an_proc
                -- generate protocol rules, starting from variables in initial tilde x
                protoRule <-  gen (trans an_proc) an_proc [] initTx
                -- add these rules
                eProtoRule <- pathCompression $ map toRule (initRules ++ protoRule)

                th1 <- foldM liftedAddProtoRule th $ map (`OpenProtoRule` []) eProtoRule
                -- add restrictions
                rest<- restrictions an_proc protoRule
                th2 <- foldM liftedAddRestriction th1 rest
                -- add heuristic, if not already defined:
                let th3 = fromMaybe th2 (addHeuristic heuristics th2) -- does not overwrite user defined heuristic
                return (removeSapicItems th3)
      _   -> throw (MoreThanOneProcess :: SapicException AnnotatedProcess)
  where
    ops = L.get thyOptions th
    translateReport anp =
      if L.get transReport ops then
        translateTermsReport anp
      else
        anp
    sigRules =  stRules (L.get sigpMaudeSig (L.get thySignature th))
    checkOps lens x
        | L.get lens ops = Just x
        | otherwise = Nothing
    initialRules anP = foldM (flip ($))  (BT.baseInit anP) --- fold from left to right
                        $ catMaybes [
                        checkOps transProgress (PT.progressInit anP)
                        , checkOps transReliable (RCT.reliableChannelInit anP)
                        , checkOps transReport (reportInit anP)
                      ]
    trans anP = foldr ($) (BT.baseTrans needsAssImmediate)  --- fold from right to left, not that foldr applies ($) the other way around compared to foldM
                        $ mapMaybe (uncurry checkOps) [ --- remove if fst element does not point to option that is set
                        (transProgress, PT.progressTrans anP)
                      , (transReliable, RCT.reliableChannelTrans )
                      ]
    restrictions:: (MonadThrow m1, MonadCatch m1) => LProcess (ProcessAnnotation LVar) -> [AnnotatedRule (ProcessAnnotation LVar)] -> m1 [SyntacticRestriction]
    restrictions anP pRules = foldM (flip ($)) []  --- fold from left to right
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
                        $ BT.baseRestr anP needsAssImmediate (containChannelIn pRules) True :
                           mapMaybe (uncurry checkOps) [
                            (transProgress, PT.progressRestr anP)
                          , (transReliable, RCT.reliableChannelRestr anP)
                           ]
    heuristics = [SapicRanking]
    needsAssImmediate = not (all checkAssImmediate (theoryLemmas th))
    containChannelIn rules = not $ null [a | anR <- rules, a@ChannelIn {} <- acts anR]

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
  --- ^ "end"

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

-- Checks if the lemma is in the fragment of formulas for which the resInEv restriction is not needed.
checkAssImmediate :: Lemma p -> Bool
checkAssImmediate lem = case (L.get lTraceQuantifier lem, isPosNegFormula $ L.get lFormula lem) of
  (AllTraces,   (_, True))     -> True  -- L- for all-traces
  (ExistsTrace, (True, _))     -> True  -- L+ for exists-trace
  (ExistsTrace, (False, True)) -> False -- L- for exists-trace
  (AllTraces,   (True, False)) -> False -- L+ for all-traces
  _                            -> False -- not in L- and L+ should not be possible
