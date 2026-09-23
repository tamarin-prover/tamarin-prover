-- |
-- Copyright   : (c) 2019 Robert Künnemann and Alexander Dax
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation from Theories with Processes to multiset rewrite rules

module Sapic
  ( translate
  , module Sapic.Typing
  , module Sapic.Warnings
  ) where

import Control.Exception hiding (catch)
import Control.Monad.Fresh
import Control.Monad.Catch
import Control.Monad.Trans.FastFresh ()
import Data.List.NonEmpty qualified as NE
import Data.Maybe
import Data.Set qualified as S
import Data.Typeable

import Items.OptionItem (Option(..))
import Sapic.Annotation
import Sapic.Basetranslation qualified as BT
import Sapic.Compression
import Sapic.Exceptions
import Sapic.Facts
import Sapic.LetDestructors
import Sapic.Locks
import Sapic.ProcessUtils
import Sapic.ReliableChannelTranslation qualified as RCT
import Sapic.Report
import Sapic.SecretChannels
import Sapic.States
import Sapic.Typing
import Sapic.ProgressTranslation qualified as PT
import Sapic.Warnings
import Theory
import TheoryObject (theoryMacros)
import Theory.Sapic
import Theory.Text.Parser

-- | Translates the process (singular) into a set of rules and adds them to the theory.
translate :: (Monad m, MonadThrow m, MonadCatch m) =>
             OpenTheory -> m OpenTheory
translate th =
  case theoryProcesses th of
    []  -> if ops._transReliable then
             throwM (ReliableTransmissionButNoProcess :: SapicException AnnotatedProcess)
           else
             return th
    [p] -> do
      -- annotate
      substituted <- translateLetDestr (theoryMacros th) sigRules
        $ checkOps' (._transReport) translateTermsReport
        $ propagateNames
        $ toAnProcess p
      -- Substitution can expose channel names in outputs and state accesses.
      let an_proc_pre = checkOps' (._stateChannelOpt) annotatePureStates
                      $ annotateSecretChannels substituted
      an_proc <- annotateLocks an_proc_pre
      -- compute initial rules
      (initRules,initTx) <-
                  checkOps (._transReport) (reportInit an_proc)
              =<< checkOps (._transReliable) (RCT.reliableChannelInit an_proc)
              =<< checkOps (._transProgress) (PT.progressInit an_proc)
                  (BT.baseInit an_proc)
      -- generate protocol rules, starting from variables in initial tilde x
      protoRule <-  gen (trans an_proc) an_proc [] initTx
      -- apply path compression
      let eProtoRules' = map toRule (initRules ++ protoRule)
      eProtoRule <-  checkOps (._transProgress)
                        (pathCompression ops._compressEvents) eProtoRules'
      -- add rules we have produced to theory
      th1 <- foldM liftedAddProtoRule th $ map (`OpenProtoRule` []) eProtoRule
      -- add restrictions
      rest <- checkOps (._transReliable) (RCT.reliableChannelRestr an_proc)
           =<<  checkOps (._transProgress) (PT.progressRestr an_proc)
           =<<  BT.baseRestr an_proc needsInEvRes True []
      checkReservedNames th th1 p (initRules ++ protoRule) rest
      th2 <- foldM liftedAddRestriction th1 rest
      -- add heuristic, if not already defined by user
      let th3 = fromMaybe th2 (addHeuristic [SapicRanking] th2)
      -- for state optimisation: force special facts  to be injective
      let th4 = checkOps' (._stateChannelOpt) (setforcedInjectiveFacts (S.fromList [pureStateFactTag, pureStateLockFactTag])) th3
      let th5 = th4 { _thyIsSapic = True }
      return th5
    _   -> throw (MoreThanOneProcess :: SapicException AnnotatedProcess)
  where
    ops = th._thyOptions
    checkOps l x
      | l ops = x
      | otherwise = return
    -- evaluate lens on options, if true, behave like f, otherwise, do nothing
    checkOps' l f
      | l ops = f
      | otherwise = id
    sigRules =  stRules th._thySignature._sigMaudeInfo
    trans anP = checkOps' (._transProgress) (PT.progressTrans anP)
              $ checkOps' (._transReliable) RCT.reliableChannelTrans
              $ BT.baseTrans ops._asynchronousChannels needsInEvRes
    needsInEvRes = any lemmaNeedsInEvRes (theoryLemmas th)

-- | The translation introduces facts of its own, such as State_1 or Message,
-- and gives actions of its own, such as Insert, Init or the guards of the
-- restrictions of its conditionals, their meaning through restrictions. A
-- fact or action of the user with the same name would silently take part in
-- this machinery: a user rule could produce the state of a process, or a
-- user event could be constrained by a restriction and remove traces. Reject
-- such names.
checkReservedNames :: MonadThrow m => OpenTheory -> OpenTheory -> PlainProcess
                   -> [AnnotatedRule ann] -> [SyntacticRestriction] -> m ()
checkReservedNames th th1 p generated restrictions =
  case filter (`S.member` reserved) used of
    [] -> return ()
    (kind, name):_ -> throwM (ReservedName kind name :: SapicException AnnotatedProcess)
  where
    reserved = S.fromList $ map ("action",) restrictedActions ++ map ("fact",) internalFacts
    (actions, facts) = pfoldMap processNames p
    used = map ("action",) actions
        ++ map ("fact",) facts
        ++ concat [ruleNames ru ++ concatMap ruleNames variants
                  | OpenProtoRule ru variants <- theoryRules th]
    -- th1 adds a restriction for each conditional and embedded restriction of
    -- the generated rules, guarded by an action named like the restriction.
    restrictedActions = concatMap (formulaActions . (._rstrFormula)) restrictions
                     ++ filter (`S.notMember` userRestrictions) (map (._rstrName) $ theoryRestrictions th1)
    userRestrictions = S.fromList $ map (._rstrName) $ theoryRestrictions th
    formulaActions = foldFormula atomActions (const []) id (const (++)) (const $ const id)
    atomActions (Action _ fa) = [nameOf fa]
    atomActions _ = []
    internalFacts = [ nameOf (factToFact f)
                    | ru <- generated, f <- ru.prems ++ ru.concs, isInternal f ]
                 -- These tags receive forced injectivity even when this
                 -- process generates no state facts. User facts must not
                 -- inherit that assumption.
                 ++ [ factTagName tag | th._thyOptions._stateChannelOpt
                    , tag <- [pureStateFactTag, pureStateLockFactTag] ]
    isInternal (Fr _) = False
    isInternal (In _) = False
    isInternal (Out _) = False
    isInternal (TamarinFact _) = False -- a fact of an embedded rule of the user
    isInternal _ = True
    processNames (ProcessAction (Event fa) _ _) = ([nameOf fa], [])
    processNames (ProcessAction (MSR prems acts concs _ _) _ _) =
      (map nameOf acts, map nameOf (prems ++ concs))
    processNames _ = ([], [])
    ruleNames :: Rule i -> [(String, String)]
    ruleNames ru = map (("action",) . nameOf) ru._rActs
               ++ map (("fact",) . nameOf) (ru._rPrems ++ ru._rConcs)
    nameOf :: Fact t -> String
    nameOf = factTagName . factTag

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
gen (trans_null, trans_action, trans_comb) anP p tildex = do
  proc' <- processAt anP p
  case proc' of
    ProcessNull ann -> do
      msrs <- catch (trans_null ann p tildex) (handler proc')
      return $ mapToAnnotatedRule proc' msrs
    ProcessComb NDC _ _ _ -> do
      let subst p_old = map_prems (substStatePos p_old p)
      l <- gen trans anP ( p++[1] ) tildex
      r <- gen trans anP (p++[2]) tildex
      return $ subst (p++[1]) l ++ subst (p++[2]) r
    ProcessComb c ann _ _ -> do
      (msrs, tildex'1, tildex'2) <- catch (trans_comb c ann p tildex) (handler proc')
      msrs_l <- gen trans anP (p++[1]) tildex'1
      msrs_r <- maybe (return [])
                    (gen trans anP (p++[2]))
                    tildex'2
      return $ mapToAnnotatedRule proc' msrs ++ msrs_l ++ msrs_r
    ProcessAction ac ann _ -> do
      (msrs, tildex') <- catch (trans_action ac ann p tildex) (handler proc')
      msr' <-  gen trans anP (p++[1]) tildex'
      return $ mapToAnnotatedRule proc' msrs ++ msr'
    where
      map_prems f = map (\r -> r { prems = map f r.prems })
      --  Substitute every occurence of  State(p_old,v) with State(p_new,v)
      substStatePos p_old p_new fact
        | (State s p' vs) <- fact, p'==p_old, not $ isSemiState s = State LState p_new vs
        | otherwise = fact
      trans = (trans_null, trans_action, trans_comb)
      -- convert prems, acts and concls generated for current process
      -- into annotated rule
      mapToAnnotatedRule proc rules = zipWith toAnnotatedRule rules [0..]
        where
          -- Share the equation-pattern index across this node's generated rules.
          -- Only internal equation matches skip derivation checking; user
          -- patterns must still pass it.
          equationPatterns = S.fromList
            [ (letStagePosition p i, lhs)
            | (i, LetStage _ alternatives _) <- zip [0..] (processGetAnnotation proc).letPlan
            , (lhs, Just _) <- NE.toList alternatives ]
          isEquationMatch (FLet pos term _) = (pos, term) `S.member` equationPatterns
          isEquationMatch _ = False
          toAnnotatedRule (l,a,r,res) =
            AnnotatedRule Nothing proc (Left p) l a r res (any isEquationMatch l)
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

-- | Checks if the lemma is in the fragment of formulas for which the resInEv restriction is needed.
lemmaNeedsInEvRes :: Lemma p -> Bool
lemmaNeedsInEvRes lem = case (lem._lTraceQuantifier, isPosNegFormula lem._lFormula) of
  (AllTraces,   (_, True))     -> False -- L- for all-traces
  (ExistsTrace, (True, _))     -> False -- L+ for exists-trace
  (ExistsTrace, (False, True)) -> True  -- L- for exists-trace
  (AllTraces,   (True, False)) -> True  -- L+ for all-traces
  _                            -> True  -- not in L- and L+
