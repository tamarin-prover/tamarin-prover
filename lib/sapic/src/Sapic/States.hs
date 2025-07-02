-- |
-- Copyright   : (c) 2019 Charlie Jacomme and Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--

module Sapic.States
  ( annotatePureStates
  , hasBoundUnboundStates
  ) where

import Sapic.Annotation

import Theory
import Theory.Sapic

import Data.Set qualified as S
import Data.Map qualified as M
import Data.Maybe (fromMaybe)
import Data.List qualified as L
import Control.Monad.Fresh

-- Returns all states identifiers that are completely bound by names, when there is no states with a free identifier

isBound :: S.Set LVar -> SapicTerm -> Bool
isBound boundNames t = S.fromList (frees $ toLNTerm t) `S.isSubsetOf` boundNames

hasBoundUnboundStates ::  LProcess (ProcessAnnotation LVar) -> (Bool, Bool)
hasBoundUnboundStates p = (bounds /= S.empty, unbounds /= S.empty)
  where (bounds, unbounds) = getAllStates p S.empty

getAllStates ::  LProcess (ProcessAnnotation LVar) ->  S.Set LVar-> (S.Set SapicTerm, S.Set SapicTerm)
getAllStates (ProcessAction (Insert t _) _ p) boundNames | isBound boundNames t = (S.insert t boundStates, freeStates)
  where (boundStates,freeStates) = getAllStates p boundNames
getAllStates (ProcessAction (Insert t _) _ p) boundNames  = (boundStates, S.insert t freeStates)
  where (boundStates,freeStates) = getAllStates p boundNames
getAllStates (ProcessAction (Lock t) _ p) boundNames | isBound boundNames t = (S.insert t boundStates, freeStates)
  where (boundStates,freeStates) = getAllStates p boundNames
getAllStates (ProcessAction (Lock t) _ p) boundNames  = (boundStates, S.insert t freeStates)
  where (boundStates,freeStates) = getAllStates p boundNames
getAllStates (ProcessAction (Unlock t) _ p) boundNames | isBound boundNames t = (S.insert t boundStates, freeStates)
  where (boundStates,freeStates) = getAllStates p boundNames
getAllStates (ProcessAction (Unlock t ) _ p) boundNames  = (boundStates, S.insert t freeStates)
  where (boundStates,freeStates) = getAllStates p boundNames


getAllStates (ProcessAction (New (SapicLVar v _)) _ p) boundNames = getAllStates p (v `S.insert` boundNames)
getAllStates (ProcessAction _ _ p) boundNames = getAllStates p boundNames
getAllStates (ProcessNull _) _ = (S.empty, S.empty)

getAllStates (ProcessComb  (Lookup t _)  _ pl pr) boundNames | isBound boundNames t  =
  (t `S.insert` boundStatesL `S.union` boundStatesR, freeStatesL `S.union` freeStatesR)
  where (boundStatesL,freeStatesL) = getAllStates pl boundNames
        (boundStatesR,freeStatesR) = getAllStates pr boundNames
getAllStates (ProcessComb  (Lookup t _)  _ pl pr) boundNames  =
  (boundStatesL `S.union` boundStatesR, t `S.insert`  freeStatesL `S.union` freeStatesR)
  where (boundStatesL,freeStatesL) = getAllStates pl boundNames
        (boundStatesR,freeStatesR) = getAllStates pr boundNames


getAllStates (ProcessComb _ _ pl pr) boundNames =
    (boundStatesL `S.union` boundStatesR, freeStatesL `S.union` freeStatesR)
  where (boundStatesL,freeStatesL) = getAllStates pl boundNames
        (boundStatesR,freeStatesR) = getAllStates pr boundNames



-- State channels declaration
-- We first go once into the process, to add where need the channel identifiers for each required state.

type StateMap = M.Map SapicTerm (AnVar LVar)

stateChannelName :: String
stateChannelName = "StateChannel"

addStatesChannels ::  LProcess (ProcessAnnotation LVar) -> LProcess (ProcessAnnotation LVar)
addStatesChannels p = evalFresh (declareStateChannel p (S.toList allBoundStates) S.empty M.empty) initStateChan
 where
   allBoundStates =  fst $ getAllStates p S.empty
   initState = avoidPreciseVars . map (\(SapicLVar lvar _) -> lvar) $ S.toList $ varsProc p
   initStateChan = fromMaybe 0 (M.lookup stateChannelName initState)

-- Descends into a process. Whenever all the names of a state term are declared, we declare a name corresponding to this state term, that will be used as the corresponding channel name.
declareStateChannel ::  MonadFresh m => LProcess (ProcessAnnotation LVar) -> [SapicTerm] -> S.Set SapicLVar -> StateMap -> m (LProcess (ProcessAnnotation LVar))
declareStateChannel p toDeclare boundNames stateMap =
  let (declarables, undeclarables) =  L.partition (\v -> S.fromList (freesSapicTerm v) `S.isSubsetOf` boundNames) toDeclare in
  if null declarables then  do
    case p of
      ProcessNull _ -> return p
      ProcessComb a an pl pr -> do
        pl' <- declareStateChannel pl toDeclare boundNames stateMap
        pr' <- declareStateChannel pr toDeclare boundNames stateMap
        case a of
          Lookup t _ -> return $ ProcessComb a an{  stateChannel = M.lookup t stateMap} pl' pr'
          _ -> return $ ProcessComb a an pl' pr'
      ProcessAction (New var) an pr -> do
        pr' <-  declareStateChannel pr toDeclare (var `S.insert` boundNames) stateMap
        return $ ProcessAction (New var) an pr'

      ProcessAction act an pr -> do
        pr' <- declareStateChannel pr toDeclare boundNames stateMap
        case act of
          Insert t _   -> return $ ProcessAction act an{ stateChannel = M.lookup t stateMap} pr'
          Lock t  -> return $ ProcessAction act an{ stateChannel = M.lookup t stateMap} pr'
          Unlock t  -> return $ ProcessAction act an{ stateChannel = M.lookup t stateMap} pr'
          _  -> return $ ProcessAction act an pr'
  else do
    (newvars, newMap) <- newStates p declarables [] stateMap
    p' <- declareStateChannel p undeclarables boundNames newMap
    return $ addNews p' newvars
      where addNews pr [] = pr
            addNews pr ((var, term):d) = ProcessAction (New (SapicLVar var (Just "channel"))) mempty{ isStateChannel = Just term } (addNews pr d)

newStates :: MonadFresh m =>  LProcess (ProcessAnnotation LVar) -> [SapicTerm] -> [(LVar, SapicTerm)]
  -> StateMap -> m ([(LVar, SapicTerm)], StateMap)
newStates _ [] declared stateMap = return (declared, stateMap)
newStates p (v:declarables) declared stateMap = do
    newvar <-  freshLVar stateChannelName LSortMsg
--    let  newslvar = SapicLVar newvar (Just "channel")
    let newMap =  M.insert v (AnVar newvar) stateMap
    newStates p declarables ((newvar, v):declared) newMap



-- We now have a process with defined states channels. We want to optimize on pure states, that is
-- a state channel such that, 1) there is a single insert outside of a lock (this is the state initialisation); 2) every occurence of the state channel is either lock t; lookup t or insert t; unlock t.

-- Remark that if there is a state identifier based on an input variable accessed not in a pure fashion, no state is considered pure
existsAttackerUnpure :: LProcess (ProcessAnnotation LVar) -> S.Set LVar -> Bool
existsAttackerUnpure p boundNames =
  case p of
     ProcessAction  (New (SapicLVar v _)) _ pl
          ->  existsAttackerUnpure pl (v `S.insert` boundNames)
     ProcessAction (Insert t _) _  (ProcessAction (Unlock t2) _ pl) | t == t2
          ->  existsAttackerUnpure pl  boundNames
     ProcessAction (Lock t) _   (ProcessComb (Lookup t2 _ )  _ pl (ProcessNull _)) | t == t2
          ->  existsAttackerUnpure pl boundNames
     -- any lone action on unbound identifier raises the warning
     ProcessAction (Insert t _) _ _ | not (isBound boundNames t)
          -> True
     ProcessAction (Lock t) _ _ | not (isBound boundNames t)
          -> True
     ProcessAction (Unlock t) _ _ | not (isBound boundNames t)
          -> True
     ProcessComb (Lookup t _ )  _ _ (ProcessNull _) | not (isBound boundNames t)
          -> True
     ProcessAction _ _ pl
          -> existsAttackerUnpure pl boundNames
     ProcessComb _ _ pl pr ->
       let bl = existsAttackerUnpure pl boundNames in
       let br = existsAttackerUnpure pr boundNames in
         bl || br
     ProcessNull _ -> False

-- isPureState decides if a state is pure. It returns (isPure, loneInsert), where loneInsert describes that there is at least one lone insert for this state.
isPureState ::  LProcess (ProcessAnnotation LVar) -> SapicTerm -> Bool -> (Bool, Bool)
isPureState p target loneInsert =
  case p of
     (ProcessAction (Insert t _) _  (ProcessAction (Unlock t2) _ pl)) | t == t2
          -> isPureState pl target loneInsert
     (ProcessAction (Lock t) _   (ProcessComb (Lookup t2 _ )  _ pl (ProcessNull _)) ) | t == t2
          -> isPureState pl target loneInsert
     (ProcessAction (Insert t _) _ pl) | t == target
          ->
       -- when we see a lone insert, if there is another lone insert somewhere else we return false
       let (pure', lone) = isPureState pl target loneInsert in
         if lone then
           (False, lone)
         else (pure', lone)
     (ProcessAction (Lock t ) _ _) | t == target
          -> (False, False)
     (ProcessAction (Unlock t) _ _) | t == target
          -> (False, False)
     (ProcessAction _ _ pl)
          -> isPureState pl target loneInsert
     ProcessComb Parallel _ pl pr ->
       -- in parallel, we sum the oneOutSide, and in all other cases, we just merge them (as the two branches can never be taken
       let (pur, lone) = isPureState pl target loneInsert in
       let (pure', lone') = isPureState pr target loneInsert in
         ( pur && pure' && not (lone && lone'), lone || lone')
     ProcessComb _ _ pl pr ->
       let (pur, lone) = isPureState pl target loneInsert in
       let (pure', lone') = isPureState pr target loneInsert in
         ( pur && pure', lone || lone')
     ProcessNull _ -> (True, False)

-- getPureStates ::  LProcess (ProcessAnnotation LVar)  -> S.Set SapicTerm -> S.Set SapicTerm
-- getPureStates p currentPures = fst $ computePureStates p currentPures S.empty
--    where (pureStates, unPureStates)
annotatePureStates :: LProcess (ProcessAnnotation LVar)  -> LProcess (ProcessAnnotation LVar)
annotatePureStates p
  | existsAttackerUnpure p S.empty           = addStatesChannels p
  | fst (getAllStates p S.empty)  == S.empty = p
  | otherwise                                = annotateEachPureStates (addStatesChannels p) S.empty
--  where pureStates = getPureStates p (getAllBoundStates p)


-- | For each input or output, if the variable is secret, we annotate the process
annotateEachPureStates :: LProcess (ProcessAnnotation LVar) -> S.Set SapicTerm -> LProcess (ProcessAnnotation LVar)
annotateEachPureStates (ProcessNull an) _ = ProcessNull an
annotateEachPureStates (ProcessComb comb an pl pr ) pureStates
  | Lookup t _ <- comb =
      if t `S.member` pureStates then
            ProcessComb comb an{pureState=True} pl' pr'
      else
            ProcessComb comb an pl' pr'
  | otherwise = ProcessComb comb an pl' pr'
            where
              pl' = annotateEachPureStates pl pureStates
              pr' = annotateEachPureStates pr pureStates
annotateEachPureStates (ProcessAction ac an p) pureStates
  | New _ <- ac, Just cid <- an.isStateChannel =
      if fst $ isPureState p cid False then
        ProcessAction ac an{pureState=True, isStateChannel = Just cid} (annotateEachPureStates p (cid `S.insert` pureStates))
      else
        ProcessAction ac an p
  | Unlock t <- ac =
      if t `S.member` pureStates then
        ProcessAction ac an{pureState=True} p'
      else
        ProcessAction ac an p'
  | Lock t <- ac =
      if t `S.member` pureStates then
        ProcessAction ac an{pureState=True} p'
      else
        ProcessAction ac an p'
  | Insert t _ <- ac =
      if t `S.member` pureStates then
        ProcessAction ac an{pureState=True} p'
      else
        ProcessAction ac an p'
  | otherwise = ProcessAction ac an p'
  where p'= annotateEachPureStates p pureStates
