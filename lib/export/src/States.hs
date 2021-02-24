-- |
-- Copyright   : (c) 2019 Charlie Jacomme and Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation from Sapic processes to Proverif
-- In sapic, states identifiers are terms. We associate to each state identifier a fresh corresponding channel name.
-- When a state identifier depends on names, we declare the fresh channel name after all the names that it depends of.

module States (
  addStatesChannels,
  StateMap,
  getPureStates) where

import         Theory
import         Theory.Sapic
import qualified  Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import           Control.Monad.Fresh

type StateMap = M.Map SapicTerm SapicLVar


addStatesChannels :: PlainProcess -> (PlainProcess, StateMap)
addStatesChannels p = (p', stateMap)
 where
   allStates = getAllStates p
   (p', stateMap) =  evalFresh (declareStateChannel p (S.toList allStates) S.empty M.empty) 0


getAllStates :: PlainProcess -> (S.Set SapicTerm)
getAllStates (ProcessAction (Insert t _) _ p) = S.insert t (getAllStates p)
getAllStates (ProcessAction _ _ p) = (getAllStates p)
getAllStates (ProcessNull _) = S.empty
getAllStates (ProcessComb  (Lookup t _)  _ pl pr) =  t `S.insert` (getAllStates pl) `S.union` (getAllStates pr)
getAllStates (ProcessComb _ _ pl pr) = (getAllStates pl) `S.union` (getAllStates pr)


-- Descends into a process. Whenever all the names of a state term are declared, we declare a name corresponding to this state term, that will be used as the corresponding channel name.
declareStateChannel ::  MonadFresh m => PlainProcess -> [SapicTerm] -> (S.Set SapicLVar) -> StateMap -> m (PlainProcess,  M.Map SapicTerm SapicLVar)
declareStateChannel p [] _ stateMap = return (p, stateMap)
declareStateChannel p toDeclare boundNames stateMap =
  let (declarables, undeclarables) =  L.partition (\v -> (S.fromList $ freesSapicTerm v) `S.isSubsetOf` boundNames) toDeclare in
  if declarables == [] then  do
    case p of
      ProcessNull _ -> return (p, stateMap)
      ProcessComb a b pl pr -> do
        (pl', lMap) <- declareStateChannel pl toDeclare boundNames stateMap
        (pr', rMap) <- declareStateChannel pr toDeclare boundNames stateMap
        return (ProcessComb a b pl' pr', M.union lMap rMap)
      ProcessAction (New var) an pr -> do
        (pr', stateMap') <-  declareStateChannel pr toDeclare (var `S.insert` boundNames) stateMap
        return (ProcessAction (New var) an pr', stateMap')

      ProcessAction act an pr -> do
        (pr', stateMap') <- declareStateChannel pr toDeclare boundNames stateMap
        return (ProcessAction act an pr', stateMap')
  else do
    (newvars, newMap) <- newStates p declarables [] stateMap
    (p', newMap')<- declareStateChannel p undeclarables boundNames newMap
    return (addNews p' newvars, newMap')
      where addNews pr [] = pr
            addNews pr (v:d) = ProcessAction (New v) mempty (addNews pr d)

newStates :: MonadFresh m => PlainProcess -> [SapicTerm] -> [SapicLVar]
  -> StateMap -> m ([SapicLVar], StateMap)
newStates _ [] declared stateMap = return (declared, stateMap)
newStates p (v:declarables) declared stateMap = do
    newvar <-  freshLVar "StateChannel" LSortMsg
    let  newslvar = SapicLVar newvar (Just "channel")
    let newMap =  M.insert v newslvar stateMap
    newStates p declarables (newslvar:declared) newMap

-- a state channel such that, 1) there is a single insert outside of a lock (this is the state initialisation); 2) every occurence of the state channel is either lock t; lookup t or insert t; unlock t.
--getPureStates p currentPures oneOutside =
computePureStates :: PlainProcess -> S.Set SapicTerm -> S.Set SapicTerm -> (S.Set SapicTerm, S.Set SapicTerm)
computePureStates p currentPures oneOutside =
  case p of
     (ProcessAction (Insert t _) _  (ProcessAction (Unlock t2) _ pl)) | t == t2
          ->  computePureStates pl currentPures oneOutside
     (ProcessAction (Lock t) _   (ProcessComb (Lookup t2 _ )  _ pl (ProcessNull _)) ) | t == t2
          ->  computePureStates pl currentPures oneOutside
     (ProcessAction (Insert t _) _ pl)
          ->
       -- when we see a lone insert, if there is another lone insert somewhere else we remove it from the pureStates
       let (cP, oO) = computePureStates pl currentPures oneOutside in
         if S.member t oO then
           (S.delete t cP, oO)
         else (cP, S.insert t oO)
     (ProcessAction (Lock t ) _ pl)
          ->
       let (cP, oO) = computePureStates pl currentPures oneOutside in
           (S.delete t cP, oO)
     (ProcessAction (Unlock t) _ pl)
          ->
       let (cP, oO) = computePureStates pl currentPures oneOutside in
           (S.delete t cP, oO)

     (ProcessAction _ _ pl)
          ->
       computePureStates pl currentPures oneOutside
     ProcessComb Parallel _ pl pr ->
       -- in parallel, we sum the oneOutSide, and in all other cases, we just merge them (as the two branches can never be taken
       let (cP, oO) = computePureStates pl currentPures oneOutside in
       let (cP', oO') = computePureStates pr currentPures oneOutside in
       let newUnpure =  oO `S.intersection` oO' in
         (cP `S.intersection` cP' `S.difference` newUnpure, oO `S.union` oO')
     ProcessComb _ _ pl pr ->
       let (cP, oO) = computePureStates pl currentPures oneOutside in
       let (cP', oO') = computePureStates pr currentPures oneOutside in
         (cP `S.intersection` cP', oO `S.union` oO')
     ProcessNull _ -> (currentPures, oneOutside)

getPureStates :: PlainProcess  -> S.Set SapicTerm -> S.Set SapicTerm
getPureStates p currentPures = fst $ computePureStates p currentPures S.empty
