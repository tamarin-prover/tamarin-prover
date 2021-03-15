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
  StateMap
  ) where

import         Theory
import         Theory.Sapic

import         Sapic.Annotation
import         Sapic.States

import qualified  Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import           Control.Monad.Fresh

type StateMap = M.Map SapicTerm (AnVar LVar)


addStatesChannels ::  LProcess (ProcessAnnotation LVar) -> LProcess (ProcessAnnotation LVar)
addStatesChannels p =  evalFresh (declareStateChannel p (S.toList allStates) S.empty M.empty) 0
 where
   allStates = getAllBoundStates p


-- Descends into a process. Whenever all the names of a state term are declared, we declare a name corresponding to this state term, that will be used as the corresponding channel name.
declareStateChannel ::  MonadFresh m => LProcess (ProcessAnnotation LVar) -> [SapicTerm] -> (S.Set SapicLVar) -> StateMap -> m (LProcess (ProcessAnnotation LVar))
declareStateChannel p [] _ _ = return p
declareStateChannel p toDeclare boundNames stateMap =
  let (declarables, undeclarables) =  L.partition (\v -> (S.fromList $ freesSapicTerm v) `S.isSubsetOf` boundNames) toDeclare in
  if declarables == [] then  do
    case p of
      ProcessNull _ -> return p
      ProcessComb a an pl pr -> do
        pl' <- declareStateChannel pl toDeclare boundNames stateMap
        pr' <- declareStateChannel pr toDeclare boundNames stateMap
        case a of
          Lookup t _ -> return $ ProcessComb a  an{ stateChannel = M.lookup t stateMap} pl' pr'
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
            addNews pr (v:d) = ProcessAction (New (SapicLVar v (Just "channel"))) mempty{ pureState = True } (addNews pr d)

newStates :: MonadFresh m =>  LProcess (ProcessAnnotation LVar) -> [SapicTerm] -> [LVar]
  -> StateMap -> m ([LVar], StateMap)
newStates _ [] declared stateMap = return (declared, stateMap)
newStates p (v:declarables) declared stateMap = do
    newvar <-  freshLVar "StateChannel" LSortMsg
--    let  newslvar = SapicLVar newvar (Just "channel")
    let newMap =  M.insert v (AnVar newvar) stateMap
    newStates p declarables (newvar:declared) newMap
