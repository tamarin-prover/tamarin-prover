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

type StateMap = M.Map SapicTerm SapicLVar


addStatesChannels ::  LProcess (ProcessAnnotation LVar) -> (LProcess (ProcessAnnotation LVar), StateMap)
addStatesChannels p = (p', stateMap)
 where
   allStates = getAllBoundStates p
   (p', stateMap) =   evalFresh (declareStateChannel p (S.toList allStates) S.empty M.empty) 0


-- Descends into a process. Whenever all the names of a state term are declared, we declare a name corresponding to this state term, that will be used as the corresponding channel name.
declareStateChannel ::  MonadFresh m =>  LProcess (ProcessAnnotation LVar) -> [SapicTerm] -> (S.Set SapicLVar) -> StateMap -> m (LProcess (ProcessAnnotation LVar),  M.Map SapicTerm SapicLVar)
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

newStates :: MonadFresh m =>  LProcess (ProcessAnnotation LVar) -> [SapicTerm] -> [SapicLVar]
  -> StateMap -> m ([SapicLVar], StateMap)
newStates _ [] declared stateMap = return (declared, stateMap)
newStates p (v:declarables) declared stateMap = do
    newvar <-  freshLVar "StateChannel" LSortMsg
    let  newslvar = SapicLVar newvar (Just "channel")
    let newMap =  M.insert v newslvar stateMap
    newStates p declarables (newslvar:declared) newMap
