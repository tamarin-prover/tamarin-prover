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
import qualified  Data.Set as S
import qualified Data.Map as M
import           Control.Monad.Fresh

type StateMap = M.Map SapicTerm SapicLVar

-- freesSapicTerm :: S.Set a
freesSapicTerm :: Term (Lit Name a) -> [a]
freesSapicTerm =   foldMap $ foldMap (: [])


addStatesChannels :: PlainProcess -> (PlainProcess, StateMap)
addStatesChannels p = (p', stateMap)
 where
   allStates = getAllStates p
   (p', stateMap) = evalFresh (declareStateChannel p (S.toList allStates) S.empty M.empty) 0


getAllStates :: PlainProcess -> (S.Set SapicTerm)
getAllStates (ProcessAction (Insert t _) _ p) = S.insert t (getAllStates p)
getAllStates (ProcessAction _ _ p) = (getAllStates p)
getAllStates (ProcessNull _) = S.empty
getAllStates (ProcessComb  (Lookup t _)  _ pl pr) =  t `S.insert` (getAllStates pl) `S.union` (getAllStates pr)
getAllStates (ProcessComb _ _ pl pr) = (getAllStates pl) `S.union` (getAllStates pr)


-- Descends into a process. Whenever all the names of a state term are declared, we declare a name corresponding to this state term, that will be used as the corresponding channel name.
declareStateChannel ::  MonadFresh m => PlainProcess -> [SapicTerm] -> (S.Set SapicLVar) -> StateMap -> m (PlainProcess,  M.Map SapicTerm SapicLVar)
declareStateChannel p [] _ stateMap = return (p, stateMap)
declareStateChannel p tD@(v:toDeclare) boundNames stateMap =
  if (S.fromList $ freesSapicTerm v) `S.isSubsetOf` boundNames then  do
    newvar <- freshLVar "StateChannel" LSortMsg
    let  newslvar = SapicLVar newvar (Just "channel")
    let newMap =  M.insert v newslvar stateMap
    (p', newMap')<- declareStateChannel p toDeclare boundNames newMap
    return (ProcessAction (New newslvar) mempty p', newMap')
  else
    case p of
      ProcessNull _ -> return (p, stateMap)
      ProcessComb a b pl pr -> do
        (pl', lMap) <- declareStateChannel pl tD boundNames stateMap
        (pr', rMap) <- declareStateChannel pr tD boundNames stateMap
        return (ProcessComb a b pl' pr', M.union lMap rMap)
      ProcessAction (New var) an pr -> do
        (pr', stateMap') <- declareStateChannel pr tD (var `S.insert` boundNames) stateMap
        return (ProcessAction (New var) an pr', stateMap')

      ProcessAction act an pr -> do
        (pr', stateMap') <- declareStateChannel pr tD boundNames stateMap
        return (ProcessAction act an pr', stateMap')
