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
import Sapic.ProcessUtils (processContains)

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

-- | The state identifier accessed by this node, independent of its continuation.
stateIdentifier :: LProcess ann -> Maybe SapicTerm
stateIdentifier proc = case proc of
  ProcessAction (Insert t _) _ _ -> Just t
  ProcessAction (Lock t) _ _ -> Just t
  ProcessAction (Unlock t) _ _ -> Just t
  ProcessAction (Delete t) _ _ -> Just t
  ProcessComb (Lookup t _) _ _ _ -> Just t
  _ -> Nothing

getAllStates :: LProcess (ProcessAnnotation LVar) -> S.Set LVar -> (S.Set SapicTerm, S.Set SapicTerm)
getAllStates p boundNames = case stateIdentifier p of
  Just t | isBound boundNames t -> (S.insert t boundStates, freeStates)
         | otherwise -> (boundStates, S.insert t freeStates)
  Nothing -> (boundStates, freeStates)
  where
    (boundStates, freeStates) = case p of
      ProcessAction (New (SapicLVar v _)) _ rest ->
        getAllStates rest (S.insert v boundNames)
      ProcessAction _ _ rest -> getAllStates rest boundNames
      ProcessComb _ _ left right ->
        let (boundLeft, freeLeft) = getAllStates left boundNames
            (boundRight, freeRight) = getAllStates right boundNames
        in (S.union boundLeft boundRight, S.union freeLeft freeRight)
      ProcessNull _ -> (S.empty, S.empty)


-- State channels declaration
-- We first go once into the process, to add where need the channel identifiers for each required state.

type StateMap = M.Map SapicTerm (AnVar LVar)

stateChannelName :: String
stateChannelName = "StateChannel"

addStatesChannels ::  LProcess (ProcessAnnotation LVar) -> LProcess (ProcessAnnotation LVar)
addStatesChannels p = evalFresh (declareStateChannel p (S.toList allBoundStates) S.empty M.empty) initStateChan
 where
   allBoundStates =  fst $ getAllStates p S.empty
   initState = avoidPreciseVars $ translationVars p
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



-- A pure cell is initialized once per fresh state identifier, before replicating
-- or splitting its accesses between parallel branches, then accessed through
-- locked read/write sections. Replication above the fresh declaration creates
-- distinct cells and is allowed. Outside this fragment the ordinary translation
-- retains overwrite, deletion, and lookup-failure semantics through restrictions.
data CellPhase = InitializerAllowed | InitializerForbidden | Ready | Locked
  deriving (Eq)

isPureState :: LProcess (ProcessAnnotation LVar) -> SapicTerm -> Bool
isPureState p target = check InitializerAllowed p
  where
    check phase proc = case proc of
      ProcessAction (Insert t _) _ rest
        | t == target, phase == InitializerAllowed -> check Ready rest
      ProcessAction (Lock t) _ (ProcessComb (Lookup t' _) _ body (ProcessNull _))
        | t == target, t' == target, phase == Ready -> check Locked body
      ProcessAction (Insert t _) _ (ProcessAction (Unlock t') _ rest)
        | t == target, t' == target, phase == Locked -> check Ready rest
      _ | stateIdentifier proc == Just target -> False
      -- Initialization cannot be replicated or separated from users in another
      -- parallel branch. An unrelated branch does not affect an isolated cell.
      -- A fresh cell inside replication is checked at its declaration.
      ProcessAction Rep _ rest -> phase /= Locked && check (withoutInit phase) rest
      ProcessComb Parallel _ left right
        | phase == InitializerAllowed, not (usesTarget left && usesTarget right) ->
            check phase left && check phase right
        | otherwise ->
            phase /= Locked && check (withoutInit phase) left && check (withoutInit phase) right
      ProcessAction _ _ rest -> check phase rest
      ProcessComb _ _ left right -> check phase left && check phase right
      -- Terminating while holding the cell also leaves the original lock held.
      ProcessNull _ -> True
    withoutInit InitializerAllowed = InitializerForbidden
    withoutInit phase = phase
    usesTarget proc = processContains proc ((== Just target) . stateIdentifier)

annotatePureStates :: LProcess (ProcessAnnotation LVar)  -> LProcess (ProcessAnnotation LVar)
annotatePureStates p
  -- A variable state identifier may alias an otherwise pure cell.
  | not (S.null freeStates) = addStatesChannels p
  | S.null boundStates = p
  | otherwise = annotateEachPureStates (addStatesChannels p) S.empty
  where (boundStates, freeStates) = getAllStates p S.empty


-- | Annotate every access to cells with a supported access pattern.
annotateEachPureStates :: LProcess (ProcessAnnotation LVar) -> S.Set SapicTerm -> LProcess (ProcessAnnotation LVar)
annotateEachPureStates proc pureStates = case proc of
    ProcessNull _ -> proc
    ProcessComb comb an left right ->
      ProcessComb comb (mark an) (recurse left) (recurse right)
    ProcessAction ac an p
      | New _ <- ac, Just cid <- an.isStateChannel
      , isolatedCell p cid && isPureState p cid ->
          ProcessAction ac an{pureState=True}
            (annotateEachPureStates p (cid `S.insert` pureStates))
      | otherwise -> ProcessAction ac (mark an) (recurse p)
  where
    recurse p = annotateEachPureStates p pureStates
    -- A cell with a delete cannot enter pureStates.
    mark an
      | Just t <- stateIdentifier proc, t `S.member` pureStates = an{pureState=True}
      | otherwise = an
    -- Syntactic comparisons suffice for a fresh-name identifier only if no other
    -- state identifier contains that name (and might reduce to it).
    isolatedCell p t = case viewTerm t of
      Lit (Var v) -> not $ processContains p $ \node -> case stateIdentifier node of
        Just other -> other /= t && toLVar v `elem` frees (toLNTerm other)
        Nothing -> False
      _ -> False
