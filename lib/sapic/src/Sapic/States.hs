{-# LANGUAGE PatternGuards #-}
-- |
-- Copyright   : (c) 2019 Charlie Jacomme and Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--

module Sapic.States (
    annotatePureStates,
    getAllBoundStates,
    getPureStates
) where

import         Sapic.Annotation

import         Theory
import         Theory.Sapic

import qualified  Data.Set as S

import Debug.Trace

-- Returns all states identifiers that are completely bound by names, when there is no states with a free identifier
getAllBoundStates ::  LProcess (ProcessAnnotation LVar) -> (S.Set SapicTerm)
getAllBoundStates p = if freeStates == S.empty then boundStates else S.empty
    where (boundStates,freeStates) = getAllStates p S.empty

isBound :: S.Set LVar -> SapicTerm -> Bool
isBound boundNames t = (S.fromList $ frees $ toLNTerm t) `S.isSubsetOf` boundNames

getAllStates ::  LProcess (ProcessAnnotation LVar) ->  (S.Set LVar)-> (S.Set SapicTerm, S.Set SapicTerm)
getAllStates (ProcessAction (Insert t _) _ p) boundNames | isBound boundNames t = (S.insert t boundStates, freeStates)
  where (boundStates,freeStates) = (getAllStates p boundNames)
getAllStates (ProcessAction (Insert t _) _ p) boundNames  = (boundStates, S.insert t freeStates)
  where (boundStates,freeStates) = (getAllStates p boundNames)


getAllStates (ProcessAction (New (SapicLVar v _)) _ p) boundNames = getAllStates p (v `S.insert` boundNames)
getAllStates (ProcessAction _ _ p) boundNames = getAllStates p boundNames
getAllStates (ProcessNull _) _ = (S.empty, S.empty)

getAllStates (ProcessComb  (Lookup t _)  _ pl pr) boundNames | isBound boundNames t  =
  (t `S.insert` boundStatesL `S.union` boundStatesR, freeStatesL `S.union` freeStatesR)
  where (boundStatesL,freeStatesL) = (getAllStates pl boundNames)
        (boundStatesR,freeStatesR) = (getAllStates pr boundNames)
getAllStates (ProcessComb  (Lookup t _)  _ pl pr) boundNames  =
  (boundStatesL `S.union` boundStatesR, t `S.insert`  freeStatesL `S.union` freeStatesR)
  where (boundStatesL,freeStatesL) = (getAllStates pl boundNames)
        (boundStatesR,freeStatesR) = (getAllStates pr boundNames)


getAllStates (ProcessComb _ _ pl pr) boundNames =
    (boundStatesL `S.union` boundStatesR, freeStatesL `S.union` freeStatesR)
  where (boundStatesL,freeStatesL) = (getAllStates pl boundNames)
        (boundStatesR,freeStatesR) = (getAllStates pr boundNames)



-- a state channel such that, 1) there is a single insert outside of a lock (this is the state initialisation); 2) every occurence of the state channel is either lock t; lookup t or insert t; unlock t.
--getPureStates p currentPures oneOutside =
computePureStates ::  LProcess (ProcessAnnotation LVar) -> S.Set SapicTerm -> S.Set SapicTerm -> (S.Set SapicTerm, S.Set SapicTerm)
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

getPureStates ::  LProcess (ProcessAnnotation LVar)  -> S.Set SapicTerm -> S.Set SapicTerm
getPureStates p currentPures = fst $ computePureStates p currentPures S.empty


annotatePureStates :: LProcess (ProcessAnnotation LVar)  -> LProcess (ProcessAnnotation LVar)
annotatePureStates p = trace (show pureStates) annotateEachPureStates p pureStates
  where pureStates = getPureStates p (getAllBoundStates p)


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
