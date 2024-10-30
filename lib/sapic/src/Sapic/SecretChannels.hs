-- |
-- Copyright   : (c) 2019 Charlie Jacomme <charlie.jacomme@lsv.fr>
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Compute annotations for always-secret channels
--
-- A channel is defined always-secret iff it correspond to a fresh variable
-- only used as a channel identifier. For these channels, we can use a more
-- efficient translation, as the adversary can never deduce then, and thus only
-- a silent transition is possible.

module Sapic.SecretChannels
  ( annotateSecretChannels
  ) where

import Data.Set as S
import Data.List as L

import Sapic.Annotation
import Sapic.Basetranslation

import Theory
import Theory.Sapic


-- | Get all variables inside a term
getTermVariables :: SapicTerm -> S.Set LVar
getTermVariables ts =
  S.fromList $ L.map fst $ varOccurences $ toLNTerm ts

-- | Get all variables that were never output
getSecretChannels :: LProcess (ProcessAnnotation LVar) -> S.Set LVar -> S.Set LVar
getSecretChannels (ProcessAction (New v) _ p) candidates =
  let c = S.insert (toLVar v) candidates in
    getSecretChannels p c
getSecretChannels (ProcessAction (ChOut _ t2) _ p) candidates =
  let c = S.difference candidates (getTermVariables t2) in
    getSecretChannels p c
getSecretChannels (ProcessAction (Insert _ t2) _ p) candidates =
  let c = S.difference candidates (getTermVariables t2) in
    getSecretChannels p c
getSecretChannels (ProcessAction _ _ p) candidates =
    getSecretChannels p candidates
getSecretChannels (ProcessNull _) candidates =  candidates
getSecretChannels (ProcessComb _ _ pl pr ) candidates =
            S.intersection c1 c2
            where
              c1 = getSecretChannels pl candidates
              c2 = getSecretChannels pr candidates

-- | For each input or output, if the variable is secret, we annotate the process
annotateEachSecretChannels :: LProcess (ProcessAnnotation LVar) -> S.Set LVar -> LProcess (ProcessAnnotation LVar)
annotateEachSecretChannels (ProcessNull an) _ = ProcessNull an
annotateEachSecretChannels (ProcessComb comb an pl pr ) svars =
            ProcessComb comb an pl' pr'
            where
              pl' = annotateEachSecretChannels pl svars
              pr' = annotateEachSecretChannels pr svars
annotateEachSecretChannels (ProcessAction ac an p) svars
  | (ChIn (Just t1) _ _) <- ac, Lit (Var v') <- viewTerm t1
   , v <- toLVar v' =
      if S.member v svars then
        ProcessAction ac (an `mappend` annSecretChannel (AnVar v)) p'
      else
        ProcessAction ac an p'
  | (ChOut (Just t1) _) <- ac, Lit (Var v') <- viewTerm t1
   , v <- toLVar v' =
      if S.member v svars then
        ProcessAction ac (an `mappend` annSecretChannel (AnVar v)) p'
      else
        ProcessAction ac an p'
  | otherwise = ProcessAction ac an p'
  where p'= annotateEachSecretChannels p svars


annotateSecretChannels :: LProcess (ProcessAnnotation LVar) -> LProcess (ProcessAnnotation LVar)
annotateSecretChannels anp =
  annotateEachSecretChannels anp svars
  where svars = getSecretChannels anp S.empty
