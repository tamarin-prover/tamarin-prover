{-# LANGUAGE PatternGuards #-}
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
-- only use as a channel identifier. For these channels, we can use a more
-- efficient translation, as the adversary can never deduce then, and thus only
-- a silent transition is possible.

module Sapic.SecretChannels (
    annotateSecretChannels
) where
-- import           Control.Exception
-- import           Control.Monad.Catch
-- import           Control.Monad.Fresh
import           Data.Set as S
import           Data.List as L
import           Sapic.Annotation
-- import           Sapic.Exceptions
import           Theory
import           Theory.Sapic


-- | Get all variables inside a term
getTermVariables :: LNTerm -> S.Set LVar
getTermVariables ts =
  S.fromList $ L.map fst $ varOccurences ts

-- | Get all variables never outputed
getSecretChannels :: AnProcess ProcessAnnotation -> S.Set LVar -> S.Set LVar
getSecretChannels (ProcessAction (New v) _ p) candidates =
  let c = S.insert v candidates in
    getSecretChannels p c
getSecretChannels (ProcessAction (ChOut _ t2) _ p) candidates =
  let c = S.difference candidates (getTermVariables t2) in
    getSecretChannels p c
getSecretChannels (ProcessAction (Insert _ t2) _ p) candidates =
  let c = S.difference candidates (getTermVariables t2) in
    getSecretChannels p c
getSecretChannels (ProcessAction (_) _ p) candidates =
    getSecretChannels p candidates
getSecretChannels (ProcessNull _) candidates =  candidates
getSecretChannels (ProcessComb _ _ pl pr ) candidates =
            S.intersection c1 c2
            where
              c1 = getSecretChannels pl candidates
              c2 = getSecretChannels pr candidates
              
-- | For each input or output, if the variable is secret, we annotate the process              
annotateEachSecretChannels :: AnProcess ProcessAnnotation -> S.Set LVar -> AnProcess ProcessAnnotation
annotateEachSecretChannels (ProcessNull an) _ = (ProcessNull an)
annotateEachSecretChannels (ProcessComb comb an pl pr ) svars =
            (ProcessComb comb an pl' pr')
            where
              pl' = annotateEachSecretChannels pl svars
              pr' = annotateEachSecretChannels pr svars
annotateEachSecretChannels (ProcessAction ac an p) svars
  | (ChIn (Just t1) _) <- ac, Lit (Var v) <- viewTerm t1 =
      if S.member v svars then
        (ProcessAction ac (an `mappend` annSecretChannel (AnLVar v)) p')
      else
        (ProcessAction ac an p')
  | (ChOut (Just t1) _) <- ac, Lit (Var v) <- viewTerm t1 =
      if S.member v svars then
        (ProcessAction ac (an `mappend` annSecretChannel (AnLVar v)) p')
      else
        (ProcessAction ac an p')                           
  | otherwise = (ProcessAction ac an p')
  where p'= annotateEachSecretChannels p svars


annotateSecretChannels :: AnProcess ProcessAnnotation -> (AnProcess ProcessAnnotation)
annotateSecretChannels anp = 
  annotateEachSecretChannels anp svars
  where svars = getSecretChannels anp S.empty

