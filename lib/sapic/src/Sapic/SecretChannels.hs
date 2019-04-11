-- |
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Compute annotations for secret channels
-- a channel is secret if it correspond to a fresh variable only use as a channel identifier

module Sapic.SecretChannels (
    annotateSecretChannels
) where
import           Control.Exception
import           Control.Monad.Catch
import           Control.Monad.Fresh
import           Data.Set as S
import           Data.List as L
import           Sapic.Annotation
import           Sapic.Exceptions
import           Theory
import           Theory.Sapic


-- | Get all variables inside a term
getTermVariables :: LNTerm -> S.Set LVar
getTermVariables ts =
  S.fromList $ L.map fst $ varOccurences ts

-- | Get all variables never outputed
getSecretChannels :: AnProcess ProcessAnnotation -> S.Set LVar -> S.Set LVar
getSecretChannels (ProcessAction (New v) an p) candidates =
  let c = S.insert v candidates in
    getSecretChannels p c
getSecretChannels (ProcessAction (ChOut t1 t2) an p) candidates =
  let c = S.difference candidates (getTermVariables t2) in
    getSecretChannels p c
getSecretChannels (ProcessAction (Insert t1 t2) an p) candidates =
  let c = S.difference candidates (getTermVariables t2) in
    getSecretChannels p c
getSecretChannels (ProcessAction (_) an p) candidates =
    getSecretChannels p candidates
getSecretChannels (ProcessNull an) candidates =  candidates
getSecretChannels (ProcessComb comb an pl pr ) candidates =
            S.intersection c1 c2
            where
              c1 = getSecretChannels pl candidates
              c2 = getSecretChannels pr candidates
              
-- | For each input or output, if the variable is secret, we annotate the process              
annotateEachSecretChannels :: AnProcess ProcessAnnotation -> S.Set LVar -> AnProcess ProcessAnnotation
annotateEachSecretChannels (ProcessNull an) svars = (ProcessNull an)
annotateEachSecretChannels (ProcessComb comb an pl pr ) svars =
            (ProcessComb comb an pl' pr')
            where
              pl' = annotateEachSecretChannels pl svars
              pr' = annotateEachSecretChannels pr svars
annotateEachSecretChannels (ProcessAction ac an p) svars
  | (ChIn (Just t1) t2) <- ac, Lit (Var v) <- viewTerm t1 =
      if S.member v svars then
        (ProcessAction ac (an `mappend` annSecretChannel (AnLVar v)) p')
      else
        (ProcessAction ac an p')
  | (ChOut (Just t1) t2) <- ac, Lit (Var v) <- viewTerm t1 =
      if S.member v svars then
        (ProcessAction ac (an `mappend` annSecretChannel (AnLVar v)) p')
      else
        (ProcessAction ac an p')                           
  | otherwise <- ac = (ProcessAction ac an p')
  where p'= annotateEachSecretChannels p svars


annotateSecretChannels :: AnProcess ProcessAnnotation -> (AnProcess ProcessAnnotation)
annotateSecretChannels anp = 
  annotateEachSecretChannels anp svars
  where svars = getSecretChannels anp S.empty

