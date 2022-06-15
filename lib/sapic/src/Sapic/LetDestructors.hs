{-# LANGUAGE PatternGuards #-}
-- |
-- Copyright   : (c) 2019 Charlie Jacomme <charlie.jacomme@lsv.fr>
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Compute annotations for let destructors

module Sapic.LetDestructors (
  translateLetDestr
) where

import           Data.Set as S
import           Data.List as L

import           Sapic.Annotation

import           Theory
import           Theory.Sapic

import           Term.SubtermRule

import           Control.Monad.Catch

mapProc :: ( MonadThrow m)
                    =>  Set CtxtStRule -> LProcess (ProcessAnnotation LVar) -> m (LProcess (ProcessAnnotation LVar))
mapProc _  (ProcessNull ann)  = return $ ProcessNull ann
mapProc rules (ProcessAction ac ann p') = do
  pr <- mapProc rules p'
  return $ ProcessAction (ac) ann pr

mapProc rules (ProcessComb c@(Let t1 t2 mv) _ pl pr) =
  case (t1, viewTerm t1', viewTerm t2') of
    ( (LIT (Var _)) ,(Lit (Var _)), FApp funsym@(NoEq (_, (_,_,Destructor))) rightterms) ->
      -- we are in the case where the let binding is of the form let invar = dest(rightTerms) in
      (case  L.foldl (findRule funsym) Nothing rules of
        -- if the desrtructor does not have any associated rule, it never succeed, and we thus always go in the else branch we simply substitute in the process, to optimize
        Nothing -> mapProc rules pr
        Just  (leftterms, outvar) -> do
          -- TODO we should handle fresh vars here
          -- We extract the equation of the dest, in the case where it is of the
          -- form dest(lefTerms) = outvar.

          -- in this case, we are going to transform the let binding into a
          -- binding of the form let leftterms Sigma = rightterms, where Sigma is the substitution outvar -> invar

          -- e.g in the case of symmetric decryption, we turn "let x =
          -- sdec(m,sk) in" with the equation "sdec(senc(v,key),key) = v" into
          -- the binding "let senc(x,key),key = m,sk in"

          npl <- mapProc rules pl
          npr <- mapProc rules pr
          return $ ProcessComb c new_an npl npr
          where leftermssubst = apply subst $ toPairs leftterms
                subst = substFromList [(outvar, t1')]
                new_an = annDestructorEquation leftermssubst (toPairs rightterms) elsebranch
          )
    ( (LIT (Var svar)) , _ , _ )  | not(svar `S.member` mv) -> do
            res <- applyM (substFromList  (L.map (\x -> (x,t2)) (make_untyped_variant svar))) pl
            npl <- mapProc rules res
            return npl
    _ -> do
      npl <- mapProc rules pl
      npr <- mapProc rules pr
      return $ ProcessComb c (annElse elsebranch)  npl npr


    where t1'= toLNTerm t1
          t2'= toLNTerm t2
        -- toPairs produce a pattern match over a list. We do not use fAppList, because List is reducible and cannot be used to pattern match.
          toPairs [] = fAppOne
          toPairs [s] = s
          toPairs (p:q) = fAppPair (p, toPairs q)
          elsebranch = case pr of
            ProcessNull _ -> False
            _ -> True
            -- essentially, with let sk:skey in P, if with subsitute variable sk:skey inside P, it will not substitute untyped occurences of sk, which is bad.
          make_untyped_variant svar@(SapicLVar sl_var (Just _)) =
            [svar, (SapicLVar sl_var Nothing)]
          make_untyped_variant svar = [svar]

mapProc rules (ProcessComb c ann pl pr) = do
  npl <- mapProc rules pl
  npr <- mapProc rules pr
  return $ ProcessComb c ann npl npr

findRule :: FunSym
            -> Maybe ([Term (Lit Name LVar)], LVar)
            -> CtxtStRule
            -> Maybe ([Term (Lit Name LVar)], LVar)
findRule funsym acc rule =
  case ctxtStRuleToRRule rule of
    (fhs `RRule` rhs) ->
      case (viewTerm fhs, viewTerm rhs) of
        (FApp fs y, (Lit (Var v))) | fs == funsym -> Just (y, v)
        _ -> acc

translateLetDestr :: ( MonadThrow m)
                    =>  Set CtxtStRule -> LProcess (ProcessAnnotation LVar) -> m (LProcess (ProcessAnnotation LVar))
translateLetDestr rules anp = mapProc rules anp
