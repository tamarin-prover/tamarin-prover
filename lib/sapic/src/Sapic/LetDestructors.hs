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
-- import           Control.Exception
-- import           Control.Monad.Catch
-- import           Control.Monad.Fresh
import           Data.Set as S
import           Data.List as L
import           Sapic.Annotation
import           Sapic.Facts
-- import           Sapic.Exceptions
import           Theory
import           Theory.Sapic
import           Term.Builtin.Signature
import Term.SubtermRule

 -- case ctxtStRuleToRRule r of
 --  (lhs `RRule` rhs) ->

mapProc rules  (ProcessNull ann)  = ProcessNull ann
mapProc rules (ProcessAction ac ann p') = ProcessAction (ac) ann
  $ mapProc rules p'


mapProc rules (ProcessComb c ann pl pr) = ProcessComb c (annComb rules c ann pr)
  (mapProc rules pl)
  (mapProc rules pr)

findRule funsym acc rule =
  case ctxtStRuleToRRule rule of
    (fhs `RRule` rhs) ->
      case (viewTerm fhs, viewTerm rhs) of
        (FApp fs y, (Lit (Var v))) | fs == funsym -> Just (y, v)
        _ -> acc

annComb rules (Let t1 t2) _ pr =
  case (viewTerm t1', viewTerm t2') of
    ((Lit (Var _)), FApp funsym@(NoEq (f, (_,_,Destructor))) rightterms) ->
      -- we are in the case where the let binding is of the form let invar = dest(rightTerms) in
      case  L.foldl (findRule funsym) Nothing rules of
        Nothing -> annElse elsebranch
        Just  (leftterms, outvar) ->
          -- We extract the equation of the dest, in the case where it is of the
          -- form dest(lefTerms) = outvar.

          -- in this case, we are going to transform the let binding into a
          -- binding of the form let leftterms Sigma = rightterms, where Sigma is the substitution outvar -> invar

          -- e.g in the case of symmetric decryption, we turn "let x =
          -- sdec(m,sk) in" with the equation "sdec(senc(v,key),key) = v" into
          -- the binding "let senc(x,key),key = m,sk in"

          annDestructorEquation leftermssubst (toPairs rightterms) elsebranch
          where leftermssubst = apply subst $ toPairs leftterms
                subst = substFromList [(outvar, t1')]
    _ -> annElse elsebranch
    where t1'= toLNTerm t1
          t2'= toLNTerm t2
          toPairs [] = fAppOne
          toPairs [s] = s
          toPairs (p:q) = fAppPair (p, toPairs q)
          elsebranch = case pr of
            ProcessNull _ -> False
            _ -> True

annComb _ _ ann _ = ann

translateLetDestr ::  Set CtxtStRule -> LProcess (ProcessAnnotation LVar) -> LProcess (ProcessAnnotation LVar)
translateLetDestr rules anp = mapProc rules anp
