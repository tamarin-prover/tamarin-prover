-- | This module implements normalization with respect to DH u AC using class
--   rewriting. It relies on the Maude based AC-unification module.
module Term.Rewriting.NormMaude where

import MatchAC
import Substitution

import Term
import Utils

-- *****************************************************************************
-- Normalization by class rewriting mod AC (R,E)
-- *****************************************************************************

-- | @norm1 rules t@ applies one rewriting step to @t@ for the rewriting theory @rules@.
--   Formally : If there is a unifier sigma for a non-variable position @p@ of @t@ and
--              an @l@ for a rule @l -> r@, then return @t[s(r)]p@.
norm1 :: [Rule VTerm] -> VTerm -> Term Atom
norm1 rules0 t =
 case [(p,m',subst) | (m,m') <- rules, p <- reverse ps, subst <- match' (t >* p) m] of
   (p,m',subst):_ -> t >=* (applyS2T subst m',p)
   [] -> t
 where ps = positionsNonVar t
       rules = renameRulesAwayFrom rules0 (vars t)

-- | @normRewrite rules t@ uses class rewriting DH,AC to normalize terms.
normRewrite :: [Rule VTerm] -> VTerm -> VTerm
normRewrite rules = fixpoint (norm1 rules)