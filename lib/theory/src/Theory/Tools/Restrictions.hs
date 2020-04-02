-- |
-- Copyright   : (c) 2020 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert.kuennemann@cispa.saarland>
-- Portability : GHC only
--
-- Tools for transforming rule-level restrictions

module Restriction (
    fromRuleRestriction
)

-- | From f, create restriction with rname and an action to insert in some protocol rule
fromRuleRestriction rname f =
                (mkRestriction rname,  mkFact rname getVarTerms)
            where

                --- canot handle predicates with reducible function symbols
                -- what we should do:
                -- 1. find those in f
                -- 2. substitute by variables
                -- 3. quantify over variables in restriction
                -- 3. in actions, create fact with these terms

                -- creates restriction with prefix "restr_"++rname and counter n
                -- and formula f quantified over free variables and varnow
                mkRestriction:: String -> (Int,LNFormula) -> Restriction
                mkRestriction rname (n,f) = Restriction
                                        ("restr_"++ nameSuffix rname n)
                                        (foldr (hinted forall) f'' (frees' f'))
                                        where
                                            f'' = Ato (Action timepoint (facts (n,f'))) .==>. f'
                                            f' = rewrF f
                                            timepoint = varTerm $ Free varNow
                                            facts = mkFact rname getBVarTerms

                nameSuffix rname n = rname ++ "_" ++ show n

                -- rewrite f so all formulas with free variables are substituted by fresh free variables. 
                -- output modified formula and substitution
                rewrite f = evalFreshT (State.runState (traverseFormulaAtom fAt' f) emptySubst) 0
                -- fAt' ::ProtoAtom syn1 (VTerm Name (BVar v1))
                --     -> State.StateT (Subst c v) Identity (ProtoFormula syn2 s c2 LNTerm)
                fAt' atom = Ato <$> traverse fAt atom
                -- fAt :: State.MonadState (Subst c v) m => LNTerm -> m LNTerm
                fAt t = if contains_free t then do
                                v <- freshLVar "par" LSortMsg
                                m <- State.get
                                State.put (insert v t m)
                                return $ varTerm  $ Free v
                            else 
                                return t
                -- (f,emptySubst)
                rewrF = fst . rewrite -- rewritten formula
                -- rewrSubst = snd . rewrite -- substitution
                contains_free t = True

                frees' f = frees f `L.union` [varNow]

                getBVarTerms =  map (varTerm . Free) . L.delete varNow . frees
                getVarTerms =   map (varTerm) . frees 
                mkFact  rname getTerms (n,f)  =
                        protoFactAnn 
                            Linear ("_rstr_"++ nameSuffix rname n) 
                            S.empty  -- no annotations
                            (getTerms f) -- TODO apply substitution
                            -- (apply (rewrSubst f) getTerms f) -- does not work need to get expanded formula



