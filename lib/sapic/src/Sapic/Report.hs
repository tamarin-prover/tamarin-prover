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

module Sapic.Report
  ( translateTermsReport
  , reportInit
  ) where

import Data.Set as S
import Data.List as L
import Sapic.Annotation
import Sapic.Facts
import Theory
import Theory.Sapic
import Term.Builtin.Signature

reportInit ::  Monad m => LProcess ann -> ([AnnotatedRule ann], Set LVar) -> m ([AnnotatedRule ann], Set LVar)
reportInit anP (initrules,initTx) = return (reportrule : initrules, initTx)
  where
        reportrule = AnnotatedRule (Just "ReportRule") anP (Right NoPosition)
                    [In $ fAppPair (varTerm x,varTerm loc)] -- prem
                    []
                    [Out $ fAppNoEq repSym [varTerm x, varTerm loc]]
                    [Ato protFact]
                    0
        var s = LVar s LSortMsg 0
        x = var "x"
        loc = var "loc"
        -- protFact =  Syntactic . Pred $ (protoFact Linear "Report" [varTerm x, varTerm loc])
        protFact =  Syntactic . Pred $ protoFact Linear "Report" [varTerm (Free x), varTerm (Free loc)]

-- | This rules use the builtin restriction system to bind the Report predicate (which must be defined by the user), to this rule.
opt_loc :: Maybe SapicTerm -> ProcessAnnotation v -> Maybe SapicTerm
opt_loc loc ann =
 case location ann.parsingAnn of
  Nothing -> loc
  Just x -> Just x

-- | Rewrite the report terms of a process. @loc@ is the location in scope: a
-- node's own location annotation replaces it for that node and its subtree.
reportMapTerms :: Maybe SapicTerm
            -> LProcess (ProcessAnnotation LVar)
            -> LProcess (ProcessAnnotation LVar)
reportMapTerms _  (ProcessNull ann)  = ProcessNull ann
reportMapTerms loc (ProcessAction ac ann p') = ProcessAction (reportMapTermsAction (opt_loc loc ann) ac) ann
  $ reportMapTerms (opt_loc loc ann) p'
reportMapTerms loc (ProcessComb c ann pl pr) = ProcessComb (reportMapTermsComb (opt_loc loc ann) c) ann
  (reportMapTerms (opt_loc loc ann) pl)
  (reportMapTerms (opt_loc loc ann) pr)
reportMapTermsAction :: Maybe SapicTerm
            -> LSapicAction
            -> LSapicAction
reportMapTermsAction loc ac
        | (New v) <- ac = New v -- a name binding holds no term
        | (ChIn  mt t vs) <- ac   = ChIn (fmap f mt) (f t) vs
        | (ChOut mt t) <- ac   = ChOut (fmap f mt) (f t)
        | (Insert t1 t2) <- ac = Insert (f t1) (f t2)
        | (Delete t) <- ac     = Delete (f t)
        | (Lock t) <- ac       = Lock (f t)
        | (Unlock t) <- ac     = Unlock (f t)
        | (Event fa) <- ac      = Event (fmap f fa)
        | (MSR l a r rest vs) <- ac  = MSR (f2mapf l) (f2mapf a) (f2mapf r) (L.map (substFormula loc) rest) vs
        |  Rep <- ac            = Rep
        |  (ProcessCall _ _) <- ac  = ac
            where f = subst loc
                  f2mapf = L.map (fmap f)
reportMapTermsComb :: Maybe SapicTerm
            -> ProcessCombinator SapicLVar
            -> ProcessCombinator SapicLVar
reportMapTermsComb loc c
        | (Cond fm) <- c = Cond (substFormula loc fm)
        | (CondEq t1 t2) <- c = CondEq (f t1) (f t2)
        | (Let t1 t2 vs) <- c = Let (f t1) (f t2) vs
        | (Lookup t v) <- c = Lookup (f t) v
        | otherwise = c
            where f = subst loc

-- | Rewrite every @report(t)@ in a term to @rep(t, loc)@. Without a location
-- the term is unchanged. Applications are rebuilt with @fApp@, which keeps an
-- AC argument list in normal form.
subst :: Ord l => Maybe (Term l) -> Term l -> Term l
subst Nothing t = t
subst (Just loc) t = case viewTerm t of
  Lit _ -> t
  FApp (NoEq sym) [a] | sym == reportSym -> fAppNoEq repSym [subst (Just loc) a, loc]
  FApp k as -> fApp k (L.map (subst (Just loc)) as)

-- | @subst@ on the terms of a formula. Formula terms have @BVar@ variables, so
-- the location's variables are wrapped in @Free@.
substFormula :: Maybe SapicTerm -> SapicFormula -> SapicFormula
substFormula loc = mapAtoms (const (fmap (subst (fmap (fmap (fmap Free)) loc))))

translateTermsReport :: LProcess (ProcessAnnotation LVar) -> LProcess (ProcessAnnotation LVar)
translateTermsReport = reportMapTerms Nothing
