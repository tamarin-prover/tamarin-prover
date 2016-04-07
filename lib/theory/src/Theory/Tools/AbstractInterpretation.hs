{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE ViewPatterns     #-}
-- FIXME: Better solution for absTerm
{-# LANGUAGE FlexibleContexts #-}
-- |
-- Copyright   : (c) 2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
--
-- Abstract intepretation for partial evaluation of multiset rewriting
-- systems.
module Theory.Tools.AbstractInterpretation (
  -- * Combinator to define abstract interpretations
    interpretAbstractly

  -- ** Actual interpretations
  , EvaluationStyle(..)
  , partialEvaluation

  ) where

import           Debug.Trace

import           Control.Basics
import           Control.Monad.Bind
import           Control.Monad.Reader

import           Data.Label
import           Data.List
import qualified Data.Set             as S
-- import           Data.Traversable     (traverse)

import           Term.Substitution
import           Theory.Model
import           Theory.Text.Pretty


------------------------------------------------------------------------------
-- Abstract enough versions of builtin rules for computing
------------------------------------------------------------------------------


-- | Higher-order combinator to construct abstract interpreters.
interpretAbstractly
    :: (Eq s, HasFrees i, Apply i, Show i)
    => ([Equal LNFact] -> [LNSubstVFresh])
    -- ^ Unification  of equalities over facts. We assume that facts with
    -- different tags are never unified.
    -> s                  -- ^ Initial abstract state.
    -> (LNFact -> s -> s) -- ^ Add a fact to the abstract state
    -> (s -> [LNFact])    -- ^ Facts of a state.
    -> [Rule i]
    -- ^ Multiset rewriting rules to apply abstractly.
    -> [(s, [Rule i])]
    -- ^ Sequence of abstract states and refined versions of all given
    -- multiset rewriting rules.
interpretAbstractly unifyFactEqs initState addFact stateFacts rus =
    go st0
  where
    st0 = addFact (freshFact (varTerm (LVar "z" LSortFresh 0))) $
          addFact (inFact (varTerm (LVar "z" LSortMsg   0))) $
          initState

    -- Repeatedly refine all rules and add all their conclusions until the
    -- state doesn't change anymore.
    go st =
        (st, rus') : if st == st' then [] else go st'
      where
        rus' = concatMap refineRule rus
        st'  = foldl' (flip addFact) st $ concatMap (get rConcs) rus'

        -- Refine a rule in the context of an abstract state: for all premise
        -- to state facts combinations, try to solve the corresponding
        -- E-unification problem. If successful, return the rule with the
        -- unifier applied.
        refineRule ru = (`evalFreshT` avoid ru) $ do
            eqs <- forM (get rPrems ru) $ \prem -> msum $ do
                fa <- stateFacts st
                guard (factTag prem == factTag fa)
                -- we compute a list of 'FreshT []' actions for the outer msum
                return (Equal prem <$> rename fa)
            subst <- msum $ freshToFree <$> unifyFactEqs eqs
            return $ apply subst ru

-- | How to report on performing a partial evaluation.
data EvaluationStyle = Silent | Summary | Tracing

-- | Concrete partial evaluator activated with flag: --partial-evaluation
partialEvaluation :: EvaluationStyle
                  -> [ProtoRuleE] -> WithMaude (S.Set LNFact, [ProtoRuleE])
partialEvaluation evalStyle ruEs = reader $ \hnd ->
    consumeEvaluation $ interpretAbstractly
        ((`runReader` hnd) . unifyLNFactEqs)  -- FIXME: Use E-unification here
        S.empty
        (S.insert . absFact)
        S.toList
        ruEs
  where
    consumeEvaluation [] = error "partialEvaluation: impossible"
    consumeEvaluation ((st0, rus0) : rest0) =
        go (0 :: Int) st0 rus0 rest0
      where
        go _ st rus [] =
          ( st
          , nubBy eqModuloFreshnessNoAC $                 -- remove duplicates
            map ((`evalFresh` nothingUsed) . rename) rus
          )
        go i st _   ((st', rus') : rest) =
            withTrace (go (i + 1) st' rus' rest)
          where
            incDesc = " partial evaluation: step " ++ show i ++ " added " ++
                      show (S.size st' - S.size st) ++ " facts"
            withTrace = case evalStyle of
              Silent  -> id
              Summary -> trace incDesc
              Tracing -> trace $ incDesc ++ "\n\n" ++
                ( render $ nest 2 $ numbered' $ map prettyLNFact $
                  S.toList $ st' `S.difference` st ) ++ "\n"


    -- NOTE: We should use an abstract state that identifies all variables at
    -- the same position provided they have the same sort.
    absFact :: LNFact -> LNFact
    absFact fa = case fa of
        Fact OutFact _ -> outFact (varTerm (LVar "z" LSortMsg 0))
        Fact tag ts    -> Fact tag $ evalAbstraction $ traverse absTerm ts
      where
        evalAbstraction = (`evalBind` noBindings) . (`evalFreshT` nothingUsed)

        absTerm t = case viewTerm t of
          Lit (Con _)                   -> pure t
          FApp (sym@(NoEq _)) ts
                                        -> fApp sym <$> traverse absTerm ts
          _                             -> importBinding mkVar t (varName t)
          where
            mkVar name idx        = varTerm (LVar name (sortOfLNTerm t) idx)
            varName (viewTerm -> Lit (Var v)) = lvarName v
            varName _                         = "z"

{- FIXME: Implement

-- | Perform a simple propagation of sorts at the fact level.
propagateSorts :: [ProtoRuleE]
               -> WithMaude (M.Map FactTag [LSort], [ProtoRuleE])
propagateSorts ruEs = reader $ \hnd ->

-}
