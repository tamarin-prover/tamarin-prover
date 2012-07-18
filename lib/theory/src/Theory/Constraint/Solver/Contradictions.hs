{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- This is the public interface for constructing and deconstructing constraint
-- systems. The interface for performing constraint solving provided by
-- "Theory.Constraint.Solver".
module Theory.Constraint.Solver.Contradictions (

  -- * Contradictory constraint systems
    Contradiction(..)
  , substCreatesNonNormalTerms
  , contradictions
  , contradictorySystem

  -- ** Pretty-printing
  , prettyContradiction

  ) where

import           Prelude                        hiding (id, (.))

import           Data.Binary
import qualified Data.DAG.Simple                as D (cyclic, reachableSet)
import           Data.DeriveTH
import qualified Data.Foldable                  as F
import           Data.List
import qualified Data.Map                       as M
import           Data.Maybe                     (fromMaybe)
import           Data.Monoid
import qualified Data.Set                       as S
import           Safe                           (headMay)

import           Control.Basics
import           Control.Category
import           Control.DeepSeq
import           Control.Monad.Reader

import qualified Extension.Data.Label           as L
import           Extension.Prelude

import           Theory.Constraint.Solver.Types
import           Theory.Constraint.System
import           Theory.Model
import           Theory.Text.Pretty

import           Term.Rewriting.Norm            (maybeNotNfSubterms, nf')


------------------------------------------------------------------------------
-- Contradictions
------------------------------------------------------------------------------

-- | Reasons why a constraint 'System' can be contradictory.
data Contradiction =
    Cyclic                         -- ^ The paths are cyclic.
  | NonNormalTerms                 -- ^ Has terms that are not in normal form.
  -- | NonLastNode                    -- ^ Has a non-silent node after the last node.
  | ForbiddenExp                   -- ^ Forbidden Exp-down rule instance
  | NonInjectiveFactInstance (NodeId, NodeId, NodeId)
    -- ^ Contradicts that certain facts have unique instances.
  | IncompatibleEqs                -- ^ Incompatible equalities.
  | FormulasFalse                  -- ^ False in formulas
  | SuperfluousLearn LNTerm NodeId -- ^ A term is derived both before and after a learn
  | NodeAfterLast (NodeId, NodeId) -- ^ There is a node after the last node.
  deriving( Eq, Ord, Show )


-- | 'True' if the constraint system is contradictory.
contradictorySystem :: ProofContext -> System -> Bool
contradictorySystem ctxt = not . null . contradictions ctxt

-- | All CR-rules reducing a constraint system to *⟂* represented as a list of
-- trivial contradictions. Note that some constraint systems are also removed
-- because they have no unifier. This is part of unification. Note also that
-- *S_{¬,\@}* is handled as part of *S_∀*.
contradictions :: ProofContext -> System -> [Contradiction]
contradictions ctxt sys = F.asum
    -- CR-rule **
    [ guard (D.cyclic $ rawLessRel sys)             *> pure Cyclic
    -- CR-rule *N1*
    , guard (hasNonNormalTerms sig sys)             *> pure NonNormalTerms
    -- CR-rule *N7*
    , guard (hasForbiddenExp sys)                   *> pure ForbiddenExp
    -- CR-rules *S_≐* and *S_≈* are implemented via the equation store
    , guard (eqsIsFalse $ L.get sEqStore sys)       *> pure IncompatibleEqs
    -- CR-rules *S_⟂*, *S_{¬,last,1}*, *S_{¬,≐}*, *S_{¬,≈}*
    , guard (S.member gfalse $ L.get sFormulas sys) *> pure FormulasFalse
    ]
    ++
    -- This rule is not yet documented. It removes constraint systems that
    -- require a unique fact to be present in the system state more than once.
    -- Unique facts are declared as part of the specification of the rule
    -- system.
    (NonInjectiveFactInstance <$> nonInjectiveFactInstances ctxt sys)
    ++
    -- TODO: Document corresponding constraint reduction rule.
    (NodeAfterLast <$> nodesAfterLast sys)
  where
    sig = L.get pcSignature ctxt

-- | True iff there are terms in the node constraints that are not in normal form wrt.
-- to 'Term.Rewriting.Norm.norm' (DH/AC).
hasNonNormalTerms :: SignatureWithMaude -> System -> Bool
hasNonNormalTerms sig se =
    any (not . (`runReader` hnd) . nf') (maybeNonNormalTerms hnd se)
  where hnd = L.get sigmMaudeHandle sig

-- | Returns all (sub)terms of node constraints that may be not in normal form.
maybeNonNormalTerms :: MaudeHandle -> System -> [LNTerm]
maybeNonNormalTerms hnd se =
    sortednub . concatMap getTerms . M.elems . L.get sNodes $ se
  where getTerms (Rule _ ps cs as) = do
          f <- ps++cs++as
          t <- factTerms f
          maybeNotNfSubterms (mhMaudeSig hnd) t

substCreatesNonNormalTerms :: MaudeHandle -> System -> LNSubstVFresh -> Bool
substCreatesNonNormalTerms hnd se =
    \subst -> any (not . nfApply subst) terms
  where terms = maybeNonNormalTerms hnd se
        nfApply subst0 t = t == t'  || nf' t' `runReader` hnd
          where tvars = freesList t
                subst = restrictVFresh tvars subst0
                t'  = apply (freshToFreeAvoidingFast subst tvars) t

-- | True if there is no @EXP-down@ rule that should be replaced by an
-- @EXP-up@ rule.
hasForbiddenExp :: System -> Bool
hasForbiddenExp se =
    any (isForbiddenExp) $ M.elems $ L.get sNodes se

-- | @isForbiddenExp ru@ returns @True@ if @ru@ is not allowed in
-- a normal dependency graph.
--
-- > isForbiddenExp (Rule () [undefined, Fact KUFact [undefined, Mult (Inv x1) x2]]
-- >                         [Fact KDFact [expTagToTerm IsExp, Exp p1 (Mult x2 x3)]] [])
-- > False
-- > isForbiddenExp (Rule () [undefined, Fact KUFact [undefined, Mult (Inv x1) x2]]
-- >                         [Fact KDFact [expTagToTerm IsExp, Exp p1 x2]] [])
-- > True
--
isForbiddenExp :: Rule a -> Bool
isForbiddenExp ru = fromMaybe False $ do
    [p1,p2] <- return $ L.get rPrems ru
    [conc]  <- return $ L.get rConcs ru
    (DnK, viewTerm2 -> FExp _ _) <- kFactView p1
    (UpK, b                    ) <- kFactView p2
    (DnK, viewTerm2 -> FExp g c) <- kFactView conc

    -- For a forbidden exp the following conditions must hold: g must be of
    -- sort 'pub' and the required inputs for c are already required by b
    return $    sortOfLNTerm g == LSortPub
             && (inputTerms c \\ inputTerms b == [])
  where
    -- The required components to construct the message.
    inputTerms :: LNTerm -> [LNTerm]
    inputTerms (viewTerm2 -> FMult ts)    = concatMap inputTerms ts
    inputTerms (viewTerm2 -> FInv t1)     = inputTerms t1
    inputTerms (viewTerm2 -> FPair t1 t2) = inputTerms t1 ++ inputTerms t2
    inputTerms t                          = [t]

-- | Compute all contradictions to injective fact instances.
--
-- Formally, they are computed as follows. Let 'f' be a fact symbol with
-- injective instances. Let i, j, and k be temporal variables ordered
-- according to
--
--   i < j < k
--
-- and let there be an edge from (i,u) to (k,w) for some indices u and v
--
-- Then, we have a contradiction if both the premise (k,w) that requires a
-- fact 'f(t,...)' and there is a premise (j,v) requiring a fact 'f(t,...)'.
--
-- These two premises would have to be merged, but cannot due to the ordering
-- constraint 'j < k'.
nonInjectiveFactInstances :: ProofContext -> System -> [(NodeId, NodeId, NodeId)]
nonInjectiveFactInstances ctxt se = do
    Edge c@(i, _) (k, _) <- S.toList $ L.get sEdges se
    let kFaPrem            = nodeConcFact c se
        kTag               = factTag kFaPrem
        kTerm              = firstTerm kFaPrem
        conflictingFact fa = factTag fa == kTag && firstTerm fa == kTerm

    guard (kTag `S.member` L.get pcInjectiveFactInsts ctxt)
    j <- S.toList $ D.reachableSet [i] less

    let isCounterExample = (j /= i) && (j /= k) &&
                           maybe False checkRule (M.lookup j $ L.get sNodes se)

        -- FIXME: There should be a weaker version of the rule that just
        -- introduces the constraint 'k < j || k == j' here.
        checkRule jRu    = any conflictingFact (L.get rPrems jRu) &&
                           k `S.member` D.reachableSet [j] less

    guard isCounterExample
    return (i, j, k) -- counter-example to unique fact instances
  where
    less      = rawLessRel se
    firstTerm = headMay . factTerms

-- | The node-ids that must be instantiated to the trace, but are temporally
-- after the last node.
nodesAfterLast :: System -> [(NodeId, NodeId)]
nodesAfterLast sys = case L.get sLastAtom sys of
  Nothing -> []
  Just i  -> do j <- S.toList $ D.reachableSet [i] $ rawLessRel sys
                guard (j /= i && isInTrace sys j)
                return (i, j)


-- | Pretty-print a 'Contradiction'.
prettyContradiction :: Document d => Contradiction -> d
prettyContradiction contra = case contra of
    Cyclic                       -> text "cyclic"
    IncompatibleEqs              -> text "incompatible equalities"
    NonNormalTerms               -> text "non-normal terms"
    ForbiddenExp                 -> text "non-normal exponentiation instance"
    NonInjectiveFactInstance cex -> text $ "non-injective facts " ++ show cex
    FormulasFalse                -> text "from formulas"
    SuperfluousLearn m v         ->
        doubleQuotes (prettyLNTerm m) <->
        text ("derived before and after") <->
        doubleQuotes (prettyNodeId v)
    NodeAfterLast (i,j)       ->
        text $ "node " ++ show j ++ " after last node " ++ show i


-- Instances
------------

instance HasFrees Contradiction where
  foldFrees f (SuperfluousLearn t v)       = foldFrees f t `mappend` foldFrees f v
  foldFrees f (NonInjectiveFactInstance x) = foldFrees f x
  foldFrees f (NodeAfterLast x)            = foldFrees f x
  foldFrees _ _                            = mempty

  mapFrees f (SuperfluousLearn t v)       = SuperfluousLearn <$> mapFrees f t <*> mapFrees f v
  mapFrees f (NonInjectiveFactInstance x) = NonInjectiveFactInstance <$> mapFrees f x
  mapFrees f (NodeAfterLast x)            = NodeAfterLast <$> mapFrees f x
  mapFrees _ c                            = pure c

$( derive makeBinary ''Contradiction)
$( derive makeNFData ''Contradiction)
