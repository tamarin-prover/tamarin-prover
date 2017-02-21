{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE DeriveAnyClass  #-}
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

import           GHC.Generics                   (Generic)
import           Data.Binary
import qualified Data.DAG.Simple                as D (cyclic, reachableSet)
import qualified Data.Foldable                  as F
import           Data.List
import qualified Data.Map                       as M
import           Data.Maybe                     (fromMaybe, listToMaybe)
-- import           Data.Monoid
import qualified Data.Set                       as S
import           Safe                           (headMay)

import           Control.Basics
import           Control.Category
import           Control.DeepSeq
import           Control.Monad.Reader

import qualified Extension.Data.Label           as L
import           Extension.Prelude

-- import           Theory.Constraint.Solver.Types
import           Theory.Constraint.System
import           Theory.Model
import           Theory.Tools.IntruderRules
import           Theory.Text.Pretty

import           Term.Rewriting.Norm            (maybeNotNfSubterms, nf')

-- import           Debug.Trace

------------------------------------------------------------------------------
-- Contradictions
------------------------------------------------------------------------------

-- | Reasons why a constraint 'System' can be contradictory.
data Contradiction =
    Cyclic                         -- ^ The paths are cyclic.
  | NonNormalTerms                 -- ^ Has terms that are not in normal form.
  -- | NonLastNode                    -- ^ Has a non-silent node after the last node.
  | ForbiddenExp                   -- ^ Forbidden Exp-down rule instance
  | ForbiddenBP                    -- ^ Forbidden bilinear pairing rule instance
  | ForbiddenKD                    -- ^ has forbidden KD-fact
  | ImpossibleChain                -- ^ has impossible chain
  | ForbiddenChain                 -- ^ has forbidden chain
  | NonInjectiveFactInstance (NodeId, NodeId, NodeId)
    -- ^ Contradicts that certain facts have unique instances.
  | IncompatibleEqs                -- ^ Incompatible equalities.
  | FormulasFalse                  -- ^ False in formulas
  | SuperfluousLearn LNTerm NodeId -- ^ A term is derived both before and after a learn
  | NodeAfterLast (NodeId, NodeId) -- ^ There is a node after the last node.
  deriving( Eq, Ord, Show, Generic, NFData, Binary )


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
    -- FIXME: add CR-rule
    , guard (hasForbiddenKD sys)                    *> pure ForbiddenKD
    -- FIXME: add CR-rule
    , guard (hasImpossibleChain ctxt sys)           *> pure ImpossibleChain
    -- CR-rule *N7*
    , guard (enableDH msig && hasForbiddenExp sys)  *> pure ForbiddenExp
    -- FIXME: add CR-rule
    , guard (enableBP msig && hasForbiddenBP sys)   *> pure ForbiddenBP
    -- New CR-Rule *N6'*
    , guard (hasForbiddenChain sys)                 *> pure ForbiddenChain
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
    sig  = L.get pcSignature ctxt
    msig = mhMaudeSig . L.get pcMaudeHandle $ ctxt

-- | New normal form condition:
-- We do not allow @KD(t)@ facts if @t@ does not contain
-- any fresh names or private functions.
hasForbiddenKD :: System -> Bool
hasForbiddenKD sys = (not $ isDiffSystem sys) &&
    (any isForbiddenKD $ M.elems $ L.get sNodes sys)
  where
    isForbiddenKD ru = fromMaybe False $ do
        [conc] <- return $ L.get rConcs ru
        (DnK, t) <- kFactView conc
        return $ neverContainsFreshPriv t


-- | True iff there are terms in the node constraints that are not in normal form wrt.
-- to 'Term.Rewriting.Norm.norm' (DH/AC).
hasNonNormalTerms :: SignatureWithMaude -> System -> Bool
hasNonNormalTerms sig se = -- trace ("non-normal terms" ++ show (maybeNonNormalTerms hnd se) ++ " -- " ++ show (map ((`runReader` hnd) . nf') (maybeNonNormalTerms hnd se)) ) $
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

substCreatesNonNormalTerms :: MaudeHandle -> System -> LNSubst -> LNSubstVFresh -> Bool
substCreatesNonNormalTerms hnd sys fsubst =
    \subst -> any (not . nfApply subst) terms
  where terms = apply fsubst $ maybeNonNormalTerms hnd sys
        nfApply subst0 t = t == t'  || nf' t' `runReader` hnd
          where tvars = freesList t
                subst = restrictVFresh tvars subst0
                t'    = apply (freshToFreeAvoidingFast subst tvars) t


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
                           (k `S.member` D.reachableSet [j] less
                             || isLast se k)

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

-- | Detect impossible chains early by checking if
-- it is possible to deduce the chain-end from the
-- chain-start by extending the chain or replacing
-- it with an edge.
hasImpossibleChain :: ProofContext -> System -> Bool
hasImpossibleChain ctxt sys = {-trace (show (L.get pcTrueSubterm ctxt)) $-}
    any impossibleChain [ (c,p) | ChainG c p <- M.keys $ L.get sGoals sys ]
  where
    impossibleChain (c,p) = fromMaybe False $ do
        (DnK, t_start) <- kFactView $ nodeConcFact c sys
        (DnK, t_end)   <- kFactView $ nodePremFact p sys
        -- the possible root symbols after applying deconstruction
        -- rules to the chain-start if they can be determined
        poss_end_syms  <- possibleRootSyms t_start
        -- the chain is impossible if both the required root-symbol
        -- and the possible root-symbols for the chain-end can be
        -- determined and the required symbol is not possible.
        if (L.get pcTrueSubterm ctxt)
           then do
              -- the root symbol of the chain-end if it can be determined
              req_end_sym_subterm <- rootSym t_end
              return $ not  (req_end_sym_subterm `elem` poss_end_syms)
           else do
              -- the root symbols of the chain-end if they can be determined
              req_end_sym_gen     <- possibleEndSyms t_end
              return $ null (req_end_sym_gen `intersect` poss_end_syms)

    rootSym :: LNTerm -> Maybe (Either LSort FunSym)
    rootSym t =
      case viewTerm t of
        FApp sym _                           -> return $ Right sym
        Lit _ | sortOfLNTerm t == LSortMsg   -> Nothing
                  -- we cannot determine the root symbols of a message-variable
              | otherwise                    -> return $ Left (sortOfLNTerm t)
                  -- a public or fresh name or variable

    possibleEndSyms :: LNTerm -> Maybe [Either LSort FunSym]
    possibleEndSyms t = case viewTerm2 t of
        FExp   a _b -> -- cannot obtain a subterm of the exponents @_b@
            ((Right (NoEq expSym)):) <$> possibleEndSyms a
        FPMult _b a -> -- cannot obtain a subterm of the scalars @_b@
            ((Right <$> [NoEq expSym, NoEq pmultSym, C EMap])++) <$> possibleEndSyms a
        FEMap _ _   -> return [Right (C EMap)]
        _ -> case viewTerm t of
                 Lit _       -> (:[]) <$> rootSym t
                 FApp o args -> ((Right o):) . concat <$> mapM possibleEndSyms args

    possibleRootSyms :: LNTerm -> Maybe [Either LSort FunSym]
    possibleRootSyms t | neverContainsFreshPriv t = return []
      -- this is an 'isForbiddenDeconstruction'
    possibleRootSyms t = case viewTerm2 t of
        FExp   a _b -> -- cannot obtain a subterm of the exponents @_b@
            ((Right (NoEq expSym)):) <$> possibleRootSyms a
        FPMult _b a -> -- cannot obtain a subterm of the scalars @_b@
            ((Right <$> [NoEq expSym, NoEq pmultSym, C EMap])++) <$> possibleRootSyms a
        FEMap _ _   -> return [Right (C EMap)]
        _ -> case viewTerm t of
                 Lit _       -> (:[]) <$> rootSym t
                 FApp o args -> ((Right o):) . concat <$> mapM possibleRootSyms args


-- | Detect non-normal chains ending in rules other than IEquality
-- and starting from a KD(x) that follows from a KU(x).
hasForbiddenChain :: System -> Bool
hasForbiddenChain sys =
    any illegalChain [ (c,p) | ChainG c p <- M.keys $ L.get sGoals sys ]
  where
    illegalChain :: (NodeConc, NodePrem) -> Bool
    illegalChain (c,p) = fromMaybe False $ do
        -- start and end terms of the chain
        (DnK, t_start)  <- kFactView $ nodeConcFact c sys
        (DnK, _)        <- kFactView $ nodePremFact p sys
        -- check whether the chain starts with a msg var
        is_msg_var      <- pure $ isMsgVar t_start
        -- and whether we do not have an equality rule instance at the end
        is_not_equality <- pure $ not $ isIEqualityRule $ nodeRule (fst p) sys
        -- get all KU-facts with the same msg var
        ku_start        <- pure $ filter (\x -> (fst x) == t_start) $ map (\(i, _, m) -> (m, i)) $ allKUActions sys 
        -- and check whether any of them happens before the KD-conclusion
        ku_before       <- pure $ any (\(_, x) -> alwaysBefore sys x (fst c)) ku_start 
        return (is_msg_var && is_not_equality && ku_before)

-- Diffie-Hellman and Bilinear Pairing
--------------------------------------

-- | 'True' if there is a @Exp-down@ rule that is not allowed in
-- a normal dependency graph.
hasForbiddenExp :: System -> Bool
hasForbiddenExp sys =
    any forbiddenDExp $ M.toList $ L.get sNodes sys
  where
    forbiddenDExp (i,ru) = fromMaybe False $ do
        [p1,p2] <- return $ L.get rPrems ru
        [conc]  <- return $ L.get rConcs ru
        (DnK, viewTerm2 -> FExp _ _) <- kFactView p1
        (UpK, b                    ) <- kFactView p2
        case kFactView conc of
          Just (DnK, viewTerm2 -> FExp g c) ->
              -- For a forbidden dexp, the following conditions must hold: g does not
              -- contain fresh names/vars, all msg vars in g must be KU-known earlier,
              -- and the factors of c are already factors of b
              return $    (isSimpleTerm g && allMsgVarsKnownEarlier i (varTerm <$> frees g))
                       && (niFactors c \\ niFactors b == [])
          Just (DnK, g)                     ->
              return $ isSimpleTerm g && allMsgVarsKnownEarlier i (varTerm <$> frees g)
          _                                -> return False

    allMsgVarsKnownEarlier i args =
        all (`elem` earlierMsgVars) (filter isMsgVar args)
      where earlierMsgVars = do (j, _, t) <- allKUActions sys
                                guard $ isMsgVar t && alwaysBefore sys j i
                                return t

-- | 'True' if there is a @Pmult-down@ or @Em-down@ rule that
-- is not allowed in a normal dependency graph.
hasForbiddenBP :: System -> Bool
hasForbiddenBP sys =
    (any isForbiddenDPMult $ M.elems $ L.get sNodes sys) ||
    (any (isForbiddenDEMap sys) $ M.toList $ L.get sNodes sys) ||
    (any (isForbiddenDEMapOrder sys) $ M.toList $ L.get sNodes sys)

-- | @isForbiddenDPMult ru@ returns @True@ if @ru@ is not allowed in
-- a normal dependency graph.
isForbiddenDPMult :: Rule a -> Bool
isForbiddenDPMult ru = fromMaybe False $ do
    [p1,p2] <- return $ L.get rPrems ru
    [conc]  <- return $ L.get rConcs ru
    (DnK, viewTerm2 -> FPMult _ _) <- kFactView p1
    (UpK, b                      ) <- kFactView p2
    (DnK, viewTerm2 -> FPMult c p) <- kFactView conc

    -- For a forbidden dpmult, the following conditions must hold: p does not
    -- contain fresh names and the factors of c are already factors of b
    return $    neverContainsFreshPriv p
             && (niFactors c \\ niFactors b == [])

-- | We detect many scenarios where a 'dem' rule followed
-- by a 'dexp' rule can be replaced by simpler variants.
-- As an example consider:
--
--   [s]P     [r]Q                              P    [r]Q
--   -------------- dem                        ------------ dem
--     em(P,Q)^(s*r)                 ==>        em(P,Q)^r
--       |           ke=inv(s)*ke'                 |        ke'
--   ------------------------------ dexp       ----------------- dexp
--      em(P,Q)^r*ke'                            em(P,Q)^r*ke'
--
-- It is also possible that r is removed or that s is added a second time
-- to the exponent.
-- FIXME: This requires a new normal-form condition
isForbiddenDEMap :: System -> (NodeId, RuleACInst) -> Bool
isForbiddenDEMap sys (i, ruExp) = fromMaybe False $ do
    guard (isDExpRule ruExp)

    ke_f      <- resolveNodePremFact (i, PremIdx 1) sys
    (UpK, ke) <- kFactView ke_f

    ruEMap <- flip nodeRule sys <$>
                 listToMaybe [ ns | Edge (ns,_) (nt,pit) <- S.toList (L.get sEdges sys)
                             , nt == i, pit == PremIdx 0 ]
    guard (isDEMapRule ruEMap)

    [sP_f, rQ_f] <- return $ L.get rPrems ruEMap
    (DnK, viewTerm2 -> FPMult s p) <- kFactView sP_f
    (DnK, viewTerm2 -> FPMult r q) <- kFactView rQ_f

    return (overComplicated s p ke || overComplicated r q ke)
  where
    overComplicated scalar point ke =
        (niFactors scalar \\ niFactors ke == []) && neverContainsFreshPriv point

-- | We enforce that if both premises of the @Emap-down@ rule
-- KD([s]p), KD([r]q) --> KD(em(p,q)^(s*r) (where s,r are not
-- products) are provided by @IRecv@ and protocol rules @P1@ and
-- @P2@, then the factTags of @P1@ cannot be greater than the
-- factTags of @P2@.
-- This requires another normal-form condition.
isForbiddenDEMapOrder :: System -> (NodeId, RuleACInst) -> Bool
isForbiddenDEMapOrder sys (i, ruDEMap) = fromMaybe False $ do
    guard (isDEMapRule ruDEMap)

    -- ensure that ruDEMap is instance of the right rule
    [f_p0, f_p1] <- return $ L.get rPrems ruDEMap
    [f_c0] <- return $ L.get rConcs ruDEMap
    (DnK, viewTerm2 -> FPMult s p) <- kFactView f_p0
    (DnK, viewTerm2 -> FPMult r q) <- kFactView f_p1
    (DnK, viewTerm2 -> FExp (viewTerm2 -> FEMap p' q') (viewTerm2 -> FMult as)) <- kFactView f_c0
    guard (((p,q) == (p',q') || (p,q) == (q',p')) && as \\ [s,r] == [])

    -- there must be at least one rule (IRecv) between 'i' and the
    -- protocol rules
    j1 <- lookupPremProvider (i,PremIdx 0)
    j2 <- lookupPremProvider (i,PremIdx 1)

    ruProto1 <- flip nodeRule sys <$> lookupPremProvider (j1, PremIdx 0)
    ruProto2 <- flip nodeRule sys <$> lookupPremProvider (j2, PremIdx 0)
    -- ensure that both are protocol rules
    guard (isStandRule ruProto1 && isStandRule ruProto2)

    return $ (factTags ruProto1) > (factTags ruProto2)
  where
    lookupPremProvider (k,prem) =
        listToMaybe [ ns | Edge (ns,_) (nt,pit) <- S.toList (L.get sEdges sys)
                    , nt == k, pit == prem ]

    factTags ru = map (map factTag) [L.get rPrems ru, L.get rConcs ru, L.get rActs ru]

    isStandRule ru = ruleInfo (isStandName . L.get praciName) (const False) $ L.get rInfo ru
    isStandName (StandRule _) = True
    isStandName _             = False


-- Pretty printing
------------------

-- | Pretty-print a 'Contradiction'.
prettyContradiction :: Document d => Contradiction -> d
prettyContradiction contra = case contra of
    Cyclic                       -> text "cyclic"
    IncompatibleEqs              -> text "incompatible equalities"
    NonNormalTerms               -> text "non-normal terms"
    ForbiddenExp                 -> text "non-normal exponentiation rule instance"
    ForbiddenBP                  -> text "non-normal bilinear pairing rule instance"
    ForbiddenKD                  -> text "forbidden KD-fact"
    ForbiddenChain               -> text "forbidden chain"
    ImpossibleChain              -> text "impossible chain"
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

  foldFreesOcc  _ _ = const mempty

  mapFrees f (SuperfluousLearn t v)       = SuperfluousLearn <$> mapFrees f t <*> mapFrees f v
  mapFrees f (NonInjectiveFactInstance x) = NonInjectiveFactInstance <$> mapFrees f x
  mapFrees f (NodeAfterLast x)            = NodeAfterLast <$> mapFrees f x
  mapFrees _ c                            = pure c
