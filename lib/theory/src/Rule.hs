{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Rule (
    module Rule
    ,module Items.RuleItem
)where

import Items.RuleItem

import Prelude                             hiding (id, (.))

import Control.Category

import qualified Extension.Data.Label                as L

import Theory.Model
import Theory.Proof
import Theory.Tools.RuleVariants

import Term.Macro
import Theory.Constraint.Solver.Sources (IntegerParameters)
import Data.Maybe (maybeToList, listToMaybe)
import Data.List (nub)
import qualified Data.Map.Strict as M

-- | Get an OpenProtoRule's name
getOpenProtoRuleName :: OpenProtoRule -> String
getOpenProtoRuleName (OpenProtoRule ruE _) = getRuleName ruE

-- | Add the diff label to an OpenProtoRule
addProtoDiffLabel :: OpenProtoRule -> String -> OpenProtoRule
addProtoDiffLabel (OpenProtoRule ruE ruAC) label = OpenProtoRule (addDiffLabel ruE label) (fmap ((flip addDiffLabel) label) ruAC)

-- | Closing appends one parent-owned label. Remove that final occurrence when
-- reopening, retaining any identically named actions supplied by the user.
removeGeneratedDiffLabel :: String -> Rule i -> Rule i
removeGeneratedDiffLabel label = L.modify rActs (reverse . removeFirst . reverse)
  where
    marker = protoFact Linear label []
    removeFirst [] = []
    removeFirst (fact:rest)
      | fact == marker = rest
      | otherwise = fact : removeFirst rest

-- Relation between open and closed rule sets
---------------------------------------------

-- | All intruder rules of a set of classified rules.
intruderRules :: ClassifiedRules -> [IntrRuleAC]
intruderRules rules = do
    Rule (IntrInfo i) ps cs as nvs <- joinAllRules rules
    return $ Rule i ps cs as nvs

-- | Open a rule cache. Variants and precomputed case distinctions are dropped.
openRuleCache :: ClosedRuleCache -> OpenRuleCache
openRuleCache = intruderRules . L.get crcRules

-- | Open a protocol rule; i.e., drop variants and proof annotations.
openProtoRule :: ClosedProtoRule -> OpenProtoRule
openProtoRule r = OpenProtoRule ruleE ruleAC
  where
    ruleE   = L.get cprRuleE r
    ruleAC' = L.get cprRuleAC r
    ruleAC  = if equalUpToTerms ruleAC' ruleE
               then []
               else [ruleAC']

-- | Unfold rule variants, i.e., return one ClosedProtoRule for each
-- variant
unfoldRuleVariants :: ClosedProtoRule -> [ClosedProtoRule]
unfoldRuleVariants (ClosedProtoRule ruE ruAC@(Rule ruACInfoOld ps cs as nvs))
   | isTrivialProtoVariantAC ruAC ruE = [ClosedProtoRule ruE ruAC]
   -- Supplied or previously unfolded members already have their own names.
   -- Re-unfolding their identity substitution must not append another suffix.
   | L.get pracVariants ruACInfoOld == Disj [emptySubstVFresh]
   , ruleName ruAC /= ruleName ruE = [ClosedProtoRule ruE ruAC]
   | otherwise = map toClosedProtoRule variants
        where
          ruACInfo i = ProtoRuleACInfo (ruleVariantName i (L.get pracName ruACInfoOld)) rAttributes (Disj [emptySubstVFresh]) loopBreakers
          rAttributes = L.get pracAttributes ruACInfoOld
          loopBreakers = L.get pracLoopBreakers ruACInfoOld
          toClosedProtoRule (i, (ps', cs', as', nvs'))
            = ClosedProtoRule ruE (Rule (ruACInfo i) ps' cs' as' nvs')
          variants = zip [1::Int ..] $ map (\x -> apply x (ps, cs, as, nvs)) $ substs (L.get pracVariants ruACInfoOld)
          substs (Disj s) = map (`freshToFreeAvoiding` ruAC) s

-- | Name of an explicitly numbered member of a rule's variant family.
ruleVariantName :: Int -> ProtoRuleName -> ProtoRuleName
ruleVariantName _ FreshRule = FreshRule
ruleVariantName i (StandRule name) = StandRule $ name ++ "___VARIANT_" ++ show i

-- | Close a protocol rule; i.e., compute AC variant and source assertion
-- soundness sequent, if required.
closeProtoRule :: MaudeHandle -> [LNMacro] -> OpenProtoRule -> [ClosedProtoRule]
-- if there are no macros, we do not call applyMacroInRule to make sure that new vars are not overwritten (important for diff mode)
closeProtoRule hnd []     (OpenProtoRule ruE [])   = ClosedProtoRule ruE <$> maybeToList (variantsProtoRule hnd ruE)
closeProtoRule hnd macros (OpenProtoRule ruE [])   = ClosedProtoRule ruE <$> maybeToList (variantsProtoRule hnd (applyMacroInRule macros ruE))
closeProtoRule _   macros (OpenProtoRule ruE ruAC) =
    map (ClosedProtoRule ruE . applyMacroInRulePreservingNewVars macros) ruAC


-- | Recover a member's mirror slots and inherited actions from the same
-- correspondence. Hidden parent slots survive unfolding; visible slots must
-- have the same image under every admissible AC renaming/action selection.
diffVariantAlignment :: ProtoRuleAC -> ProtoRuleAC -> Maybe ([LNTerm], [LNFact])
diffVariantAlignment supplied canonical
  -- Exact names preserve deliberate references to hidden parent variables in
  -- added actions, including annotations on an already compiled member.
  | equalUpToAddedActions supplied canonical && substitutions supplied == substitutions canonical =
      Just (L.get rNewVars canonical, L.get rActs canonical)
  | substitutions supplied /= Disj [emptySubstVFresh]
    || substitutions canonical /= Disj [emptySubstVFresh] = Nothing
  | otherwise = do
      (inherited, _) <- listToMaybe alignments
      -- Ground slot vectors cannot distinguish variable correspondences.
      vector <- if null (frees (L.get rNewVars canonical) :: [LVar])
        then Just $ L.get rNewVars canonical
        else case take 2 $ nub [transport env | (_,env) <- alignments] of
          [slots] -> Just slots
          _ -> Nothing
      return (vector, inherited)
  where
    substitutions = L.get (pracVariants . rInfo)
    alignments = ruleAlignmentsUpToRenaming supplied canonical
    transport env = apply (substFromList [(v,varTerm w) | (v,w) <- M.toList complete] :: LNSubst)
                          (L.get rNewVars canonical)
      where
        -- An invisible canonical variable must not capture an extra action's
        -- variable (or another transported slot) in the supplied member.
        complete = foldl addHidden env (frees (L.get rNewVars canonical))
        suppliedFacts = (L.get rPrems supplied, L.get rConcs supplied, L.get rActs supplied)
        addHidden mapping v
          | M.member v mapping = mapping
          | otherwise = M.insert v fresh mapping
          where
            fresh | v `notElem` frees suppliedFacts && v `notElem` M.elems mapping = v
                  | otherwise = renameAvoiding v (suppliedFacts, canonical, M.elems mapping)

-- | Prepare a supplied diff family with one shared match matrix. Coverage and
-- unique positional alignment and added-action checks use the same matches.
-- Invalid input retains its members for the usual wellformedness diagnostics.
prepareDiffRule :: MaudeHandle -> OpenProtoRule
                -> (OpenProtoRule, [(ProtoRuleAC, [LNFact])], Bool)
prepareDiffRule hnd (OpenProtoRule ruE supplied) =
    (OpenProtoRule ruE aligned, inheritedActions, null supplied || complete)
  where
    automatic = closeProtoRule hnd [] (OpenProtoRule ruE [])
    compact = map (L.get cprRuleAC) automatic
    unfolded = map (L.get cprRuleAC) (concatMap unfoldRuleVariants automatic)
    candidates = nub (compact ++ unfolded)
    matches = [[(c, vector, inherited) | c <- candidates,
                Just (vector, inherited) <- [diffVariantAlignment p c]]
              | p <- supplied]
    inheritedActions = [(member, inherited) | (member, accepted) <- zip aligned matches,
                                            (_, _, inherited) <- accepted]
    vectors = map (nub . map (\(_, vector, _) -> vector)) matches
    aligned = zipWith align supplied vectors
    align p [vector] = L.set rNewVars vector p
    align p _ = p
    unique [_] = True
    unique _ = False
    covered c = any (any (\(candidate, _, _) -> candidate == c)) matches
    -- A matching compact member represents its whole unfolded family.
    complete = all unique vectors &&
      (all covered compact || all covered unfolded)


-- | Returns true if the REFINED sources contain open chains.
containsPartialDeconstructions :: ClosedRuleCache    -- ^ Cached rules and case distinctions.
                     -> Bool               -- ^ Result
containsPartialDeconstructions (ClosedRuleCache _ _ cases _) =
      sum (map (sum . unsolvedChainConstraints) cases) /= 0

-- | Add an action to a closed Proto Rule.
--   Note that we only add the action to the variants modulo AC, not the initial rule.
addActionClosedProtoRule :: ClosedProtoRule -> LNFact -> ClosedProtoRule
addActionClosedProtoRule (ClosedProtoRule e ac) f
   = ClosedProtoRule e (addAction ac f)
