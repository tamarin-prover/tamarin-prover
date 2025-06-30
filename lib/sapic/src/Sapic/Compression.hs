-- |
-- Copyright   : (c) 2019 Charlie Jacomme <charlie.jacomme@lsv.fr>
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- We try to compress as much as possible the MSR rules
--
--

-- Two rules can be merged if they do not merge obaservable actions.
--

module Sapic.Compression
  ( pathCompression
  ) where

import Control.Monad.Catch
import Data.List qualified as List
import Data.Set qualified as S

import Theory
import Sapic.Facts

-- We compress as much as possible silent actions


noCompressSapicKeyWords :: [String]
noCompressSapicKeyWords = ["IsIn", "IsNotSet", "Insert", "Delete",  "Lock", "Unlock", "Progress" ]

isSapicNoCompress :: Fact LNTerm -> Bool
isSapicNoCompress (Fact (ProtoFact _ name _) _ _) =
  any (`List.isPrefixOf` name) noCompressSapicKeyWords
isSapicNoCompress _ = False

isStateProcessFact  :: Fact LNTerm -> Bool
isStateProcessFact f = isStateFact f || isLetFact f

sameName :: Fact LNTerm ->  Fact LNTerm -> Bool
sameName  (Fact (ProtoFact _ name _) _ _)  (Fact (ProtoFact _ name2 _) _ _) = name==name2
sameName _ _ = False

-- get all rules with premice the given fact
getPremRules:: Fact LNTerm ->  [Rule ProtoRuleEInfo] -> ([Rule ProtoRuleEInfo],[Rule ProtoRuleEInfo])
getPremRules fact = List.partition  (List.any (sameName fact) . (._rPrems))

-- get all rules producing the given fact
getConcsRules:: Fact LNTerm ->  [Rule ProtoRuleEInfo] -> ([Rule ProtoRuleEInfo],[Rule ProtoRuleEInfo])
getConcsRules fact = List.partition  (List.any (sameName fact) . (._rConcs))

-- Get the list of all state facts produced by a rule
getProducedFacts :: [Rule ProtoRuleEInfo] -> S.Set (Fact LNTerm)
getProducedFacts rules = facts
  where
    facts = List.foldl (\acc (Rule _ _ rconc _ _) ->
                              List.foldl (flip S.insert) acc (List.filter isStateProcessFact rconc)
                           ) S.empty rules

mergeInfo :: ProtoRuleEInfo -> ProtoRuleEInfo -> ProtoRuleEInfo
mergeInfo (ProtoRuleEInfo (StandRule name) attr res) (ProtoRuleEInfo (StandRule name2) attr2 res2) =
  ProtoRuleEInfo (StandRule (mergeStand name name2)) (mergeAttrs attr attr2) (res ++ res2)
 where
       mergeStand n _ = n  -- ++ "_" ++ n'
       -- NOTE: concatenating makes veryyyy big name rules, that completely make the the graphs unreadble
       -- NOTE: if we reintroduce Yavor's Dot output, recall 9e7e99fe070776172bd09cb977e8d3a83da3ed51
       mergeAttrs a a' =  a <> a'
mergeInfo _ _ = error "FreshRule(s) passed to mergeInfo"


canMerge  :: Bool -> Rule ProtoRuleEInfo -> Rule ProtoRuleEInfo -> Bool
canMerge compEvents r1 r2
  | any isSapicNoCompress ract && any isSapicNoCompress ract2  = False  -- we cannot merge rules if it makes events be simulataneous

  | not compEvents && (ract /= []) && (ract2 /= [])  = False  -- we cannot merge rules if it makes events be simulataneous
  | (List.length rprem2' > 1) && (List.length rconc >1) = False   -- we cannot merge rules if we are breaking asynchronous behavior (i.e u->v,w and w,r->t cannot be compress, as r might be produced byi
  | (List.length rconc > 1) && (ract2 /= []) = False   -- we cannot merge rules if we are breaking asynchronous behavior (i.e u->v,w, and v-E->t cannot be compressed, else an event that could have happened with w before E cannot do so anymore.
  | List.any isOutFact rconc && List.any isOutFact rconc2 = False -- we cannot merge rules if two Out become simultaneous (might break the fact that the attacker can know smth and not smth else at a timepoint
  | List.any isLetFact rconc ||  List.any isLetFact rprem   = False -- we cannot merge rules when we are performing a let pattern matching
  | List.any isOutFact rconc && (ract2 /= []) = False -- we cannot merge rules if a Out and an event become simultaneous (might break the fact that the attacker can know smth and not smth else at a timepoint
  |otherwise = True
  where Rule _ rprem rconc ract _ = r1
        Rule _ rprem2 rconc2 ract2 _ = r2
        rprem2' = List.filter (not . isLockFact) rprem2

-- We try to merge two rules together, and add the result or themselves in case of failure to a set
merge:: Bool -> Rule ProtoRuleEInfo -> Rule ProtoRuleEInfo -> S.Set (Rule ProtoRuleEInfo) ->S.Set (Rule ProtoRuleEInfo)
merge compEvents rule1 rule2 ruleset =
  if canMerge compEvents rule1 rule2 then
    Rule (mergeInfo rinfo rinfo2) newprem newrconc (ract `List.union` ract2) (rnew++rnew2) `S.insert` ruleset
  else
    rule1 `S.insert` (rule2 `S.insert` ruleset)
  where Rule rinfo rprem rconc ract rnew = rule1
        Rule rinfo2 rprem2 rconc2 ract2 rnew2 = rule2
        newprem = rprem ++ List.filter (`notElem` rconc) rprem2
        newrconc = rconc2 ++ List.filter (`notElem` rprem2) rconc

-- Given two set of rules, such that the leftrules all produce a state (the same) consumed by the right rules, try to compress rules for each possible pairing between rules in leftrules and rightrules
mergeRules:: Bool -> [Rule ProtoRuleEInfo] -> [Rule ProtoRuleEInfo] -> [Rule ProtoRuleEInfo]
mergeRules compEvents leftrules rightrules =
  if List.length leftrules == 1 && List.length rightrules == 1 then
    S.toList rulesset
  else
    leftrules ++ rightrules
  where rulesset = List.foldl (\set l -> List.foldl (flip (merge compEvents l)) set rightrules) S.empty leftrules


-- simpR ( Rule (ProtoRuleEInfo (StandRule name) _ _) rprem rconc ract rnew) =  ( Rule (ProtoRuleEInfo (StandRule name) [] []) rprem rconc ract rnew)

  -- Given a fact and an msr, compress the msr with respect to this fact, and return the new msr, and the new facts (facts reachable in one step from the fact) that we may try to compress
compressOne :: Bool -> Fact LNTerm -> [Rule ProtoRuleEInfo] -> ([Rule ProtoRuleEInfo], S.Set (Fact LNTerm))
compressOne compEvents fact msr
  | isPersistentFact fact =  (msr, new_facts)
  | otherwise =  (msr3 ++ new_rules, new_facts)
  where (prem_rules,msr2) = getPremRules fact msr
        (concs_rules,msr3) =  getConcsRules fact msr2
        new_rules = mergeRules compEvents concs_rules prem_rules
        new_facts =  getProducedFacts new_rules

-- Compress one by one the facts inside the given list, maintaining a set of already compressed facts to avoid loops, and adding the new facts to explore progressively.
compress :: Bool -> [Fact LNTerm] -> S.Set (Fact LNTerm) -> [Rule ProtoRuleEInfo] -> [Rule ProtoRuleEInfo]
compress _ [] _ msr = msr
compress compEvents (fact:remainder) compressed_facts msr =
  compress compEvents new_facts_remainder new_compressed_facts new_msr
  where (new_msr,new_facts) = compressOne compEvents fact msr
        new_compressed_facts = fact `S.insert` compressed_facts
        new_facts_no_compress = new_facts S.\\ new_compressed_facts
        new_facts_no_remainder = new_facts_no_compress S.\\ S.fromList remainder
        new_facts_remainder = S.toList new_facts_no_remainder++remainder   -- we avoid duplicates between remainder and newfactsnocompress


-- Start the compression by the init fact introduced by the translation
pathCompression:: MonadCatch m =>
    Bool -> [Rule ProtoRuleEInfo] -> m [Rule ProtoRuleEInfo]
pathCompression compEvents msr =
  return $ filterDeadend $ compress compEvents [initfact] S.empty msr
  where initfact = Sapic.Facts.factToFact (State LState [] S.empty)
         -- in the end, we remove the useless dangling rules
        filterDeadend = List.filter (\  (Rule _ _ rconc ract _) ->
                                          not (null ract && null rconc)  )
