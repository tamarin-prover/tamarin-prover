-- | Compile passive trace lemmas to ordinary protocol rules and trace formulas.
module PassiveNetwork
  ( passiveNamespace, passiveRules, guardPassiveLemma
  ) where

import Data.List (isPrefixOf)
import Data.Maybe (mapMaybe)
import qualified Data.Set as S

import Items.OpenTheoryItem
import Rule
import Theory.Model
import TheoryObject

-- | Keep generated identifiers legal in printed proof steps, but disjoint from
-- user facts, rules (including supplied AC variants), and formula actions.
passiveNamespace :: OpenTranslatedTheory -> Maybe String
passiveNamespace thy
  | any isPassiveLemma (theoryLemmas thy) = Just $
      head [p | p <- iterate (++ "_") "TamarinPassive_", not (any (isPrefixOf p) names)]
  | otherwise = Nothing
  where
    names = concatMap ruleNames (theoryRules thy)
         ++ concatMap factNames (_thyCache thy)
         ++ map (factTagName . factTag) (concatMap formulaFacts formulas)
         ++ map factTagName (S.toList (_forcedInjectiveFacts (_thyOptions thy)))
    formulas = map _lFormula (theoryLemmas thy) ++ map _rstrFormula (theoryRestrictions thy)
    ruleNames (OpenProtoRule e ac) = getRuleName e : factNames e ++ concatMap memberNames ac
    memberNames :: ProtoRuleAC -> [String]
    memberNames r = getRuleName r : factNames r
    factNames r = map (factTagName . factTag) (_rPrems r ++ _rConcs r ++ _rActs r)

unrestricted :: String -> Fact t
unrestricted prefix = protoFact Linear (prefix ++ "UnrestrictedReceive") []

-- | Append facts so existing premise/conclusion indices in proof steps keep
-- their meaning. Both receive branches still have In and hence the usual K.
passiveRules :: String -> ClosedProtoRule -> [ClosedProtoRule]
passiveRules prefix (ClosedProtoRule e ac)
  | any isInFact (_rPrems ac) =
      [ ClosedProtoRule (deliver e) (deliver ac)
      , ClosedProtoRule (fallback renameE e) (fallback renameAC ac)
      ]
  | otherwise = [ClosedProtoRule (publish e) (publish ac)]
  where
    wire m = protoFact Linear (prefix ++ "Wire") [m]
    publish r = r { _rConcs = _rConcs r ++ map wire (mapMaybe outFactView (_rConcs r)) }
    deliver r = (publish r) { _rPrems = _rPrems r ++ map wire (mapMaybe inFactView (_rPrems r)) }
    fallback renameInfo r = (publish r)
      { _rInfo = renameInfo (_rInfo r), _rActs = _rActs r ++ [unrestricted prefix] }
    renameE i = i { _preName = StandRule (prefix ++ getRuleName e) }
    renameAC i = i { _pracName = StandRule (prefix ++ getRuleName ac) }

-- | Store the effective theorem before reuse and source refinement see it.
-- The original formula is retained by applyMacroInLemma for display/reopening.
guardPassiveLemma :: Maybe String -> Lemma p -> Lemma p
guardPassiveLemma (Just prefix) l | isPassiveLemma l =
    l { _lFormula = connective passive (_lFormula l) }
  where
    connective = case _lTraceQuantifier l of
      AllTraces   -> (.==>.)
      ExistsTrace -> (.&&.)
    passive = Not (Qua Ex ("i", LSortNode) (Ato (Action (varTerm (Bound 0)) (unrestricted prefix))))
guardPassiveLemma _ l = l
