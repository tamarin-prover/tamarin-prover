{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module TheoryObject
  ( module Lemma,
    module Items.OptionItem,
    module Items.ProcessItem,
    module Items.TheoryItem,
    module Items.CaseTestItem,
    module Items.AccLemmaItem,
    LemmaAttribute (..),
    TraceQuantifier (..),
    ProtoLemma (..),
    Theory (..),
    DiffTheory (..),
    TheoryItem (..),
    DiffTheoryItem (..),
    DiffLemma (..),
    ProcessDef (..),
    Predicate (..),
    Option (..),
    TranslationElement (..),
    TranslationElement (..),
    foldDiffTheoryItem,
    mapTheoryItem,
    mapDiffTheoryItem,
    theoryRules,
    diffTheoryDiffRules,
    diffTheorySideRules,
    leftTheoryRules,
    rightTheoryRules,
    theoryRestrictions,
    theoryLemmas,
    theoryProcesses,
    theoryProcessDefs,
    theoryPredicates,
    theoryMacros,
    theoryFormalComments,
    diffTheoryRestrictions,
    diffTheorySideRestrictions,
    diffTheoryLemmas,
    diffTheorySideLemmas,
    diffTheoryDiffLemmas,
    theoryConfigBlock,
    diffTheoryConfigBlock,
    diffTheoryMacros,
    diffTheoryFormalComments,
    expandFormula,
    expandRestriction,
    expandLemma,
    addRestriction,
    addRestrictions,
    addRules,
    addLemma,
    addLemmas,
    addDiffLemmas,
    addLemmaAtIndex,
    modifyLemma,
    addProcess,
    findProcess,
    addProcessDef,
    addPredicate,
    setOption,
    addRestrictionDiff,
    addLemmaDiff,
    addDiffLemma,
    addHeuristic,
    addDiffHeuristic,
    addTactic,
    addDiffTactic,
    addMacros,
    addDiffMacros,
    removeLemma,
    removeLemmaDiff,
    removeDiffLemma,
    addComment,
    addDiffComment,
    addStringComment,
    addFormalComment,
    addFormalCommentDiff,
    isRuleItem,
    itemToRule,
    foldTheoryItem,
    lookupDiffLemma,
    lookupLemmaDiff,
    lookupLemma,
    lookupLemmaIndex,
    getLemmaPreItems,
    lookupProcessDef,
    filterSide,
    mapMProcesses,
    mapMProcessesDef,
    theoryFunctionTypingInfos,
    theoryBuiltins,
    theoryExportInfos,
    theoryEquivLemmas,
    theoryDiffEquivLemmas,
    addFunctionTypingInfo,
    clearFunctionTypingInfos,
    addExportInfo,
    setforcedInjectiveFacts,
    filterLemma,
    lookupFunctionTypingInfo,
    prettyTheory,
    prettyMacros,
    prettyTranslationElement,
    prettyProcessDef,
    prettyEitherRestriction,
    lookupExportInfo,
    prettyRestriction,
    prettyProcess,
    prettyTactic,
    prettyVarList,
    prettyConfigBlock,
    theoryCaseTests,
    theoryAccLemmas,
    addAccLemma,
    addCaseTest,
    lookupAccLemma,
    lookupCaseTest,
  )
where

-- import Theory.Constraint.Solver.Heuristics

import Control.Basics
import Control.Parallel.Strategies
import Data.Binary
import Data.ByteString.Char8 (unpack)
import Data.ByteString.Char8 qualified as BC
import Data.List
import Data.Maybe
import Data.Set qualified as S
import GHC.Generics
import Items.AccLemmaItem
import Items.CaseTestItem
import Items.ExportInfo
import Items.OptionItem
import Items.ProcessItem
import Items.TheoryItem
import Lemma
import Pretty
import Term.LTerm
import Term.Macro
import Theory.Constraint.Solver
import Theory.Model
import Theory.Sapic
import Theory.Sapic.Print
import Theory.Syntactic.Predicate
import Theory.Text.Pretty

import Optics.Core (set, over, (%), Lens)
import Optics.TH (makeFieldLabelsNoPrefix)

-- | A theory contains a single set of rewriting rules modeling a protocol
-- and the lemmas that
data Theory sig c r p s = Theory
  { name :: String,
    inFile :: String,
    heuristic :: [GoalRanking ProofContext],
    tactic :: [Tactic ProofContext],
    signature :: sig,
    cache :: c,
    items :: [TheoryItem r p s],
    options :: Option,
    isSapic :: Bool
  }
  deriving (Eq, Ord, Show, Generic, NFData, Binary)

makeFieldLabelsNoPrefix ''Theory

-- | A diff theory contains a set of rewriting rules with diff modeling two instances
data DiffTheory sig c r r2 p p2 = DiffTheory
  { name :: String,
    inFile :: String,
    heuristic :: [GoalRanking ProofContext],
    tactic :: [Tactic ProofContext],
    signature :: sig,
    cacheLeft :: c,
    cacheRight :: c,
    diffCacheLeft :: c,
    diffCacheRight :: c,
    items :: [DiffTheoryItem r r2 p p2],
    options :: Option,
    isSapic :: Bool
  }
  deriving (Eq, Ord, Show, Generic, NFData, Binary)

makeFieldLabelsNoPrefix ''DiffTheory

-- Shared theory modification functions
---------------------------------------

filterSide :: Side -> [(Side, a)] -> [a]
filterSide s l = case l of
  x : xs -> if (fst x) == s then (snd x) : (filterSide s xs) else (filterSide s xs)
  [] -> []

-- | Fold a theory item.
foldTheoryItem ::
  (r -> a) ->
  (Restriction -> a) ->
  (Lemma p -> a) ->
  (FormalComment -> a) ->
  (ConfigBlock -> a) ->
  (Predicate -> a) ->
  ([LNMacro] -> a) ->
  (s -> a) ->
  TheoryItem r p s ->
  a
foldTheoryItem fRule fRestriction fLemma fText fConfigBlock fPredicate fMacroItem fTranslationItem i = case i of
  RuleItem ru -> fRule ru
  LemmaItem lem -> fLemma lem
  TextItem txt -> fText txt
  ConfigBlockItem b -> fConfigBlock b
  RestrictionItem rstr -> fRestriction rstr
  PredicateItem p -> fPredicate p
  MacroItem m -> fMacroItem m
  TranslationItem s -> fTranslationItem s

-- | Fold a theory item.
foldDiffTheoryItem ::
  (r -> a) ->
  ((Side, r2) -> a) ->
  (DiffLemma p -> a) ->
  ((Side, Lemma p2) -> a) ->
  ((Side, Restriction) -> a) ->
  ([LNMacro] -> a) ->
  (FormalComment -> a) ->
  (ConfigBlock -> a) ->
  DiffTheoryItem r r2 p p2 ->
  a
foldDiffTheoryItem fDiffRule fEitherRule fDiffLemma fEitherLemma fRestriction fMacroItem fText fConfigBlock i = case i of
  DiffRuleItem ru -> fDiffRule ru
  EitherRuleItem (side, ru) -> fEitherRule (side, ru)
  DiffLemmaItem lem -> fDiffLemma lem
  EitherLemmaItem (side, lem) -> fEitherLemma (side, lem)
  EitherRestrictionItem (side, rstr) -> fRestriction (side, rstr)
  DiffMacroItem m -> fMacroItem m
  DiffTextItem txt -> fText txt
  DiffConfigBlockItem b -> fConfigBlock b

-- | Map a theory item.
mapTheoryItem :: (r -> r') -> (p -> p') -> TheoryItem r p s -> TheoryItem r' p' s
mapTheoryItem f g =
  foldTheoryItem (RuleItem . f) RestrictionItem (LemmaItem . fmap g) TextItem ConfigBlockItem PredicateItem MacroItem TranslationItem

-- | Map a diff theory item.
mapDiffTheoryItem :: (r -> r') -> ((Side, r2) -> (Side, r2')) -> (DiffLemma p -> DiffLemma p') -> ((Side, Lemma p2) -> (Side, Lemma p2')) -> DiffTheoryItem r r2 p p2 -> DiffTheoryItem r' r2' p' p2'
mapDiffTheoryItem f g h i =
  foldDiffTheoryItem (DiffRuleItem . f) (EitherRuleItem . g) (DiffLemmaItem . h) (EitherLemmaItem . i) EitherRestrictionItem DiffMacroItem DiffTextItem DiffConfigBlockItem

-- | Map a process
mapMProcesses :: (Monad m) => (PlainProcess -> m (PlainProcess)) -> Theory sig c r p TranslationElement -> m (Theory sig c r p TranslationElement)
mapMProcesses f thy = do
  itms' <- mapM f' itms
  return $ set #items itms' thy
  where
    itms = thy.items
    f' (TranslationItem (ProcessItem p)) = TranslationItem . ProcessItem <$> f p
    f' (TranslationItem (DiffEquivLemma p)) = TranslationItem . DiffEquivLemma <$> f p
    f' (TranslationItem (EquivLemma p1 p2)) = do
      fp1 <- f p1
      fp2 <- f p2
      return $ TranslationItem (EquivLemma fp1 fp2)
    f' other = return other

-- | Map a process definition
mapMProcessesDef :: (Monad m) => (ProcessDef -> m (ProcessDef)) -> Theory sig c r p TranslationElement -> m (Theory sig c r p TranslationElement)
mapMProcessesDef f thy = do
  itms' <- mapM f' itms
  return $ set #items itms' thy
  where
    itms = thy.items
    f' (TranslationItem (ProcessDefItem p)) = TranslationItem . ProcessDefItem <$> f p
    f' other = return other

-- | All rules of a theory.
theoryRules :: Theory sig c r p s -> [r]
theoryRules =
  foldTheoryItem return (const []) (const []) (const []) (const []) (const []) (const []) (const []) <=< (.items)

-- | All diff rules of a theory.
diffTheoryDiffRules :: DiffTheory sig c r r2 p p2 -> [r]
diffTheoryDiffRules =
  foldDiffTheoryItem return (const []) (const []) (const []) (const []) (const []) (const []) (const []) <=< (.items)

-- | All rules of a theory.
diffTheorySideRules :: Side -> DiffTheory sig c r r2 p p2 -> [r2]
diffTheorySideRules s =
  foldDiffTheoryItem (const []) (\(x, y) -> if (x == s) then [y] else []) (const []) (const []) (const []) (const []) (const []) (const []) <=< (.items)

-- | All left rules of a theory.
leftTheoryRules :: DiffTheory sig c r r2 p p2 -> [r2]
leftTheoryRules =
  foldDiffTheoryItem (const []) (\(x, y) -> if (x == LHS) then [y] else []) (const []) (const []) (const []) (const []) (const []) (const []) <=< (.items)

-- | All right rules of a theory.
rightTheoryRules :: DiffTheory sig c r r2 p p2 -> [r2]
rightTheoryRules =
  foldDiffTheoryItem (const []) (\(x, y) -> if (x == RHS) then [y] else []) (const []) (const []) (const []) (const []) (const []) (const []) <=< (.items)

-- |  All macros of a theory.
theoryMacros :: Theory sig c r p s -> [LNMacro]
theoryMacros =
  foldTheoryItem (const []) (const []) (const []) (const []) (const []) (const []) (\m -> m) (const []) <=< (.items)

-- |  All formal comments of a theory.
theoryFormalComments :: Theory sig c r p s -> [FormalComment]
theoryFormalComments =
  foldTheoryItem (const []) (const []) (const []) return (const []) (const []) (const []) (const []) <=< (.items)

-- | All restrictions of a theory.
theoryRestrictions :: Theory sig c r p s -> [Restriction]
theoryRestrictions =
  foldTheoryItem (const []) return (const []) (const []) (const []) (const []) (const []) (const []) <=< (.items)

-- | All lemmas of a theory.
theoryLemmas :: Theory sig c r p s -> [Lemma p]
theoryLemmas =
  foldTheoryItem (const []) (const []) return (const []) (const []) (const []) (const []) (const []) <=< (.items)

translationElements :: Theory sig c1 b p c2 -> [c2]
translationElements = foldTheoryItem (const []) (const []) (const []) (const []) (const []) (const []) (const []) return <=< (.items)

-- | All CaseTest definitions of a theory.
theoryCaseTests :: Theory sig c r p TranslationElement -> [CaseTest]
theoryCaseTests t = [i | CaseTestItem i <- translationElements t]

-- | All AccLemmas definitions of a theory.
theoryAccLemmas :: Theory sig c r p TranslationElement -> [AccLemma]
theoryAccLemmas t = [i | AccLemmaItem i <- translationElements t]

-- | All processes of a theory (TODO give warning if there is more than one...)
theoryProcesses :: Theory sig c r p TranslationElement -> [PlainProcess]
theoryProcesses t = [i | ProcessItem i <- translationElements t]

-- | All process definitions of a theory.
theoryProcessDefs :: Theory sig c r p TranslationElement -> [ProcessDef]
theoryProcessDefs t = [i | ProcessDefItem i <- translationElements t]

-- | All function typing information in a theory.
theoryFunctionTypingInfos :: Theory sig c r p TranslationElement -> [SapicFunSym]
theoryFunctionTypingInfos t = [i | FunctionTypingInfo i <- translationElements t]

-- | All process definitions of a theory.
theoryPredicates :: Theory sig c r p s -> [Predicate]
theoryPredicates = foldTheoryItem (const []) (const []) (const []) (const []) (const []) return (const []) (const []) <=< (.items)

-- | All export info definitions of a theory.
theoryExportInfos :: Theory sig c b p TranslationElement -> [ExportInfo]
theoryExportInfos t = [i | ExportInfoItem i <- translationElements t]

-- | All Builtins of a theory
theoryBuiltins :: Theory sig c r p TranslationElement -> [String]
theoryBuiltins t = [i | SignatureBuiltin i <- translationElements t]

-- | All Equivalence queries of a theory
theoryEquivLemmas :: Theory sig c r p TranslationElement -> [(PlainProcess, PlainProcess)]
theoryEquivLemmas t = [(p1, p2) | EquivLemma p1 p2 <- translationElements t]

-- | All Equivalence queries of a theory
theoryDiffEquivLemmas :: Theory sig c r p TranslationElement -> [PlainProcess]
theoryDiffEquivLemmas t = [p | DiffEquivLemma p <- translationElements t]

-- | All restrictions of a theory.
diffTheoryRestrictions :: DiffTheory sig c r r2 p p2 -> [(Side, Restriction)]
diffTheoryRestrictions =
  foldDiffTheoryItem (const []) (const []) (const []) (const []) return (const []) (const []) (const []) <=< (.items)

-- |  All macros of a diff theory.
diffTheoryMacros :: DiffTheory sig c r r2 p p2 -> [LNMacro]
diffTheoryMacros =
  foldDiffTheoryItem (const []) (const []) (const []) (const []) (const []) (\m -> m) (const []) (const []) <=< (.items)

-- |  All formal comments of a diff theory.
diffTheoryFormalComments :: DiffTheory sig c r r2 p p2 -> [FormalComment]
diffTheoryFormalComments =
  foldDiffTheoryItem (const []) (const []) (const []) (const []) (const []) (const []) return (const []) <=< (.items)

-- | All restrictions of one side of a theory.
diffTheorySideRestrictions :: Side -> DiffTheory sig c r r2 p p2 -> [Restriction]
diffTheorySideRestrictions s =
  foldDiffTheoryItem (const []) (const []) (const []) (const []) (\(x, y) -> if (x == s) then [y] else []) (const []) (const []) (const []) <=< (.items)

-- | All lemmas of a theory.
diffTheoryLemmas :: DiffTheory sig c r r2 p p2 -> [(Side, Lemma p2)]
diffTheoryLemmas =
  foldDiffTheoryItem (const []) (const []) (const []) return (const []) (const []) (const []) (const []) <=< (.items)

-- | All lemmas of a theory.
diffTheorySideLemmas :: Side -> DiffTheory sig c r r2 p p2 -> [Lemma p2]
diffTheorySideLemmas s =
  foldDiffTheoryItem (const []) (const []) (const []) (\(x, y) -> if (x == s) then [y] else []) (const []) (const []) (const []) (const []) <=< (.items)

-- | All lemmas of a theory.
diffTheoryDiffLemmas :: DiffTheory sig c r r2 p p2 -> [DiffLemma p]
diffTheoryDiffLemmas =
  foldDiffTheoryItem (const []) (const []) return (const []) (const []) (const []) (const []) (const []) <=< (.items)

-- | The configuration block of a theory.
theoryConfigBlock :: Theory sig c r p s -> ConfigBlock
theoryConfigBlock = foldTheoryItem (const []) (const []) (const []) (const []) id (const []) (const []) (const []) <=< (.items)

-- | The configuration block of a theory.
diffTheoryConfigBlock :: DiffTheory sig c r r2 p p2 -> ConfigBlock
diffTheoryConfigBlock = foldDiffTheoryItem (const []) (const []) (const []) (const []) (const []) (const []) (const []) id <=< (.items)

expandRestriction ::
  Theory sig c r p s ->
  ProtoRestriction SyntacticLNFormula ->
  Either FactTag (ProtoRestriction LNFormula)
expandRestriction thy (Restriction n f ofm) = do
  f' <- expandFormula (theoryPredicates thy) f
  ofm' <- mapM (expandFormula (theoryPredicates thy)) ofm
  return $ Restriction n f' ofm'

expandLemma ::
  Theory sig c r p1 s ->
  ProtoLemma SyntacticLNFormula p2 ->
  Either FactTag (ProtoLemma LNFormula p2)
expandLemma thy (Lemma n u m tq f ofm a p) = do
  f' <- expandFormula (theoryPredicates thy) f
  ofm' <- mapM (expandFormula (theoryPredicates thy)) ofm
  return $ Lemma n u m tq f' ofm' a p

-- | Add a new restriction. Fails, if restriction with the same name exists.
addRestriction :: Restriction -> Theory sig c r p s -> Maybe (Theory sig c r p s)
addRestriction l thy = do
  guard (isNothing $ lookupRestriction l.name thy)
  return $ over #items (++ [RestrictionItem l]) thy

addRestrictions :: [Restriction] -> Theory sig c r p s -> Theory sig c r p s
addRestrictions rts thy = fromMaybe thy $ foldl ( \fm rest -> addRestriction rest (fromJust fm)) (Just thy) rts

-- | Add a new lemma. Fails, if a lemma with the same name exists.
addLemma :: Lemma p -> Theory sig c r p s -> Maybe (Theory sig c r p s)
addLemma l thy = do
  guard (isNothing $ lookupLemma l.name thy)
  return $ over #items (++ [LemmaItem l]) thy

addLemmas :: Foldable t =>t (Lemma p) -> Theory sig c r p s -> Theory sig c r p s
addLemmas lemmas thy = fromMaybe thy $ foldl ( \fm lemma -> addLemma lemma (fromJust fm)) (Just thy) lemmas

addRules :: [r] -> Theory sig c r p s -> Theory sig c r p s
addRules rules = over #items (++ map RuleItem rules)
-- | Add a new lemma at a specific index. Fails, if a lemma with the same name exists.
addLemmaAtIndex :: Lemma p -> Int -> Theory sig c r p s -> Maybe (Theory sig c r p s)
addLemmaAtIndex l i thy = do
  guard (isNothing $ lookupLemma l.name thy)
  return $ over #items (\ls -> (take i ls) ++ [LemmaItem l] ++ (drop i ls)) thy

-- | apply function on lemmas, temporary test
modifyLemma :: (Lemma p -> Lemma p) -> Theory sig c r p s -> Maybe (Theory sig c r p s)
modifyLemma f thy = do
  return $ over #items (map mlemma) thy
  where
    mlemma (LemmaItem l) = (LemmaItem (f l))
    mlemma i = i

-- | Add a new process expression.  Since expression (and not definitions)
-- could appear several times, checking for doubled occurrence isn't necessary
addProcess :: PlainProcess -> Theory sig c r p TranslationElement -> Theory sig c r p TranslationElement
addProcess l = over #items (++ [TranslationItem (ProcessItem l)])

-- | Add function typing info to a theory
addFunctionTypingInfo :: SapicFunSym -> Theory sig c r p TranslationElement -> Theory sig c r p TranslationElement
addFunctionTypingInfo l = over #items (++ [TranslationItem $ FunctionTypingInfo l])

-- | Add new Macros.
addMacros :: [LNMacro] -> Theory sig c r p s -> Maybe (Theory sig c r p s)
addMacros m thy = return $ over #items (++ [MacroItem m]) thy

-- | Add new Macros.
addDiffMacros :: [LNMacro] -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
addDiffMacros m thy = return $ over #items (++ [DiffMacroItem m]) thy

-- | Remove all Function Typing information in Theory
clearFunctionTypingInfos :: Theory sig c r p TranslationElement -> Theory sig c r p TranslationElement
clearFunctionTypingInfos = over #items (filter f)
  where
    f (TranslationItem (FunctionTypingInfo _)) = False
    f _ = True

-- | Add a new case test. Fails if CaseTest with the same name already exists.
addCaseTest :: CaseTest -> Theory sig c r p TranslationElement -> Maybe (Theory sig c r p TranslationElement)
addCaseTest cTest thy = do
  guard (isNothing $ lookupCaseTest cTest.name thy)
  return $ over #items (++ [TranslationItem (CaseTestItem cTest)]) thy

-- | Add a new AccLemma  fails if AccLemma with the same name already exists
addAccLemma :: AccLemma -> Theory sig c r p TranslationElement -> Maybe (Theory sig c r p TranslationElement)
addAccLemma aLem thy = do
  guard (isNothing $ lookupAccLemma aLem.name thy)
  return $ over #items (++ [TranslationItem (AccLemmaItem aLem)]) thy

-- | Add a new process expression.
addExportInfo :: ExportInfo -> Theory sig c r p TranslationElement -> (Theory sig c r p TranslationElement)
addExportInfo eInfo thy = do
  over #items (++ [TranslationItem (ExportInfoItem eInfo)]) thy

-- search process
findProcess :: String -> Theory sig c r p TranslationElement -> Maybe (Theory sig c r p TranslationElement)
findProcess s thy = do
  guard (isJust $ lookupProcessDef s thy)
  return thy

-- | Add a new process definition. fails if process with the same name already exists
addProcessDef :: ProcessDef -> Theory sig c r p TranslationElement -> Maybe (Theory sig c r p TranslationElement)
addProcessDef pDef thy = do
  guard (isNothing $ lookupProcessDef pDef.name thy)
  return $ over #items (++ [TranslationItem (ProcessDefItem pDef)]) thy

-- | Add a new process definition. fails if process with the same name already exists
addPredicate :: Predicate -> Theory sig c r p TranslationElement -> Maybe (Theory sig c r p TranslationElement)
addPredicate pDef thy = do
  guard (isNothing $ lookupPredicate pDef.fact (theoryPredicates thy))
  return $ over #items (++ [PredicateItem pDef]) thy

-- | Add a new option. Overwrite previous settings
setOption ::
  Lens Option Option a Bool ->
  Theory sig c r p s ->
  Theory sig c r p s
setOption l = set (#options % l) True

setforcedInjectiveFacts ::
  S.Set FactTag ->
  Theory sig c r p s ->
  Theory sig c r p s
setforcedInjectiveFacts = set (#options % #forcedInjectiveFacts)

-- | Add a new restriction. Fails, if restriction with the same name exists.
addRestrictionDiff :: Side -> Restriction -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
addRestrictionDiff s l thy = do
  guard (isNothing $ lookupRestrictionDiff s l.name thy)
  return $ over #items (++ [EitherRestrictionItem (s, l)]) thy

filterLemma :: (ProtoLemma LNFormula p -> Bool) -> Theory sig c r p s -> Theory sig c r p s
filterLemma lemmaSelector = over #items (concatMap fItem)
  where
    fItem =
      foldTheoryItem
        (return . RuleItem)
        (return . RestrictionItem)
        check
        (return . TextItem)
        (return . ConfigBlockItem)
        (return . PredicateItem)
        (return . MacroItem)
        (return . TranslationItem)
    check l = do guard (lemmaSelector l); return (LemmaItem l)

-- | Add a new lemma. Fails, if a lemma with the same name exists.
addLemmaDiff :: Side -> Lemma p2 -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
addLemmaDiff s l thy = do
  guard (isNothing $ lookupLemmaDiff s l.name thy)
  return $ over #items (++ [EitherLemmaItem (s, l)]) thy

-- | Add a new lemma. Fails, if a lemma with the same name exists.
addDiffLemma :: DiffLemma p -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
addDiffLemma l thy = do
  guard (isNothing $ lookupDiffLemma l.name thy)
  return $ over #items (++ [DiffLemmaItem l]) thy

addDiffLemmas :: Foldable t =>t (Lemma p2)-> DiffTheory sig c r r2 p p2 -> DiffTheory sig c r r2 p p2
addDiffLemmas lemmas thy = fromMaybe thy $ foldl ( \fm lemma ->  addLemmaDiff LHS lemma (fromJust fm)) (Just thy) lemmas

-- | Add a new default heuristic. Fails if a heuristic is already defined.
addHeuristic :: [GoalRanking ProofContext] -> Theory sig c r p s -> Maybe (Theory sig c r p s)
addHeuristic h (Theory n f [] t sig c i o sapic) = Just (Theory n f h t sig c i o sapic)
addHeuristic _ _ = Nothing

addDiffHeuristic :: [GoalRanking ProofContext] -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
addDiffHeuristic h (DiffTheory n f [] t sig cl cr dcl dcr i opt sapic) = Just (DiffTheory n f h t sig cl cr dcl dcr i opt sapic)
addDiffHeuristic _ _ = Nothing

addTactic :: Tactic ProofContext -> Theory sig c r p s -> Maybe (Theory sig c r p s)
addTactic t (Theory n f h [] sig c i o sapic) = Just (Theory n f h [t] sig c i o sapic)
addTactic t (Theory n f h l sig c i o sapic) = Just (Theory n f h (l ++ [t]) sig c i o sapic)

-- addTactic _ _ = Nothing

addDiffTactic :: Tactic ProofContext -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
addDiffTactic t (DiffTheory n f h [] sig cl cr dcl dcr i o sapic) = Just (DiffTheory n f h [t] sig cl cr dcl dcr i o sapic)
addDiffTactic t (DiffTheory n f h l sig cl cr dcl dcr i o sapic) = Just (DiffTheory n f h (l ++ [t]) sig cl cr dcl dcr i o sapic)

-- | Remove a lemma by name. Fails, if the lemma does not exist.
removeLemma :: String -> Theory sig c r p s -> Maybe (Theory sig c r p s)
removeLemma lemmaName thy = do
  _ <- lookupLemma lemmaName thy
  return $ over #items (concatMap fItem) thy
  where
    fItem =
      foldTheoryItem
        (return . RuleItem)
        (return . RestrictionItem)
        check
        (return . TextItem)
        (return . ConfigBlockItem)
        (return . PredicateItem)
        (return . MacroItem)
        (return . TranslationItem)
    check l = do guard (l.name /= lemmaName); return (LemmaItem l)

-- | Remove a lemma by name. Fails, if the lemma does not exist.
removeLemmaDiff :: Side -> String -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
removeLemmaDiff s lemmaName thy = do
  _ <- lookupLemmaDiff s lemmaName thy
  return $ over #items (concatMap fItem) thy
  where
    fItem =
      foldDiffTheoryItem
        (return . DiffRuleItem)
        (return . EitherRuleItem)
        (return . DiffLemmaItem)
        check
        (return . EitherRestrictionItem)
        (return . DiffMacroItem)
        (return . DiffTextItem)
        (return . DiffConfigBlockItem)
    check (s', l) = do guard (l.name /= lemmaName || s' /= s); return (EitherLemmaItem (s, l))

-- | Remove a lemma by name. Fails, if the lemma does not exist.
removeDiffLemma :: String -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
removeDiffLemma lemmaName thy = do
  _ <- lookupDiffLemma lemmaName thy
  return $ over #items (concatMap fItem) thy
  where
    fItem =
      foldDiffTheoryItem
        (return . DiffRuleItem)
        (return . EitherRuleItem)
        check
        (return . EitherLemmaItem)
        (return . EitherRestrictionItem)
        (return . DiffMacroItem)
        (return . DiffTextItem)
        (return . DiffConfigBlockItem)
    check l = do guard (l.name /= lemmaName); return (DiffLemmaItem l)

-- | Find the restriction with the given name.
lookupRestriction :: String -> Theory sig c r p s -> Maybe Restriction
lookupRestriction name = find ((name ==) . (.name)) . theoryRestrictions

-- | Find the lemma with the given name.
lookupLemma :: String -> Theory sig c r p s -> Maybe (Lemma p)
lookupLemma name = find ((name ==) . (.name)) . theoryLemmas

lookupLemmaIndex :: String -> Theory sig c r p s -> Maybe Int
lookupLemmaIndex name ti = (+ 1) <$> findIndex (\i -> case i of (LemmaItem l) -> name == l.name; _ -> False) ti.items

getLemmaPreItems :: String -> Theory sig c r p s -> [TheoryItem r p s]
getLemmaPreItems name ti = fromMaybe [] $ (\li -> [i | (nr, i) <- zip [1 ..] ti.items, nr < li]) <$> lookupLemmaIndex name ti

-- | Find the case test with the given name.
lookupCaseTest :: CaseIdentifier -> Theory sig c r p TranslationElement -> Maybe CaseTest
lookupCaseTest name = find ((name ==) . (.name)) . theoryCaseTests

-- | Find the acc lemma with the given name.
lookupAccLemma :: String -> Theory sig c r p TranslationElement -> Maybe (AccLemma)
lookupAccLemma name = find ((name ==) . (.name)) . theoryAccLemmas

-- | Find the process with the given name.
lookupProcessDef :: String -> Theory sig c r p TranslationElement -> Maybe (ProcessDef)
lookupProcessDef name = find ((name ==) . (.name)) . theoryProcessDefs

-- | Find the function typing info for a given function symbol.
lookupFunctionTypingInfo :: UserDefinedSym -> Theory sig c r p TranslationElement -> Maybe SapicFunSym
lookupFunctionTypingInfo tag = find (\(fs,_,_) -> tag == fs) . theoryFunctionTypingInfos

-- | Find the export info for the given tag.
lookupExportInfo :: String -> Theory sig c r p TranslationElement -> [ExportInfo]
lookupExportInfo tag = filter ((tag ==) . (.tag)) . theoryExportInfos

-- | Find the restriction with the given name.
lookupRestrictionDiff :: Side -> String -> DiffTheory sig c r r2 p p2 -> Maybe Restriction
lookupRestrictionDiff s name = find ((name ==) . (.name)) . (diffTheorySideRestrictions s)

-- | Find the lemma with the given name.
lookupLemmaDiff :: Side -> String -> DiffTheory sig c r r2 p p2 -> Maybe (Lemma p2)
lookupLemmaDiff s name = find ((name ==) . (.name)) . (diffTheorySideLemmas s)

-- | Find the lemma with the given name.
lookupDiffLemma :: String -> DiffTheory sig c r r2 p p2 -> Maybe (DiffLemma p)
lookupDiffLemma name = find ((name ==) . (.name)) . diffTheoryDiffLemmas

-- | Add a comment to the theory.
addComment :: Doc -> Theory sig c r p s -> Theory sig c r p s
addComment c = over #items (++ [TextItem ("", render c)])

-- | Add a comment to the diff theory.
addDiffComment :: Doc -> DiffTheory sig c r r2 p p2 -> DiffTheory sig c r r2 p p2
addDiffComment c = over #items (++ [DiffTextItem ("", render c)])

-- | Add a comment represented as a string to the theory.
addStringComment :: String -> Theory sig c r p s -> Theory sig c r p s
addStringComment = addComment . vcat . map text . lines

addFormalComment :: FormalComment -> Theory sig c r p s -> Theory sig c r p s
addFormalComment c = over #items (++ [TextItem c])

addFormalCommentDiff :: FormalComment -> DiffTheory sig c r r2 p p2 -> DiffTheory sig c r r2 p p2
addFormalCommentDiff c = over #items (++ [DiffTextItem c])

isRuleItem :: TheoryItem r p s -> Bool
isRuleItem (RuleItem _) = True
isRuleItem _ = False

itemToRule :: TheoryItem r p s -> Maybe r
itemToRule (RuleItem r) = Just r
itemToRule _ = Nothing

------------------------------------------------------------------------------
-- Pretty Print
------------------------------------------------------------------------------

-- Pretty print a theory
prettyTheory ::
  (HighlightDocument d) =>
  (sig -> d) ->
  (c -> d) ->
  (r -> d) ->
  (p -> d) ->
  (s -> d) ->
  Theory sig c r p s ->
  d
prettyTheory ppSig ppCache ppRule ppPrf ppSap thy =
  vsep $
    [ kwTheoryName $ text thy.name]
    ++ parMap rdeepseq ppItem (filter isConfigBlock thy.items)
    ++ [kwTheoryBegin,
      lineComment_ "Function signature and definition of the equational theory E",
      ppSig thy.signature,
      if null thyT then emptyDoc else vcat $ map prettyTactic thyT,
      if null thyH then emptyDoc else text "heuristic: " <> text (prettyGoalRankings thyH),
      ppCache thy.cache
    ]
      ++ parMap rdeepseq ppItem (filter (not . isConfigBlock) thy.items)
      ++ [kwEnd]
  where
    isConfigBlock (ConfigBlockItem _) = True
    isConfigBlock _ = False
    ppItem =
      foldTheoryItem
        ppRule
        prettyRestriction
        (prettyLemma ppPrf)
        (uncurry prettyFormalComment)
        prettyConfigBlock
        prettyPredicate
        prettyMacros
        ppSap
    thyH = thy.heuristic
    thyT = thy.tactic

prettyTranslationElement :: (HighlightDocument d) => TranslationElement -> d
prettyTranslationElement (ProcessItem p) = text "process" <> colon $-$ (nest 2 $ prettyProcess p)
prettyTranslationElement (DiffEquivLemma p) = text "diffEquivLemma" <> colon $-$ (nest 2 $ prettyProcess p)
prettyTranslationElement (EquivLemma p1 p2) = text "equivLemma" <> colon $-$ (nest 2 $ prettyProcess p1) $$ (nest 2 $ prettyProcess p2)
prettyTranslationElement (AccLemmaItem a) = prettyAccLemma a
prettyTranslationElement (CaseTestItem c) = prettyCaseTest c
prettyTranslationElement (ProcessDefItem p) =
  (text "let ")
    <-> (text p.name)
    <-> ( case p.vars of
            Nothing -> emptyDoc
            Just l -> text ("(" ++ intercalate "," (map show l) ++ ")")
        )
    <-> (text "=")
    <-> nest 2 (prettyProcess p.body)
prettyTranslationElement (FunctionTypingInfo (ACfctUser (fsn,(priv,constr,ndc)), intypes, outtype)) =
  (text "function:")
    <-> text (unpack fsn)
    <-> parens (fsep $ punctuate comma $ map printType intypes)
    <-> text ":"
    <-> printType outtype
    <-> text " [AC]"
    <-> text (showPriv priv)
    <-> text (showConst constr)
    <-> text (showNDC ndc)
  where
    printType = maybe (text defaultSapicTypeS) text
    showPriv Private = " [private]"
    showPriv Public = ""
    showConst Constructor = ""
    showConst Destructor = " [destructor]"
    showNDC NotNDC = ""
    showNDC IsNDC = " [NDC]"
    showNDC IsNDCDiff = " [NDC-Diff]"
    showNDC IsNDCBoth = " [NDC,NDC-Diff]"
prettyTranslationElement (FunctionTypingInfo (NoEqUser (fsn, (_, priv, constr, ndc)), intypes, outtype)) =
  (text "function:")
    <-> text (unpack fsn)
    <-> parens (fsep $ punctuate comma $ map printType intypes)
    <-> text ":"
    <-> printType outtype
    <-> text (showPriv priv)
    <-> text (showConst constr)
    <-> text (showNDC ndc)
  where
    printType = maybe (text defaultSapicTypeS) text
    showPriv Private = " [private]"
    showPriv Public = ""
    showConst Constructor = ""
    showConst Destructor = " [destructor]"
    showNDC NotNDC = ""
    showNDC IsNDC = " [NDC]"
    showNDC IsNDCDiff = " [NDC-Diff]"
    showNDC IsNDCBoth = " [NDC,NDC-Diff]"
prettyTranslationElement (ExportInfoItem eInfo) =
  (text "export: ")
    <-> text eInfo.tag
    <-> nest 2 (doubleQuotes $ text eInfo.text)
prettyTranslationElement (SignatureBuiltin s) = (text "builtin ") <-> (text s)

prettyPredicate :: (HighlightDocument d) => Predicate -> d
prettyPredicate p = kwPredicate <> colon <-> text (factstr ++ "<=>" ++ formulastr)
  where
    factstr = render $ prettyFact prettyLVar p.fact
    formulastr = render $ prettyLNFormula p.formula

prettyProcess :: (HighlightDocument d) => PlainProcess -> d
prettyProcess = prettySapic

prettyProcessDef :: (HighlightDocument d) => ProcessDef -> d
prettyProcessDef pDef = text "let " <-> text pDef.name <-> text " = " <-> prettySapic pDef.body

-- | Pretty-print a comma, separated list of 'LVar's.
prettyVarList :: (Document d) => [LVar] -> d
prettyVarList = fsep . punctuate comma . map prettyLVar

-- |  Pretty print all macros
prettyMacros :: (HighlightDocument d) => [LNMacro] -> d
prettyMacros [] = emptyDoc
prettyMacros m = keyword_ "macros:" $$ nest 4
  (vcat [if i == length m - 1
          then prettyMacro macro
          else prettyMacro macro <> comma
        | (i, macro) <- zip [0..] m])

-- |  Pretty print a macro.
prettyMacro :: (HighlightDocument d) => LNMacro -> d
prettyMacro (op, args, out) =
  vcat
    [ ppNonEmptyList
        (\ds -> sep (map (nest 4) ds))
        text
        ([BC.unpack op ++ "("])
        <-> prettyVarList args
        <-> text (") = ")
        <-> prettyTerm (text . show) out
    ]
  where
    ppNonEmptyList _ _ [] = emptyDoc
    ppNonEmptyList hdr pp xs = hdr $ punctuate comma $ map pp xs

-- "\t" ++ BC.unpack op ++ "(" ++ show (args) ++ ") = " ++ show(out) ++ "\n"

-- | Pretty print a restriction.
prettyRestriction :: (HighlightDocument d) => Restriction -> d
prettyRestriction rstr =
  kwRestriction <-> text rstr.name
    <> colon
      $-$ (nest 2 $ doubleQuotes $ prettyLNFormula (fromMaybe expandedFormula ogFormula))
      $-$ (nest 2 $ if safety then lineComment_ "safety formula" else emptyDoc)
      $--$ (case ogFormula of
            Just _ -> nest 2 $ multiComment $ text "expanded formula:" $-$ 
                             doubleQuotes (prettyLNFormula expandedFormula)
            _ -> emptyDoc)
  where
    expandedFormula = rstr.formula
    ogFormula = rstr.originalFormula
    safety = isSafetyFormula $ formulaToGuarded_ expandedFormula

-- | Pretty print an either restriction.
prettyEitherRestriction :: (HighlightDocument d) => (Side, Restriction) -> d
prettyEitherRestriction (s, rstr) =
  kwRestriction <-> text rstr.name <-> prettySide s
    <> colon
      $-$ (nest 2 $ doubleQuotes $ prettyLNFormula (fromMaybe expandedFormula ogFormula))
      $-$ (nest 2 $ if safety then lineComment_ "safety formula" else emptyDoc)
      $--$ case ogFormula of
            Just _ -> nest 2 $ multiComment $ text "expanded formula:" $-$ 
                             doubleQuotes (prettyLNFormula expandedFormula)
            _ -> emptyDoc
  where
    expandedFormula = rstr.formula
    ogFormula = rstr.originalFormula
    safety = isSafetyFormula $ formulaToGuarded_ expandedFormula

-- | Pretty print a configuration block.
prettyConfigBlock :: (HighlightDocument d) => ConfigBlock -> d
prettyConfigBlock cb = text "configuration: " <> doubleQuotes (text cb)

prettyTactic :: (HighlightDocument d) => Tactic ProofContext -> d
prettyTactic tactic =
  kwTactic
    <> colon
    <> space
    <> (text tactic.name)
      $-$ kwPresort
    <> colon
    <> space
    <> (char $ goalRankingToChar tactic.presort)
      $-$ sep
        [ ppTabTab "prio" (map (.stringRankingPrio) tactic.prios) (map (.stringsPrio) tactic.prios),
          ppTabTab "deprio" (map (.stringRankingDeprio) tactic.deprios) (map (.stringsDeprio) tactic.deprios)
        ]
  where
    -- pretty print for a prio block
    ppTab "prio" (rankingName, xs) = kwPrio <> colon <> space <> braces (text rankingName) $-$ (nest 2 $ vcat $ map prettify (map words xs))
    ppTab "deprio" (rankingName, xs) = kwDeprio <> colon <> space <> braces (text rankingName) $-$ (nest 2 $ vcat $ map prettify (map words xs))
    ppTab _ _ = emptyDoc

    ppTabTab _ _ [] = emptyDoc
    ppTabTab param rankingName listFunctions = vcat (map (ppTab param) (zip rankingName listFunctions))

    prettify :: (HighlightDocument d) => [String] -> d
    prettify [] = emptyDoc
    prettify ("|" : t) = (operator_ " | ") <> prettify t -- if (s == "|") || (s == "&") || (s == "not") then (operator_ s) <> prettify t else text s <> prettify t
    prettify ("&" : t) = (operator_ " & ") <> prettify t
    prettify ("not" : t) = (operator_ "not ") <> prettify t
    prettify (s : t) = text s <> prettify t
