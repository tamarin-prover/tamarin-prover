{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TemplateHaskell #-}

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
    thyName,
    thyInFile,
    thySignature,
    thyCache,
    thyItems,
    thyOptions,
    thyIsSapic,
    diffThyName,
    diffThyInFile,
    diffThyItems,
    diffThySignature,
    diffThyCacheLeft,
    diffThyCacheRight,
    diffThyDiffCacheLeft,
    diffThyDiffCacheRight,
    diffThyOptions,
    diffThyIsSapic,
    thyHeuristic,
    diffThyHeuristic,
    thyTactic,
    diffThyTactic,
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
    addLemma,
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
import Control.Category
import Control.Parallel.Strategies
import Data.Binary
import Data.ByteString.Char8 (unpack)
import Data.ByteString.Char8 qualified as BC
import Data.Label as L
import Data.Label.Poly qualified
import Data.Label.Total qualified as Data.Label.Point
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
import Prelude hiding (id, (.))

-- | A theory contains a single set of rewriting rules modeling a protocol
-- and the lemmas that
data Theory sig c r p s = Theory
  { _thyName :: String,
    _thyInFile :: String,
    _thyHeuristic :: [GoalRanking ProofContext],
    _thyTactic :: [Tactic ProofContext],
    _thySignature :: sig,
    _thyCache :: c,
    _thyItems :: [TheoryItem r p s],
    _thyOptions :: Option,
    _thyIsSapic :: Bool
  }
  deriving (Eq, Ord, Show, Generic, NFData, Binary)

$(mkLabels [''Theory])

-- | A diff theory contains a set of rewriting rules with diff modeling two instances
data DiffTheory sig c r r2 p p2 = DiffTheory
  { _diffThyName :: String,
    _diffThyInFile :: String,
    _diffThyHeuristic :: [GoalRanking ProofContext],
    _diffThyTactic :: [Tactic ProofContext],
    _diffThySignature :: sig,
    _diffThyCacheLeft :: c,
    _diffThyCacheRight :: c,
    _diffThyDiffCacheLeft :: c,
    _diffThyDiffCacheRight :: c,
    _diffThyItems :: [DiffTheoryItem r r2 p p2],
    _diffThyOptions :: Option,
    _diffThyIsSapic :: Bool
  }
  deriving (Eq, Ord, Show, Generic, NFData, Binary)

$(mkLabels [''DiffTheory])

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
  ([Macro] -> a) ->
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
  ([Macro] -> a) ->
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
  return $ L.set thyItems itms' thy
  where
    itms = L.get thyItems thy
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
  return $ L.set thyItems itms' thy
  where
    itms = L.get thyItems thy
    f' (TranslationItem (ProcessDefItem p)) = TranslationItem . ProcessDefItem <$> f p
    f' other = return other

-- | All rules of a theory.
theoryRules :: Theory sig c r p s -> [r]
theoryRules =
  foldTheoryItem return (const []) (const []) (const []) (const []) (const []) (const []) (const []) <=< L.get thyItems

-- | All diff rules of a theory.
diffTheoryDiffRules :: DiffTheory sig c r r2 p p2 -> [r]
diffTheoryDiffRules =
  foldDiffTheoryItem return (const []) (const []) (const []) (const []) (const []) (const []) (const []) <=< L.get diffThyItems

-- | All rules of a theory.
diffTheorySideRules :: Side -> DiffTheory sig c r r2 p p2 -> [r2]
diffTheorySideRules s =
  foldDiffTheoryItem (const []) (\(x, y) -> if (x == s) then [y] else []) (const []) (const []) (const []) (const []) (const []) (const []) <=< L.get diffThyItems

-- | All left rules of a theory.
leftTheoryRules :: DiffTheory sig c r r2 p p2 -> [r2]
leftTheoryRules =
  foldDiffTheoryItem (const []) (\(x, y) -> if (x == LHS) then [y] else []) (const []) (const []) (const []) (const []) (const []) (const []) <=< L.get diffThyItems

-- | All right rules of a theory.
rightTheoryRules :: DiffTheory sig c r r2 p p2 -> [r2]
rightTheoryRules =
  foldDiffTheoryItem (const []) (\(x, y) -> if (x == RHS) then [y] else []) (const []) (const []) (const []) (const []) (const []) (const []) <=< L.get diffThyItems

-- |  All macros of a theory.
theoryMacros :: Theory sig c r p s -> [Macro]
theoryMacros =
  foldTheoryItem (const []) (const []) (const []) (const []) (const []) (const []) (\m -> m) (const []) <=< L.get thyItems

-- |  All formal comments of a theory.
theoryFormalComments :: Theory sig c r p s -> [FormalComment]
theoryFormalComments =
  foldTheoryItem (const []) (const []) (const []) return (const []) (const []) (const []) (const []) <=< L.get thyItems

-- | All restrictions of a theory.
theoryRestrictions :: Theory sig c r p s -> [Restriction]
theoryRestrictions =
  foldTheoryItem (const []) return (const []) (const []) (const []) (const []) (const []) (const []) <=< L.get thyItems

-- | All lemmas of a theory.
theoryLemmas :: Theory sig c r p s -> [Lemma p]
theoryLemmas =
  foldTheoryItem (const []) (const []) return (const []) (const []) (const []) (const []) (const []) <=< L.get thyItems

translationElements :: Theory sig c1 b p c2 -> [c2]
translationElements = foldTheoryItem (const []) (const []) (const []) (const []) (const []) (const []) (const []) return <=< L.get thyItems

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
theoryPredicates = foldTheoryItem (const []) (const []) (const []) (const []) (const []) return (const []) (const []) <=< L.get thyItems

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
  foldDiffTheoryItem (const []) (const []) (const []) (const []) return (const []) (const []) (const []) <=< L.get diffThyItems

-- |  All macros of a diff theory.
diffTheoryMacros :: DiffTheory sig c r r2 p p2 -> [Macro]
diffTheoryMacros =
  foldDiffTheoryItem (const []) (const []) (const []) (const []) (const []) (\m -> m) (const []) (const []) <=< L.get diffThyItems

-- |  All formal comments of a diff theory.
diffTheoryFormalComments :: DiffTheory sig c r r2 p p2 -> [FormalComment]
diffTheoryFormalComments =
  foldDiffTheoryItem (const []) (const []) (const []) (const []) (const []) (const []) return (const []) <=< L.get diffThyItems

-- | All restrictions of one side of a theory.
diffTheorySideRestrictions :: Side -> DiffTheory sig c r r2 p p2 -> [Restriction]
diffTheorySideRestrictions s =
  foldDiffTheoryItem (const []) (const []) (const []) (const []) (\(x, y) -> if (x == s) then [y] else []) (const []) (const []) (const []) <=< L.get diffThyItems

-- | All lemmas of a theory.
diffTheoryLemmas :: DiffTheory sig c r r2 p p2 -> [(Side, Lemma p2)]
diffTheoryLemmas =
  foldDiffTheoryItem (const []) (const []) (const []) return (const []) (const []) (const []) (const []) <=< L.get diffThyItems

-- | All lemmas of a theory.
diffTheorySideLemmas :: Side -> DiffTheory sig c r r2 p p2 -> [Lemma p2]
diffTheorySideLemmas s =
  foldDiffTheoryItem (const []) (const []) (const []) (\(x, y) -> if (x == s) then [y] else []) (const []) (const []) (const []) (const []) <=< L.get diffThyItems

-- | All lemmas of a theory.
diffTheoryDiffLemmas :: DiffTheory sig c r r2 p p2 -> [DiffLemma p]
diffTheoryDiffLemmas =
  foldDiffTheoryItem (const []) (const []) return (const []) (const []) (const []) (const []) (const []) <=< L.get diffThyItems

-- | The configuration block of a theory.
theoryConfigBlock :: Theory sig c r p s -> ConfigBlock
theoryConfigBlock = foldTheoryItem (const []) (const []) (const []) (const []) id (const []) (const []) (const []) <=< L.get thyItems

-- | The configuration block of a theory.
diffTheoryConfigBlock :: DiffTheory sig c r r2 p p2 -> ConfigBlock
diffTheoryConfigBlock = foldDiffTheoryItem (const []) (const []) (const []) (const []) (const []) (const []) (const []) id <=< L.get diffThyItems

expandRestriction ::
  Theory sig c r p s ->
  ProtoRestriction SyntacticLNFormula ->
  Either FactTag (ProtoRestriction LNFormula)
expandRestriction thy (Restriction n f) = Restriction n <$> expandFormula (theoryPredicates thy) f

expandLemma ::
  Theory sig c r p1 s ->
  ProtoLemma SyntacticLNFormula p2 ->
  Either FactTag (ProtoLemma LNFormula p2)
expandLemma thy (Lemma n u m tq f a p) = (\f' -> Lemma n u m tq f' a p) <$> expandFormula (theoryPredicates thy) f

-- | Add a new restriction. Fails, if restriction with the same name exists.
addRestriction :: Restriction -> Theory sig c r p s -> Maybe (Theory sig c r p s)
addRestriction l thy = do
  guard (isNothing $ lookupRestriction (L.get rstrName l) thy)
  return $ modify thyItems (++ [RestrictionItem l]) thy

-- | Add a new lemma. Fails, if a lemma with the same name exists.
addLemma :: Lemma p -> Theory sig c r p s -> Maybe (Theory sig c r p s)
addLemma l thy = do
  guard (isNothing $ lookupLemma (L.get lName l) thy)
  return $ modify thyItems (++ [LemmaItem l]) thy

-- | Add a new lemma at a specific index. Fails, if a lemma with the same name exists.
addLemmaAtIndex :: Lemma p -> Int -> Theory sig c r p s -> Maybe (Theory sig c r p s)
addLemmaAtIndex l i thy = do
  guard (isNothing $ lookupLemma (L.get lName l) thy)
  return $ modify thyItems (\ls -> (take i ls) ++ [LemmaItem l] ++ (drop i ls)) thy

-- | apply function on lemmas, temporary test
modifyLemma :: (Lemma p -> Lemma p) -> Theory sig c r p s -> Maybe (Theory sig c r p s)
modifyLemma f thy = do
  return $ modify thyItems (map mlemma) thy
  where
    mlemma (LemmaItem l) = (LemmaItem (f l))
    mlemma i = i

-- | Add a new process expression.  Since expression (and not definitions)
-- could appear several times, checking for doubled occurrence isn't necessary
addProcess :: PlainProcess -> Theory sig c r p TranslationElement -> Theory sig c r p TranslationElement
addProcess l = modify thyItems (++ [TranslationItem (ProcessItem l)])

-- | Add function typing info to a theory
addFunctionTypingInfo :: SapicFunSym -> Theory sig c r p TranslationElement -> Theory sig c r p TranslationElement
addFunctionTypingInfo l = modify thyItems (++ [TranslationItem $ FunctionTypingInfo l])

-- | Add new Macros.
addMacros :: [Macro] -> Theory sig c r p s -> Maybe (Theory sig c r p s)
addMacros m thy = return $ modify thyItems (++ [MacroItem m]) thy

-- | Add new Macros.
addDiffMacros :: [Macro] -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
addDiffMacros m thy = return $ modify diffThyItems (++ [DiffMacroItem m]) thy

-- | Remove all Function Typing information in Theory
clearFunctionTypingInfos :: Theory sig c r p TranslationElement -> Theory sig c r p TranslationElement
clearFunctionTypingInfos = modify thyItems (filter f)
  where
    f (TranslationItem (FunctionTypingInfo _)) = False
    f _ = True

-- | Add a new case test. Fails if CaseTest with the same name already exists.
addCaseTest :: CaseTest -> Theory sig c r p TranslationElement -> Maybe (Theory sig c r p TranslationElement)
addCaseTest cTest thy = do
  guard (isNothing $ lookupCaseTest (L.get cName cTest) thy)
  return $ modify thyItems (++ [TranslationItem (CaseTestItem cTest)]) thy

-- | Add a new AccLemma  fails if AccLemma with the same name already exists
addAccLemma :: AccLemma -> Theory sig c r p TranslationElement -> Maybe (Theory sig c r p TranslationElement)
addAccLemma aLem thy = do
  guard (isNothing $ lookupAccLemma (L.get aName aLem) thy)
  return $ modify thyItems (++ [TranslationItem (AccLemmaItem aLem)]) thy

-- | Add a new process expression.
addExportInfo :: ExportInfo -> Theory sig c r p TranslationElement -> (Theory sig c r p TranslationElement)
addExportInfo eInfo thy = do
  modify thyItems (++ [TranslationItem (ExportInfoItem eInfo)]) thy

-- search process
findProcess :: String -> Theory sig c r p TranslationElement -> Maybe (Theory sig c r p TranslationElement)
findProcess s thy = do
  guard (isJust $ lookupProcessDef s thy)
  return thy

-- | Add a new process definition. fails if process with the same name already exists
addProcessDef :: ProcessDef -> Theory sig c r p TranslationElement -> Maybe (Theory sig c r p TranslationElement)
addProcessDef pDef thy = do
  guard (isNothing $ lookupProcessDef (L.get pName pDef) thy)
  return $ modify thyItems (++ [TranslationItem (ProcessDefItem pDef)]) thy

-- | Add a new process definition. fails if process with the same name already exists
addPredicate :: Predicate -> Theory sig c r p TranslationElement -> Maybe (Theory sig c r p TranslationElement)
addPredicate pDef thy = do
  guard (isNothing $ lookupPredicate (L.get pFact pDef) (theoryPredicates thy))
  return $ modify thyItems (++ [PredicateItem pDef]) thy

-- | Add a new option. Overwrite previous settings
setOption ::
  Data.Label.Poly.Lens
    Data.Label.Point.Total
    (Option -> Option)
    (Bool -> Bool) ->
  Theory sig c r p s ->
  Theory sig c r p s
setOption l = L.set (l . thyOptions) True

setforcedInjectiveFacts ::
  S.Set FactTag ->
  Theory sig c r p s ->
  Theory sig c r p s
setforcedInjectiveFacts = L.set (forcedInjectiveFacts . thyOptions)

-- | Add a new restriction. Fails, if restriction with the same name exists.
addRestrictionDiff :: Side -> Restriction -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
addRestrictionDiff s l thy = do
  guard (isNothing $ lookupRestrictionDiff s (L.get rstrName l) thy)
  return $ modify diffThyItems (++ [EitherRestrictionItem (s, l)]) thy

filterLemma :: (ProtoLemma LNFormula p -> Bool) -> Theory sig c r p s -> Theory sig c r p s
filterLemma lemmaSelector = modify thyItems (concatMap fItem)
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
  guard (isNothing $ lookupLemmaDiff s (L.get lName l) thy)
  return $ modify diffThyItems (++ [EitherLemmaItem (s, l)]) thy

-- | Add a new lemma. Fails, if a lemma with the same name exists.
addDiffLemma :: DiffLemma p -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
addDiffLemma l thy = do
  guard (isNothing $ lookupDiffLemma (L.get lDiffName l) thy)
  return $ modify diffThyItems (++ [DiffLemmaItem l]) thy

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
  return $ modify thyItems (concatMap fItem) thy
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
    check l = do guard (L.get lName l /= lemmaName); return (LemmaItem l)

-- | Remove a lemma by name. Fails, if the lemma does not exist.
removeLemmaDiff :: Side -> String -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
removeLemmaDiff s lemmaName thy = do
  _ <- lookupLemmaDiff s lemmaName thy
  return $ modify diffThyItems (concatMap fItem) thy
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
    check (s', l) = do guard (L.get lName l /= lemmaName || s' /= s); return (EitherLemmaItem (s, l))

-- | Remove a lemma by name. Fails, if the lemma does not exist.
removeDiffLemma :: String -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
removeDiffLemma lemmaName thy = do
  _ <- lookupDiffLemma lemmaName thy
  return $ modify diffThyItems (concatMap fItem) thy
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
    check l = do guard (L.get lDiffName l /= lemmaName); return (DiffLemmaItem l)

-- | Find the restriction with the given name.
lookupRestriction :: String -> Theory sig c r p s -> Maybe Restriction
lookupRestriction name = find ((name ==) . L.get rstrName) . theoryRestrictions

-- | Find the lemma with the given name.
lookupLemma :: String -> Theory sig c r p s -> Maybe (Lemma p)
lookupLemma name = find ((name ==) . L.get lName) . theoryLemmas

lookupLemmaIndex :: String -> Theory sig c r p s -> Maybe Int
lookupLemmaIndex name ti = (+ 1) <$> findIndex (\i -> case i of (LemmaItem l) -> name == L.get lName l; _ -> False) (L.get thyItems ti)

getLemmaPreItems :: String -> Theory sig c r p s -> [TheoryItem r p s]
getLemmaPreItems name ti = fromMaybe [] $ (\li -> [i | (nr, i) <- zip [1 ..] (L.get thyItems ti), nr < li]) <$> lookupLemmaIndex name ti

-- | Find the case test with the given name.
lookupCaseTest :: CaseIdentifier -> Theory sig c r p TranslationElement -> Maybe CaseTest
lookupCaseTest name = find ((name ==) . L.get cName) . theoryCaseTests

-- | Find the acc lemma with the given name.
lookupAccLemma :: String -> Theory sig c r p TranslationElement -> Maybe (AccLemma)
lookupAccLemma name = find ((name ==) . L.get aName) . theoryAccLemmas

-- | Find the process with the given name.
lookupProcessDef :: String -> Theory sig c r p TranslationElement -> Maybe (ProcessDef)
lookupProcessDef name = find ((name ==) . L.get pName) . theoryProcessDefs

-- | Find the function typing info for a given function symbol.
lookupFunctionTypingInfo :: NoEqSym -> Theory sig c r p TranslationElement -> Maybe SapicFunSym
lookupFunctionTypingInfo tag = find (\(fs, _, _) -> tag == fs) . theoryFunctionTypingInfos

-- | Find the export info for the given tag.
lookupExportInfo :: String -> Theory sig c r p TranslationElement -> [ExportInfo]
lookupExportInfo tag = filter ((tag ==) . L.get eTag) . theoryExportInfos

-- | Find the restriction with the given name.
lookupRestrictionDiff :: Side -> String -> DiffTheory sig c r r2 p p2 -> Maybe Restriction
lookupRestrictionDiff s name = find ((name ==) . L.get rstrName) . (diffTheorySideRestrictions s)

-- | Find the lemma with the given name.
lookupLemmaDiff :: Side -> String -> DiffTheory sig c r r2 p p2 -> Maybe (Lemma p2)
lookupLemmaDiff s name = find ((name ==) . L.get lName) . (diffTheorySideLemmas s)

-- | Find the lemma with the given name.
lookupDiffLemma :: String -> DiffTheory sig c r r2 p p2 -> Maybe (DiffLemma p)
lookupDiffLemma name = find ((name ==) . L.get lDiffName) . diffTheoryDiffLemmas

-- | Add a comment to the theory.
addComment :: Doc -> Theory sig c r p s -> Theory sig c r p s
addComment c = modify thyItems (++ [TextItem ("", render c)])

-- | Add a comment to the diff theory.
addDiffComment :: Doc -> DiffTheory sig c r r2 p p2 -> DiffTheory sig c r r2 p p2
addDiffComment c = modify diffThyItems (++ [DiffTextItem ("", render c)])

-- | Add a comment represented as a string to the theory.
addStringComment :: String -> Theory sig c r p s -> Theory sig c r p s
addStringComment = addComment . vcat . map text . lines

addFormalComment :: FormalComment -> Theory sig c r p s -> Theory sig c r p s
addFormalComment c = modify thyItems (++ [TextItem c])

addFormalCommentDiff :: FormalComment -> DiffTheory sig c r r2 p p2 -> DiffTheory sig c r r2 p p2
addFormalCommentDiff c = modify diffThyItems (++ [DiffTextItem c])

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
    [ kwTheoryHeader $ text $ L.get thyName thy,
      lineComment_ "Function signature and definition of the equational theory E",
      ppSig $ L.get thySignature thy,
      if thyT == [] then text "" else vcat $ map prettyTactic thyT,
      if null thyH then text "" else text "heuristic: " <> text (prettyGoalRankings thyH),
      ppCache $ L.get thyCache thy
    ]
      ++ parMap rdeepseq ppItem (L.get thyItems thy)
      ++ [kwEnd]
  where
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
    thyH = L.get thyHeuristic thy
    thyT = L.get thyTactic thy

prettyTranslationElement :: (HighlightDocument d) => TranslationElement -> d
prettyTranslationElement (ProcessItem p) = text "process" <> colon $-$ (nest 2 $ prettyProcess p)
prettyTranslationElement (DiffEquivLemma p) = text "diffEquivLemma" <> colon $-$ (nest 2 $ prettyProcess p)
prettyTranslationElement (EquivLemma p1 p2) = text "equivLemma" <> colon $-$ (nest 2 $ prettyProcess p1) $$ (nest 2 $ prettyProcess p2)
prettyTranslationElement (AccLemmaItem a) = prettyAccLemma a
prettyTranslationElement (CaseTestItem c) = prettyCaseTest c
prettyTranslationElement (ProcessDefItem p) =
  (text "let ")
    <-> (text (L.get pName p))
    <-> ( case L.get pVars p of
            Nothing -> emptyDoc
            Just l -> text ("(" ++ intercalate "," (map show l) ++ ")")
        )
    <-> (text "=")
    <-> nest 2 (prettyProcess $ L.get pBody p)
prettyTranslationElement (FunctionTypingInfo ((fsn, (_, priv, _)), intypes, outtype)) =
  (text "function:")
    <-> text (unpack fsn)
    <-> parens (fsep $ punctuate comma $ map printType intypes)
    <-> text ":"
    <-> printType outtype
    <-> text (showPriv priv)
  where
    printType = maybe (text defaultSapicTypeS) text
    showPriv Private = " [private]"
    showPriv Public = ""
prettyTranslationElement (ExportInfoItem eInfo) =
  (text "export: ")
    <-> text (L.get eTag eInfo)
    <-> nest 2 (doubleQuotes $ text $ L.get eText eInfo)
prettyTranslationElement (SignatureBuiltin s) = (text "builtin ") <-> (text s)

prettyPredicate :: (HighlightDocument d) => Predicate -> d
prettyPredicate p = kwPredicate <> colon <-> text (factstr ++ "<=>" ++ formulastr)
  where
    factstr = render $ prettyFact prettyLVar $ L.get pFact p
    formulastr = render $ prettyLNFormula $ L.get pFormula p

prettyProcess :: (HighlightDocument d) => PlainProcess -> d
prettyProcess = prettySapic

prettyProcessDef :: (HighlightDocument d) => ProcessDef -> d
prettyProcessDef pDef = text "let " <-> text (L.get pName pDef) <-> text " = " <-> prettySapic (L.get pBody pDef)

-- | Pretty-print a comma, separated list of 'LVar's.
prettyVarList :: (Document d) => [LVar] -> d
prettyVarList = fsep . punctuate comma . map prettyLVar

-- |  Pretty print all macros
prettyMacros :: (HighlightDocument d) => [Macro] -> d
prettyMacros m = if m == [] then text empty else vcat (keyword_ "macros:" : map prettyMacro m)

-- |  Pretty print a macro.
prettyMacro :: (HighlightDocument d) => Macro -> d
prettyMacro (op, args, out) =
  vcat
    [ ppNonEmptyList
        (\ds -> sep (map (nest 4) ds))
        text
        ([BC.unpack op ++ "("])
        <-> prettyVarList args
        <-> text (") = " ++ show (out))
    ]
  where
    ppNonEmptyList _ _ [] = emptyDoc
    ppNonEmptyList hdr pp xs = hdr $ punctuate comma $ map pp xs

-- "\t" ++ BC.unpack op ++ "(" ++ show (args) ++ ") = " ++ show(out) ++ "\n"

-- | Pretty print a restriction.
prettyRestriction :: (HighlightDocument d) => Restriction -> d
prettyRestriction rstr =
  kwRestriction <-> text (L.get rstrName rstr)
    <> colon
      $-$ (nest 2 $ doubleQuotes $ prettyLNFormula $ L.get rstrFormula rstr)
      $-$ (nest 2 $ if safety then lineComment_ "safety formula" else emptyDoc)
  where
    safety = isSafetyFormula $ formulaToGuarded_ $ L.get rstrFormula rstr

-- | Pretty print an either restriction.
prettyEitherRestriction :: (HighlightDocument d) => (Side, Restriction) -> d
prettyEitherRestriction (s, rstr) =
  kwRestriction <-> text (L.get rstrName rstr) <-> prettySide s
    <> colon
      $-$ (nest 2 $ doubleQuotes $ prettyLNFormula $ L.get rstrFormula rstr)
      $-$ (nest 2 $ if safety then lineComment_ "safety formula" else emptyDoc)
  where
    safety = isSafetyFormula $ formulaToGuarded_ $ L.get rstrFormula rstr

-- | Pretty print a configuration block.
prettyConfigBlock :: (HighlightDocument d) => ConfigBlock -> d
prettyConfigBlock cb = text "configuration: " <> doubleQuotes (text cb)

prettyTactic :: (HighlightDocument d) => Tactic ProofContext -> d
prettyTactic tactic =
  kwTactic
    <> colon
    <> space
    <> (text $ _name tactic)
      $-$ kwPresort
    <> colon
    <> space
    <> (char $ goalRankingToChar $ _presort tactic)
      $-$ sep
        [ ppTabTab "prio" (map stringRankingPrio $ _prios tactic) (map stringsPrio $ _prios tactic),
          ppTabTab "deprio" (map stringRankingDeprio $ _deprios tactic) (map stringsDeprio $ _deprios tactic),
          char '\n'
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
