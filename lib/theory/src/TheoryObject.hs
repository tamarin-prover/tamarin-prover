{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module TheoryObject (
   module Lemma
  , module Items.OptionItem
  , module Items.ProcessItem
  , module Items.TheoryItem
  , module Items.CaseTestItem
  , module Items.AccLemmaItem
  , LemmaAttribute(..)
  , TraceQuantifier(..)
  , ProtoLemma(..)
  , Theory(..)
  , DiffTheory(..)
  , TheoryItem(..)
  , DiffTheoryItem(..)
  , thyName
  , thySignature
  , thyCache
  , thyItems
  , thyOptions
  , diffThyName
  , diffThyItems
  , diffThySignature
  , diffThyCacheLeft
  , diffThyCacheRight
  , diffThyDiffCacheLeft
  , diffThyDiffCacheRight
  , thyHeuristic
  , diffThyHeuristic
  , DiffLemma(..)
  , ProcessDef(..)
  , Predicate(..)
  , Option(..)
  , TranslationElement (..)
  , TranslationElement (..)
  , foldDiffTheoryItem
  , mapTheoryItem
  , mapDiffTheoryItem
  , theoryRules
  , diffTheoryDiffRules
  , diffTheorySideRules
  , leftTheoryRules
  , rightTheoryRules
  , theoryRestrictions
  , theoryLemmas
  , theoryProcesses
  , theoryProcessDefs
  , theoryPredicates
  , diffTheoryRestrictions
  , diffTheorySideRestrictions
  , diffTheoryLemmas
  , diffTheorySideLemmas
  , diffTheoryDiffLemmas
  , expandFormula
  , expandRestriction
  , expandLemma
  , addRestriction
  , addLemma
  , addProcess
  , findProcess
  , addProcessDef
  , addPredicate
  , setOption
  , addRestrictionDiff
  , addLemmaDiff
  , addDiffLemma
  , addHeuristic
  , addDiffHeuristic
  , removeLemma
  , removeLemmaDiff
  , removeDiffLemma
  , addComment
  , addDiffComment
  , addStringComment
  , addFormalComment
  , addFormalCommentDiff
  , isRuleItem
  , itemToRule
  , foldTheoryItem
  , lookupDiffLemma
  , lookupLemmaDiff
  , lookupLemma
  , lookupProcessDef
  , filterSide
  , mapMProcesses
  , mapMProcessesDef
  , theoryFunctionTypingInfos
  , theoryBuiltins
  , theoryExportInfos
  , theoryEquivLemmas
  , theoryDiffEquivLemmas
  , addFunctionTypingInfo
  , clearFunctionTypingInfos
  , addExportInfo
  , setforcedInjectiveFacts
  , filterLemma
  , lookupFunctionTypingInfo
  , prettyTheory
  , prettyTranslationElement
  , prettyProcessDef
  , prettyEitherRestriction
  , lookupExportInfo
  , prettyRestriction
  , prettyProcess
  , theoryCaseTests
  , theoryAccLemmas
  , addAccLemma
  , addCaseTest
  , lookupAccLemma
  , lookupCaseTest
  ) where

import Theory.Constraint.Solver.Heuristics
import Data.Label as L
import Theory.Model.Restriction
import Theory.Model.Fact
import Term.LTerm
import Theory.Constraint.Solver

import Items.OptionItem
import Items.ProcessItem
import Items.TheoryItem
import Items.CaseTestItem
import Items.AccLemmaItem
import Lemma
import qualified Data.Label.Poly
import qualified Data.Label.Total as Data.Label.Point



import           Prelude                             hiding (id, (.))

import           Data.List
import           Data.Maybe

import           Control.Basics
import           Control.Category

import           Theory.Model

import           Theory.Text.Pretty

import           Prelude                             hiding (id, (.))

import Pretty
import Theory.Sapic.Print
import Control.Parallel.Strategies
import GHC.Generics
import Data.Binary
import Theory.Sapic
import Items.ExportInfo
import qualified Data.Set as S
import Theory.Syntactic.Predicate
import Data.ByteString.Char8 (unpack)
import Items.AccLemmaItem (prettyAccLemma)
import Items.CaseTestItem (prettyCaseTest)


-- | A theory contains a single set of rewriting rules modeling a protocol
-- and the lemmas that
data Theory sig c r p s = Theory {
         _thyName      :: String
       , _thyHeuristic :: [GoalRanking]
       , _thySignature :: sig
       , _thyCache     :: c
       , _thyItems     :: [TheoryItem r p s]
       , _thyOptions   :: Option
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

$(mkLabels [''Theory])


-- | A diff theory contains a set of rewriting rules with diff modeling two instances
data DiffTheory sig c r r2 p p2 = DiffTheory {
         _diffThyName           :: String
       , _diffThyHeuristic      :: [GoalRanking]
       , _diffThySignature      :: sig
       , _diffThyCacheLeft      :: c
       , _diffThyCacheRight     :: c
       , _diffThyDiffCacheLeft  :: c
       , _diffThyDiffCacheRight :: c
       , _diffThyItems          :: [DiffTheoryItem r r2 p p2]
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )
$(mkLabels [''DiffTheory])


-- Shared theory modification functions
---------------------------------------

filterSide :: Side -> [(Side, a)] -> [a]
filterSide s l = case l of
                    x:xs -> if (fst x) == s then (snd x):(filterSide s xs) else (filterSide s xs)
                    []   -> []

-- | Fold a theory item.
foldTheoryItem
    :: (r -> a) -> (Restriction -> a) -> (Lemma p -> a) -> (FormalComment -> a) -> (Predicate -> a) -> (s -> a)
    -> TheoryItem r p s -> a
foldTheoryItem fRule fRestriction fLemma fText fPredicate fTranslationItem i = case i of
    RuleItem ru   -> fRule ru
    LemmaItem lem -> fLemma lem
    TextItem txt  -> fText txt
    RestrictionItem rstr  -> fRestriction rstr
    PredicateItem     p  -> fPredicate p
    TranslationItem s -> fTranslationItem s

-- | Fold a theory item.
foldDiffTheoryItem
    :: (r -> a) -> ((Side, r2) -> a) -> (DiffLemma p -> a) -> ((Side, Lemma p2) -> a) -> ((Side, Restriction) -> a) -> (FormalComment -> a)
    -> DiffTheoryItem r r2 p p2 -> a
foldDiffTheoryItem fDiffRule fEitherRule fDiffLemma fEitherLemma fRestriction fText i = case i of
    DiffRuleItem ru   -> fDiffRule ru
    EitherRuleItem (side, ru) -> fEitherRule (side, ru)
    DiffLemmaItem lem -> fDiffLemma lem
    EitherLemmaItem (side, lem) -> fEitherLemma (side, lem)
    EitherRestrictionItem (side, rstr)  -> fRestriction (side, rstr)
    DiffTextItem txt  -> fText txt

-- | Map a theory item.
mapTheoryItem :: (r -> r') -> (p -> p') -> TheoryItem r p s -> TheoryItem r' p' s
mapTheoryItem f g =
    foldTheoryItem (RuleItem . f) RestrictionItem (LemmaItem . fmap g) TextItem PredicateItem TranslationItem

-- | Map a diff theory item.
mapDiffTheoryItem :: (r -> r') -> ((Side, r2) -> (Side, r2')) -> (DiffLemma p -> DiffLemma p') -> ((Side, Lemma p2) -> (Side, Lemma p2')) -> DiffTheoryItem r r2 p p2 -> DiffTheoryItem r' r2' p' p2'
mapDiffTheoryItem f g h i =
    foldDiffTheoryItem (DiffRuleItem . f) (EitherRuleItem . g) (DiffLemmaItem . h) (EitherLemmaItem . i) EitherRestrictionItem DiffTextItem

-- | Map a process
mapMProcesses :: Monad m => (PlainProcess -> m(PlainProcess)) -> Theory sig c r p TranslationElement -> m (Theory sig c r p TranslationElement)
mapMProcesses f thy = do
        itms' <- mapM f' itms
        return $ L.set thyItems itms' thy
    where
        itms =  L.get thyItems thy
        f' (TranslationItem (ProcessItem p)) = TranslationItem . ProcessItem <$> f p
        f' (TranslationItem (DiffEquivLemma p)) = TranslationItem . DiffEquivLemma <$> f p
        f' (TranslationItem (EquivLemma p1 p2)) = do
          fp1 <- f p1
          fp2 <- f p2
          return $ TranslationItem (EquivLemma fp1 fp2)
        f' other                       = return other


-- | Map a process definition
mapMProcessesDef :: Monad m => (ProcessDef -> m(ProcessDef)) -> Theory sig c r p TranslationElement -> m (Theory sig c r p TranslationElement)
mapMProcessesDef f thy = do
        itms' <- mapM f' itms
        return $ L.set thyItems itms' thy
    where
        itms =  L.get thyItems thy
        f' (TranslationItem (ProcessDefItem p)) = TranslationItem . ProcessDefItem <$> f p
        f' other                       = return other

-- | All rules of a theory.
theoryRules :: Theory sig c r p s -> [r]
theoryRules =
    foldTheoryItem return (const []) (const []) (const []) (const []) (const []) <=< L.get thyItems

-- | All diff rules of a theory.
diffTheoryDiffRules :: DiffTheory sig c r r2 p p2 -> [r]
diffTheoryDiffRules =
    foldDiffTheoryItem return (const []) (const []) (const []) (const []) (const []) <=< L.get diffThyItems

-- | All rules of a theory.
diffTheorySideRules :: Side -> DiffTheory sig c r r2 p p2 -> [r2]
diffTheorySideRules s =
    foldDiffTheoryItem (const []) (\(x, y) -> if (x == s) then [y] else []) (const []) (const []) (const []) (const []) <=< L.get diffThyItems

-- | All left rules of a theory.
leftTheoryRules :: DiffTheory sig c r r2 p p2 -> [r2]
leftTheoryRules =
    foldDiffTheoryItem (const []) (\(x, y) -> if (x == LHS) then [y] else []) (const []) (const []) (const []) (const []) <=< L.get diffThyItems

-- | All right rules of a theory.
rightTheoryRules :: DiffTheory sig c r r2 p p2 -> [r2]
rightTheoryRules =
    foldDiffTheoryItem (const []) (\(x, y) -> if (x == RHS) then [y] else []) (const []) (const []) (const []) (const []) <=< L.get diffThyItems


-- | All restrictions of a theory.
theoryRestrictions :: Theory sig c r p s -> [Restriction]
theoryRestrictions =
    foldTheoryItem (const []) return (const []) (const []) (const []) (const []) <=< L.get thyItems

-- | All lemmas of a theory.
theoryLemmas :: Theory sig c r p s -> [Lemma p]
theoryLemmas =
    foldTheoryItem (const []) (const []) return (const []) (const []) (const []) <=< L.get thyItems

translationElements :: Theory sig c1 b p c2 -> [c2]
translationElements = foldTheoryItem (const []) (const []) (const []) (const []) (const []) return <=< L.get thyItems

-- | All CaseTest definitions of a theory.
theoryCaseTests :: Theory sig c r p TranslationElement -> [CaseTest]
theoryCaseTests t = [ i | CaseTestItem i <- translationElements t]

-- | All AccLemmas definitions of a theory.
theoryAccLemmas :: Theory sig c r p TranslationElement -> [AccLemma]
theoryAccLemmas t =  [ i | AccLemmaItem i <- translationElements t]

-- | All processes of a theory (TODO give warning if there is more than one...)
theoryProcesses :: Theory sig c r p TranslationElement -> [PlainProcess]
theoryProcesses t = [ i | ProcessItem i <- translationElements t]

-- | All process definitions of a theory.
theoryProcessDefs :: Theory sig c r p TranslationElement -> [ProcessDef]
theoryProcessDefs t = [ i | ProcessDefItem i <- translationElements t]

-- | All function typing information in a theory.
theoryFunctionTypingInfos :: Theory sig c r p TranslationElement -> [SapicFunSym]
theoryFunctionTypingInfos t = [ i | FunctionTypingInfo i <- translationElements t]

-- | All process definitions of a theory.
theoryPredicates :: Theory sig c r p s -> [Predicate]
theoryPredicates =  foldTheoryItem (const []) (const []) (const []) (const []) return (const []) <=< L.get thyItems

-- | All export info definitions of a theory.
theoryExportInfos :: Theory sig c b p TranslationElement -> [ExportInfo]
theoryExportInfos t = [ i | ExportInfoItem i <- translationElements t]

-- | All Builtins of a theory
theoryBuiltins :: Theory sig c r p TranslationElement -> [String]
theoryBuiltins t = [ i | SignatureBuiltin i <- translationElements t]

-- | All Equivalence queries of a theory
theoryEquivLemmas :: Theory sig c r p TranslationElement -> [(PlainProcess, PlainProcess)]
theoryEquivLemmas t =  [ (p1,p2) | EquivLemma p1 p2 <- translationElements t]

-- | All Equivalence queries of a theory
theoryDiffEquivLemmas :: Theory sig c r p TranslationElement -> [PlainProcess]
theoryDiffEquivLemmas t =  [ p | DiffEquivLemma p <- translationElements t]

-- | All restrictions of a theory.
diffTheoryRestrictions :: DiffTheory sig c r r2 p p2 -> [(Side, Restriction)]
diffTheoryRestrictions =
    foldDiffTheoryItem (const []) (const []) (const []) (const []) return (const []) <=< L.get diffThyItems

-- | All restrictions of one side of a theory.
diffTheorySideRestrictions :: Side -> DiffTheory sig c r r2 p p2 -> [Restriction]
diffTheorySideRestrictions s =
    foldDiffTheoryItem (const []) (const []) (const []) (const []) (\(x, y) -> if (x == s) then [y] else []) (const []) <=< L.get diffThyItems

-- | All lemmas of a theory.
diffTheoryLemmas :: DiffTheory sig c r r2 p p2 -> [(Side, Lemma p2)]
diffTheoryLemmas =
   foldDiffTheoryItem (const []) (const []) (const []) return (const []) (const []) <=< L.get diffThyItems

-- | All lemmas of a theory.
diffTheorySideLemmas :: Side -> DiffTheory sig c r r2 p p2 -> [Lemma p2]
diffTheorySideLemmas s =
    foldDiffTheoryItem (const []) (const []) (const []) (\(x, y) -> if (x == s) then [y] else []) (const []) (const []) <=< L.get diffThyItems

-- | All lemmas of a theory.
diffTheoryDiffLemmas :: DiffTheory sig c r r2 p p2 -> [DiffLemma p]
diffTheoryDiffLemmas =
    foldDiffTheoryItem (const []) (const []) return (const []) (const []) (const []) <=< L.get diffThyItems


expandRestriction :: Theory sig c r p s -> ProtoRestriction SyntacticLNFormula
    -> Either FactTag (ProtoRestriction LNFormula)
expandRestriction thy (Restriction n f) =  Restriction n <$> expandFormula (theoryPredicates thy) f


expandLemma :: Theory sig c r p1 s
               -> ProtoLemma SyntacticLNFormula p2
               -> Either FactTag (ProtoLemma LNFormula p2)
expandLemma thy (Lemma n tq f a p) =  (\f' -> Lemma n tq f' a p) <$> expandFormula (theoryPredicates thy) f


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

addProcess :: PlainProcess -> Theory sig c r p TranslationElement -> Theory sig c r p TranslationElement
addProcess l = modify thyItems (++ [TranslationItem (ProcessItem l)])

-- | Add a new process expression.  Since expression (and not definitions)
-- could appear several times, checking for doubled occurrence isn't necessary
addFunctionTypingInfo :: SapicFunSym -> Theory sig c r p TranslationElement -> Theory sig c r p TranslationElement
addFunctionTypingInfo l = modify thyItems (++ [TranslationItem $ FunctionTypingInfo l])

-- | Remove all Function Typing information in Theory
clearFunctionTypingInfos :: Theory sig c r p TranslationElement -> Theory sig c r p TranslationElement
clearFunctionTypingInfos = modify thyItems (filter f)
  where
    f (TranslationItem (FunctionTypingInfo _)) = False
    f _                                  = True
-- | Add a new case test. Fails if CaseTest with the same name already exists.
addCaseTest :: CaseTest -> Theory sig c r p TranslationElement -> Maybe (Theory sig c r p TranslationElement)
addCaseTest cTest thy = do
    guard (isNothing  $ lookupCaseTest (L.get cName cTest) thy)
    return $ modify thyItems (++ [TranslationItem (CaseTestItem cTest)]) thy

-- | Add a new AccLemma  fails if AccLemma with the same name already exists
addAccLemma :: AccLemma -> Theory sig c r p TranslationElement -> Maybe (Theory sig c r p TranslationElement)
addAccLemma aLem thy = do
    guard (isNothing $ lookupAccLemma (L.get aName aLem) thy)
    return $ modify thyItems (++ [TranslationItem (AccLemmaItem aLem)]) thy


-- | Add a new process expression.
addExportInfo :: ExportInfo -> Theory sig c r p TranslationElement -> Maybe (Theory sig c r p TranslationElement)
addExportInfo eInfo thy = do
    guard (isNothing $ lookupExportInfo (L.get eTag eInfo) thy)
    return $ modify thyItems (++ [TranslationItem (ExportInfoItem eInfo)]) thy

-- search process
findProcess :: String -> Theory sig c r p TranslationElement -> Maybe (Theory sig c r p TranslationElement)
findProcess s thy =  do
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
setOption :: Data.Label.Poly.Lens
               Data.Label.Point.Total (Option -> Option) (Bool -> Bool)
             -> Theory sig c r p s -> Theory sig c r p s
setOption l = L.set (l . thyOptions) True

setforcedInjectiveFacts :: S.Set FactTag
             -> Theory sig c r p s -> Theory sig c r p s
setforcedInjectiveFacts = L.set (forcedInjectiveFacts . thyOptions)

-- | Add a new restriction. Fails, if restriction with the same name exists.
addRestrictionDiff :: Side -> Restriction -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
addRestrictionDiff s l thy = do
    guard (isNothing $ lookupRestrictionDiff s (L.get rstrName l) thy)
    return $ modify diffThyItems (++ [EitherRestrictionItem (s, l)]) thy

filterLemma :: (ProtoLemma LNFormula p -> Bool) -> Theory sig c r p s -> Theory sig c r p s
filterLemma lemmaSelector = modify thyItems (concatMap fItem)
    where
    fItem   = foldTheoryItem (return . RuleItem)
                             (return . RestrictionItem)
                             check
                             (return . TextItem)
                             (return . PredicateItem)
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
addHeuristic :: [GoalRanking] -> Theory sig c r p s -> Maybe (Theory sig c r p s)
addHeuristic h (Theory n [] sig c i o) = Just (Theory n h sig c i o)
addHeuristic _ _ = Nothing

addDiffHeuristic :: [GoalRanking] -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
addDiffHeuristic h (DiffTheory n [] sig cl cr dcl dcr i) = Just (DiffTheory n h sig cl cr dcl dcr i)
addDiffHeuristic _ _ = Nothing

-- | Remove a lemma by name. Fails, if the lemma does not exist.
removeLemma :: String -> Theory sig c r p s -> Maybe (Theory sig c r p s)
removeLemma lemmaName thy = do
    _ <- lookupLemma lemmaName thy
    return $ modify thyItems (concatMap fItem) thy
  where
    fItem   = foldTheoryItem (return . RuleItem)
                             (return . RestrictionItem)
                             check
                             (return . TextItem)
                             (return . PredicateItem)
                             (return . TranslationItem)
    check l = do guard (L.get lName l /= lemmaName); return (LemmaItem l)

-- | Remove a lemma by name. Fails, if the lemma does not exist.
removeLemmaDiff :: Side -> String -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
removeLemmaDiff s lemmaName thy = do
    _ <- lookupLemmaDiff s lemmaName thy
    return $ modify diffThyItems (concatMap fItem) thy
  where
    fItem   = foldDiffTheoryItem (return . DiffRuleItem)
                                 (return . EitherRuleItem)
                                 (return . DiffLemmaItem)
                                 check
                                 (return . EitherRestrictionItem)
                                 (return . DiffTextItem)
    check (s', l) = do guard (L.get lName l /= lemmaName || s'/=s); return (EitherLemmaItem (s, l))

-- | Remove a lemma by name. Fails, if the lemma does not exist.
removeDiffLemma :: String -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
removeDiffLemma lemmaName thy = do
    _ <- lookupDiffLemma lemmaName thy
    return $ modify diffThyItems (concatMap fItem) thy
  where
    fItem   = foldDiffTheoryItem (return . DiffRuleItem)
                                 (return . EitherRuleItem)
                                 check
                                 (return . EitherLemmaItem)
                                 (return . EitherRestrictionItem)
                                 (return . DiffTextItem)
    check l = do guard (L.get lDiffName l /= lemmaName); return (DiffLemmaItem l)

-- | Find the restriction with the given name.
lookupRestriction :: String -> Theory sig c r p s -> Maybe Restriction
lookupRestriction name = find ((name ==) . L.get rstrName) . theoryRestrictions

-- | Find the lemma with the given name.
lookupLemma :: String -> Theory sig c r p s -> Maybe (Lemma p)
lookupLemma name = find ((name ==) . L.get lName) . theoryLemmas

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
lookupFunctionTypingInfo tag = find (\(fs,_,_) -> tag == fs) . theoryFunctionTypingInfos

-- | Find the export info for the given tag.
lookupExportInfo :: String -> Theory sig c r p TranslationElement -> Maybe ExportInfo
lookupExportInfo tag = find ((tag ==) . L.get eTag) . theoryExportInfos

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
isRuleItem _            = False

itemToRule :: TheoryItem r p s -> Maybe r
itemToRule (RuleItem r) = Just r
itemToRule _            = Nothing

--Pretty print a theory
prettyTheory :: HighlightDocument d
             => (sig -> d) -> (c -> d) -> (r -> d) -> (p -> d) -> (s -> d)
             -> Theory sig c r p s -> d
prettyTheory ppSig ppCache ppRule ppPrf ppSap thy = vsep $
    [ kwTheoryHeader $ text $ L.get thyName thy
    , lineComment_ "Function signature and definition of the equational theory E"
    , ppSig $ L.get thySignature thy
    , if null thyH then text "" else text "heuristic: " <> text (prettyGoalRankings thyH)
    , ppCache $ L.get thyCache thy
    ] ++
    parMap rdeepseq ppItem (L.get thyItems thy) ++
    [ kwEnd ]
  where
    ppItem = foldTheoryItem
        ppRule prettyRestriction (prettyLemma ppPrf) (uncurry prettyFormalComment) prettyPredicate ppSap
    thyH = L.get thyHeuristic thy


prettyTranslationElement :: HighlightDocument d => TranslationElement -> d
prettyTranslationElement (ProcessItem p) = text "process" <> colon $-$ (nest 2 $ prettyProcess p)
prettyTranslationElement (DiffEquivLemma p) = text "diffEquivLemma" <> colon $-$ (nest 2 $ prettyProcess p)
prettyTranslationElement (EquivLemma p1 p2) = text "equivLemma" <> colon $-$ (nest 2 $ prettyProcess p1) $$ (nest 2 $ prettyProcess p2)
prettyTranslationElement (AccLemmaItem a) = prettyAccLemma a
prettyTranslationElement (CaseTestItem c) = prettyCaseTest c
prettyTranslationElement (ProcessDefItem p) =
    (text "let ")
    <->
    (text (L.get pName p))
    <->
    (case L.get pVars p of
        Nothing -> emptyDoc
        Just l  -> text ("(" ++ intercalate "," (map show l) ++ ")")
    )
    <->
    (text "=")
    <->
    nest 2 (prettyProcess $ L.get pBody p)
prettyTranslationElement (FunctionTypingInfo ((fsn,(_,priv,_)), intypes, outtype)) =
    (text "function:")
    <->
    text (unpack fsn)
    <->
    parens (fsep $ punctuate comma $ map printType intypes)
    <->
    text ":"
    <->
    printType outtype
    <->
    text (showPriv priv)
    where
        printType = maybe (text defaultSapicTypeS) text
        showPriv Private = " [private]"
        showPriv Public  = ""
prettyTranslationElement (ExportInfoItem eInfo) =
    (text "export: ")
    <->
    text (L.get eTag eInfo)
    <->
    nest 2 (doubleQuotes $ text $ L.get eText eInfo)
prettyTranslationElement (SignatureBuiltin s) = (text "builtin ")<->(text s)

prettyPredicate :: HighlightDocument d => Predicate -> d
prettyPredicate p = kwPredicate <> colon <-> text (factstr ++ "<=>" ++ formulastr)
    where
        factstr = render $ prettyFact prettyLVar $ L.get pFact p
        formulastr = render $ prettyLNFormula $ L.get pFormula p

prettyProcess :: HighlightDocument d => PlainProcess -> d
prettyProcess = prettySapic


prettyProcessDef :: HighlightDocument d => ProcessDef -> d
prettyProcessDef pDef = text "let " <-> text (L.get pName pDef) <-> text " = " <-> prettySapic (L.get pBody pDef)


-- | Pretty print a restriction.
prettyRestriction :: HighlightDocument d => Restriction -> d
prettyRestriction rstr =
    kwRestriction <-> text (L.get rstrName rstr) <> colon $-$
    (nest 2 $ doubleQuotes $ prettyLNFormula $ L.get rstrFormula rstr) $-$
    (nest 2 $ if safety then lineComment_ "safety formula" else emptyDoc)
  where
    safety = isSafetyFormula $ formulaToGuarded_ $ L.get rstrFormula rstr

-- | Pretty print an either restriction.
prettyEitherRestriction :: HighlightDocument d => (Side, Restriction) -> d
prettyEitherRestriction (s, rstr) =
    kwRestriction <-> text (L.get rstrName rstr) <-> prettySide s <> colon $-$
    (nest 2 $ doubleQuotes $ prettyLNFormula $ L.get rstrFormula rstr) $-$
    (nest 2 $ if safety then lineComment_ "safety formula" else emptyDoc)
  where
    safety = isSafetyFormula $ formulaToGuarded_ $ L.get rstrFormula rstr
