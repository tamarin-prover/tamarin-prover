-- |
-- Copyright   : (c) 2019 Charlie Jacomme <charlie.jacomme@lsv.fr>
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Compute annotations for let destructors

module Sapic.LetDestructors
  ( translateLetDestr
  ) where

import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import           Data.List.NonEmpty (NonEmpty(..))

import           Sapic.Annotation
import           Sapic.Exceptions

import           Theory
import           Theory.Sapic

import           Term.SubtermRule
import           Term.Macro (LNMacro, applyMacros)

import           Control.Monad.Catch
import           Control.Monad.Fresh (MonadFresh)

-- | Extract proper-subterm destructors in left-to-right, innermost-first
-- order. The resulting plan stays on the original let: neither continuation
-- is copied, and equation matching stays separate from the source pattern.
splitTerm :: MonadFresh m => Bool -> SapicTerm -> m (SapicTerm, [(SapicTerm, SapicTerm)])
splitTerm extract t = do
  (term, build) <- split extract t
  return (term, build [])
  where
    -- Difference-list composition preserves postorder without copying each
    -- descendant prefix. mapM still allocates fresh variables left to right.
    split takeResult term = case viewTerm term of
      Lit _ -> return (term, id)
      FApp fs args -> do
        parts <- mapM (split True) args
        let rhs = fApp fs (map fst parts)
            bindings = foldr ((.) . snd) id parts
        case fs of
          NoEq (_, (_, _, Destructor, _)) | takeResult -> do
            v <- freshLVar "destructor" LSortMsg
            let result = varTerm (SapicLVar v Nothing)
            return (result, bindings . ((result, rhs) :))
          _ -> return (rhs, bindings)

-- | The equations of each destructor, as left-hand side arguments and
-- right-hand side.
type DestructorEquations = M.Map FunSym [([LNTerm], LNTerm)]

mapProc :: (MonadThrow m, MonadFresh m) => DestructorEquations -> AnnotatedProcess -> m AnnotatedProcess
mapProc _ (ProcessNull ann) = return $ ProcessNull ann
mapProc rules (ProcessAction ac ann p') =
  ProcessAction ac ann <$> mapProc rules p'
mapProc rules (ProcessComb c@(Let lhs rhs mv) ann pl pr) = do
  (rhs', bindings) <- splitTerm False rhs
  plan <- stages (bindings ++ [(lhs, rhs')])
  case plan of
    -- No defining equation means evaluation necessarily fails. Do not visit
    -- unreachable later stages or the success continuation.
    Nothing -> mapProc rules pr
    Just _ | null bindings, not (isDestructor rhs),
             LIT (Var svar) <- lhs, not (svar `S.member` mv) -> do
      res <- applyM (substFromList [(v, rhs) | v <- untypedVariants svar]) pl
      mapProc rules res
    Just steps -> do
      npl <- mapProc rules pl
      npr <- mapProc rules pr
      return $ ProcessComb c (ann {letPlan = steps, elseBranch = hasElse}) npl npr
  where
    hasElse = case pr of ProcessNull _ -> False; _ -> True
    isDestructor t = case viewTerm t of
      FApp (NoEq (_, (_, _, Destructor, _))) _ -> True
      _ -> False
    untypedVariants svar@(SapicLVar v (Just _)) = [svar, SapicLVar v Nothing]
    untypedVariants svar = [svar]
    stages [] = return $ Just []
    stages ((patternTerm, term):rest) = do
      let result = toLNTerm patternTerm
          bound = S.fromList $ frees result
      step <- case viewTerm (toLNTerm term) of
        FApp fs@(NoEq (_, (_, _, Destructor, _))) args ->
          case M.findWithDefault [] fs rules of
            [] -> return Nothing
            equations@(_:_) | any (containsDestructor . snd) equations ->
              throwM (NotImplementedError
                "SAPIC destructor equation results must not contain destructor calls."
                :: SapicException AnnotatedProcess)
            equation:equations -> do
              -- Equation matching may bind opaque auxiliary variables which
              -- the process never learns. Keep it separate from the user's
              -- pattern, whose bindings still need derivation checking.
              reduct <- freshLVar "destructor" LSortMsg
              let reduce (leftterms, reductTerm) = (toPairs leftterms, Just reductTerm)
              return $ Just
                [ LetStage (toPairs args) (reduce equation :| map reduce equations) S.empty
                , LetStage (varTerm reduct) ((result, Nothing) :| []) bound ]
        _ -> return $ Just [LetStage (toLNTerm term) ((result, Nothing) :| []) bound]
      case step of
        Nothing -> return Nothing
        Just sts -> fmap (sts ++) <$> stages rest
    -- List is reducible, so use constructor pairs for multi-argument matching.
    toPairs [] = fAppOne
    toPairs [s] = s
    toPairs (s:ss) = fAppPair (s, toPairs ss)
mapProc rules (ProcessComb c ann pl pr) =
  ProcessComb c ann <$> mapProc rules pl <*> mapProc rules pr

-- Equation results are passed to the user-pattern stage as messages. The
-- translator cannot evaluate destructor calls introduced by an equation.
containsDestructor :: LNTerm -> Bool
containsDestructor t = case viewTerm t of
  FApp (NoEq (_, (_, _, Destructor, _))) _ -> True
  FApp _ args -> any containsDestructor args
  _ -> False

-- Index once, preserving equation order.
indexEquations :: [LNTerm] -> Set CtxtStRule -> DestructorEquations
indexEquations avoidTerms = M.map (`renameAvoiding` avoidTerms)
                         . M.fromListWith (flip (++)) . concatMap entry . S.toList
  where
    entry rule = case ctxtStRuleToRRule rule of
      lhs `RRule` rhs -> case viewTerm lhs of
        FApp fs args -> [(fs, [(args, rhs)])]
        _ -> []

translateLetDestr :: MonadThrow m => [LNMacro] -> Set CtxtStRule -> AnnotatedProcess -> m AnnotatedProcess
translateLetDestr macros rules source = evalFreshTAvoiding (mapProc indexed p) avoidVars
  where
    -- Global macros use the destructor tag too, but are substitutions, not
    -- partial functions. Expand them before deciding which calls can fail,
    -- including destructors introduced (or arguments discarded) by a macro.
    -- Preserve the types of substituted process arguments.
    sapicMacros = [(name, map untyped args, fmap (fmap untyped) body) | (name, args, body) <- macros]
    untyped v = SapicLVar v Nothing
    expand = applyMacros sapicMacros
    expandLets (ProcessComb (Let lhs rhs mv) ann pl pr) =
      ProcessComb (Let (expand lhs) (expand rhs) mv) ann (expandLets pl) (expandLets pr)
    expandLets (ProcessComb c ann pl pr) = ProcessComb c ann (expandLets pl) (expandLets pr)
    expandLets (ProcessAction ac ann rest) = ProcessAction ac ann (expandLets rest)
    expandLets p'@(ProcessNull _) = p'
    p = if null macros then source else expandLets source
    sourceVars = [varTerm v :: LNTerm | SapicLVar v _ <- S.toList $ varsProc p]
    indexed = indexEquations sourceVars rules
    -- Equation variables and internal temporaries occupy the same untyped
    -- namespace. Allocate temporaries after reserving the freshened equations.
    avoidVars = sourceVars ++
      [t | equations <- M.elems indexed, (args, rhs) <- equations,
           t <- rhs : args]
