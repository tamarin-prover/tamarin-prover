{-# LANGUAGE ViewPatterns #-}

module Sapic.Typing
  ( typeTheory
  , typeTheoryEnv
  , typeTermsWithEnv
  , typeProcess
  , TypingEnvironment (..)
  ) where

import Control.Monad.Catch
import Control.Monad.Fresh
import Control.Monad.Trans.PreciseFresh qualified as Precise
import Control.Monad.Trans.State.Lazy
import Data.Bifunctor (Bifunctor(second))
import Data.Foldable qualified as F
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Set qualified as S
import Data.Tuple
import Data.Typeable (Typeable)
import GHC.Stack (HasCallStack)

import Theory
import Theory.Sapic
import Term.SubtermRule
import Sapic.Exceptions
import Sapic.Bindings

-- | Smaller-or-equal / More-or-equally-specific relation on types.
smallerType :: Eq a => Maybe a -> Maybe a -> Bool
smallerType _ Nothing = True
smallerType (Just t) (Just t') = t == t'
smallerType Nothing  (Just _) = False

data TypingException = CannotMerge SapicType SapicType
instance Show TypingException
    where
        show (CannotMerge t1 t2) = "Cannot merge types" ++ show t1 ++ " and " ++ show t2 ++ "."
instance Exception TypingException

-- | Largest lower bound on types. Give the more specific of two types, unless
-- they are contradicting. Can also be used as Either type.
sqcap :: MonadThrow m => Maybe String -> Maybe String -> m (Maybe String)
sqcap t1 t2
          | t1 `smallerType` t2 = return t1
          | t2 `smallerType` t1 = return t2
          | otherwise = throwM (CannotMerge t1 t2)

-- | Default type for function with unspecified types or no type
defaultFunctionType :: Int -> ([Maybe a1], Maybe a2)
defaultFunctionType n =  (replicate n Nothing ,Nothing) -- if no type defined, assume Nothing^n -> Nothing

data TypingEnvironment = TypingEnvironment {
        vars :: Map.Map LVar SapicType
    ,   funs :: Map.Map NoEqSym ([SapicType],SapicType)
    ,   events :: Map.Map FactTag [SapicType]
}

-- | Try to type term `t` with a type more specific than `tt`. Returns typed
-- term and its type in a Throw-Monad that contains the TypingEnvironment state.
typeWith :: (MonadThrow m, MonadCatch m) =>
    Term (Lit Name SapicLVar)
    -> Maybe String
    -> StateT
        TypingEnvironment m (Term (Lit Name SapicLVar), SapicType)
typeWith t tt
    | Lit2 (Var v) <- viewTerm2 t , lvar' <- slvar v -- CASE: variable
    = do
        stype' <-
            if lvarSort lvar' == LSortPub then
                return Nothing
            else do
                maybeType <- Map.lookup lvar' <$> gets (.vars)
                case maybeType of
                    Nothing -> throwM $ WFUnbound (S.singleton lvar')
                    Just t' -> return t'
        t' <- catch (sqcap stype' tt) (sqHandler t)
        te <- get
        modify' (\s -> s { vars = Map.insert (slvar v) t' te.vars })
        return (termViewToTerm $ Lit (Var (SapicLVar lvar' t')), t')
    | FAppNoEq fs@(_,(n,_,_)) ts   <- viewTerm2 t -- CASE: standard function application
    = do
        -- First determine output type of function from target constraint and update FunctionTypingEnvironment
        (intypes1,outtype1) <- getFun n fs
        mintype1 <- catch (sqcap outtype1 tt) (sqHandler t)
        insertFun fs (intypes1, mintype1)
        -- Then try to type arguments
        (_,ptypes) <- unzip <$> zipWithM typeWith ts intypes1
        -- From typing our arguments, we might have learned a more precise
        -- output type, e.g., for t=h(h(x:lol)) we learn that h must have output
        -- lol.
        -- So we recompute the output type ...
        (intypes2,outtype2) <- getFun n fs
        mintype2 <- catch (sqcap outtype2 tt) (sqHandler t)
        insertFun fs (ptypes, mintype2)
        -- ... and now type the arguments for real.
        (ts',ptypes') <- unzip <$> zipWithM typeWith ts intypes2
        insertFun fs (ptypes', outtype2)
        return (termViewToTerm $ FApp (NoEq fs) ts', outtype2)
    | FApp fs ts <- viewTerm t = do  -- list, AC or C symbol: ignore, i.e., assume polymorphic
        ts' <- mapM (\t' -> fst <$> typeWith t' Nothing) ts
        return (termViewToTerm $ FApp fs ts', Nothing)
    | otherwise = return (t, Nothing) -- This case should never occur.
    where
        insertFun fs newFunType = do
                    fte <- gets (.funs)
                    case Map.lookup fs fte of
                        Nothing -> modify' (\s -> s {funs =  Map.insert fs newFunType fte })
                        Just oldFunType -> do
                            case mergeFunTypes newFunType oldFunType of
                                Right mergedFunType ->
                                  modify' (\s -> s {funs =  Map.insert fs mergedFunType fte })
                                Left _ -> throwM $ TypingErrorFunctionMerge fs newFunType oldFunType
        getFun n fs = do
            maybeFType <- Map.lookup fs <$> gets (.funs)
            return $ fromMaybe (defaultFunctionType n) maybeFType
        mergeFunTypes (ins1,out1) (ins2,out2)= do
            ins <- zipWithM sqcap ins1 ins2
            out <- sqcap out1 out2
            return (ins,out)
        sqHandler term (CannotMerge outt tterm) =
                throwM $ TypingError term outt tterm

-- | Types a term with a given environment
-- | Ignores unbounded vars by populating the set of bound vars with all free vars inside terms
typeTermsWithEnv ::  (MonadThrow m, MonadCatch m) => TypingEnvironment -> [Term (Lit Name SapicLVar)] -> m TypingEnvironment
typeTermsWithEnv typeEnv terms = execStateT (mapM typeWith' terms) typeEnv'
         where typeWith' t = typeWith t Nothing
               freeVars = foldl (\acc x -> acc `List.union` frees x) [] (map toLNTerm terms)
               nVars = foldl (\acc x -> Map.insert x Nothing acc ) typeEnv.vars freeVars
               typeEnv' = typeEnv{ vars = nVars}

typeProcess :: (GoodAnnotation a, MonadThrow m, MonadCatch m, Show a, Typeable a) =>
    Process a SapicLVar ->  StateT
        TypingEnvironment m (Process a SapicLVar)
typeProcess = traverseProcess fNull fAct fComb gAct gComb
     where
        -- fNull/fAcc/fComb collect variables that are bound when going downwards
        fNull ann  = return (ProcessNull ann)
        fAct ann ac       = F.traverse_ insertVar (bindingsAct ann ac)
        fComb ann c        = F.traverse_ insertVar (bindingsComb ann c)
        -- gAct/gComb reconstruct process tree assigning types to the terms
        gAct ac@(Event (Fact tag _ ts)) ann r = do -- r is typed subprocess
            ac' <- traverseTermsAction (typeWith' $ ProcessAction ac ann r) typeWithFact typeWithVar ac
            argTypes <- mapM (`typeWith` Nothing) ts
            te <- get
            _ <- modify' (\s -> s { events = Map.insert tag (map snd argTypes) te.events })
            return (ProcessAction ac' ann r)
        gAct ac ann r = do -- r is typed subprocess
            ac' <- traverseTermsAction (typeWith' $ ProcessAction ac ann r) typeWithFact typeWithVar ac
            return (ProcessAction ac' ann r)
        gComb c ann rl rr = do
            c' <- traverseTermsComb (typeWith' $ ProcessComb c ann rl rr) typeWithFact typeWithVar c
            return $ ProcessComb c' ann rl rr
        typeWith' p' t = catch (fst <$> typeWith t Nothing) (handleEx p')
        typeWithVar  v -- variables are correctly typed, as we just inserted them
            | Nothing <- stype v = return $ SapicLVar (slvar v) defaultSapicType
            | otherwise = return v
        typeWithFact = return -- typing facts is hard because of quantified variables. We skip for now.
        insertVar v = do
            te <- get
            case Map.lookup (slvar v) te.vars of
                Just _ -> throwM $ WFBoundTwice v
                Nothing ->
                  modify' (\s -> s { vars = Map.insert (slvar v) (stype v) te.vars })
        handleEx p' wferror = throwM $ ProcessNotWellformed wferror (Just p')

toSapicLVar :: LVar -> SapicLVar
toSapicLVar v = SapicLVar v Nothing

toSapicTerm :: LNTerm -> SapicTerm
toSapicTerm = fmap f
  where
    f (Con c) = Con c
    f (Var v) = Var $ toSapicLVar v

typeRule ::  (MonadThrow m, MonadCatch m) =>  TypingEnvironment -> CtxtStRule -> m TypingEnvironment
typeRule typeEnv r | (lhs `RRule` rhs) <- ctxtStRuleToRRule r = do
                       typeTermsWithEnv typeEnv (map toSapicTerm [lhs, rhs])

initTEFromSig :: (MonadThrow m, MonadCatch m) => OpenTheory -> m TypingEnvironment
initTEFromSig th = do
  foldM typeRule initTE sigRules
  where
    -- we load all funs and add default type
    sig = th._thySignature._sigMaudeInfo
    funSet = stFunSyms sig
    funTyped = foldMap (\fs@(_,(n,_,_)) -> Map.singleton fs (defaultFunctionType n)) funSet
    -- we then also add the custom used defined types
    withUserDefinedFuns = foldr (\(s,inp,out) acc -> Map.insert s (inp,out) acc) funTyped (theoryFunctionTypingInfos th)
    initTE = TypingEnvironment{
                vars = Map.empty,
                funs =  withUserDefinedFuns,
                events = Map.empty
                 }
    sigRules = stRules sig


typeTheoryEnv :: (MonadThrow m, MonadCatch m) => OpenTheory -> m (OpenTheory, TypingEnvironment)
-- typeTheory :: Theory sig c r p TranslationElement -> m (Theory sig c r p TranslationElement)
typeTheoryEnv th = do
    initTE <- initTEFromSig th
    (thaux, fteaux) <- runStateT (mapMProcesses typeAndRenameProcess th) initTE
    (th', fte) <- runStateT (mapMProcessesDef typeAndRenameProcessDef thaux) fteaux
    let th'' = Map.foldrWithKey addFunctionTypingInfo' (clearFunctionTypingInfos th') fte.funs
    return (th'', fte)
    where
        typeAndRenameProcess p = do
                pUnique <- renameUnique p
                modify' (\s -> s { vars = Map.empty})
                typeProcess pUnique
        typeAndRenameProcessDef p = do
                let pr = p._pBody
                let pvars = fromMaybe (S.toList (varsProc pr) List.\\ accBindings pr) p._pVars
                let aux_pr = ProcessAction (ChIn Nothing (fAppList (map varTerm pvars)) S.empty) mempty pr
                renamedP <- typeAndRenameProcess aux_pr
                case renamedP of
                  ProcessAction (ChIn _ (viewTerm2 -> FList tVars) _) _ prf ->
                    return $ p { _pBody = prf, _pVars = Just $ map termVar' tVars}
                  _ -> return p -- should not be taken
        addFunctionTypingInfo' sym (ins,out) = addFunctionTypingInfo (sym, ins,out)

-- | Type the Sapic processes in a theory
typeTheory :: (MonadThrow m, MonadCatch m) => OpenTheory -> m OpenTheory
typeTheory th = fst <$> typeTheoryEnv th

-- | Rename a process so that all its names are unique. Returns renamed process
-- p' and substitution such that: let (p',subst) = renameUnique p in apply subst
-- p' equals p
renameUnique :: (Monad m, Apply (Subst Name LVar) ann, GoodAnnotation ann, HasCallStack) =>
    Process ann SapicLVar -> m (Process ann SapicLVar)
renameUnique p = Precise.evalFreshT actualCall initState
    where
        actualCall = renameUnique' emptySubst p
        initState = avoidPreciseVars . map (\(SapicLVar lvar _) -> lvar) $ S.toList $ varsProc p

renameUnique' ::
  (MonadFresh m, Apply (Subst Name LVar) ann, GoodAnnotation ann) =>
  Subst Name LVar -> Process ann SapicLVar -> m (Process ann SapicLVar)
renameUnique' initSubst p = do
        let p' = apply initSubst p -- apply outstanding substitution subst, ignore capturing and hope for the best
        case p' of
            ProcessNull _ -> return p'
            ProcessAction ac ann pl -> do
                (subst,inv) <- mkSubst $ bindingsAct ann ac
                let ann' = mappendProcessParsedAnnotation (mempty {backSubstitution = inv}) ann
                let ac' = apply subst ac -- use apply instead of applyM because we want to ignore capturing, i.e., rename bound names...
                pl' <- renameUnique' subst pl
                return $ ProcessAction ac' ann' pl'
            ProcessComb comb ann pl pr -> do
                (subst,inv) <- mkSubst $ bindingsComb ann comb
                let ann' = mappendProcessParsedAnnotation (mempty {backSubstitution = inv}) ann
                let comb' = apply subst comb
                pl' <- renameUnique' subst pl
                pr' <- renameUnique' subst pr
                return $ ProcessComb comb' ann' pl' pr'
    where
        substFromVarList = substFromList . map (second varTerm)
        -- f v = do v' <- freshSapicLVarCopy v; return (v, v')
        -- we rename based on LVars, not SapicLVars because variables we want to rename are not properly typed yet.
        f v = do
            let lv = toLVar v
            v' <- freshLVar (lvarName lv) (lvarSort lv);
            return (lv, v')
        mkSubst bvars = do -- create substitution renaming all elements of bind' into a fresh variable
                vmap <- mapM f bvars
                return (substFromVarList vmap, substFromVarList $ map swap vmap)
