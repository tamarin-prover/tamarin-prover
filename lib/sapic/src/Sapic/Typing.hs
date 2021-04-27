{-# LANGUAGE PatternGuards #-}
module Sapic.Typing (
      typeTheory
    , typeProcess
) where

import qualified Data.Map.Strict as Map
import qualified Data.Foldable as F
import Data.Maybe
import Control.Monad.Trans.State.Lazy
import Control.Monad.Catch
import Theory
import Theory.Sapic
import Sapic.Exceptions
import Sapic.Annotation
import Sapic.Bindings
import Control.Monad.Fresh
import Control.Monad.Trans.FastFresh   ()

-- | Smaller-or-equal / More-or-equally-specific relation on types.
smallerType :: Eq a => Maybe a -> Maybe a -> Bool
smallerType _ Nothing = True
smallerType (Just t) (Just t') = t == t'
smallerType Nothing  (Just _) = False

-- | Assert that `at` is smaller or equal to `tt`, otherwise throw an exception for term `t`
assertSmaller :: MonadThrow m => Maybe String -> Maybe String -> SapicTerm -> m ()
assertSmaller at tt t =
                if at `smallerType` tt then
                    return ()
                else throwM (ProcessNotWellformed (TypingError t at tt) :: SapicException AnnotatedProcess)

-- | Largest lower bound on types. Give the more specific of two types, unless
-- they are contradicting.
sqcap :: Eq a => Maybe a -> Maybe a -> Either (Maybe a) ()
sqcap t1 t2 
          | t1 `smallerType` t2 = Left t1
          | t2 `smallerType` t1 = Left t2
          | otherwise = Right ()

-- | Default type for function with unspecified types or no type
defaultFunctionType :: Int -> ([Maybe a1], Maybe a2)
defaultFunctionType n =  (replicate n Nothing ,Nothing) -- if no type defined, assume Nothing^n -> Nothing 

-- | Typing environment for variables and functions. Functions are typed
-- globally, variables may be differently typed if they are bound at different
-- positions of the process.
type FunctionTypingEnvironment = Map.Map NoEqSym ([SapicType],SapicType)
type VarTypingEnvironment = Map.Map LVar SapicType

-- | Try to type term `t` with a type more specific than `tt` within VarTypingEnvironment.
--  Returns typed term and its type in a ThrowMonad that contains the FunctionTypingEnvironment state.
typeWith :: MonadThrow m =>
    VarTypingEnvironment
    -> SapicTerm
    -> SapicType
    -> StateT
        FunctionTypingEnvironment m (Term (Lit Name SapicLVar), SapicType)
typeWith vte t tt 
    | Lit2 (Var v) <- viewTerm2 t , lvar' <- slvar v -- CASE: variable
    = do
        let stype' = fromMaybe Nothing $ Map.lookup lvar' vte
        -- Note: we graciously ignore unbound variables. Wellformedness
        -- checks on MSRs detect them for us. We might change that in
        -- the future. 
        case sqcap stype' tt of 
            Left t' -> return (termViewToTerm $ Lit (Var (SapicLVar lvar' t')), t')
            Right () -> throwM (ProcessNotWellformed (TypingError t stype' tt) :: SapicException AnnotatedProcess)
    | FAppNoEq fs@(_,(n,_,_)) ts   <- viewTerm2 t -- CASE: standard function application 
    = do
        maybeFType <- Map.lookup fs <$> get 
        let (intypes,outtype) = fromMaybe (defaultFunctionType n) maybeFType 
                -- throwM (ProcessNotWellformed (FunctionNotDefined fs) :: SapicException AnnotatedProcess)
        assertSmaller outtype tt t
        (ts',ptypes) <- unzip <$> zipWithM (typeWith vte) ts intypes
        insertFun fs (ptypes, outtype)
        return (termViewToTerm $ FApp (NoEq fs) ts', outtype)
    | FApp fs ts <- viewTerm t = do  -- list, AC or C symbol: ignore, i.e., assume polymorphic
        ts' <- mapM (\t' -> fst <$> typeWith vte t' Nothing) ts
        return (termViewToTerm $ FApp fs ts', Nothing)
    | otherwise = return (t, Nothing) -- This case should never occur.
    where
        insertFun fs types = do
                    modify' (Map.insert fs types)

typeProcess :: (GoodAnnotation a, MonadThrow m) =>
    Process a SapicLVar -> StateT FunctionTypingEnvironment m (Process a SapicLVar)
typeProcess = foldMProcess fNull fAct fComb gAct gComb initVarTE
    where
        -- initial typing environment with functions as far as declared
        initVarTE = Map.empty -- passed explicitely to account for process structure
        -- fNull/fAcc/fComb collect variables that are bound when going downwards
        fNull _  ann  = return (ProcessNull ann)
        fAct  vte ann ac       = F.foldrM insertVar vte (bindingsAct ann ac)
        fComb vte ann c        = F.foldrM insertVar vte (bindingsComb ann c)
        -- gAct/gComb reconstruct process tree assigning types to the terms
        gAct vte ac ann r = do -- r is typed subprocess
            ac' <- traverseTermsAction (typeWith' vte) typeWithFact typeWithVar ac
            return (ProcessAction ac' ann r)
        gComb vte c ann rl rr = do
            c' <- traverseTermsComb (typeWith' vte) typeWithFact typeWithVar c
            return $ ProcessComb c' ann rl rr
        typeWith' vte t = fst <$> typeWith vte t Nothing
        typeWithVar = return -- variables are correctly typed, as we just inserted them
        typeWithFact = return -- typing facts is hard because of quantified variables. We skip for now.
        insertVar v vte =
            case Map.lookup (slvar v) vte of
                Just _ -> throwM (ProcessNotWellformed ( WFBoundTwice v ) :: SapicException AnnotatedProcess)
                Nothing -> return $ Map.insert (slvar v) (stype v) vte

typeTheory :: MonadThrow m => Theory sig c r p SapicElement -> m (Theory sig c r p SapicElement)
-- typeTheory :: Theory sig c r p SapicElement -> m (Theory sig c r p SapicElement)
typeTheory th = do 
        (th',fte) <- runStateT (mapMProcesses typeProcess th) initFunTE
        return $ Map.foldrWithKey addFunctionTypingInfo' (clearFunctionTypingInfos th') fte 
    where
        initFunTE = -- initial value for state monad, because it is global
             foldMap (\(s,inp,out) -> Map.singleton s (inp,out)) (theoryFunctionTypingInfos th)
        addFunctionTypingInfo' sym (ins,out) = addFunctionTypingInfo (sym, ins,out)