{-# LANGUAGE PatternGuards #-}
module Sapic.Typing (
      typeTheory
    , typeTheoryEnv
    , typeProcess
    , TypingEnvironment (..)
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
        maybeType <- Map.lookup lvar' <$> gets vars
        let stype' = fromMaybe Nothing maybeType
        -- Note: we graciously ignore unbound variables. Wellformedness
        -- checks on MSRs detect them for us. We might change that in
        -- the future.
        t' <- catch (sqcap stype' tt) (sqHandler t)
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
                    fte <- gets funs
                    case Map.lookup fs fte of
                        Nothing -> modify' (\s -> s {funs =  Map.insert fs newFunType fte })
                        Just oldFunType -> do
                            case mergeFunTypes newFunType oldFunType of
                                Right mergedFunType ->
                                  modify' (\s -> s {funs =  Map.insert fs mergedFunType fte })
                                Left _ -> throwM (ProcessNotWellformed (TypingErrorFunctionMerge fs newFunType oldFunType) :: SapicException AnnotatedProcess)
        getFun n fs = do
            maybeFType <- Map.lookup fs <$> gets funs
            return $ fromMaybe (defaultFunctionType n) maybeFType
        mergeFunTypes (ins1,out1) (ins2,out2)= do
            ins <- zipWithM sqcap ins1 ins2
            out <- sqcap out1 out2
            return (ins,out)
        sqHandler term (CannotMerge outt tterm) =
                throwM (ProcessNotWellformed (TypingError term outt tterm) :: SapicException AnnotatedProcess)

typeProcess :: (GoodAnnotation a, MonadThrow m, MonadCatch m) =>
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
            ac' <- traverseTermsAction typeWith' typeWithFact typeWithVar ac
            argTypes <- mapM (\t -> typeWith t Nothing) ts
            te <- get
            _ <- modify' (\s -> s { events = Map.insert tag (map snd argTypes) (events te)})
            return (ProcessAction ac' ann r)
        gAct ac ann r = do -- r is typed subprocess
            ac' <- traverseTermsAction typeWith' typeWithFact typeWithVar ac
            return (ProcessAction ac' ann r)
        gComb c ann rl rr = do
            c' <- traverseTermsComb typeWith' typeWithFact typeWithVar c
            return $ ProcessComb c' ann rl rr
        typeWith' t = fst <$> typeWith t Nothing
        typeWithVar  v -- variables are correctly typed, as we just inserted them
            | Nothing <- stype v = return $ SapicLVar (slvar v) defaultSapicType
            | otherwise = return v
        typeWithFact = return -- typing facts is hard because of quantified variables. We skip for now.
        insertVar v = do
            te <- get
            case Map.lookup (slvar v) (vars te) of
                Just _ -> throwM (ProcessNotWellformed ( WFBoundTwice v ) :: SapicException AnnotatedProcess)
                Nothing ->
                  modify' (\s -> s { vars = Map.insert (slvar v) (stype v) (vars te)})



typeTheoryEnv :: (MonadThrow m, MonadCatch m) => Theory sig c r p SapicElement -> m (Theory sig c r p SapicElement, TypingEnvironment)
-- typeTheory :: Theory sig c r p SapicElement -> m (Theory sig c r p SapicElement)
typeTheoryEnv th = do
    (th', fte) <- runStateT (mapMProcesses typeProcess th) initTE
    return $ (Map.foldrWithKey addFunctionTypingInfo' (clearFunctionTypingInfos th') (funs fte), fte)
    where
        -- initial typing environment with functions as far as declared
        initTE = TypingEnvironment{
                vars = Map.empty,
                funs = foldMap (\(s,inp,out) -> Map.singleton s (inp,out)) (theoryFunctionTypingInfos th),
                events = Map.empty
                 }
        addFunctionTypingInfo' sym (ins,out) = addFunctionTypingInfo (sym, ins,out)

typeTheory :: (MonadThrow m, MonadCatch m) => Theory sig c r p SapicElement -> m (Theory sig c r p SapicElement)
-- typeTheory :: Theory sig c r p SapicElement -> m (Theory sig c r p SapicElement)
typeTheory th = do
        (th', _) <- typeTheoryEnv th
        return th'
    where
