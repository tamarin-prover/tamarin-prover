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

data TypingEnvironment = TypingEnvironment {
        vars :: Map.Map LVar SapicType
    ,   funs :: Map.Map NoEqSym ([SapicType],SapicType)
}

typeProcess :: (GoodAnnotation a, MonadThrow m) =>
    Theory sig c r p SapicElement
    -> Process a SapicLVar -> m (Process a SapicLVar)
typeProcess th = foldMProcess fNull fAct fComb gAct gComb initte
    where
        -- initial typing environment with functions as far as declared
        initte = TypingEnvironment{
                vars = Map.empty,
                funs = foldMap (\(s,inp,out) -> Map.singleton s (inp,out)) (theoryFunctionTypingInfos th)
                 }
        -- fNull/fAcc/fComb collect variables that are bound when going downwards
        fNull _  ann  = return (ProcessNull ann)
        fAct  te ann ac       = F.foldrM insertVar te (bindingsAct ann ac)
        fComb te ann c        = F.foldrM insertVar te (bindingsComb ann c)
        -- gAct/gComb reconstruct process tree assigning types to the terms
        gAct te ac ann r = do -- r is typed subprocess
            ac' <- traverseTermsAction (typeWith te) typeWithFact typeWithVar ac
            return (ProcessAction ac' ann r)
        gComb te c ann rl rr = do
            c' <- traverseTermsComb (typeWith te) typeWithFact typeWithVar c
            return $ ProcessComb c' ann rl rr
        typeWith te t = fst <$> evalStateT (typeWith' t Nothing) te -- start with te as initial state, throw type away, take term (first element)
        typeWith' t tt -- Try to type term t with a type more specific than tt
            | Lit2 (Var v) <- viewTerm2 t , lvar' <- slvar v
            = do
                maybeType <- Map.lookup lvar' <$> gets vars
                -- Note: we graciously ignore unbound variables. Wellformedness
                -- checks on MSRs detect them for us. We might change that in
                -- the future. 
                let stype' = fromMaybe Nothing maybeType
                case sqcap stype' tt of 
                    Left t' -> return (termViewToTerm $ Lit (Var (SapicLVar lvar' t')), t')
                    Right () -> throwM (ProcessNotWellformed (TypingError t stype' tt) :: SapicException AnnotatedProcess)
            | FAppNoEq fs@(_,(n,_,_)) ts   <- viewTerm2 t
            = do
                maybeFType <- Map.lookup fs <$> gets funs
                let (intypes,outtype) = fromMaybe (defaultFunctionType n) maybeFType 
                        -- throwM (ProcessNotWellformed (FunctionNotDefined fs) :: SapicException AnnotatedProcess)
                assertSmaller outtype tt t
                (ts',ptypes) <- unzip <$> zipWithM typeWith' ts intypes
                insertFun fs (ptypes, outtype)
                return (termViewToTerm $ FApp (NoEq fs) ts', outtype)
            | FApp fs ts <- viewTerm t = do  -- list, AC or C symbol: ignore, i.e., assume polymorphic
                ts' <- mapM (\t' -> fst <$> typeWith' t' Nothing) ts
                return (termViewToTerm $ FApp fs ts', Nothing)
            | otherwise = return (t, defaultSapicType) -- TODO no idea how to type here...
        typeWithVar  v -- variables are correctly typed, as we just inserted them
            | Nothing <- stype v = return $ SapicLVar (slvar v) defaultSapicType
            | otherwise = return v
        typeWithFact = return -- typing facts is hard because of quantified variables. We skip for now.
        insertVar v te =
            case Map.lookup (slvar v) (vars te) of
                Just _ -> throwM (ProcessNotWellformed ( WFBoundTwice v ) :: SapicException AnnotatedProcess)
                Nothing -> return $ te { vars = Map.insert (slvar v) (stype v) (vars te)}
        insertFun fs types = do
                    modify' (\s -> s {funs = Map.insert fs types (funs s) })
        defaultFunctionType n =  (replicate n Nothing ,Nothing) -- if no type defined, assume Nothing^n -> Nothing 
        smallerType _ Nothing = True
        smallerType (Just t) (Just t') = t == t'
        smallerType Nothing  (Just _) = False
        sqcap t1 t2 -- give largest lower bound if possible
          | t1 `smallerType` t2 = Left t1
          | t2 `smallerType` t1 = Left t2
          | otherwise = Right ()
        assertSmaller at tt t =
                if at `smallerType` tt then
                    return ()
                else throwM (ProcessNotWellformed (TypingError t at tt) :: SapicException AnnotatedProcess)

typeTheory :: MonadThrow m => Theory sig c r p SapicElement -> m (Theory sig c r p SapicElement)
typeTheory th = mapMProcesses (typeProcess th) th
