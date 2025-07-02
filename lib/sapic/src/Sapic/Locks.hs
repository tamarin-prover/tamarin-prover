-- |
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Compute annotations for locks.
module Sapic.Locks
  ( annotateLocks,
    checkLocks
  ) where

import Control.Exception
import Data.Monoid
import Control.Monad.Fresh
import Control.Monad.Except
import Control.Monad.Catch
import Sapic.Annotation
import Sapic.Exceptions
import Theory
import Theory.Sapic

-- This exceptions is thrown im annotateEachClosestUnlock finds
-- a parallel or replications below the locks. The calling function
-- annotateLocks catches it and outputs the proper exception with the
-- complete process.
newtype LocalException = LocalException WFLockTag deriving (Show)
instance Exception LocalException


-- | Annotate the closest occurence of unlock that has term t with the
-- variable v output the exception above if we encounter rep or parallel
annotateEachClosestUnlock ::  SapicTerm
                             -> AnVar LVar
                             -> AnnotatedProcess
                             -> Either LocalException AnnotatedProcess
annotateEachClosestUnlock _ _ (ProcessNull a') = return $ ProcessNull a'
annotateEachClosestUnlock t v (ProcessAction (Unlock t') a' p) =
            if t == t' then
                return $ ProcessAction (Unlock t') (a' <> annUnlock v) p
            else do
                p' <- annotateEachClosestUnlock t v p
                return $ ProcessAction (Unlock t') a' p'
annotateEachClosestUnlock t v (ProcessAction (Insert t1 t2) a' p) | t1==t =
               do
                p' <- annotateEachClosestUnlock t v p
                return $ ProcessAction (Insert t1 t2)  (a' <> annUnlock v) p'
annotateEachClosestUnlock _ _ (ProcessAction Rep _ _) = Left $ LocalException WFRep
annotateEachClosestUnlock _ _ (ProcessComb Parallel _ _ _) = Left $ LocalException WFPar
annotateEachClosestUnlock t v (ProcessAction ac a' p) = do p' <- annotateEachClosestUnlock t v p
                                                           return $ ProcessAction ac a' p'
annotateEachClosestUnlock t v (ProcessComb (Lookup st vt) a' pl pr ) | st==t =
  do pl' <- annotateEachClosestUnlock t v pl
     pr' <- annotateEachClosestUnlock t v pr
     return $ ProcessComb (Lookup st vt) (a' <> annUnlock v) pl' pr'
annotateEachClosestUnlock t v (ProcessComb c a' pl pr ) = do pl' <- annotateEachClosestUnlock t v pl
                                                             pr' <- annotateEachClosestUnlock t v pr
                                                             return $ ProcessComb c a' pl' pr'

annotateEachClosestUnlock' :: SapicTerm
                             -> AnVar LVar
                             -> AnnotatedProcess
                             -> Either AnnotatedSapicException AnnotatedProcess
annotateEachClosestUnlock' t v p = case annotateEachClosestUnlock t v p of
        Left (LocalException tag ) -> Left $  ProcessNotWellformed (WFLock tag) (Just p)
        Right ok -> Right ok

throwOnError :: MonadError e m => Either e a -> m a
throwOnError (Left e)  = throwError e
throwOnError (Right r) = return r

-- | Annotate locks in a process: chose fresh lock variable and -- annotateEachClosestUnlock.
annotateLocks' :: (
    MonadError AnnotatedSapicException m,
    MonadFresh m
                ) => AnnotatedProcess -> m AnnotatedProcess
annotateLocks' (ProcessAction (Lock t) a p) = do
            v <- freshLVar "lock" LSortMsg
            p1 <- throwOnError $ annotateEachClosestUnlock' t (AnVar v) p
            p2 <- annotateLocks' p1
            return $ ProcessAction (Lock t) (a `mappend` annLock (AnVar v)) p2
annotateLocks' (ProcessAction ac an p) = do
            p1 <- annotateLocks' p
            return $ ProcessAction ac an p1
annotateLocks' (ProcessNull an ) =
            return $ ProcessNull an
annotateLocks' (ProcessComb comb an pl pr ) = do
            pl' <- annotateLocks' pl
            pr' <- annotateLocks' pr
            return $ ProcessComb comb an pl' pr'

-- | Annotate locks in a process: chose fresh lock variable and -- annotateEachClosestUnlock.
annotateLocks :: MonadThrow m => AnnotatedProcess -> m AnnotatedProcess
annotateLocks p = case run $ annotateLocks' p of
    Left e -> throwM e
    Right p' -> return p'
    where
        run a = runExcept $ evalFreshT a 0

-- | Check if each unlock in p is matched by a lock or if the annotation process returned a different wellformedness error.
-- checkLocks :: GoodAnnotation a => Process a SapicLVarAnnotatedProcess -> Maybe WFerror
checkLocks :: PlainProcess -> Maybe WFerror
checkLocks p = case run $ annotateLocks' $ toAnProcess p of
        Left (ProcessNotWellformed wferror _) -> Just wferror
        Left _  -> Nothing
        (Right pAnnotated) | checkUnmatchedUnlock pAnnotated-> Just WFUnAnnotatedLock
        (Right _ ) -> Nothing
    where
        run a = runExcept $ evalFreshT a 0
        checkUnmatchedUnlock = getAny . pfoldMap (Any . isUnmatchedUnlock)
        isUnmatchedUnlock (ProcessAction (Unlock _) annotation _)
                | Nothing <- annotation.lock = True
        isUnmatchedUnlock _ = False
