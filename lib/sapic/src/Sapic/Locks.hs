-- |
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Compute annotations for locks.
module Sapic.Locks (
    annotateLocks
) where
import           Control.Exception
import           Control.Monad.Catch as Catch
import           Control.Monad.Fresh
import           Data.Typeable
-- import qualified Data.Traversable as T
import           Sapic.Annotation
import           Sapic.Exceptions
import           Theory
import           Theory.Sapic

-- This exceptions is thrown im annotateEachClosestUnlock finds
-- a parallel or replications below the locks. The calling function
-- annotateLocks catches it and outputs the proper exception with the
-- complete process.
newtype LocalException = LocalException WFLockTag deriving (Show)
instance Exception LocalException


-- | Annotate the closes occurence of unlock that has term t with the
-- variable v output the exception above if we encounter rep or parallel
annotateEachClosestUnlock :: (Eq v1, MonadThrow m) =>
                             SapicNTerm v1
                             -> AnVar v2
                             -> Process (ProcessAnnotation v2) v1
                             -> m (Process (ProcessAnnotation v2) v1)
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
annotateEachClosestUnlock _ _ (ProcessAction Rep _ _) = throwM $ LocalException WFRep
annotateEachClosestUnlock _ _ (ProcessComb Parallel _ _ _) = throwM $ LocalException WFPar
annotateEachClosestUnlock t v (ProcessAction ac a' p) = do p' <- annotateEachClosestUnlock t v p
                                                           return $ ProcessAction ac a' p'
annotateEachClosestUnlock t v (ProcessComb (Lookup st vt) a' pl pr ) | st==t =
  do pl' <- annotateEachClosestUnlock t v pl
     pr' <- annotateEachClosestUnlock t v pr
     return $ ProcessComb (Lookup st vt) (a' <> annUnlock v) pl' pr'
annotateEachClosestUnlock t v (ProcessComb c a' pl pr ) = do pl' <- annotateEachClosestUnlock t v pl
                                                             pr' <- annotateEachClosestUnlock t v pr
                                                             return $ ProcessComb c a' pl' pr'

annotateEachClosestUnlock' :: (MonadCatch m, Typeable v2) =>
                             SapicNTerm SapicLVar
                             -> AnVar v2
                             -> Process (ProcessAnnotation v2) SapicLVar
                             -> m (Process (ProcessAnnotation v2) SapicLVar)
annotateEachClosestUnlock' t v p = 
        Catch.catch (annotateEachClosestUnlock t v p)
        (\(LocalException tag) 
            -> throwM (ProcessNotWellformed (WFLock tag) (Just p))
        )

-- | Annotate locks in a process: chose fresh lock variable and
-- annotateEachClosestUnlock.
annotateLocks :: ( MonadThrow m,
                   MonadCatch m,
                   MonadFresh m
                )
                    => LProcess (ProcessAnnotation LVar) -> m (LProcess (ProcessAnnotation LVar))
annotateLocks (ProcessAction (Lock t) a p) = do
            v <- freshLVar "lock" LSortMsg
            p' <- annotateEachClosestUnlock' t (AnVar v) p
            p'' <- annotateLocks p'
            return (ProcessAction (Lock t) (a `mappend` annLock (AnVar v)) p'')
            -- return (ProcessAction (Lock t) (annLock (AnLVar v)) p'')
annotateLocks (ProcessAction ac an p) = do
            p' <- annotateLocks p
            return (ProcessAction ac an p')
annotateLocks (ProcessNull an ) =
            return (ProcessNull an)
annotateLocks (ProcessComb comb an pl pr ) = do
            pl' <- annotateLocks pl
            pr' <- annotateLocks pr
            return (ProcessComb comb an pl' pr')
