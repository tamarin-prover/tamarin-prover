{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Theory.Sapic.Substitution (
    SapicSubst -- convenience export: defined in Theory.Sapic.Term
    -- classes
    , ApplyM (..)
)
where
import Control.Monad.Catch
import Data.Data
import Term.Substitution
import Theory.Sapic.Annotation
import Theory.Sapic.Term

-- | Apply a substitution, but raise an error if necessary
-- class like Apply but with possibility to raise exceptions...
-- note that we have an instance for Apply (without exceptions) automatically.
class ApplyM t' t where
    applyM :: (MonadThrow m) => t' -> t -> m t

data ApplyException v t = ExSubstituteWithTerm v t
instance (Show t, Show v) => Show (ApplyException v t)
    where
        show (ExSubstituteWithTerm v t) = 
          "apply (LVar): variable '" ++ show v
          ++ "' substituted with term '" ++ show t ++ "'"

instance (Typeable v, Typeable t, Show t, Show v) => Exception (ApplyException v t)

instance (Show c, Typeable c, Show v, IsVar v, Typeable v) => ApplyM (Subst c v) v 
    where
    applyM subst x = case imageOf subst x of
            Nothing -> return x
            Just y  -> extractVar y
      where
        extractVar (viewTerm -> Lit (Var x')) = return x'
        extractVar t              =
          throwM $ ExSubstituteWithTerm x t

-- TODO remove!
-- NOTE: We avoid creating proper applyM instances for Lits, Terms and so, as we would
-- repeat much of the implementation for the typeclass Apply from SubstVFree.hs
-- Downside: we risk triggering errors in apply instead of getting proper exceptions
-- instance ApplyM SapicSubst SapicTerm where
--     applyM subst t = return $ apply subst t

instance (ApplyM s v) => ApplyM s (Lit n v) where
        applyM subst = mapM (applyM subst)
instance (Ord l,ApplyM s l) => ApplyM s (Term l) where
        applyM subst = traverseTerm (applyM subst)
instance (ApplyM s v )=> ApplyM s (BVar v) where
        applyM subst = mapM (applyM subst)

instance {-# INCOHERENT #-} (GoodAnnotation a) => ApplyM SapicSubst a
-- INCOHERENT ensures that this instance is selected if other candidates remain (barring knowledge about the context
-- see https://ghc.readthedocs.io/en/8.0.1/glasgow_exts.html?highlight=incoherentinstances#instance-overlap)
    where
        applyM subst ann = do
            ann' <- applyMProcessParsedAnnotation subst $ getProcessParsedAnnotation ann
            return $ setProcessParsedAnnotation ann' ann



-- applyMProcessParsedAnnotation :: (MonadThrow m, ApplyM t' SapicTerm,
--     ApplyM t' SapicLVar) =>
--     t' -> ProcessParsedAnnotation -> m ProcessParsedAnnotation
applyMProcessParsedAnnotation :: 
    (MonadThrow m) =>
    SapicSubst -> ProcessParsedAnnotation -> m ProcessParsedAnnotation
-- applyMProcessParsedAnnotation :: (ApplyM (Map.Map SapicLVar (VTerm c SapicLVar)) SapicTerm,
--     MonadThrow m) =>
--     Map.Map SapicLVar (VTerm c SapicLVar)
--     -> ProcessParsedAnnotation -> m ProcessParsedAnnotation
applyMProcessParsedAnnotation subst ann = do
        loc <- mapM (applyM subst) (location ann)
        return ann {location = loc
                    -- , backSubstitution = undefined 
                    -- WARNING: we do not apply the substitution to the back
                    -- translation, as this is not always possible. If variables
                    -- are renamed, modify the backtranslation by hand.
                    }
