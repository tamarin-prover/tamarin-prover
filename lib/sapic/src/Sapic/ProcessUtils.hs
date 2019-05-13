{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards #-}
-- Copyright   : (c) 2019 Robert Künnemann 
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Utilities for processes
module Sapic.ProcessUtils (
   processAt 
) where
-- import Data.Maybe
-- import Data.Foldable
-- import Control.Exception
-- import Control.Monad.Fresh
import Data.Typeable
import Control.Monad.Catch
-- import Sapic.Exceptions
-- import Theory
import Theory.Sapic
import Sapic.Exceptions
-- import Theory.Model.Rule
-- import Data.Typeable
-- import qualified Data.Set                   as S
-- import Control.Monad.Trans.FastFresh

-- | Return subprocess at position p. Throw exceptions if p is an invalid
-- positions. 
processAt :: forall m ann. (Show ann, MonadThrow m, MonadCatch m, Typeable ann) =>  AnProcess ann -> ProcessPosition -> m (AnProcess ann)
processAt p [] = return p
processAt (ProcessNull _) (x:xs) = throwM (InvalidPosition (x:xs) :: SapicException (AnProcess ann))
processAt pro pos 
    | (ProcessAction _ _ p ) <- pro,  1:xl <- pos =  catch (processAt p xl) (h pos)
    | (ProcessComb _ _ pl _) <- pro,  1:xl <- pos =  catch (processAt pl xl) (h pos)
    | (ProcessComb _ _ _ pr) <- pro,  2:xl <- pos =  catch (processAt pr xl) (h pos)
    where --- report original position by catching exception at each level in error case.
        h:: ProcessPosition -> SapicException (AnProcess ann) -> m (AnProcess ann)
        h p (InvalidPosition _) = throwM ( InvalidPosition p :: SapicException (AnProcess ann))
        h _ e = throwM e
processAt _ p = throwM (InvalidPosition p :: SapicException (AnProcess ann))
