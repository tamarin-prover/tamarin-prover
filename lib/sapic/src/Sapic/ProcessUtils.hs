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
,  processContains
,  isLookup
,  isEq
,  isDelete
,  isLock
,  isUnlock
,  isChIn
,  isChOut
) where
-- import Data.Maybe
-- import Data.Foldable
-- import Control.Exception
-- import Control.Monad.Fresh
import Data.Typeable
import Control.Monad.Catch
import qualified Data.Monoid            as M
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

processContains :: AnProcess ann -> (AnProcess ann -> Bool) -> Bool
processContains anP f = M.getAny $ pfoldMap  (M.Any . f) anP

isLookup :: AnProcess ann -> Bool
isLookup (ProcessComb (Lookup _ _) _ _ _) = True
isLookup _  = False

isDelete :: AnProcess ann -> Bool
isDelete (ProcessAction (Delete _) _ _) = True
isDelete _  = False

isLock :: AnProcess ann -> Bool
isLock (ProcessAction (Lock _) _ _) = True
isLock _  = False

isUnlock :: AnProcess ann -> Bool
isUnlock (ProcessAction (Unlock _) _ _) = True
isUnlock _  = False

isChIn :: AnProcess ann -> Bool
isChIn (ProcessAction (ChIn _ _) _ _) = True
isChIn _  = False

isChOut :: AnProcess ann -> Bool
isChOut (ProcessAction (ChOut _ _) _ _) = True
isChOut _  = False

isEq :: AnProcess ann -> Bool
isEq (ProcessComb (CondEq _ _) _ _ _) = True
isEq _  = False
