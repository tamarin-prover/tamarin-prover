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

import Control.Monad.Catch
import Data.Typeable
import Data.Monoid qualified as M
import Theory.Sapic
import Theory
import Sapic.Exceptions
import Sapic.Annotation

-- | Return subprocess at position p. Throw exceptions if p is an invalid
-- positions.
processAt :: forall ann m v. (Show ann, MonadThrow m, MonadCatch m, Typeable ann, Typeable v, Show v) =>  Process ann v -> ProcessPosition -> m (Process ann v)
processAt p [] = return p
processAt (ProcessNull _) (x:xs) = throwM (InvalidPosition (x:xs) :: SapicException (Process ann v))
processAt pro pos
    | (ProcessAction _ _ p ) <- pro,  1:xl <- pos =  catch (processAt p xl) (h pos)
    | (ProcessComb _ _ pl _) <- pro,  1:xl <- pos =  catch (processAt pl xl) (h pos)
    | (ProcessComb _ _ _ pr) <- pro,  2:xl <- pos =  catch (processAt pr xl) (h pos)
    where --- report original position by catching exception at each level in error case.
        h:: ProcessPosition -> SapicException (Process ann v) -> m (Process ann v)
        h p (InvalidPosition _) = throwM ( InvalidPosition p :: SapicException (Process ann v))
        h _ e = throwM e
processAt _ p = throwM (InvalidPosition p :: SapicException (Process ann v))

processContains :: Process ann v -> (Process ann v -> Bool) -> Bool
processContains anP f = M.getAny $ pfoldMap  (M.Any . f) anP

isLookup :: Process  (ProcessAnnotation LVar) v -> Bool
isLookup (ProcessComb (Lookup _ _) ProcessAnnotation{pureState=False} _ _) = True
isLookup _  = False

isDelete :: Process (ProcessAnnotation LVar) v -> Bool
isDelete (ProcessAction (Delete _) ProcessAnnotation{pureState=False} _) = True
isDelete _  = False

isLock :: Process ann v -> Bool
isLock (ProcessAction (Lock _) _ _) = True
isLock _  = False

isUnlock :: Process ann v -> Bool
isUnlock (ProcessAction (Unlock _) _ _) = True
isUnlock _  = False

isChIn :: Process ann v -> Bool
isChIn (ProcessAction (ChIn _ _ _) _ _) = True
isChIn _  = False

isChOut :: Process ann v -> Bool
isChOut (ProcessAction (ChOut _ _) _ _) = True
isChOut _  = False

isEq :: Process ann v -> Bool
isEq (ProcessComb (CondEq _ _) _ _ _) = True
isEq _  = False
