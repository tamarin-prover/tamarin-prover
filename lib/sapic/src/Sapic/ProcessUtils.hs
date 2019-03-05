-- Copyright   : (c) 2019 Robert Künnemann and Alexander Dax
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- TODO
module Sapic.ProcessUtils (
    basetrans
) where
-- import Data.Maybe
-- import Data.Foldable
-- import Control.Exception
-- import Control.Monad.Fresh
-- import Control.Monad.Catch
-- import Sapic.Exceptions
import Theory
import Theory.Sapic
-- import Theory.Model.Rule
-- import Data.Typeable
-- import qualified Data.Set                   as S
-- import Control.Monad.Trans.FastFresh

processAt :: AnProcess ann -> Position -> AnProcess
process_at p [] = p
process_at (ProcessNull _) (x:xs) = throwM $ InvalidPosition (x:xs)
process_at pro pos 
    | (ProcessAction _ _ p ) <- pro,  1:xl <- pos =  catch (process_at p xl) (h pos)
    | (ProcessComb _ _ pl pr) <- pro,  1:xl <- pos =  catch (process_at p xl) (h pos)
    | (ProcessComb _ _ pl pr) <- pro,  2:xr <- pos =  catch (process_at p xr) (h pos)
    where --- report original position by catching exception at each level in error case.
        h p (InvalidPosition _) = InvalidPosition p
process_at _ p = throwM $ InvalidPosition p
