module Sapic.Warnings
  ( module Sapic.Warnings
  ) where

import Control.Monad.Catch
import Data.Foldable (toList, traverse_)

import Theory
import Theory.Sapic
import Sapic.Exceptions
import Sapic.Bindings
import Sapic.Locks
import Theory.Tools.Wellformedness (WfErrorReport)
import Theory.Text.Pretty (text)

-- | Checks process (after parsing, before annotation) for wellformedness.
warnProcess :: Process ProcessParsedAnnotation SapicLVar -> [WFerror]
warnProcess p =
    map WFBoundTwice (capturedVariables p)
    <>
    toList (checkLocks p)

-- | Checks process (after parsing, before annotation) for wellformedness and produces report.
toWfErrorReport :: [WFerror] -> WfErrorReport
toWfErrorReport = map f
    where
        f e = ("Wellformedness-error in Process", (text . show) e)

throwWarningsProcess :: MonadThrow m => Process ProcessParsedAnnotation SapicLVar -> m (Process ProcessParsedAnnotation SapicLVar)
throwWarningsProcess p = traverse_ throwM capture_warnings >> return p -- search for warnings, then return process
    where
        capture_warnings = warnProcess p

warnings :: (Monad m, MonadThrow m) => Theory sig c r p TranslationElement -> m (Theory sig c r p TranslationElement)
warnings = mapMProcesses throwWarningsProcess

checkWellformedness :: OpenTheory  -> WfErrorReport
checkWellformedness = concatMap (toWfErrorReport . warnProcess) . theoryProcesses
