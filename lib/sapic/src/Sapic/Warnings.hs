module Sapic.Warnings(
    module Sapic.Warnings
) where

import Theory
import Theory.Sapic
import Sapic.Exceptions
import Sapic.Bindings
import Control.Monad.Catch
import Sapic.Annotation (AnnotatedProcess)
import Data.Foldable (traverse_)
import Theory.Tools.Wellformedness (WfErrorReport)
import Theory.Text.Pretty (text)


-- warnProcess :: [WFerror AnnotatedProcess]
warnProcess :: GoodAnnotation a => Process a SapicLVar -> [WFerror AnnotatedProcess]
warnProcess p = map WFBoundTwice (capturedVariables p)

toWfErrorReport :: (Show p) => [WFerror p] -> WfErrorReport
toWfErrorReport = map f
    where
        f e = ("Wellformedness-error in Process", (text . show) e)

throwWarningsProcess :: (GoodAnnotation a, MonadThrow m) => Process a SapicLVar -> m (Process a SapicLVar)
throwWarningsProcess p = traverse_ throwM capture_warnings >> return p -- search for warnings, then return process
    where
        capture_warnings = warnProcess p

-- warningsTheory :: Theory sig c r p SapicElement -> m (Theory sig c r p SapicElement)
warnings :: (Monad m, MonadThrow m) => Theory sig c r p SapicElement -> m (Theory sig c r p SapicElement)
warnings = mapMProcesses throwWarningsProcess

checkWellformednessSapic :: OpenTheory  -> WfErrorReport
checkWellformednessSapic = concatMap (toWfErrorReport . warnProcess) . theoryProcesses