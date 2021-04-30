module Theory.Sapic.PlainProcess

where

import Theory.Sapic.Process
import Theory.Sapic.Annotation

type PlainProcess = LProcess ProcessParsedAnnotation

-- | Add another element to the existing annotations, e.g., yet another identifier.
paddAnn :: PlainProcess -> ProcessParsedAnnotation -> PlainProcess
paddAnn (ProcessNull ann) ann' = ProcessNull $ ann `mappend` ann'
paddAnn (ProcessComb c ann pl pr ) ann' = ProcessComb c (ann `mappend` ann')  pl pr
paddAnn (ProcessAction a ann p ) ann' = ProcessAction a (ann `mappend` ann')  p

