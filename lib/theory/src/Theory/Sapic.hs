{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Data types for SAPIC processes in theories
module Theory.Sapic (
    -- convenience exports
      module Theory.Sapic.Term
    , module Theory.Sapic.Process
    , module Theory.Sapic.Annotation
    , module Theory.Sapic.Position
    , module Theory.Sapic.Substitution
    , module Theory.Sapic.PlainProcess
) where
import Theory.Sapic.Term
import Theory.Sapic.Process
import Theory.Sapic.Annotation
import Theory.Sapic.Position
import Theory.Sapic.Substitution
import Theory.Sapic.PlainProcess
