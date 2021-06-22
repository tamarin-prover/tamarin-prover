-- Copyright   : (c) 2021 Robert Künnemann & Kevin Morio
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Parsing case tests which are used in accountability lemmas.
module Theory.Text.Parser.CaseTest(
      caseTest
)
where

import           Prelude                    hiding (id, (.))
import           Theory
import           Theory.Text.Parser.Token
import           Theory.Text.Parser.Formula


caseTest :: Parser CaseTest
caseTest =  CaseTest <$> (symbol "test" *> identifier)
                     <*> (colon *> doubleQuoted standardFormula)
