module Pretty (
    module Pretty
) where

import           Prelude                             hiding (id, (.))


-- import           Data.Typeable
import           Data.List

import           Control.Category

-- import qualified Data.Label.Total


import           Theory.Model
import           Theory.Proof
import           Theory.Text.Pretty


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Pretty print a side for parameters
prettySide :: HighlightDocument d => Side -> d
prettySide LHS = text "[left]"
prettySide RHS = text "[right]"

-- | Pretty print a formal comment
prettyFormalComment :: HighlightDocument d => String -> String -> d
prettyFormalComment "" body = multiComment_ [body]
prettyFormalComment header body = text $ header ++ "{*" ++ body ++ "*}"


emptyString :: HighlightDocument d => () -> d
emptyString _ = text ("")



