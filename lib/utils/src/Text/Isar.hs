-- | Generating Isabelle/ISAR theory files using 'Text.PrettyPrint'.
module Text.Isar (
    -- * ISAR Output
    Isar(..)
    -- ** Configuration
  , IsarStyle(..)
  , IsarConf(..)
  , defaultIsarConf
  , isPlainStyle
  , isarPlain
  , isarXSymbol

  -- ** Constructions of our security protocol verification theory
  , isaExecutionSystemState

  -- ** Special Symbols
  , isarightArrow
  , isaLongRightArrow
  , isaLParr
  , isaRParr
  , isaLBrack
  , isaRBrack
  , isaMetaAll
  , isaExists
  , isaAnd
  , isaNotIn
  , isaIn
  , isaSubsetEq
  , isaAlpha
  , isaSublocale

    -- * Extensions of 'Text.PrettyPrint'
  , module Text.PrettyPrint.Class
  , nestBetween
  , nestShort
  , nestShort'
  , nestShortNonEmpty
  , nestShortNonEmpty'
  , fixedWidthText
  , symbol
  , numbered
  , numbered'

) where

import Data.List

import Extension.Prelude

import Text.PrettyPrint.Class

-- | The ISAR style to be used for output.
data IsarStyle = 
    PlainText 
  | XSymbol
  deriving( Eq, Show )

-- | The configuration to be used for output. Apart from the ISAR style, the
-- configuration also stores the representation of the reachable state of the
-- protocol which we are reasoning about. 
data IsarConf = IsarConf {
    isarStyle :: IsarStyle
  , isarTrace :: Doc        -- ^ The ISAR code of the trace
  , isarPool  :: Doc        -- ^ The ISAR code of the thread pool
  , isarSubst :: Doc        -- ^ The ISAR code of the substitution
  }
  deriving( Show )

-- | Default configuration: plaintext ISAR style and reachable state @(t,r,s)@.
defaultIsarConf :: IsarConf
defaultIsarConf = IsarConf PlainText (char 't') (char 'r') (char 's') 

-- | Check if the plaintext style was chosen.
isPlainStyle :: IsarConf -> Bool
isPlainStyle = (PlainText ==) . isarStyle


-- | Values that can be output as ISAR code. 
--
-- Minimal definition: 'isar'
class Isar a where
  isar :: IsarConf -> a -> Doc

-- | Output as ISAR code using 'defaultIsarConf'.
isarPlain :: Isar a => a -> Doc
isarPlain = isar defaultIsarConf

-- | Output as ISAR code using 'defaultIsarConf'
-- with the XSymbol style.
isarXSymbol :: Isar a => a -> Doc
isarXSymbol = isar (defaultIsarConf { isarStyle = XSymbol })

------------------------------------------------------------------------------
-- General pretty printing combinators
------------------------------------------------------------------------------

-- | Nest a document surrounded by a leading and a finishing document breaking
-- lead, body, and finish onto separate lines, if they don't fit on a single
-- line.
nestBetween :: Document d =>
               Int -- ^ Indent of body
            -> d -- ^ Leading document
            -> d -- ^ Finishing document
            -> d -- ^ Body document
            -> d
nestBetween n l r x = sep [l, nest n x, r]

-- | Nest a document surrounded by a leading and a finishing document with an
-- non-compulsory break between lead and body.
nestShort :: Document d =>
             Int -- ^ Indent of body
          -> d -- ^ Leading document
          -> d -- ^ Finishing document
          -> d -- ^ Body document
          -> d
nestShort n lead finish body = sep [lead $$ nest n body, finish]

-- | Nest document between two strings and indent body by @length lead + 1@.
nestShort' :: Document d => String -> String -> d -> d
nestShort' lead finish = 
  nestShort (length lead + 1) (text lead) (text finish)

-- | Like 'nestShort' but doesn't print the lead and finish, if the document is
-- empty.
nestShortNonEmpty :: Document d => Int -> d -> d -> d -> d
nestShortNonEmpty n lead finish body =
  caseEmptyDoc emptyDoc (nestShort n lead finish body) body

-- | Like 'nestShort'' but doesn't print the lead and finish, if the document is
-- empty.
nestShortNonEmpty' :: Document d => String -> String -> d -> d
nestShortNonEmpty' lead finish = 
  nestShortNonEmpty (length lead + 1) (text lead) (text finish)

-- | Output text with a fixed width: if it is smaller then nothing happens,
-- otherwise care is taken to make the text appear having the given width.
fixedWidthText :: Document d => Int -> String -> d
fixedWidthText n cs
  | length cs <= n  = text cs
  | otherwise = text as <> zeroWidthText bs
  where 
  (as,bs) = splitAt n cs

-- | Print string as symbol having width 1.
symbol :: Document d => String -> d
symbol = fixedWidthText 1

-- | Number a list of documents that are vertically separated by the given
-- separator.
numbered :: Document d => d -> [d] -> d
numbered _   [] = emptyDoc
numbered vsep ds = 
    foldr1 ($-$) $ intersperse vsep $ map pp $ zip [(1::Int)..] ds
  where
    n         = length ds
    nWidth    = length (show n)
    pp (i, d) = text (flushRight nWidth (show i)) <> d
    
-- | Number a list of documents with numbers terminated by "." and vertically
-- separate using an empty line.
numbered' :: Document d => [d] -> d
numbered' = numbered (text "") . map (text ". " <>)


------------------------------------------------------------------------------
-- Operational Semantics Constructions
------------------------------------------------------------------------------

-- | Isabelle representation of the exeuction system state of our operational
-- semantics.
isaExecutionSystemState :: IsarConf -> Doc
isaExecutionSystemState conf = 
  parens . hcat . punctuate comma $ 
    [isarTrace conf, isarPool conf, isarSubst conf]


------------------------------------------------------------------------------
-- Isabelle symbols in both styles.
------------------------------------------------------------------------------

-- | A 'not in' symbol: @~:@
isaNotIn :: Document d => IsarConf -> d
isaNotIn conf
  | isPlainStyle conf = text "~:"
  | otherwise         = symbol "\\<notin>"

-- | An 'in' symbol: @:@
isaIn :: Document d => IsarConf -> d
isaIn conf
  | isPlainStyle conf  = text ":"
  | otherwise         = symbol "\\<in>"

-- | A left parenthesis with an additional vertical line: @(|@
isaLParr :: Document d => IsarConf -> d
isaLParr conf
  | isPlainStyle conf = text "(|"
  | otherwise         = symbol "\\<lparr>"

-- | A right parenthesis with an additional vertical line: @|)@
isaRParr :: Document d => IsarConf -> d
isaRParr conf
  | isPlainStyle conf = text "|)"
  | otherwise         = symbol "\\<rparr>"

-- | A left bracket with an additional vertical line: @[|@
isaLBrack :: Document d => IsarConf -> d
isaLBrack conf
  | isPlainStyle conf = text "[|"
  | otherwise         = symbol "\\<lbrakk>"

-- | A right bracket with an additional vertical line: @|]@
isaRBrack :: Document d => IsarConf -> d
isaRBrack conf
  | isPlainStyle conf = text "|]"
  | otherwise         = symbol "\\<rbrakk>"

-- | A short right arrow: @->@
isarightArrow :: Document d => IsarConf -> d
isarightArrow conf
  | isPlainStyle conf = text "->"
  | otherwise         = fixedWidthText 2 "\\<rightarrow>"

-- | A long double right arrow: @==>@
isaLongRightArrow :: Document d => IsarConf -> d
isaLongRightArrow conf
  | isPlainStyle conf = text "==>"
  | otherwise         = fixedWidthText 3 "\\<Longrightarrow>"


-- | The greek letter alpha: @\\<alpha>@
isaAlpha :: Document d => IsarConf -> d
isaAlpha conf
  | isPlainStyle conf = text "\\<alpha>"
  | otherwise         = symbol "\\<alpha>"

-- | The meta all quantifier: @!!@
isaMetaAll :: Document d => IsarConf -> d
isaMetaAll conf
  | isPlainStyle conf = text "!! "
  | otherwise         = symbol "\\<And>"

-- | The exists symbol: @?@
isaExists :: Document d => IsarConf -> d
isaExists conf
  | isPlainStyle conf = text "? "
  | otherwise         = symbol "\\<exists>"

-- | The logical and symbol: @&@
isaAnd :: Document d => IsarConf -> d
isaAnd conf
  | isPlainStyle conf = text "&"
  | otherwise         = symbol "\\<and>"

-- | The non-strict subset symbol.
isaSubsetEq :: Document d => IsarConf -> d
isaSubsetEq conf
  | isPlainStyle conf = text "<="
  | otherwise         = symbol "\\<subseteq>"

-- | The sublocale sign.
isaSublocale :: Document d => IsarConf -> d
isaSublocale conf
  | isPlainStyle conf = text "<"
  | otherwise         = symbol "\\<subseteq>"

------------------------------------------------------------------------------
-- Isabelle theory components
------------------------------------------------------------------------------

{- TODO: Finish, if it is used

isaTheory :: Document d =>
             String     -- ^ Theory name
          -> [String]   -- ^ Imported theories
          -> d          -- ^ Theory body
          -> d          -- ^ The complete theory statement.
isaTheory name imports body =
  text "theory" <-> text name $-$
  text "imports" $-$
  nest 2 (vcat $ map (text . (++"\"") . ('"':)) imports) $-$
  text "begin" $-$ text "" $-$
  body $-$
  text "" $-$ text "end"


-- | An logic identifier; properly escaped if needed.
-- TODO: Add escaping
logicIdent :: String -> Doc
logicIdent = text


-- | A generic text command.
genTextCmd :: String -> String -> Doc
genTextCmd name content = 
  sep [text name <> text "{*", nest 2 (fsep . map text $ words content), text "*}"]

chapter = genTextCmd "chapter"
section = genTextCmd "section"
subsection = genTextCmd "subsection"
subsubsection = genTextCmd "subsubsection"
paragraph = genTextCmd "text"

-- | A comment.
comment :: String -> Doc
comment content = nestShort' "(*" "*)" (fsep $ map text $ words content)

-- | Switch into a proof context.
context :: String -> Doc -> Doc
context name body = vcat [text name <-> text "begin", body, text "end"]

-}

