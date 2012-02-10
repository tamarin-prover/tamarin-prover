{
{-# OPTIONS_GHC -fno-warn-name-shadowing -fno-warn-unused-matches -fno-warn-unused-binds -fno-warn-missing-signatures -fno-warn-lazy-unlifted-bindings #-}
module Theory.Lexer where

-- This file works only with Alex < 3.0. In the long-term, we plan to switch
-- to a lexer-less approach, i.e., relying completely on parsec.
}


$digit = [0-9]
$letter = [a-zA-Z]
$others = [\192-\214\216-\246\248-\255]

@integer    = $digit+
@identifierFirst = ($letter | $digit | $others)
@identifierAfter = ($letter | $digit | "_" | $others)
@identifier = @identifierFirst @identifierAfter*
@comment     = $printable | $white
@text        = $printable | $white
@lineComment = "//".*

tokens :-
  <0>        $white+            ;

  <0>        @lineComment       ;
  <0>        "(*"               { beginComment "(*" comment }
  <comment>  "(*"               { beginComment "(*" comment }
  <text>     "(*"               { beginComment "(*" comment }
  <comment>  "*)"               { endComment "(*" }          
  <0>        "/*"               { beginComment "/*" comment }
  <comment>  "/*"               { beginComment "/*" comment }
  <text>     "/*"               { beginComment "/*" comment }
  <comment>  "*/"               { endComment "/*" }          
  <comment>  @comment           { skip }

  <0>        "text{*"           { beginText "text" text }
  <0>        "section{*"        { beginText "section" text }
  <0>        "subsection{*"     { beginText "subsection" text }
  <text>     "*}"               { endText 0}          
  <text>     @text              { scanString (TEXT . TextContent) }


  <0>        "∀"                { keyword FORALL }
  <0>        "∃"                { keyword EXISTS }
  <0>        "∧"                { keyword LAND }
  <0>        "∨"                { keyword LOR }
  <0>        "¬"                { keyword LNOT }
  <0>        "≈"                { keyword APPROX }

  <0>        ","                { keyword COMMA }
  <0>        "("                { keyword LPAREN }
  <0>        ")"                { keyword RPAREN }
  <0>        "["                { keyword LBRACKET }
  <0>        "]"                { keyword RBRACKET }
  <0>        "{"                { keyword LBRACE }
  <0>        "}"                { keyword RBRACE }
  <0>        "/"                { keyword SLASH }
  <0>        "\\"               { keyword BACKSLASH }
  <0>        "'"                { keyword SQUOTE }
  <0>        \"                 { keyword DQUOTE }
  <0>        "~"                { keyword TILDE }
  <0>        "^"                { keyword HAT }
  <0>        "="                { keyword EQUAL }
  <0>        ":"                { keyword COLON }
  <0>        "$"                { keyword DOLLAR }
  <0>        "@"                { keyword AT }
  <0>        "#"                { keyword SHARP }
  <0>        "%"                { keyword PERCENT }
  <0>        "*"                { keyword STAR }
  <0>        "<"                { keyword LESS } 
  <0>        ">"                { keyword GREATER } 
  <0>        "?"                { keyword QUESTIONMARK } 
  <0>        "!"                { keyword BANG } 
  <0>        "&"                { keyword AND } 
  <0>        "|"                { keyword MID } 
  <0>        "."                { keyword DOT } 
  <0>        "_"                { keyword UNDERSCORE } 
  <0>        "-"                { keyword MINUS } 
  <0>        "+"                { keyword PLUS } 
  <0>        "->"               { keyword RIGHTARROW } 
  <0>        "<-"               { keyword LEFTARROW } 
  <0>        "-->"              { keyword LONGRIGHTARROW } 
  <0>        "<--"              { keyword LONGLEFTARROW } 
  <0>        @identifier        { scanString IDENT}


{

-- | Lex a keyword
keyword :: Keyword -> AlexAction Keyword
keyword kw input len = return kw

-- | Wrap a string into a keyword
scanString :: (String -> Keyword) -> AlexAction Keyword
scanString kw (_,_,input) len = return $ kw (take len input)

{-
-- | Scan a string until EOF is encountered.
alexScanTokens :: String -> Either String [Keyword]
alexScanTokens inp = runAlex inp gather
  where
  gather = do
    t <- alexMonadScan
    case trace (show t) t of
      EOF -> return [EOF]
      _   -> (t:) `liftM` gather

-- | Scan a file.
scanFile f = do
   inp <- readFile f
   return $ alexScanTokens inp
-}

-- | Formal text types.
data TextType = 
       TextBegin String 
     | TextContent String 
     | TextEnd
     deriving( Eq, Ord, Show )

-- | Lexable Keywords
data Keyword =
    IDENT String
  | TEXT TextType 
  | SQUOTE
  | DQUOTE
  | RIGHTARROW
  | LEFTARROW
  | LONGRIGHTARROW
  | LONGLEFTARROW
  | COMMA
  | DOT
  | COLON
  | QUESTIONMARK
  | BANG
  | AND
  | MID
  | DOLLAR
  | AT
  | SHARP
  | PERCENT
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | LBRACE 
  | RBRACE
  | SLASH
  | BACKSLASH
  | TILDE
  | HAT
  | STAR
  | UNDERSCORE
  | MINUS
  | PLUS
  | EQUAL
  | LESS
  | GREATER
  | EOF
  | FORALL
  | EXISTS
  | LAND
  | LOR
  | LNOT
  | APPROX
  -- dummy keyword to get rid of overlapping pattern matches
  | DUMMY_KEYWORD
  deriving( Eq )

instance Show Keyword where
  show kw = case kw of 
      IDENT i -> identifier i
      TEXT t -> txt t
      SQUOTE -> symbol "'"
      DQUOTE -> symbol "\""
      RIGHTARROW -> symbol "->"
      LEFTARROW -> symbol "<-"
      LONGRIGHTARROW -> symbol "-->"
      LONGLEFTARROW -> symbol "<--"
      COMMA -> symbol ","
      DOT -> symbol "."
      COLON -> symbol ":"
      QUESTIONMARK -> symbol "?"
      BANG -> symbol "!"
      AND -> symbol "&"
      MID -> symbol "|"
      DOLLAR -> symbol "$"
      AT -> symbol "@"
      SHARP -> symbol "#"
      PERCENT -> symbol "%"
      LPAREN -> symbol "("
      RPAREN -> symbol ")"
      LBRACKET -> symbol "["
      RBRACKET -> symbol "]"
      LBRACE  -> symbol "{"
      RBRACE -> symbol "}"
      SLASH -> symbol "/"
      BACKSLASH -> symbol "\\"
      TILDE -> symbol "~"
      HAT -> symbol "^"
      STAR -> symbol "*"
      UNDERSCORE -> symbol "_"
      MINUS -> symbol "-"
      PLUS -> symbol "+"
      EQUAL -> symbol "="
      LESS -> symbol "<"
      GREATER -> symbol ">"
      EOF -> "end of file"
      FORALL -> symbol   "∀"  
      EXISTS -> symbol   "∃"  
      LAND -> symbol     "∧"  
      LOR -> symbol      "∨"  
      LNOT -> symbol     "¬"  
      APPROX -> symbol   "≈"  
      DUMMY_KEYWORD -> "DUMMY_KEYWORD (this should not occur!)"
    where
      identifier i        = "identifier `" ++ i ++ "'"
      txt (TextBegin t)   = "start of `" ++ t ++ "'"
      txt (TextContent t) = "text `" ++ t ++ "'"
      txt (TextEnd)       = "start of text"
      symbol s            = "symbol `" ++ s ++ "'"
      keyword s           = "keyword `" ++ s ++ "'"

-- -----------------------------------------------------------------------------
-- Alex wrapper code.
--
-- This code is in the PUBLIC DOMAIN; you may copy it freely and use
-- it for any purpose whatsoever.

-- -----------------------------------------------------------------------------
-- The input type


type AlexInput = (AlexPosn,     -- current position,
                  Char,         -- previous char
                  String)       -- current input string

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (p,c,s) = c

alexGetChar :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar (p,c,[]) = Nothing
alexGetChar (p,_,(c:s))  = let p' = alexMove p c in p' `seq`
                                Just (c, (p', c, s))


-- -----------------------------------------------------------------------------
-- Token positions

-- `Posn' records the location of a token in the input text.  It has three
-- fields: the address (number of chacaters preceding the token), line number
-- and column of a token within the file. `start_pos' gives the position of the
-- start of the file and `eof_pos' a standard encoding for the end of file.
-- `move_pos' calculates the new position after traversing a given character,
-- assuming the usual eight character tab stops.

data AlexPosn = AlexPn !Int !Int !Int
        deriving (Eq)

instance Show AlexPosn where
  show (AlexPn _ l c) = "line "++show l++" column "++show c

alexStartPos :: AlexPosn
alexStartPos = AlexPn 0 1 1

alexMove :: AlexPosn -> Char -> AlexPosn
alexMove (AlexPn a l c) '\t' = AlexPn (a+1)  l     (((c+7) `div` 8)*8+1)
alexMove (AlexPn a l c) '\n' = AlexPn (a+1) (l+1)   1
alexMove (AlexPn a l c) _    = AlexPn (a+1)  l     (c+1)


-- -----------------------------------------------------------------------------
-- Default monad


data AlexState = AlexState {
        alex_pos :: !AlexPosn,  -- position at current input location
        alex_inp :: String,     -- the current input
        alex_chr :: !Char,      -- the character before the input
        alex_scd :: !Int,       -- the current startcode
        alex_ocd :: !Int,       -- the old startcode before the comment started
        alex_cmt :: [String]    -- stack of begin comment identifiers
    }

-- Compile with -funbox-strict-fields for best results!

runAlex :: String -> Alex a -> Either String a
runAlex input (Alex f) 
   = case f (AlexState {alex_pos = alexStartPos,
                        alex_inp = input,       
                        alex_chr = '\n',
                        alex_scd = 0,
                        alex_ocd = 0,
                        alex_cmt = []
             }) of 
       Left msg -> Left msg
       Right ( _, a ) -> Right a

newtype Alex a = Alex { unAlex :: AlexState -> Either String (AlexState, a) }

instance Monad Alex where
  m >>= k  = Alex $ \s -> case unAlex m s of 
                                Left msg -> Left msg
                                Right (s',a) -> unAlex (k a) s'
  return a = Alex $ \s -> Right (s,a)

alexGetPos :: Alex AlexPosn
alexGetPos = Alex $ \s@AlexState{alex_pos=pos} -> Right (s, pos)

alexGetInput :: Alex AlexInput
alexGetInput
 = Alex $ \s@AlexState{alex_pos=pos,alex_chr=c,alex_inp=inp} -> 
        Right (s, (pos,c,inp))

alexSetInput :: AlexInput -> Alex ()
alexSetInput (pos,c,inp)
 = Alex $ \s -> case s{alex_pos=pos,alex_chr=c,alex_inp=inp} of
                  s@(AlexState{}) -> Right (s, ())

alexError :: String -> Alex a
alexError message = Alex $ \s -> Left $ message ++ " in " ++ show (alex_pos s)

alexGetStartCode :: Alex Int
alexGetStartCode = Alex $ \s@AlexState{alex_scd=sc} -> Right (s, sc)

alexSetStartCode :: Int -> Alex ()
alexSetStartCode sc = Alex $ \s -> Right (s{alex_scd=sc}, ())

alexGetOldStartCode :: Alex Int
alexGetOldStartCode = Alex $ \s@AlexState{alex_ocd=sc} -> Right (s, sc)

alexSetOldStartCode :: Int -> Alex ()
alexSetOldStartCode sc = Alex $ \s -> Right (s{alex_ocd=sc}, ())

alexGetComments :: Alex [String]
alexGetComments = Alex $ \s -> Right (s, alex_cmt s)

alexSetComments :: [String] -> Alex ()
alexSetComments cmt = Alex $ \s -> Right (s{alex_cmt=cmt}, ())

alexMonadScan = do
  inp <- alexGetInput
  sc <- alexGetStartCode
  case alexScan inp sc of
    AlexEOF -> alexEOF
    AlexError inp' -> alexError "lexical error"
    AlexSkip  inp' len -> do
        alexSetInput inp'
        alexMonadScan
    AlexToken inp' len action -> do
        alexSetInput inp'
        action inp len

-- -----------------------------------------------------------------------------
-- Useful token actions

type AlexAction result = AlexInput -> Int -> Alex result

-- just ignore this token and scan another one
skip :: AlexAction Keyword
skip input len = alexMonadScan

-- ignore this token, but set the start code to a new value
begin :: Int -> AlexAction Keyword
begin code input len = do alexSetStartCode code; alexMonadScan

-- | Begin a text starting of the given type.
beginText :: String -> Int -> AlexAction Keyword
beginText ty code _ _ = do
  alexSetStartCode code
  return $ TEXT $ TextBegin ty

-- | End a text.
endText :: Int -> AlexAction Keyword
endText code _ _ = do
  alexSetStartCode code
  return $ TEXT TextEnd

-- | Begin a comment starting with the given sign.
beginComment :: String -> Int -> AlexAction Keyword
beginComment cmtBegin code input len = do
  cmts <- alexGetComments
  alexSetComments $ cmtBegin : cmts
  if null cmts
    then alexGetStartCode >>= alexSetOldStartCode
    else return ()
  alexSetStartCode code
  alexMonadScan

-- | End a comment that started with the given begin comment sign.
endComment :: String -> AlexAction Keyword
endComment cmtBegin input len = do
  cmts <- alexGetComments
  case cmts of
    [] -> alexError $ "comment ended but no beginning '"++cmtBegin++"' marked."
    (cmt:cmts') -> do
      if cmt == cmtBegin 
        then do
          alexSetComments cmts'
          if null cmts' 
            then alexGetOldStartCode >>= alexSetStartCode 
            else return ()
        else return ()
      alexMonadScan

-- perform an action for this token, and set the start code to a new value
-- andBegin :: AlexAction result -> Int -> AlexAction result
(action `andBegin` code) input len = do alexSetStartCode code; action input len

alexEOF :: Alex Keyword
alexEOF = return EOF



}



