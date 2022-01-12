import Text.Parsec
import Text.Parsec.String (Parser)
import Debug.Trace

data Prio = Prio {
      functionsPrio :: [(String,String)]  
    }
    deriving( Eq, Ord, Show )

data Deprio = Deprio {
      functionsDeprio :: [(String,String)]
    }
    deriving( Eq, Ord, Show )

{-
data PrioDeprio = Prio [(String,String)] | Deprio [(String,String)]
-}
-- | New type for Tactis inside the theory file
data TacticI = TacticI{
      name :: String,
      prios :: [Prio],
      deprios :: [Deprio]
    }
    deriving( Eq, Ord, Show )

parserDesktop :: SourceName -> String -> Either ParseError TacticI
parserDesktop = parse tactic

parserDesktopF :: FilePath -> IO (Either ParseError TacticI)
parserDesktopF chemin = fmap (parserDesktop chemin) $ readFile chemin


tactic :: Parser TacticI
tactic = do
    tName <- tacticName
    prios <- many1 prio
    deprios <- many1 deprio
    return $ TacticI tName prios deprios
    -- <?> "mimou"


--Tactic
tacticName :: Parser String
tacticName = do 
    string "tactic:"
    skipMany (char ' ')
    tacticName <- many (alphaNum <|> oneOf "[]_-@")
    newline
    return $ tacticName

--Prio
prio :: Parser Prio
prio = do
    string "prio:"
    skipMany (char ' ')
    newline
    fs <- many1 function 
    newline
    return $ Prio fs

--Deprio
deprio :: Parser Deprio
deprio = do 
    string "deprio:"
    skipMany (char ' ')
    newline
    fs <- many1 function 
    newline
    return $ Deprio fs

--Function name
functionName :: Parser String
functionName = many (char ' ') *> many (alphaNum <|> oneOf "[]_-@")
-- functionName = many (char ' ') *> many (alphaNum <|> oneOf "[]_-@")

--Function value
functionValue :: Parser String
functionValue = many $ noneOf "\n"

--Fonction
function :: Parser (String,String)
function = do
    f <- functionName
    char ' '
    v <- functionValue
    return (f,v)

