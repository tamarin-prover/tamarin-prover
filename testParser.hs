import Text.Parsec
import Text.Parsec.String (Parser)
import Debug.Trace

data Prio = Prio {
      functionsPrio :: [String]  
    }
    deriving( Eq, Ord, Show )

data Deprio = Deprio {
      functionsDeprio :: [String]
    }
    deriving( Eq, Ord, Show )

-- | New type for Tactis inside the theory file
data TacticI = TacticI{
      name :: String,
      prios :: Prio,
      deprios :: Deprio
    }
    deriving( Eq, Ord, Show )

parserDesktop :: SourceName -> String -> Either ParseError [String]
parserDesktop = parse fichier

parserDesktopF :: FilePath -> IO (Either ParseError [String])
parserDesktopF chemin = fmap (parserDesktop chemin) $ readFile chemin

fichier :: Parser [String]
fichier = line `endBy` many1 newline

line :: Parser String
line = tactic <|> try function <|> indent 

--Tactic
tactic :: Parser String
tactic = do 
    string "tactic:"
    skipMany (char ' ')
    tacticName <- many (alphaNum <|> oneOf "[]_-@")
    return $ tacticName

--Prio or deprio
indent :: Parser String
indent = do 
    many (char ' ')
    p <- prio <|> deprio
    return p

--Prio
prio :: Parser String
prio = do 
    --lookAhead (string "   prio")
    --many1 $ char ' '
    string "prio:"
    return $ "prio"


--Deprio
deprio :: Parser String
deprio = do
    string "deprio:"
    return $ "deprio"

--Function name
functionName :: Parser String
functionName = many (char ' ') *> many (alphaNum <|> oneOf "[]_-@")

--Function value
functionValue :: Parser String
functionValue = many $ noneOf "\n"

--Fonction
function :: Parser String
function = do
    f <- functionName
    char ' '
    v <- functionValue
    return $ f ++ " takes " ++ v


{--
--Tactic
tactic :: Parser TacticI
tactic = liftA3 TacticI tacticName prio deprio

tacticName :: Parser String
tacticName = string "tactic:" *> skipMany (char ' ') *> many (alphaNum <|> oneOf "[]_-@") <* newline 

--Prio
prio :: Parser Prio
prio = string "prio:" <* newline >> liftA Prio (many function)

--Deprio
deprio :: Parser Deprio
deprio = string "deprio:" <* newline >> liftA Deprio (many function)

--Fonction
function :: Parser String
function = many $ noneOf "\n"
--}
