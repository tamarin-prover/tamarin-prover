import Text.Parsec
import Text.Parsec.String (Parser)
import Text.Parsec.Token
import Control.Applicative hiding (many,(<|>))

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

parserDesktop :: SourceName -> String -> Either ParseError [TacticI]
parserDesktop = parse fichier

parserDesktopF :: FilePath -> IO (Either ParseError [TacticI])
parserDesktopF chemin = fmap (parserDesktop chemin) $ readFile chemin

fichier :: Parser [TacticI]
fichier = tactic `endBy` many1 newline

tactic :: Parser TacticI
tactic = liftA3 TacticI tacticName prio deprio

tacticName :: Parser String
tacticName = string "tactic:" *> skipMany (char ' ') *> many (alphaNum <|> oneOf "[]_-@") <* newline 

prio :: Parser Prio
prio = string "prio:" <* newline >> liftA Prio (many function)

deprio :: Parser Deprio
deprio = string "deprio:" <* newline >> liftA Deprio (many function)

function :: Parser String
function = many $ noneOf "\n"
