module ProVerifHeader where

-- ProVerif Headers need to be ordered, and declared only once. We order them by type, and will update a set of headers.
data ProVerifHeader
  = Type String -- type declaration
  | Sym String String String [String] -- symbol declaration, (symkind,name,type,attr)
  | Fun String String Int String [String] -- symbol declaration, (symkind,name,arity,types,attr)
  | HEvent String String
  | Table String String
  | Eq String String String String -- eqtype, quantif, equation pub/priv
  deriving (Ord, Show, Eq)
