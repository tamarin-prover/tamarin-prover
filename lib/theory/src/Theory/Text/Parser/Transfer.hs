-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Parsing transfer notation. Currently defunct. 

-- Note: Found when refactoring, was commented out previously. -- Robert Künnemann

{-
-- | Parse an lit with strings for both constants as well as variables.
tlit :: Parser TTerm
tlit = asum
    [ constTerm <$> singleQuoted identifier
    , varTerm  <$> identifier
    ]
-- | Parse a single transfer.
transfer :: Parser Transfer
transfer = do
  tf <- (\l -> Transfer l Nothing Nothing) <$> identifier <* kw DOT
  (do right <- kw RIGHTARROW *> identifier <* colon
      desc <- transferDesc
      return $ tf { tfRecv = Just (desc right) }
   <|>
   do right <- kw LEFTARROW *> identifier <* colon
      descr <- transferDesc
      (do left <- try $ identifier <* kw LEFTARROW <* colon
          descl <- transferDesc
          return $ tf { tfSend = Just (descr right)
                      , tfRecv = Just (descl left) }
       <|>
       do return $ tf { tfSend = Just (descr right) }
       )
   <|>
   do left <- identifier
      (do kw RIGHTARROW
          (do right <- identifier <* colon
              desc <- transferDesc
              return $ tf { tfSend = Just (desc left)
                          , tfRecv = Just (desc right) }
           <|>
           do descl <- colon *> transferDesc
              (do right <- kw RIGHTARROW *> identifier <* colon
                  descr <- transferDesc
                  return $ tf { tfSend = Just (descl left)
                              , tfRecv = Just (descr right) }
               <|>
               do return $ tf { tfSend = Just (descl left) }
               )
           )
       <|>
       do kw LEFTARROW
          (do desc <- colon *> transferDesc
              return $ tf { tfRecv = Just (desc left) }
           <|>
           do right <- identifier <* colon
              desc <- transferDesc
              return $ tf { tfSend = Just (desc right)
                          , tfRecv = Just (desc left) }
           )
       )
    )
  where
    transferDesc = do
        ts        <- tupleterm tlit
        moreConcs <- (symbol "note" *> many1 (try $ fact tlit))
                     <|> pure []
        types     <- typeAssertions
        return $ \a -> TransferDesc a ts moreConcs types
-- | Parse a protocol in transfer notation
transferProto :: Parser [ProtoRuleE]
transferProto = do
    name <- symbol "anb-proto" *> identifier
    braced (convTransferProto name <$> abbrevs <*> many1 transfer)
  where
    abbrevs = (symbol "let" *> many1 abbrev) <|> pure []
    abbrev = (,) <$> try (identifier <* kw EQUAL) <*> multterm tlit
-}