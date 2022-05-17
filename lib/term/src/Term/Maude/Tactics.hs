{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Equational signatures for Maude.
module Term.Maude.Signature ()

where 

import qualified Text.PrettyPrint.Highlight as P

------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

prettyMaudeTactic :: P.HighlightDocument d => MaudeSig -> d
prettyMaudeSig sig = P.vcat
    [ ppNonEmptyList' "builtins:"  P.text      builtIns
    , ppNonEmptyList' "functions:" ppFunSymb $ S.toList (stFunSyms sig)
    , ppNonEmptyList
        (\ds -> P.sep (P.keyword_ "equations:" : map (P.nest 2) ds))
        prettyCtxtStRule $ S.toList (stRules sig)
    ]
  where
    ppNonEmptyList' name     = ppNonEmptyList ((P.keyword_ name P.<->) . P.fsep)
    ppNonEmptyList _   _  [] = P.emptyDoc
    ppNonEmptyList hdr pp xs = hdr $ P.punctuate P.comma $ map pp xs

    builtIns = asum $ map (\(f, x) -> guard (f sig) *> pure x)
      [ (enableDH,   "diffie-hellman")
      , (enableBP,   "bilinear-pairing")
      , (enableMSet, "multiset")
      , (enableXor,  "xor")
      ]

    ppFunSymb (f,(k,priv)) = P.text $ BC.unpack f ++ "/" ++ show k ++ showPriv priv
      where showPriv Private = " [private]"
            showPriv Public  = ""
