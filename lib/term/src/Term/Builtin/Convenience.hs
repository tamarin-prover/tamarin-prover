-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Convenience abbreviations, mostly used for testing and debugging.
module Term.Builtin.Convenience where

import Term.Term
import Term.LTerm
import Term.Builtin.Signature

----------------------------------------------------------------------
-- Shorter syntax for Term constructors
----------------------------------------------------------------------

(*:) :: Ord a => Term a -> Term a -> Term a
b *: e = fAppAC Mult [b,e]
(#) :: Ord a => Term a -> Term a -> Term a
b # e  = fAppAC Union [b,e]

adec, aenc, sdec, senc, sign :: (Term a,Term a) -> Term a
adec (a,b)   = fAppNoEq adecSym [a,b]
aenc (a,b)   = fAppNoEq aencSym [a,b]
sdec (a,b)   = fAppNoEq sdecSym [a,b]
senc (a,b)   = fAppNoEq sencSym [a,b]
sign (a,b)   = fAppNoEq signSym [a,b]

verify :: (Term a,Term a,Term a) -> Term a
verify (a,b,c) = fAppNoEq verifySym [a,b,c]

pk :: Term a -> Term a
pk a = fAppNoEq pkSym [a]

trueC :: Term a
trueC = fAppNoEq trueSym []

var :: String -> Integer -> LNTerm
var s i = varTerm $ LVar s LSortMsg i

----------------------------------------------------------------------
-- Predefined variables and names
----------------------------------------------------------------------

x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10 :: LNTerm
x0 = var "x" 0
x1 = var "x" 1
x2 = var "x" 2
x3 = var "x" 3
x4 = var "x" 4
x5 = var "x" 5
x6 = var "x" 6
x7 = var "x" 7
x8 = var "x" 8
x9 = var "x" 9
x10 = var "x" 10

y0,y1,y2,y3,y4,y5,y6,y7,y8,y9 :: LNTerm
y0 = var "y" 0
y1 = var "y" 1
y2 = var "y" 2
y3 = var "y" 3
y4 = var "y" 4
y5 = var "y" 5
y6 = var "y" 6
y7 = var "y" 7
y8 = var "y" 8
y9 = var "y" 9

freshVar :: String -> Integer -> LNTerm
freshVar s i = varTerm $ LVar s LSortFresh i

fx0,fx1,fx2,fx3,fx4,fx5,fx6,fx7,fx8,fx9,fx10 :: LNTerm
fx0  = freshVar "fx" 0
fx1  = freshVar "fx" 1
fx2  = freshVar "fx" 2
fx3  = freshVar "fx" 3
fx4  = freshVar "fx" 4
fx5  = freshVar "fx" 5
fx6  = freshVar "fx" 6
fx7  = freshVar "fx" 7
fx8  = freshVar "fx" 8
fx9  = freshVar "fx" 9
fx10 = freshVar "fx" 10

pubVar :: String -> Integer -> LNTerm
pubVar s i = varTerm $ LVar s LSortPub i

px0,px1,px2,px3,px4,px5,px6,px7,px8,px9,px10 :: LNTerm
px0  = pubVar "px" 0
px1  = pubVar "px" 1
px2  = pubVar "px" 2
px3  = pubVar "px" 3
px4  = pubVar "px" 4
px5  = pubVar "px" 5
px6  = pubVar "px" 6
px7  = pubVar "px" 7
px8  = pubVar "px" 8
px9  = pubVar "px" 9
px10 = pubVar "px" 10

lx1,lx2,lx3,lx4,lx5,lx6,lx7,lx8,lx9,lx10 :: LVar
lx1 = LVar "x" LSortMsg 1
lx2 = LVar "x" LSortMsg 2
lx3 = LVar "x" LSortMsg 3
lx4 = LVar "x" LSortMsg 4
lx5 = LVar "x" LSortMsg 5
lx6 = LVar "x" LSortMsg 6
lx7 = LVar "x" LSortMsg 7
lx8 = LVar "x" LSortMsg 8
lx9 = LVar "x" LSortMsg 9
lx10 = LVar "x" LSortMsg 10

f1,f2,f3,f4,f5,f6,f7,f8,f9 :: LNTerm
f1 = freshTerm  "f1"
f2 = freshTerm  "f2"
f3 = freshTerm  "f3"
f4 = freshTerm  "f4"
f5 = freshTerm  "f5"
f6 = freshTerm  "f6"
f7 = freshTerm  "f7"
f8 = freshTerm  "f8"
f9 = freshTerm  "f9"

p1,p2,p3,p4,p5,p6,p7,p8,p9 :: LNTerm
p1 = pubTerm  "p1"
p2 = pubTerm  "p2"
p3 = pubTerm  "p3"
p4 = pubTerm  "p4"
p5 = pubTerm  "p5"
p6 = pubTerm  "p6"
p7 = pubTerm  "p7"
p8 = pubTerm  "p8"
p9 = pubTerm  "p9"

lv1,lv2,lv3,lv4,lv5,lv6,lv7,lv8,lv9 :: LVar
lv1 = LVar "v1" LSortMsg 0
lv2 = LVar "v2" LSortMsg 0
lv3 = LVar "v3" LSortMsg 0
lv4 = LVar "v4" LSortMsg 0
lv5 = LVar "v5" LSortMsg 0
lv6 = LVar "v6" LSortMsg 0
lv7 = LVar "v7" LSortMsg 0
lv8 = LVar "v8" LSortMsg 0
lv9 = LVar "v9" LSortMsg 0

v1,v2,v3,v4,v5,v6,v7,v8,v9 :: LNTerm
v1 = lit $ Var $ lv1
v2 = lit $ Var $ lv2
v3 = lit $ Var $ lv3
v4 = lit $ Var $ lv4
v5 = lit $ Var $ lv5
v6 = lit $ Var $ lv6
v7 = lit $ Var $ lv7
v8 = lit $ Var $ lv8
v9 = lit $ Var $ lv9

li1,li2,li3,li4,li5,li6,li7,li8,li9 :: LVar
li1 = LVar "i1" LSortNode 0
li2 = LVar "i2" LSortNode 0
li3 = LVar "i3" LSortNode 0
li4 = LVar "i4" LSortNode 0
li5 = LVar "i5" LSortNode 0
li6 = LVar "i6" LSortNode 0
li7 = LVar "i7" LSortNode 0
li8 = LVar "i8" LSortNode 0
li9 = LVar "i9" LSortNode 0

i1,i2,i3,i4,i5,i6,i7,i8,i9 :: LNTerm
i1 = lit $ Var $ li1
i2 = lit $ Var $ li2
i3 = lit $ Var $ li3
i4 = lit $ Var $ li4
i5 = lit $ Var $ li5
i6 = lit $ Var $ li6
i7 = lit $ Var $ li7
i8 = lit $ Var $ li8
i9 = lit $ Var $ li9
