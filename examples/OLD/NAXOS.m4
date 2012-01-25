theory NAXOS
begin

include(macros.m4h)

define(<!name!>,<!naxos!>)

define(<!ephkey!>,<!h(<SK($1), $2>)!>)
define(<!eki!>,<!ephkey($I,~ni)!>)
define(<!ekr!>,<!ephkey($R,~nr)!>)

section{* The NAXOS Key-Exchange Protocol *}


rule Reveal_pk:
  [ ] --> [ Out( pk(lts($m)) ) ]

rule Reveal_lts:
  [ In( m ) ] --> [ LTSR( m ), Out( lts(m) ) ]


/* Protocol rules */

basicDH(name,eki,ekr)

/* Session keys */

sessionkeyI(name, h(Gr^SK($I), PK($R)^eki, Gr^eki, $I,$R), eki, ekr)
sessionkeyR(name, h(PK(I)^ekr, Gi^SK($R),  Gi^ekr, I, $R), eki, ekr)

/*
rule SeKey_compr: 
   [ SeKey(k, params) ]
   -->
   [ SeKeyCompr(k, params), Out(k) ]
*/

subsection{* Secrecy Properties *}

dnl Prefix with 'dnl' to disable. Note: '//' will not work here to
dnl comment out, because the macros unfold to multiple lines.

SecModel	// needed to add rules
DHPExecutable(name)
DHPSecrecy(name,ephkeys,eki,ekr)
DHPKeySecrecy(name)

/*
lemma I_niagree:
  "v :> iso_I_3(I, ni, R, hkr) 
   ==> 
   ( Ex u hki nr. 
       u :> iso_R_3(I, hki, R, nr) &
       hki = 'g' ^ ni &
       hkr = 'g' ^ nr
   ) 
   | 
   ( Ex r. r :> LTSR(R) & r >+> v )"

lemma session_key_consistency:
  "v1 :> SeKey (k, params1) & v2 :> SeKey(k, params2)
   ==>
   (params1 = params2) |
   (Ex R I hki hkr vr.
     params1 = <I, R, hki, hkr> &
     vr >+> v1 &
     (vr :> LTSR(I) | vr :> LTSR(R))
   )"
   // I'm curious if we can prove this: it is quite strong due to its
   // asymmetry.

*/

end
