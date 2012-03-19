theory KEAPLUS
begin

include(macros.m4h)

define(<!name!>,<!keaplus!>)

define(<!eki!>,<!~ni!>)
define(<!ekr!>,<!~nr!>)

section{* The KEA+ Key-Exchange Protocol *}

text{*
*}

rule Reveal_pk:
  [ ] --> [ Out( pk(lts($m)) ) ]

rule Reveal_lts:
  [ In( m ) ] --> [ LTSR( m ), Out( lts(m) ) ]


/* Protocol rules */

basicDH(name,eki,ekr)

/* Session keys */

sessionkeyI(name, h(Gr^SK($I), PK($R)^eki, $I, $R ), eki, ekr)
sessionkeyR(name, h(PK(I)^ekr, Gi^SK($R),  I,  $R ), eki, ekr)

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

end
