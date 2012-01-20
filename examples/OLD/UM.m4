theory UM
begin

include(macros.m4h)
define(<!name!>,<!um!>)
define(<!eki!>,<!~ni!>)
define(<!ekr!>,<!~nr!>)

section{* The UM (Unified Model) Key-Exchange Protocol *}

text{*
	 Protocol 5.10 in Boyd and Mathuria (p. 158)
*}


rule Reveal_pk:
  [ ] --> [ Send( pk(lts($m)) ) ]

rule Reveal_lts:
  [ Knows( m ) ] --> [ LTSR( m ), Send( lts(m) ) ]

/* Protocol rules */

basicDH(name,eki,ekr)

/* Session keys */

sessionkeyI(name, h(Gr^eki, PK($R)^SK($I) ), eki, ekr)
sessionkeyR(name, h(Gi^ekr, PK(I)^SK($R)  ), eki, ekr)

subsection{* Secrecy Properties *}

dnl Prefix with 'dnl' to disable. Note: '//' will not work here to
dnl comment out, because the macros unfold to multiple lines.

SecModel	// needed to add rules
DHPExecutable(name)
DHPSecrecy(name,ephkeys,eki,ekr)
DHPKeySecrecy(name)

end
