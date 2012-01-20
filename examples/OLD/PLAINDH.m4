theory PLAINDH
begin

include(macros.m4h)

define(<!name!>,<!plaindh!>)

define(<!eki!>,<!~ni!>)
define(<!ekr!>,<!~nr!>)

section{* Plain Diffie-Hellman Key-Exchange Protocol *}

text{*
*}


rule Reveal_pk:
  [ ] --> [ Send( pk(lts($m)) ) ]

rule Reveal_lts:
  [ Knows( m ) ] --> [ LTSR( m ), Send( lts(m) ) ]

/* Protocol rules */

basicDH(name,eki,ekr)

/* Session keys */

sessionkeyI(name, Gr^eki , eki, ekr)
sessionkeyR(name, Gi^ekr , eki, ekr)

subsection{* Secrecy Properties *}

SecModel	
DHPExecutable(name)
DHPSecrecy(name,ephkeys,eki,ekr)
DHPKeySecrecy(name)

end
