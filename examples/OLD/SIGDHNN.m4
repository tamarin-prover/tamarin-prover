theory SIGDHNN
begin

include(macros.m4h)

define(<!name!>,<!sigdhnn!>)

define(<!eki!>,<!~ni!>)
define(<!ekr!>,<!~nr!>)

section{* Signed Diffie-Hellman Key-Exchange Protocol without partner identities in signatures *}

text{*
*}

rule Reveal_pk:
  [ ] --> [ Send( pk(lts($m)) ) ]

rule Reveal_lts:
  [ Knows( m ) ] --> [ LTSR( m ), Send( lts(m) ) ]

/* Protocol rules */

sigDHnn(name,eki,ekr)

/* Session keys */

sessionkeyI(name, Gr^eki , eki, ekr)
sessionkeyR(name, Gi^ekr , eki, ekr)

subsection{* Secrecy Properties *}

SecModel	
DHPExecutable(name)
DHPSecrecy(name,ephkeys,eki,ekr)
DHPKeySecrecy(name)

end
