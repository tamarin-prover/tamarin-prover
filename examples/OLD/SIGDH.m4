theory SIGDH
begin

include(macros.m4h)

define(<!name!>,<!sigdh!>)

define(<!eki!>,<!~ni!>)
define(<!ekr!>,<!~nr!>)

section{* Signed Diffie-Hellman Key-Exchange Protocol *}

text{*
*}

rule Reveal_pk:
  [ ] --> [ Out( pk(lts($m)) ) ]

rule Reveal_lts:
  [ In( m ) ] --> [ LTSR( m ), Out( lts(m) ) ]


/* Protocol rules */

sigDH(name,eki,ekr)

/* Session keys */

sessionkeyI(name, Gr^eki , eki, ekr)
sessionkeyR(name, Gi^ekr , eki, ekr)

subsection{* Secrecy Properties *}

SecModel	
DHPExecutable(name)
DHPSecrecy(name,ephkeys,eki,ekr)
DHPKeySecrecy(name)

end
