
Introduction
========

The Tamarin prover is a powerful tool for the symbolic
modeling and analysis of security protocols.
It takes as input a security protocol model, specifying the actions taken by
agents running the protocol in different roles (e.g., the
protocol initiator, the responder, and the trusted key server), a specification
of the adversary, and a specification of the protocol's desired properties.
Tamarin can then be used to automatically construct a
proof that, even when arbitrarily many instances of the protocol's roles 
are interleaved in parallel, together
with the actions of the adversary, the protocol fulfils its
specified properties.  In this manual, we 
provide an overview of this tool and its use.

Tamarin provides general support for modeling and reasoning about
security protocols.  Protocols and adversaries are specified using an
expressive language based on multiset rewriting rules.  These rules
define a labeled transition system whose state consists of a symbolic
representation of the adversary’s knowledge, the messages on the
network, information about freshly generated values, and the protocol's
state.  The adversary and the protocol interact by updating network
messages and generating new messages.  Tamarin also supports the
equational specification of some cryptographic operators, such as
Diffie-Hellman exponentiation and bilinear pairings.  Security
properties are modeled as trace properties, checked against the traces
of the transition system, or in terms of the observational equivalence
of two transition systems.

Tamarin provides two ways of constructing proofs.  It has an efficient,
fully *automated mode* that combines deduction and equational
reasoning with heuristics to guide proof search.  If the tool's
automated proof search terminates, it returns either a proof of
correctness (for an unbounded number of role instances and fresh values)
or a counterexample, representing an attack that violates the stated
property.  However, since the correctness of security protocols is an
undecidable problem, the tool may not terminate on a given
verification problem.  Hence, users
may need to resort to Tamarin's *interactive mode* to explore the proof
states, inspect attack graphs, and seamlessly combine manual proof
guidance with automated proof search.

A formal treatment of Tamarin's foundations is given in the theses of
[@benediktthesis]
and [@meierthesis].  We give just a brief (technical) summary here.
For an equational theory $E$ defining cryptographic operators,
a multiset rewriting system $R$ defining a
protocol, and a formula $\phi$ defining a trace property, Tamarin can
either check the validity or the satisfiability of $\phi$ for the traces
of $R$ modulo $E$.  As usual, validity checking is reduced to checking
the satisfiability of the negated formula. Here, constraint solving is
used to perform an exhaustive, symbolic search for executions with
satisfying traces. The states of the search are constraint systems. For
example, a constraint can express that some multiset rewriting step
occurs in an execution or that one step occurs before another step. We
can also directly use formulas as constraints to express that some
behavior does not occur in an execution. Applications of constraint
reduction rules, such as simplifications or case distinctions,
correspond to the incremental construction of a satisfying trace. If no
further rules can be applied and no satisfying trace was found, then no
satisfying trace exists. For symbolic reasoning, we exploit the finite
variant property [@Comon-LundhD05]
to reduce reasoning modulo $E$ with respect to
$R$ to reasoning modulo $AC$ with respect to the variants of $R$.


This manual is written for researchers and practitioners who wish to
use Tamarin to model and analyze security protocols. We assume the
reader is familiar with basic cryptography and the basic workings of
security protocols. Our focus is on explaining Tamarin's usage so that
a new user can download, install, and use the system. We do not
attempt to describe Tamarin's formal foundations and refer the reader
to the related theses and scientific papers for these details.

Highlights
----------

In practice, the Tamarin tool has proven to be highly successful.
It features support for trace and observational equivalence properties, 
automatic and interactive modes, and has built-in support for equational 
theories such as the one modeling Diffie-Hellman Key exchanges. It supports a 
(limited) form of induction, and efficiently parallelizes its proof search. 
It has been applied to numerous protocols from different domains including:

* Advanced key agreement protocols based on Diffie-Hellman
exponentiation, such as verifying Naxos with respect to the
eCK (extended Canetti Krawczyk) model; see [@SchmidtMCB12].
* The Attack Resilient Public Key Infrastructure (ARPKI) [@ARPKI].
* Transport Layer Security (TLS) [@TLS]
* and many others


Organization and Contents of the Manual
---------------------------------------

In the next Section
[Installation](002_installation.html#sec:installation) we describe how
to install Tamarin. First-time users are then recommended to read
Section [First Example](003_example.html#initial-example) which
describes a simple protocol analysis in detail, but without
technicalities. Then, we systematically build up the technical
background a user needs, by first presenting the cryptographic
messages in Section [Cryptographic
Messages](004_cryptographic-messages.html#equational-theories), followed by
two different possible modeling approaches in Sections 5 and 6, covering
[Protocol Specification using
Rules](005_protocol-specification-rules.html#sec:model-specification)
and [Protocol Specification using
Processes](006_protocol-specification-processes.html#sec:model-specification-proc).
Property specification is then covered in Section [Property
Specification](007_property-specification.html#sec:property_specification).

We then continue with information on precomputation in Section
[Precomputation](008_precomputation.html#sec:precomputation) and
possible modeling issues in Section [Modeling
Issues](009_modeling-issues.html#sec:modeling-issues). Afterwards,
advanced features for experienced users are described in Section
[Advanced
Features](010_advanced-features.html#sec:advanced-features). We have a
list of completed case studies in Section [Case
Studies](011_case-studies.html#sec:case-studies). Alternative input
toolchains are described in Section
[Toolchains](012_toolchains.html#sec:tool-chains). Limitations are
described in Section
[Limitations](013_limitations.html#sec:limitations). We conclude the
manual with contact information and further reading in [Contact
Information and Further
Reading](014_contact-and-further-reading.html#sec:contact).


License
-------

Tamarin Prover Manual, by The Tamarin Team.
Copyright © 2016--2024.

[tamarin-prover.com](https://tamarin-prover.com)


This written work is licensed under a Creative Commons Attribution-NonCommercial-ShareAlike 4.0
International License. You may reproduce and edit this work with attribution for all non-commercial
purposes.


References
----------