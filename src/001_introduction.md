Introduction
========

The Tamarin prover is a powerful tool for the symbolic
modeling and analysis of security protocols. 
Given a protocol, consisting of different protocol roles (e.g., an
initiator, a responder, a trusted key server, etc.), Tamarin
can be used to automatically construct a
proof that, even when arbitrarily many instances of these roles 
are interleaved in parallel, together
with the actions of an active adversary, the protocol still has its
specified properties.  In this manual, we 
provide an overview of the tool and its use.

Tamarin provides general support for modeling and reasoning about
security protocols.  Protocols and adversaries are specified using an
expressive language based on multiset rewriting rules.  These rules
define a labeled transition system whose state consists of a symbolic
repersentation of the adversary’s knowledge, the messages on the
network, information about freshly generated values, and the state of
the protocol's state.  The adversary and the protocol interact by
updating network messages and generating new messages.  Tamarin also
supports the equational specification of some cryptographic operators,
notably Diffie-Hellman exponentiation.  Security properties are modeled
as trace properties, checked against the traces of the transition
system, or in terms of the observational equivalence of two transition
systems.

Tamarin provides two ways of constructing proofs.  It has an efficient,
fully *automated mode* that combines efficient deduction and equational
reasoning with heuristics to guide proof search.  If the tool's
automated proof search terminates, it returns either a proof of
correctness (for an unbounded number of role instances and fresh values)
or a counterexample, representing an attack that violates the stated
property.  However, since the correctness of security protocols is an
undecidable problem, the tool does not always terminate.  Hence, users
may need to resort to Tamarin's *interactive mode* to explore the proof
states, inspect attack graphs, and seamlessly combine manual proof
guidance with automated proof search.

*N.B. If this is too technical it can be dumbed down or deleted or
moved elsewhere.*
A formal treatment of Tamarin's foundations is given in the theses of
[@benediktthesis]
and [@meierthesis].  We give a very brief (technical) summary here.
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
variant property *CITE* to reduce reasoning modulo $E$ with respect to
$R$ to reasoning modulo $AC$ with respect to the variants of $R$.

*Do we really want to explain here how it  distinguishes itself from 
other tools.*

This manual is written for researchers who wish to use Tamarin
to model and analyze security protocols.  We assume the reader
is familiar with basic cryptography and the basic workings
of security protocols.  Our focus is on explaining Tamarin's usage
so that a new user can download, install, and use the system.
We do not attempt to describe Tamarin's formal foundations and
refer to the related theses and scientific papers for these details.

Highlights and Limitations
----------


success stories: briefly

In practice, the Tamarin tool has proven to be highly successful.
Its applications include *enumerate here and cite key papers*.
CSF~\cite{TamarinCSF}, CAV~\cite{TamarinCAV}

*Add something about limitations: 
e.g., symbolic model, large search space, may not
terminate.*




Organization [Ralf/Jannik]
--------------------------

Summary and outline of what is in the document.

