Introduction
========

The Tamarin prover is a powerful tool for the symbolic
modeling and analysis of security protocols. 
Given a protocol, consisting of different protocol roles (e.g., an
initiator, a responder, a trusted key server, etc.), Tamarin
can be used to automatically construct a
proof that, even when arbitrarily many instances of these roles (also
known as *threads*) are interleaved in parallel, together
with the actions of an active adversary, the protocol still has its
specified properties.  In this manual, we 
provide an overview of the tool and its use.

Tamarin features expressive languages for specifying protocols,
adversary models, and properties, and it supports efficient deduction
and equational reasoning for protocol analysis.


Tamarin provides general support for modeling and reasoning about
security protocols.  Protocols and adversaries are specified using
an expressive language based on multiset rewriting rules.  These rules define a labeled transition
system whose state consists of a symbolic repersentation of the
adversary’s knowledge, the messages on the network, information about
freshly generated values, and the protocol’s state. The adversary and
the protocol interact by updating network messages and generating new
messages.  Tamarin also supports the equational specification of some
cryptographic operators, notably Diffie-Hellman exponentiation.
Security properties are modeled as trace properties, checked against the
traces of the transition system, or in terms of the observational
equivalence of two transition systems.

Tamarin provides two ways of constructing proofs.  It has an efficient,
fully *automated mode* that combines efficient deduction and equational
reasoning with heuristics to guide proof search.  If the tool's
automated proof search terminates, it returns either a proof of
correctness (for an unbounded number of threads and fresh values) or a
counterexample (i.e., an attack).  However, since the correctness of
security protocols is an undecidable problem, the tool will not always
terminate.  In such cases, users may use Tamarin's *interactive mode* to
explore the proof states, inspect attack graphs, and seamlessly combine
manual proof guidance with automated proof search.


High level points

* Tool for protocol analysis: verification and falsification of
  cryptographic protocols
* Scope: protocols, attackers, properties.  (high level!)
* Limitations, e.g., symbolic model, large search space, may not
  terminate.
* But yet highly successful.   How it distinguishes itself from
  other tools.
* Who is this written for?  Our expectations for reader and where
  additional information can be found for those readers with fewer
  prerequisites.

CSF~\cite{TamarinCSF}, CAV~\cite{TamarinCAV}

Highlights
----------

success stories: briefly

Organization [Ralf/Jannik]
--------------------------

Summary and outline of what is in the document.

