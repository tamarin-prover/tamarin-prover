Model Specification
===================

Models are specificied in Tamarin using three main ingredients:

   1. Terms
   2. Facts
   3. Rules

We will discuss each of them in term and illustrate their use with respect to
the Naxos protocol, displayed below.

![The Naxos protocol](../images/naxos.png)

Each party `x` has a long-term private key `lkx` and a corresponding public key
`pkx = g^lkx`, where `g` is a generator of the Diffie-Hellman group. To start a
session, the initiator `I` first creates a fresh nonce `eskI`, also known as
`I`’s ephemeral (private) key. He then concatenates eskI with `I`’s long-term
private key `lkI`, hashes the result using the hash function `h1`, and sends
`g^h1(eskI ,lkI )` to the responder. The responder `R` stores the received value
in a variable `X`, computes a similar value based on his own nonce `eskR` and
long-term private key `lkR`, and sends the result to the initiator, who stores
the received value in the variable `Y`. Finally, both parties compute a session
key (`kI` and `kR`, respectively) whose computation includes their own long-term
private keys, such that only the intended partner can compute the same key.

Note that the messages exchanged are not authenticated, as the recipients cannot
verify that the expected longterm key was used in the construction of the
message.  The authentication is implicit and only guaranteed through ownership
of the correct key. Explicit authentication (e.g., the intended partner was
recently alive or agrees on some values) is commonly achieved in AKE protocols
by adding a key-confirmation step, where the parties exchange a MAC of the
exchanged messages that is keyed with (a variant of) the computed session key.

In this manual, we provide an informal description of the underlying model. The full details of the underlying model can be found in [@benediktthesis].

Cryptographic messages as Terms
-------------------------------

To model cryptographic messages we use terms, which are represented by trees
where the nodes are operators (such as pairing, function application,
concatenation, encryption) and the leaves are constants or variables.

For the leaves, we have 
We use the set of
sorts consisting of the top sort msg and two incomparable subsorts `fr` and
`pub` for fresh and public names. We assume there are two countably infinite
sets `FN` and `PN` of fresh and public names. We use fresh names to model
random messages such as keys or nonces and public names to model known
constants such as agent identities.





Facts
-----

Facts are of the form `F(t1,...,tN)` for a fact symbol `F` and terms `tI`.


[`In`]:

[`Out`]:

[`Fr`]:




Rules
-----

We use multiset rewriting to specify the concurrent execution of protocol and
adversary.  Multiset rewriting is commonly used to model concurrent systems
since it naturally sup- ports independent transitions. If two rewriting steps
rewrite the state at positions that do not overlap, then they can be applied in
parallel. We extend standard multiset rewriting with support for creating fresh
names. Additionally, we introduce persistent facts and enrich rewriting rules
with actions to obtain labeled transition systems.

Concretely, Tamarin's rewrite rules have sequences of facts as left-hand-sides,
labels, and right-hand-sides.

