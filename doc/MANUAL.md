User manual for the Tamarin prover
==================================

For the full manual see https://tamarin-prover.github.io/manual/


Subscribe to https://groups.google.com/group/tamarin-prover for receiving news
on updates and new releases of the Tamarin prover.


Two topics not yet explained in the manual linked above are given here:



Reasoning about Exclusivity: Facts Symbols with Injective Instances
-------------------------------------------------------------------

We say that a fact symbol 'f' has *injective instances* with respect to a
multiset rewriting system 'R', if there is no reachable state of
the multiset rewriting system 'R' with more than one instance of an f-fact
with the same term as a first argument. Injective facts typically arise from
modeling databases using linear facts. An example of an fact with injective
instances, is the 'Store'-fact in the following multiset rewriting system.

  rule CreateKey: [ Fr(handle), Fr(key) ] --> [ Store(handle, key) ]

  rule NextKey:   [ Store(handle, key) ] --> [ Store(handle, h(key)) ]

  rule DelKey:    [ Store(handle,key) ] --> []

When reasoning about the above multiset rewriting system, we exploit that
'Store' has injective instances to prove that after the 'DelKey' rule no other
rule using the same handle can be applied. This proof uses trace induction and
the following constraint-reduction rule that exploits facts with unique
instances.

Let 'f' be a fact symbol with injective instances. Let i, j, and k be temporal
variables ordered according to

  i < j < k

and let there be an edge from (i,u) to (k,w) for some indices u and v.
Then, we have a contradiction, if the premise (k,w) requires a fact 'f(t,...)'
and there is a premise (j,v) requiring a fact 'f(t,...)'.  These two premises
must be merged because the edge (i,u) >-> (k,w) crosses 'j' and the state at
'j' therefore contains 'f(t,...)'. This merging is not possible due to the
ordering constraints 'i < j < k'.

Note that computing the set of fact symbols with injective instances is
undecidable in general. We therefore compute an under-approximation to this
set using the following simple heuristic. A fact tag is guaranteed to have
injective instance, if

  1. the fact-symbol is linear,
  2. every introduction of such a fact is protected by a Fr-fact of the
     first term, and
  3. every rule has at most one copy of this fact-tag in the conclusion and
     the first term arguments agree.

We exclude facts that are not copied in a rule, as they are already handled
properly by the naive backwards reasoning.

Note that this support for reasoning about exclusivity was sufficient for our
case studies, but it is likely that more complicated case studies require
additional support. For example, that fact symbols with injective instances
can be specified by the user and the soundness proof that these symbols have
injective instances is constructed explicitly using the Tamarin prover.
Please tell us, if you encounter limitations in your case studies:
https://github.com/tamarin-prover/tamarin-prover/issues.


Equation Store
--------------

We store equations in a special form to allow delaying case splits on them.
This allows for example to determine the shape of a signed message without case
splitting on its variants. In the GUI, you can see the equation store being
pretty printed as follows.

  free-substitution

  1. fresh-substitution-group
  ...
  n. fresh substitution-group

The free-substitution represents the equalities that hold for the free
variables in the constraint system in the usual normal form, i.e., a
substitution. The variants of a protocol rule are represented as a group of
substitutions mapping free variables of the constraint system to terms
containing only fresh variables. The different fresh-substitutions in a group
are interpreted as a disjunction.

Logically, the equation store represents expression of the form

      x_1 = t_free_1
    & ...
    & x_n = t_free_n
    & ( (Ex y_111 ... y_11k. x_111 = t_fresh_111 & ... & x_11m = t_fresh_11m)
      | ...
      | (Ex y_1l1 ... y_1lk. x_1l1 = t_fresh_1l1 & ... & x_1lm = t_fresh_1lm)
      )
    & ..
    & ( (Ex y_o11 ... y_o1k. x_o11 = t_fresh_o11 & ... & x_o1m = t_fresh_o1m)
      | ...
      | (Ex y_ol1 ... y_olk. x_ol1 = t_fresh_ol1 & ... & x_1lm = t_fresh_1lm)
      )




Developing Tamarin
==================

The Tamarin prover is under active development. We are grateful to receive
bug-reports at 'https://github.com/tamarin-prover/tamarin-prover/issues'. If
you consider building on top of Tamarin, then you might consider integrating
your idea into the main source repository. Please feel free to contact us such
that we can discuss the next steps towards fully verified systems :-)

