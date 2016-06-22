
Property Specification{#sec:property_specification}
======================

Trace Properties
----------------

**FIXME: what are trace properties**

The Tamarin multiset rewriting rules define a labeled transition
system. The system's state is a multiset (bag) of facts. The initial
system state is the empty multiset. The types of facts and their use 
are described in Section [Rules](#sec:rules). Here we focus on the action facts. 

**FIXME: what is a guarded formula/variable**

We reason about a protocol's behaviour by annotating its
rules with *action facts*.  
For instance, consider the following fictitious rule 
```
rule fictitious:
   [ Pre(x), Fr(~n) ]
 --[ Act1(~n), Act2(x) ]-->
   [ Out(<x,~n>) ]
```

The rule rewrites the system state by consuming the facts `Pre(x)` and
`Fr(~n)` and producing the fact `Out(<x,~n>)`. The rule is labelled
with the actions `Act1(~n)` and `Act2(x)`.  
The rule can be applied if there are two facts `Pre` and `Fr` in the system state whose arguments are matched by the variables `x` and `~n`. In the application of 
this rule, `~n` and `x` are instantiated with the matched values and the
state transition is labelled with the instantiations of `Act1(~n)` and
`Act2(x)`. The two instantiations are thus appended to the
*trace* and considered to have occurred at the same timepoint. 
We analyze a protocol by reasoning about actions in all of its traces.

**Tamarin's property specification language**
is a guarded fragment of a many-sorted first-order logic with a sort for
timepoints.  This logic supports quantification over both messages and
timepoints. 

The syntax for specifying security properties is defined as follows:

 *  `All`      for universal quantification, temporal variables are prefixed with #
 *  `Ex`       for existential quantification, temporal variables are prefixed with #
 *  `==>`      for implication
 *  `&`        for conjunction
 *  `|`        for disjunction
 *  `not`      for  negation

 *  `f @ i`    for action constraints, the sort prefix for the temporal variable 'i'
           is optional

 * `i < j`    for temporal ordering, the sort prefix for the temporal variables 'i'
           and 'j' is optional

 * `#i = #j`  for an equality between temporal variables 'i' and 'j'
 * `x = y`    for an equality between message variables 'x' and 'y'


All action fact symbols may be used in formulas. The terms (as
arguments of those action facts) are more limited. Terms are only
allowed to be built from quantified variables, public constants (names
delimited using single-quotes), and free function symbols including
pairing. This excludes function symbols that appear in any of the equations.
Moreover, all variables must be
guarded. The error message for an unguarded variable is currently not very
helpful. **FIXME: This sentence is currently not very helpful for the reader. 
Give an example of the error message.**

To ensure guardedness, for universally quantified variables, one has to check 
that they all occur in an action constraint right after the quantifier and that 
the outermost logical operator inside the quantifier is an implication.
For existentially quantified variables, one has to check that they all
occur in an action constraint right after the quantifier and that the
outermost logical operator inside the quantifier is a conjunction.
Note also that currently the precedence of the logical connectives is
not specified. We therefore recommend to use parentheses, when in
doubt.


To specify a property about a protocol that includes the fictitious
rule above, we use the keyword `lemma` followed by a name for the
property and a guarded first-order formula.  For instance, to express
the property that the fresh value `~n` is distinct in all applications
of the fictitious rule (or rather, if an action with the same fresh
value appears twice, it actually is the same instance, identified by
the timepoint), we write

```
lemma distinct_nonces: "All n #i #j. Act1(n)@i & Act1(n)@j ==> #i=#j"
```

### Secrecy ###

In this section we briefly explain how you can express standard
secrecy properties in Tamarin and give a short example. See [Protocol
Specification and Standard Security Properties](#sec:elsewhere) for an
in-depth discussion.

Tamarin's built-in message deduction rule
```
rule isend: 
   [ !KU(x) ]
 --[  K(x)  ]-->
   [ In(x)  ]
```
allows us to reason about the Dolev-Yao adversary's knowledge.  To
specify the property that a message `x` is secret, we propose to label a
suitable protocol rule with a `Secret` action.  We then specify a secrecy lemma that states whenever the `Secret(x)` action occurs at timepoint `i`, the adversary does not know `x`.

```
lemma secrecy:
  "All x #i. 
    Secret(x) @i ==> not (Ex #j. K(x)@j)"
```

**Example.** The following Tamarin theory specifies a simple
  one-message protocol. Agent `A` sends a message encrypted with agent
  `B`'s public key to `B`. Both agents claim secrecy of a message, but
  only agent `A`'s claim is true. To distinguish between the two
  claims we add the action facts `Role('A')` and `Role('B')` for role
  `A` and `B`, respectively and specify two secrecy lemmas, one for
  each role.

~~~~ {.tamarin include="code/secrecy-asymm.spthy"}
~~~~

### Authentication ### {#sec:message-authentication}

In this section we show how to specify a simple message authentication
property. For specifications of the properties in
Lowe's hierarchy of authentication specifications [@Lowe] see the
Section [Protocol Specification and Standard Security
Properties](#sec:elsewhere).

We specify the following *message authentication* property: If an agent `a`
believes that a message `m` was sent by an agent `b`, then `m` was
indeed sent by `b`.  To specify `a`'s belief we label an appropriate
rule in `a`'s role specification with the action `Authentic(b,m)`.
The following lemma defines the set of traces that satisfy the message
authentication property.

```
lemma message_authentication: 
	"All b m #j. Authentic(b,m) @j ==> Ex #i. Send(b,m) @i &i<j"
```


Observational Equivalence
-------------------------

All the previous properties are trace properties, i.e., properties that are 
defined on traces. For example, the definition of secrecy required that there 
is no trace where the intruder could compute the secret without having 
previously corrupted the agent.

In contrast, Observational Equivalence properties reason about two systems (for 
example two instances of a protocol), by showing that an intruder cannot 
distinguish these two systems. This can be used to express privacy-type 
properties, or cryptographic indistinguishability properties.

For example, a simple definition of privacy for voting requires that an 
adversary cannot distinguish two instances of a voting protocol where two 
voters swap votes. That is, in the first instance, voter A votes for candidate 
a and voter B votes for b, and in the second instance voter A votes for 
candidate b and voter B votes for a. If the intruder cannot tell both instances 
apart, he does not know which voter votes for which candidate, even though he 
might learn the result, i.e., that there is one vote for a and one for b.

Tamarin can prove such properties for two systems that only differ in terms 
using the `diff( , )` operator. Consider the following example, where one 
creates a public key, two fresh values `~a` and `~b`, and publishes `~a`. Then 
one encrypts either `~a` or `~b` (modeled using the `diff` operator):

~~~~ {.tamarin slice="code/ObservationalEquivalenceExample.spthy" lower=16 
upper=27}
~~~~

In this example, the intruder cannot compute `~b` as formalized by the 
following lemma:

~~~~ {.tamarin slice="code/ObservationalEquivalenceExample.spthy" lower=29 
upper=36}
~~~~

However, he can know whether in the last message `~a` or `~b` was encrypted by 
simply taking the output `~a`, encrypting it with the public key and comparing 
it to the published cyphertext. This can be captured using observational 
equivalence as follows.


Axioms
------

TODO: axioms for trace and equivalence properties with motivating example

TODO: As there are no lemmas in observational equivalence you can use axioms
to remove state space, essentially remove degenerate cases. Do note
that one can use axioms to simplify writing lemmas

## Common axioms ##

Here is a list of common axioms. Do note that you need to add the
appropriate action facts to your rules for these axioms to have
impact. 

### Unique ###

First, let us show an axiom forcing an action (with a
particular value) to be unique:

```
axiom unique:
  "All x #i #j. UniqueFact(x) @i & UniqueFact(x) @j ==> #i = #j"
```

We call the action `UniqueFact` and give it one argument. If it
appears on the trace twice, it actually is only once, as the two time
points are identified.

### Equality ###

Next, let us consider an equality axiom. This is useful if you do not
want to use pattern-matching explicitly, but maybe want to ensure that
the decryption of an encrypted value is the original value, assuming correct keys. The axiom looks like this:

```
axiom Equality:
  "All x y #i. Eq(x,y) @i ==> x = y"
```

which means that all instances of the `Eq` action on the trace have
the same value as both its arguments.


### Inequality ###

Now, let us consider an inequality axiom, which ensures that the two arguments of `Neq` are different:

```
axiom Inequality:
  "All x #i. Neq(x,x) @ i ==> F"
```

This is very useful to ensure that certain arguments are different.

### OnlyOnce ###

If you have a rule that should only be executed once, put `OnlyOnce()`
as an action fact for that rule and add this axiom:

```
axiom OnlyOnce:
  "All #i #j. OnlyOnce() & OnlyOnce()@j ==> #i = #j"
```

Then that rule can only be executed once. Note that if you have
multiple rules that all have this action fact, at most one of them can
be executed a single time.

### Less than ###

If we use the `multiset` built-in we can construct numbers as
"1+1+...+1", and have an axiom enforcing that one number is less than
another, say `LessThan`:

```
axiom LessThan:
  "All x y #i. LessThan(x,y)@i ==> Ex z. x + z = y"
```

You would then add the `LessThan` action fact to a rule where you want
to enforce that a counter has strictly increased.

Similarly you can use a `GreaterThan` where we want `x` to be strictly larger than `y`:

```
axiom GreaterThan:
  "All x y #i. GreaterThan(x,y)@i ==> Ex z. x = y + z"
```


Lemma Annotations
-----------------

Tamarin supports a number of annotations to its lemmas, which change
their meaning. Any combination of them is allowed. We explain them in
this section. The usage is that any annotation goes into square
brackets after the lemma name, i.e., for a lemma called "Name" and the
added annotations "Annotation1" and "Annotation2", this looks like so: 

```
lemma Name [Annotation1,Annotation2]:
```

### `typing`

To declare a lemma as a typing lemma, we use the annotation `typing`:

```
lemma example [typing]:
  "..."
```

This means a number of things: 

* The lemma's verification will use induction.
* The lemma will be verified using the `Untyped case distinctions`.
* The lemma will be used to generate the `Typed case distinctions`, which are used for verification of all non-`typing` lemmas.

Typing lemmas are necessary whenever the analysis reports `open
chains` in the `Untyped case distinctions`. See section on [Open
chains](007_precomputation.html#sec:openchains) for details on this.

All `typing` lemmas are used only for the case distinctions and do not
benefit from other lemmas being marked as `reuse`.


### `use_induction`

As you have seen before, the first choice in any proof is whether to
use simplification (the default) or induction. If you know that a
lemma will require induction, you just annotate it with
`use_induction`, which will make it use induction instead of simplification.


### `reuse`

A lemma marked `reuse` will be used in the proofs of all lemmas
syntactically following it (except `typing` lemmas as above). This
includes other `reuse` lemmas that can transitively depend on each
other.


### `hide_lemma=L`

It can sometimes be helpful to have lemmas that are used only for the proofs of other lemmas. For example, assume 3 lemmas, called `A`, `B`, and `C`. They appear in that order, and `A` and `B` are marked reuse. Then, during the proof of `C` both `A` and `B` are reused, but sometimes you might only want to use `B`, but the proof of `B` needs `A`. The solution then is to hide the lemma `A` in `C`:

```
lemma A [reuse]:
  ...

lemma B [reuse]:
  ...

lemma C [hide_lemma=A]:
  ...
```

This way, `C` uses `B` which in turn uses `A`, but `C` does not use `A` directly.

### `left` and `right`

In the observational equivalence mode you have two protocols, the left
instantiation of the *diff-terms* and their right instantiation. If
you want to consider a lemma only on the left or right instantiation
you annotate it with `left`, respectively `right`. If you annotate a
lemma with `[left,right]` then both lemmas get generated, just as if
you did not annotate it with either of `left` or `right`.


Protocol Specification and Standard Security Properties{#sec:elsewhere}
-------------------------------------------------------

### Secrecy ###

In this section we explain how you can express standard secrecy
properties in Tamarin and give examples.

Tamarin's built-in message deduction rule
```
rule isend: 
   [ !KU(x) ]
 --[  K(x)  ]-->
   [ In(x)  ]
```
allows us to reason about the Dolev-Yao adversary's knowledge.  To
specify the property that a message `x` is secret, we propose to label a
suitable protocol rule with a `Secret` action.  
In addition to `Secret(x)` the following
lemma references the actions `Reveal` and `Honest`. We
use `Reveal(B)` to label rules in which an agent `B` is compromised
and `Honest(B)` to mark agents that are assumed to be honest. For
this mechanism to work, `Honest(B)` must occur in the same rule as
`Secret(x)`.

```
lemma secrecy:
  "All x #i. 
    Secret(x) @i ==> 
    not (Ex #j. K(x)@j)
        | (Ex B #r. Reveal(B)@r & Honest(B) @i)"
```
The lemma states that whenever a secret action `Secret(x)` occurs at timepoint `i`, the adversary does not know `x` or an agent claimed to be honest at time point `i` has been compromised at a timepoint `r`.

A stronger secrecy property is *perfect forward secrecy*. It requires
that messages labeled with a `Secret` action before a compromise remain secret.

```
lemma secrecy_PFS:
  "All x #i. 
    Secret(x) @i ==> 
    not (Ex #j. K(x)@j)
        | (Ex B #r. Reveal(B)@r & Honest(B) @i & r < i)"
```

**Example.** The following Tamarin theory specifies a simple
  one-message protocol. Agent `A` sends a message encrypted with agent
  `B`'s public key to `B`. Both agents claim secrecy of a message, but
  only agent `A`'s claim is true. To distinguish between the two
  claims we add the action facts `Role('A')` and `Role('B')` for role
  `A` and `B`, respectively and specify two secrecy lemmas, one for
  each role.

~~~~ {.tamarin include="code/secrecy-asymm.spthy"}
~~~~

### Authentication ###

In this section we explain how to express standard authentication properties, and give examples.

#### Entity Authentication ####

We show how to formalize the entity authentication properties of
Lowe's hierarchy of authentication specifications [@Lowe] for
two-party protocols.  

All the properties defined below concern the authentication of an
agent in role `'B'` to an agent in role `'A'`.  To analyze a protocol
with respect to these properties we label an appropriate rule in role
`A` with a `Commit(a,b,<'A','B',t>)` action and in role `B` with the
`Running(b,a,<'A','B',t>)` action. Here `a` and `b` are the agent
names (public constants) of roles `A` and `B`, respectively and `t` is
a term. 


1. Aliveness

A protocol guarantees to an agent `a` in role `A`
*aliveness* of another agent `b` if, whenever `a` completes a run
of the protocol, apparently with `b` in role `B`, then `b` has
previously been running the protocol.
```
lemma aliveness:
   "All a b t #i. 
     Commit(a,b,t)@i 
     ==>  (Ex id #j. Create(b,id) @ j)
          | (Ex C #r. Reveal(C) @ r & Honest(C) @ i)"
```

2. Weak agreement

A protocol guarantees to an agent `a` in role `A` *weak agreement*
with another agent `b` if, whenever agent `a` completes a run of the
protocol, apparently with `b` in role `B`, then `b` has previously
been running the protocol, apparently with `a`.

```
lemma weak_agreement:
  "All a b t1 #i. 
    Commit(a,b,t1) @i
    ==> (Ex t2 #j. Running(b,a,t2) @j)
        | (Ex C #r. Reveal(C) @ r & Honest(C) @ i)"
```

3. Non-injective agreement

A protocol guarantees to an agent `a` in role `A`
*non-injective agreement* with an agent `b` in role `B` on a message `t`
if, whenever `a` completes a run of the protocol, apparently with `b`
in role `B`, then `b` has previously been running the protocol,
apparently with `a`, and `b` was acting in role `B` in his run, and
the two principals agreed on the message `t`. 

```
lemma noninjective_agreement:
  "All a b t #i. 
    Commit(a,b,t) @i
    ==> (Ex #j. Running(b,a,t) @j)
        | (Ex C #r. Reveal(C) @ r & Honest(C) @ i)"
```


4. Injective agreement

We next show the lemma to analyze *injective agreement*. A protocol
guarantees to an agent `a` in role `A` injective agreement with an
agent `b` in role `B` on a message `t` if, whenever `a` completes a
run of the protocol, apparently with `b` in role `B`, then `b` has
previously been running the protocol, apparently with `a`, and `b` was
acting in role `B` in his run, and the two principals agreed on the
message `t`. Additionally, there is a unique matching partner instance
for each completed run of an agent, i.e., for each `Commit` by an
agent there is a unique `Running` by the supposed partner.

```
lemma injectiveagreement:
  "All A B t #i. 
    Commit(A,B,t) @i
    ==> (Ex #j. Running(B,A,t) @j 
        & j < i
        & not (Ex A2 B2 #i2. Commit(A2,B2,t) @i2
                           & not (#i2 = #i)))
              | (Ex C #r. Reveal(C)@r & Honest(C) @i)"
```

TODO: This completes the standard lemmas for secrecy and authentication - Cas: do you agree?


