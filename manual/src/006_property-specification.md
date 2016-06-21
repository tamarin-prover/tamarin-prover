Property Specification{#sec:property_specification}
======================

Trace Properties
----------------

**FIXME: what are trace properties**

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
`Act2(x)`. The two instantiations are thus appeneded to the
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


**FIXME:** Note that apart from public names (delimited using single-quotes), no terms may occur in guarded trace properties. (Terms in guarded trace properties may be built from variables, public names, pairs, and free function symbols.)
**END-FIXME**
Moreover, all variables must be
guarded. The error message for an unguarded variable is currently not very
good.

For universally quantified variables, one has to check that they all
occur in an action constraint right after the quantifier and that the
outermost logical operator inside the quantifier is an implication.
For existentially quantified variables, one has to check that they all
occur in an action constraint right after the quantifier and that the
outermost logical operator inside the quantifier is a conjunction.
Note also that currently the precedence of the logical connectives is
not specified. We therefore recommend to use parentheses, when in
doubt.


To specify a property about a protocol that includes the fictitious
rule above, we use the keyword `lemma` followed by a name for the
property and a guarded first-order formula.
For instance, to express the property that the fresh constant `~n` is
distinct in all applications of the fictitious rule, we write

```
lemma distinct_nonces: "All n #i #j. Act1(n)@i & Act1(n)@j ==> #i=#j"
```


### Secrecy ###

How to express standard secrecy properties in Tamarin, examples

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
  claims we use two different secrecy action facts, `Secret_A` for
  agent `A` and `Secret_B` for agent `B`, and we specify two secrecy lemmas, 
  one for each of the two actions.

~~~~ {.tamarin include="code/secrecy-asymm.spthy"}
~~~~

### Authentication ###

How to express standard authentication properties, examples

#### Entity Authentication ####

We propose the following lemmas to formalize the entity authentication
properties from Lowe's hierarchy of authentication specifications
[@Lowe].

1. Aliveness

A protocol guarantees to an agent `a` in role `A`
*aliveness* of another agent `b` if, whenever `a` completes a run
of the protocol, apparently with `b` in role `B`, then `b` has
previously been running the protocol.

2. Non-injective (weak) agreement

A protocol guarantees to an agent `a` in role `A` *weak agreement*
with another agent `b` if, whenever agent `a` completes a run of the
protocol, apparently with `b` in role `B`, then `b` has previously
been running the protocol, apparently with `a`.

To analyze a protocol with respect to the weak agreement property we label the
appropriate rule in role `A` with the `Commit(a,b,<'A','B'>)` action
and in role `B` with the `Running(b,a,<'A','B'>)` action.
```
lemma noninjectiveagreement:
  "All a b t #i. 
    Commit(a,b,t) @i
    ==> (Ex #j. Running(b,a,t) @j)
        | (Ex C #r. Reveal(C)@r & Honest(C) @i)"
```

We can use the same lemma to analyze the *non-injective agreement*
property.  A protocol guarantees to an agent `a` in role `A`
non-injective agreement with an agent `b` in role `B` on a message `M`
if, whenever `a` completes a run of the protocol, apparently with `b`
in role `B`, then `b` has previously been running the protocol,
apparently with `a`, and `b` was acting in role `B` in his run, and
the two principals agreed on the message `M`.


3. Injective agreement

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

#### Message Authentication ####



TODO:
  * A standard package of lemmas .e.g Secrecy and so on? 
    **NOTE** feature request; also very model-specific.


Observational Equivalence
-------------------------

TODO: difference to trace properties, examples

Axioms
------

TODO: axioms for trace and equivalence properties with motivating example

TODO: As there are no lemmas in observational equivalence you can use axioms
to remove state space, essentially remove degenerate cases. Do note
that one can use axioms to simplify writing lemmas



## Example axioms ##

Here is a list of example axioms. Do note that you need to add the
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

