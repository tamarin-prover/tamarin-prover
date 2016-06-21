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
suitable protocol rule with a `Secret` action.  In the following
lemma, the `Secret` action contains two arguments. The first argument
`A` is the agent in whose role the secrecy claim is made and the
second argument `x` is the message that is claimed to be secret.
Moreover, the lemma references the actions `Reveal` and `Honest`. We
use `Reveal(B)` to label rules in which an agent `B` is compromised
and `Honest(B)` to indicate agents that are assumed to be honest. For
this mechanism to work, `Honest(B)` must occur in the same rule as
`Secret(A,x)`.
```
lemma secrecy:
  "All A x #i. 
    Secret(A,x) @i ==> 
    not (Ex #j. K(x)@j)
        | (Ex B #r. Reveal(B)@r & Honest(B) @i)"
```

A stronger secrecy property is *perfect forward secrecy*. It requires
that messages labeled with a `Secret` action before a compromise remain secret.

```
lemma secrecy_PFS:
  "All A x #i. 
    Secret(A,x) @i ==> 
    not (Ex #j. K(x)@j)
        | (Ex X #r. Reveal(X)@r & Honest(X) @i & r < i)"
```

**Example.** The following Tamarin theory specifies a simple
  one-message protocol. Agent `A` sends a message encrypted with agent
  `B`'s public key to `B`. Both agents claim secrecy of a message, but
  only agent `A`'s claim is true. To distinguish between the two claims
  we specify two lemmas and differentiate between two secret actions, 
  `Secret_A` for agent `A` and `Secret_B` for agent `B`.

~~~~ {.tamarin include="code/secrecy-asymm.spthy"}
~~~~

### Authentication ###

How to express standard authentication properties, examples


```
lemma noninjectiveagreement:
  "All a b t #i. 
    Commit(a,b,t) @i
    ==> (Ex #j. Running(b,a,t) @j)
        | (Ex X #r. Reveal(X)@r & Honest(X) @i)"
```

```
lemma injectiveagreement:
  "All a b t #i. 
    Commit(a,b,t) @i
    ==> (Ex #j. Running(b,a,t) @j 
        & j < i
        & not (Ex a2 b2 #i2. Commit(a2,b2,t) @i2
                           & not (#i2 = #i)))
              | (Ex X #r. Reveal(X)@r & Honest(X) @i)"
```


TODO:
  * A standard package of lemmas .e.g Secrecy and so on? 
    **NOTE** feature request; also very model-specific.


Observational Equivalence
-------------------------

difference to trace properties, examples

Axioms
------
axioms for trace and equivalence properties with motivating example

As there are no lemmas in observational equivalence you can use axioms to remove state space, essentially remove degenerate cases. Do note that one can use axioms to simplify writing lemmas

TODO:
  * A standard package of axioms e.g. Unique, Eq, Neq, and so on. 
    **NOTE** Cas: perhaps this is more like a feature request?




Lemma Annotations
-----------------


TODO:

  * A complete list of the things that can annotate lemmas and what they do
    [use_induction,reuse,typing,hide_lemma=LEMMANAME] -- in observational equivalence: [left,right]

      * Typing lemmas in particular - how to tell when one would help, the
        best way to write one, and what you can’t prove in a typing lemma
