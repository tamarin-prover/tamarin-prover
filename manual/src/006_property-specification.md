Property Specification{#sec:property_specification}
======================

Trace Properties
----------------

Guarded FOL fragment, what are trace properties

We reason about a protocol's behaviour by annotating the protocol
rules with *action facts*.  Tamarin's property specification language
is a fragment of a many-sorted first-order logic with a sort for
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


Note that apart from public names (delimited using single-quotes), no terms
may occur in guarded trace properties. Moreover, all variables must be
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

For instance, consider the following fictitious rule 
```
rule fictitious:
   [ Pre(x), Fr(~n) ]
 --[ Act1(~n), Act2(x) ]-->
   [ Out(<x,~n>) ]
```

The rule rewrites the system state by consuming the facts `Pre(x)` and
`Fr(~n)` and producing the fact `Out(<x,~n>)`. The rule is labelled
with the actions `Act1(~n)` and `Act2(x)`.  When this rule is
executed, `~n` and `x` are instantiated with concrete values and the
state transition is labelled with the instantiations of `Act1(~n)` and
`Act2(x)`, i.e., the two instantiations are appeneded to the
*trace*. The two actions have identical timepoints. 
For more details see Section 3.1.2. of [@benediktthesis].

To specify a property about a protocol that includes the fictitious
rule above, we use the keyword `lemma` followed by a name for the
property and a guarded first-order formula.

For instance, to express the property that the fresh constant `~n` is
distinct in all applications of the fictitious rule (a trivial fact, since this is guaranteed by the fresh rule), we write

```
lemma "All n #i #j. Act1(n)@i & Act1(n)@j ==> #i=#j"
```


### Secrecy ###

How to express standard secrecy properties in Tamarin, examples

Tamarin's built-in message deduction rule
```
rule isend: 
   [ !KU(x) ]
 --[ K(x) ]-->
   [ In(x) ]
```
allows us to reason about the Dolev-Yao adversary's knowledge.


```
lemma secrecy:
  "All A x #i. 
    Secret(A,x) @i ==> 
    not (Ex #j. K(x)@j)
        | (Ex X #r. Reveal(X)@r & Honest(X) @i)"
```

```
lemma secrecy_PFS:
  "All A x #i. 
    Secret(A,x) @i ==> 
    not (Ex #j. K(x)@j)
        | (Ex X #r. Reveal(X)@r & Honest(X) @i & r < i)"
```

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
    Commit(a,b,<'I','R',t>) @i
    ==> (Ex #j. Running(b,a,t) @j 
        & j < i
        & not (Ex a2 b2 #i2. Commit(a2,b2,t) @i2
                           & not (#i2 = #i)))
              | (Ex X #r. Reveal(X)@r & Honest(X) @i)"
```

Observational Equivalence
-------------------------

difference to trace properties, examples

Axioms
------
axioms for trace and equivalence properties with motivating example

As there are no lemmas in observational equivalence you can use axioms to remove state space, essentially remove degenerate cases. Do note that one can use axioms to simplify writing lemmas

