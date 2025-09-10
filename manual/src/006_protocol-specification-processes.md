Model Specification using Processes {#sec:model-specification-proc}
===================

In this section, we provide an informal description of the process calculus now
integrated in tamarin. It is called **SAPIC+**, which stands for "Stateful Applied
PI-Calculus" (plus) and is described in the following papers:

- [@KK-jcs16] introduced the original version of SAPIC and its translation
      to multiset rewrite rules and axioms.

- [@BaDrKr-2016-liveness] added non-deterministic choice, reliable channels
      and [local progress](#sec:local-progress) to it.

- [@jacomme2017symbolic] added support for [isolated execution environments](#sec:iee).

- [@sapicplus] extended SAPIC to SAPIC+, introducing the new syntax
  that we will introduce in the followup and [translations to various tools](#sec:translation).

A Protocol can be modelled in terms of rules or as a (single) process. The
process is translated into a set of rules that adhere to the semantics of the
process calculus.  It is even possible to mix a process declaration and a set
of rules, although this is not recommended, as the interactions between the
rules and the process depend on how precisely this translation is defined.

Processes{#sec:proc}
-----

A SAPIC+ process is described using the grammar we will introduce and
illustrate by example in the followup. Throughout, let
`n` stand for a fresh name,
`x` for a variable,
`t`, `t1` or `t2` for terms
and
`F` for a fact and `cond` for a conditional, which is either a comparisson `t1=t2`
or a custom
[predicate](007_property-specification.html#sec:predicates).

### Standard applied-pi features

The main ingredients for modelling protocols are network communication and
parallelism. We start with the network communication and other constructs that
model local operation and call this simpler form of a process, *elementary
processes*:
```
<P,Q> :: =  (elementary processes)
    new n; P                .. binding of a fresh name
  | out(t1,t2); P           .. output of t2 on a channel t1
  | out(t); P               .. output of t on the public channel
  | in(t,x);~P              .. input on channel t binding input term to $x$}
  | in(x);~P                .. input on the public channel binding to $x$}
  | if cond then P else Q   .. conditional
  | let t1 = t2 in P else Q .. let binding
  | P | Q                   .. parallel composition
  | 0                       .. null process
```

The construct `new a;P` binds the fresh name `a` in `P`. Similar to the fact
`Fr(a)`, it models the generation of a fresh, random value.

The processes `out(t1,t2); P` represent the output of a message `t2` on
a channel `t1`, whereas `in(t,x); P` represents a process waiting to bind some
input on channel `t` to the variable `x`.  (Previous versions of SAPIC
performed pattern matching. Instead, the `let` construct offers support for
pattern matching and, similar to the applied pi calculus [@AF-popl01], we bind
to a variable.

If the channel is left out, the public channel `'c'` is assumed, which is the
case in the majority of our examples. This is exactly what the facts `In(x)` and
`Out(t)` represent.

**Example.** This process picks an encryption key, waits for an input and encrypts it.
```
new k; in(m); out(senc(m,k))
```

Processes can also branch:
`if cond then P else Q` will execute either `P` or `Q`, depending on whether `cond` holds.
Most frequently, this is the equality check of
form `t1 = t2`, but you can also define
[a predicate](007_property-specification.html#sec:predicates) using Tamarin's
security property syntax.

`Let`-bindings are allowed to faciliate writing processes
where a term occur several times (possibly as a subterm) within the process
rule and to apply destructors. Destructor are function symbols declared as
such, e.g.:
```
functions: adec/2[destructor], aenc/2
equations:
    adec(aenc(x.1, pk(x.2)), x.2) = x.1
```
declares a destructor `adec`. In contrast to the encryption (represented by
`aenc`), the decryption may fail, e.g., the term `adec(aenc(m,pk(sk)),sk')` is
not representing a valid message. A destructor symbol allows to represent this
failure. Destructors may only appear in `let`-patterns (i.e., to the right of
`=`). If one of the destructors in a let pattern fails, the process moves into the else branch, e.g.,
```
new sk; new sk'; let x=adec(aenc(m,pk(sk)),sk') in P else Q
```
always moves into `Q`. Destructors cannot appear elsewhere in the process.

Furthermore, `let`-bindings permit pattern matching. This is very useful for
deconstructing messages. E.g.:
```
in(x); let <'pair',y,z> = x in out(z); out(z)
```
To avoid user errors, pattern matchings are explicit in which variables they
bind and which they compare for equality, e.g.,
`let <y,=z>=x in ..` checks if `x` is a pair and if the second element equals `z`; then it binds the first element to x.
(Note: previous versions of Tamarin/SAPIC considered let-bindings as syntactic
sugar adhering to the same rules as [let-bindings in rules](#sec:let-rules).
Now `let` is a first-class primitive. )

The types of processes so far consists of actions that are separated with a semicolon `;` and are terminated with
`0`, which is called the terminal process or null process. This is a process that does nothing.
It is allowed to omit trailing `0` processes and `else`-branches that consist of a `0` process.

We can now come to the operations modelling parallelism.
`P | Q` is the parallel execution of processes
P and Q. This is used, e.g., to model two participants in a protocol.

`P+Q` denotes external non-deterministic choice, which can be used to model
alternatives. In that sense, it is closer to a condition rather than two
processes running in parallel: `P+Q` reduces to
*either* `P'` or `Q'`, the follow-up processes or `P` or `Q` respectively.

Now we come to *extended processes*, that include standard processes, but also
events and replications.
```
<P> :==    (extended processes)
  | event F; P  .. event   
  | !P .. replication
```

The `event` construct is similar to actions in rules. In fact, it will be translated
to actions. Like in rules, events  annotate parts of the processes and are
useful for stating security properties. Each of these constructs can be thought
of as "local" computations.


`!P` is the replication of P, which allows an unbounded number of sessions in
protocol executions. It can be thought of to be an infinite number of processes
`P | .. | P` running in parallel. If `P` describes a webserver answering
a single query, then `!P` is the webserver answering queries indefinitely.

### Manipulation of global state

The SAPIC+ calculus is a dialect of the applied-pi calculus with additional
features for storing, retrieving and modifying global state. *Stateful process*
include extended processes and, in addition, the remaining constructs that are
used to manipulate global state.

```
<P,Q> :==        (stateful processes)
  | insert t1, t2; P .. set state t1 to t2
  | delete t; P  .. delete state t
  | lookup t as x in P else Q ; P  .. read state t into variable x
  | lock t; P .. set lock on t
  | unlock t; P .. remove lock on t
```

The construct `insert t1,t2; P` binds the value `t2` to the key `t1`. Successive
  inserts overwrite this binding. The store is global, but as `t1` is a term, it
  can be used to define name spaces. E.g., if a webserver is identified by
  a name `w_id`, then it could prefix it's store as follows:
  `insert <'webservers',w_id,'store'>, data; P`.

The construct `delete t; P` ‘undefines’ the binding.

The construct `lookup t as x in P else Q` allows for retrieving the value
associated to `t` and binds it to the variable `x` when entering `P`. If the
mapping is undefined for `t`, the process behaves as `Q`.

The `lock` and `unlock` constructs are used to gain or waive exclusive access
to a resource `t`, in the style of Dijkstra’s binary semaphores: if a term `t`
has been locked, any subsequent attempt to lock `t` will be blocked until `t`
has been unlocked. This is essential for writing protocols where parallel
processes may read and update a common memory.

### Inline multiset-rewrite rules

There is a hidden feature for experts: inline multiset-rewrite rules:  `[l]
--[a]-> r; P` is a valid process. Embedded rules apply if their preconditions
apply (i.e., the facts on the left-hand-side are present) **and** the process
is reduced up to this rule.  If the rule applies in the current state, the
process reduces to `P`.  We advice to avoid these rules whenever possible, as
they run counter to the aim of SAPIC: to provide clear, provably correct
high-level abstractions for the modelling of protocols.
Note also that the state-manipulation constructs `lookup x as v`, `insert x,y`
and `delete x` manage state by emitting actions `IsIn(x,y')`, `Insert(x,y)` and
`Delete(x)` and enforcing their proper semantics via restrictions. For example:
an action `IsIn(x,y)`, which expresses a succesful lookup, requires that
an action `Insert(x,y)` has occurred previously, and in between, no other
`Insert(x,y')` or `Delete(x)` action has changed the global store at the position `x`. Hence,
the global store is distinct from the set of facts in the current state.

### Enforcing local progress (optional) {#sec:local-progress}

The translation from processes can be modified so it enforces a different
semantics. In this semantics, the set of traces consists of only those where
a process has been reduced **as far as possible**. A process can reduce unless
it is waiting for some input, it is under replication, or unless it is already
reduced up to the 0-process.

```
options: translation-progress
```

This can be used to model time-outs. The following process must reduce to either `P` or `out('help');0`:

```
( in(x); P) + (out('help');0)
```
If the input message received, it will produce regulary, in this example: with
`P`. If the input is not received, there is no other way to progress except for
the right-hand side. But progress it must, so the right-hand side can model
a recovery protocol.

In the translated rules, events
`ProgressFrom_p` and `ProgressTo_p` are added. Here `p` marks a position that,
one reached, requires the corresponding `ProgressTo` event to appear. This is
enforced by restrictions. Note that a process may need to process to more than one position, e.g.,

```
new a; (new b; 0 | new c; 0)
```
progresses to both trailing 0-processes.

It may also process to one out of many positions, e.g., here
```
in(x); if x='a' then 0 else 0
```
More details can be found in the corrsponding paper [@BaDrKr-2016-liveness].
Note that local progress by itself does not guarantee that messages arrive.
Recovery protocols often rely on a trusted third party, which is possibly
offline most of time, but can be reached using [the builtin theory for reliable channels](004_cryptographic-messages.html#sec:builtin-theories).


### Modeling Isolated Execution Environments {#sec:iee}

IEEs, or enclaves, allow to run code inside a secure environment and to provide
a certificate of the current state (including the executed program) of the
enclave. A localized version of the applied pi-calculus, defined in
[@jacomme2017symbolic] and included in SAPIC, allows to model such environments.

Processes can be given a unique identifier, which we call location:
```
let A = (...)@loc
```
Locations can be any term (which may depend on previous inputs). A location
is an identifier which allows to talk about its process.
Inside a location, a report over some value can be produced:
```
(...
let x=report(m) in
   ...)@loc
```
Some external user can then verify that some value has been produced at a
specific location, i.e produced by a specific process or program, by using the
`check_rep` function:
```
if input=check_rep(rep,loc) then
```
This will be valid only if `rep` has been produced by the previous instruction,
with `m=input`.

An important point about enclaves is that any user, e.g an attacker, can use enclaves,
and thus produce reports for its own processes or locations. But if the attacker can
produce a report for any location, he can break all security properties associated to
it. To this end, the user can define a set of untrusted locations, which amounts to defining
a set of processes that he does not trust, by defining a builtin `Report` predicate:
```
predicates:
Report(x,y) <=> phi(x,y)
```
The attacker can then produce any `report(m)@loc` if `phi(m,loc)` is true.

More details can be found in the corresponding paper [@jacomme2017symbolic], and the examples.

## Process declarations using `let`

It is advisable to structure processes around the protocol roles they
represent. These can be declared using the let construct:

```
let Webserver (identity) = in(<'Get',identity..>); ..

let Webbrowser () = ..

(! new identity !Webserver(identity)) | ! Webbroser
```

These can be nested, i.e., this is valid:

```
let A() = ..
let B() = A() | A()
!B()
```

## Typing

It is possible to declare types to avoid potential user errors. This does
not affect the attacker, as these types are disregarded after translation into
multiset-rewrite rues.

Types can be declared for function symbols:
```spthy
functions: f(bitstring):bitstring, g(lol):lol,
            h/1 // will implicitely typed later.
```
for processes:
```
new x:lol;                             // x is of type lol now
new y;                                 // y's type will be inferred
out(f(y));                             // now y must be type bitstring ...
// out(f(x));                          // fails: f expects bitstring
out(<x,y>); out(x + y); out(f(<x,y>)); // lists and AC operators are type-transparent
out(h(h(x)));                          // implictely types h as lol->lol
// out(f(h(x)));                       // fails: as h goes to lol and f wants bitstring
```
and subprocesses:
```
let P(a:lol) =
```

Export features{#sec:translation}
-----

It is possible to export processes defined in .spthy files into the formats
used by other protocol verifiers, making it possible to switch between tools.
One can even translate lemmas in one tool to assumptions in other to combine
these results. The correctness of the translation is proven in [@sapicplus].

The `-m` flag selects an output module:
```
 -m --output-module[=spthy|spthytyped|msr|proverif|deepsec]
``` 

The following outputs are supported:

- *spthy:* parse .spthy file and output
- *spthytyped* - parse and type .spthy file ad output
- *msr* - parse and type .spthy file and translate processes to multiset-rewrite rules
- *proverif*: - translate to the
  [ProVerif](https://bblanche.gitlabpages.inria.fr/proverif/) input format. 
  The translation of lookups/inserts relies on features that are not yet
  available in ProVerif (at the time of writing) and require preprocessing 
  with [GSVerif's protocol platform branch](https://gitlab.inria.fr/chevalvi/gsverif/-/tree/protocol_platform?ref_type=heads).
- *proverifequiv*: - same as `proverif`, but specifically for the translation
  of equivalence properties aka privacy properties aka ProVerif's `diff` mode.
- *deepsec*: - translate to [Deepsec](https://deepsec-prover.github.io/)'s input format

## Lemma selection

The same spthy file may be used with multiple tools as backend. To list the
tools that a lemma should be exported to, use the `output` attribute:
```
lemma secrecy[reuse, output=[proverif,msr]]:
```
Lemmas are omitted when the currently selected output module is not in that
list.

## Exporting queries

Security properties are automatically translated, if it is possible. (ProVerif
only supports two quantifier alternations, for example.) As, e.g., DeepSec,
supports queries that are not expressible in Tamarin's language, it is possible
to define blocks that are covered on export. They are written as:
```
export IDENTIFIER:
"
    text to export
"
```
where IDENTIFIER is one of the following:

- `requests`: is included in the requests the target solver tries to prove. E.g.:

    ```
    export requests:
    "
    let sys1 = new sk; (!^3 (new skP; P(sk,skP)) | !^3 S(sk)).

    let sys2 = new sk; ( ( new skP; !^3 P(sk,skP)) | !^3 S(sk)).

    query session_equiv(sys1,sys2).
    "
    ```

## Smart export features

- Some predicates / conditions appear in `if .. ` processes have [dedicates
      translations](007_property-specification.html#sec:predicates-special).


## Natural numbers

SAPIC supports the usage of the builtin natural numbers of both GSVerif and Tamarin.

To use them, variables must be declared with the `nat` type, and the corresponding builtin must be declared:
```
builtins: natural-numbers

process:

in(ctr0:nat);
let ctr1:nat = ctr0 %+ %1 in
out(ctr1)
```

The subterm operator `<<` will be translated for GSVerif as `<`.

Beware, declaring a nat variable in SAPIC does not instantiate a nat
Tamarin variable, which may create additional possible sources. To
declare and use a true Tamarin nat variable, similar to fresh
variables and other, each occurence of the variable must be prefixed
with `%` (or `~` in the case of fresh variables):
```
builtins: natural-numbers

process:

in(%ctr0:nat);
let ctr1:nat = %ctr0 %+ %1 in
out(ctr1)
```


This may however lead to divergence in Tamarin and Proverif threat models.


## Options

Some options allow altering the behaviour of the translation, but can
leat to divergence between Tamarin and Proverif. They should be used
with care.  Adding an option is performed in the headers of the file,
with:

```
options: opt1, opt2, ...
```

The available options are:

 * `translation-state-optimisation`: this enables the pure state
   translation described in the SAPIC+ paper. Both the original and
   the optimized version do not always yield the same benefit, hence
   the optional switch.
 * `translation-compress-events`: by default, each event is translated
   in a singular rule. This may create a Tamarin slowdown when
   translating a sequence of events, but is due to the fact that in
   Proverif, multiple events always occur at distinct timestampe. This
   option allows compressing events into a single rule.
 * `translation-progress`: see above.
