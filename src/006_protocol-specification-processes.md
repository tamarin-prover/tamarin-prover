
Model Specification using Processes {#sec:model-specification-proc}
===================

In this section, we provide an informal description of the process calculus now
integrated in tamarin. It is called SAPIC, which stands for "Stateful Applied
PI-Calculus".
The full details of this model can be found
in [@KK-jcs16] and [@BaDrKr-2016-liveness].


A Protocol can be modelled in terms of rules or as a (single) process. The
process is translated into a set of rules that adhere to the semantics of the
process calculus.  It is even possible to mix a process declaration and a set
of rules, although this is not recommended, as the interactions between the
rules and the process depend on how precisely this translation is defined.

Processes{#sec:proc}
-----

![Syntax of SAPIC, where a is a fresh name, x a variable, m and n terms,
F a fact and P a predicate.](../images/sapic-overview.png)\

The SAPIC calculus is a dialect of the applied-pi calculus with additional
features for storing, retrieving and modifying global state.

### Standard applied-pi features

The main ingredients for modelling protocols are network communication and
parallelism. We start with the network communication and other constructs that
model local operation.

The processes `out(m,n); P` and `in(m,n); P` represent the output, respectively
input, of message `n` on channel `m`. As opposed to the applied pi calculus
[@AF-popl01], SAPiC's input construct performs pattern matching instead of
variable binding.

<!--
TODO example here
-->

If the channel is left out, the public channel `'c'` is assumed, which is the
case in the majority of our examples. This is exactly what the facts `In(m)` and
`Out(m)` represent. Processes can also branch:
`if Pred then P else Q` will execute either `P` or `Q`, depending on whether `Pred` holds.
As of now, only the equality check is implemented, hence Pred always has the
form `t = t'` for terms `t` and `t'`.

The construct `new a;P` binds the fresh name `a` in `P`. Similar to the fact
`Fr(a)`, it models the generation of a fresh, random value.

The `event` construct is similar to actions in rules. In fact, it will be translated
to actions. Like in rules, events  annotate parts of the processes and are
useful for stating security properties. Each of these constructs can be thought
of as "local" computations. They are separated with a semicolon `;` and are terminated with
`0`,  the terminal process or null process. This is a process that does nothing.
It is allowed to omit trailing `0` processes and `else`-branches that consist of a `0` process.

We can now come to the operations modelling parallelism.
`P | Q` is the parallel execution of processes
P and Q. This is used, e.g., to model two participants in a protocol.

`!P` is the replication of P, which allows an unbounded number of sessions in
protocol executions. It can be thought of to be an infinite number of processes
`P | .. | P` running in parallel. If `P` describes a webserver answering
a single query, then `!P` is the webserver answering queries indefinitely.
`P+Q` denotes external non-deterministic choice, which can be used to model
alternatives. In that sense, it is closer to a condition rather than two
processes running in parallel: `P+Q` reduces to
*either* `P'` or `Q'`, the follow-up processes or `P` or `Q` respectively.


### Manipulation of global state

The remaining constructs are used to manipulate global state.

- The construct `insert m,n; P` binds the value `n` to the key `m`. Successive
  inserts overwrite this binding. The store is global, but as `m` is a term, it
  can be used to define name spaces. E.g., if a webserver is identified by
  a name `w_id`, then it could prefix it's store as follows:
  `insert <'webservers',w_id,'store'>, data; P`.
- The construct `delete m; P` ‘undefines’ the binding.
- The construct `lookup m as x in P else Q` allows for retrieving the value associated to `m` and binds it to the variable `x` if entering `P`. If the mapping is undefined for `m`, the process behaves as `Q`.
- The `lock` and `unlock` constructs are used to gain or waive exclusive access
  to a resource `m`, in the style of Dijkstra’s binary semaphores: if a term
  `m` has been locked, any subsequent attempt to lock `m` will be blocked until
  `m` has been unlocked. This is essential for writing protocols where parallel
  processes may read and update a common memory.

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


### Modeling Isolated Execution Environments

IEEs, or enclaves, allow to run code inside a secure environment and to provide
a certificate of the current state (including the executed program) of the
enclave. A localized version of the applied pi-calculus, defined in
[@JKS-eurosp17] and included in SAPIC, allows to model such environments.

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

More details can be found in the corresponding paper [@JKS-eurosp17], and the examples.

## Syntactic sugar

### Process declarations using `let`

It is advisable to structure processes around the protocol roles they
represent. These can be declared using the let construct:

```
let Webserver = in(<'Get',identity..>); ..

let Webbrowser = ..

(! new identity !Webserver) | ! Webbroser
```

These can be nested, i.e., this is valid:

```
let A = ..
let B = A | A
!B
```

Other process calculi, e.g., ProVerif's dialect of the applied-pi calculus,
only allow variables in inputs. While it is sometimes clearer to write
a pattern in a letblock, it may confuse users that expect the `in` construct to bind a variable:
```
let pat_m1 = <x,y> in
in(pat_m1)
```
To avoid unexpected behaviour, we allow a let-expression to apply to
a single-variable term in an `in` only if the variable is prefixed with `pat_`,
as in the above example.


### Using 'let' binding in processes

Similar to rules, `let`-bindings are allowed to faciliate writing processes
where a term occur several times (possibly as a subterm) within the process
rule. The bindings can even be nested:
```
let foo1 = h(bar)
    foo2 = <'bars', foo1>
    ...
    var5 = pk(~x)
		in
		in(<'test',y>); let response = <foo2,y> in out(response)
```
Let-bindings in processes adhere to the same rules as [let-bindings in
rules](#sec:let-rules).
