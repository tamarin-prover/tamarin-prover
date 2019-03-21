
Model Specification using Processes {#sec:model-specification-proc} 
===================

In this section, we provide an informal description of the process calculus now
integrated in tamarin. It is called SAPIC, which stands for "Stateful APlied
PI-calculus".
The full details of this model can be found
in [@KK-jcs16] and [@BaDrKr-2016-liveness].


Protocol can be modelled in terms of rules or as a (single) process. The
process is translated into a set of rules that adhere to the semantics of the
process calculus.  It is even possible to mix a process declaration and a set
of rules, although this is not recommended, as the interaction between the
rules and the process depend on how precisely this translation is defined.

Processes{#sec:proc}
-----

![Syntax of SAPIC, where a is a fresh name, x a variable, m and n terms,
F a fact and P a predicate.](../images/sapic-overview.png)\

The SAPIC calculus is a dialect of the applied-pi calculus with additional
features for storing, reading and modifying global state. 

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
`if Pred then P else Q` will execute `P` or `Q`, depending on whether `Pred` holds.
As of now, only the equality check is implemented, hence Pred always has the
form `t = t'` for terms `t` and `t'`.

The construct `new a;P` binds the fresh name a in `P`. Similar to the fact
`Fr(a)`, it models the generation of a fresh, random value.

The `event` construct is similar to actions in rules, in fact, it is translated
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
alternatives. In that sense, it is closer to a conditional than to two
processes running in parallel: `P+Q` reduces to 
*either* `P'` or `Q'`, the folow-up processes or `P` or `Q` respectively.


### Manipulation of global state

The remaining constructs are used to manipulate state. 

- The construct `insert m,n; P` binds the value `n` to a key `m`. Successive
  inserts overwrite this binding. The store is global, but as `m` is a term, it
  can be used to define name space. E.g., if a webserver is identified by
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
--[a]-> r; P` is a valid process, which reduces to `P` if the rule applies in
the current state. We advice for the use 

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

