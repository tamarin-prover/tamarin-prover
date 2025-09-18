
Initial Example {#initial-example}
===============

We will start with a simple example of a protocol that consists of just two
messages, written here in so-called Alice-and-Bob notation:

    C -> S: aenc(k, pkS)
    C <- S: h(k)

In this protocol, a client `C` generates a fresh symmetric key `k`, encrypts it
with the public key `pkS` of a server `S` (`aenc` stands for *asymmetric
encryption*), and sends it to `S`. The server confirms the key's receipt by
sending the hash of the key back to the client.

This simple protocol is artificial and satisfies only very weak security
guarantees.  We will use it to illustrate the general Tamarin workflow by
proving that, from the client's perspective, the freshly generated key is secret
provided that the server is not compromised. By default, the adversary is a
Dolev-Yao adversary that controls the network and can delete, inject, modify and
intercept messages on the network.

The protocol's Tamarin model and its security properties are given in 
the file [FirstExample.spthy](../code/FirstExample.spthy) (`.spthy` stands for 
*security protocol theory*), which can be found in the folder `manual/code` of the main repository (<https://github.com/tamarin-prover/tamarin-prover>). The Tamarin file starts with `theory` followed by 
the theory's name, here `FirstExample`.  

~~~~ {.tamarin slice="code/FirstExample.spthy" lower=12 upper=13}
~~~~

After the keyword `begin`, we first declare the cryptographic primitives the 
protocol uses. Afterward, we declare multiset rewriting rules that model
the protocol, and finally we write the properties to be proven (called
*lemmas* within the Tamarin framework), which specify the protocol's desired
security properties.  Note that we have also inserted comments to structure the
theory.

We next explain in detail the protocol model.

Cryptographic primitives
------------------------

We are working in a symbolic model of security protocols.  This means
that we model messages as terms, built from functions that satisfy
an underlying equational theory describing their properties. This will be 
explained in detail in the part on [Cryptographic 
Messages](004_cryptographic-messages.html#sec:cryptographic-messages).

In this example, we use Tamarin's built-in functions for hashing and 
asymmetric-encryption, declared in the following line:

~~~~ {.tamarin slice="code/FirstExample.spthy" lower=15 upper=15}
~~~~

These built-ins give us

  * a unary function `h`, denoting a cryptographic hash function
  * a binary function `aenc` denoting the asymmetric encryption algorithm,
  * a binary function `adec` denoting the asymmetric decryption algorithm, and
  * a unary function `pk` denoting the public key corresponding to a private 
  key.

Moreover the built-in also specifies that the decryption of the ciphertext 
using the correct private key returns the initial plaintext, i.e., 
`adec(aenc(m, pk(sk)), sk)` is reduced to `m`.


Modeling a Public Key Infrastructure
------------------------------------

In Tamarin, the protocol and its environment are modeled using *multiset
rewriting rules*. The rules operate on the system's state, which is expressed as
a multiset (i.e., a bag) of facts. Facts can be seen as predicates storing state
information.  For example, the fact `Out(h(k))` models that the protocol sent
out the message `h(k)` on the public channel, and the fact `In(x)` models that
the protocol receives the message `x` on the public channel. ^[When using the
default Tamarin setup, there is only one public channel modeling the network
controlled by the adversary, i.e., the adversary receives all messages from the
`Out( )` facts, and generates the protocol's inputs in the `In( )` facts.
Private channels can be added if required, see [Channel
Models](010_advanced-features.html#sec:channel-models) for details.]

The example starts with the model of a public key infrastructure (PKI). Again, 
we use facts to store information about the state given by their arguments. The rules 
have a premise and a conclusion, separated by the arrow symbol `-->`. Executing the 
rule requires that all facts in the premise are present in the current state 
and, as a result of the execution, the facts in the conclusion will be added to 
the state, while the premises are removed. Now consider the first rule, 
modeling the registration of a public key:

~~~~ {.tamarin slice="code/FirstExample.spthy" lower=18 upper=21}
~~~~

Here the only premise is an instance of the `Fr` fact. The `Fr` fact is
a built-in fact that denotes a freshly generated name. This mechanism is used to
model random numbers such as nonces or keys (see [Model
Specification](005_protocol-specification-rules.html#sec:model-specification) for
details).

In Tamarin, the sort of a variable is expressed using prefixes:

 *    `~x`  denotes  `x:fresh`
 *    `$x`  denotes  `x:pub`
 *    `%x`  denotes  `x:nat`
 *    `#i`  denotes  `i:temporal`
 *    `m`   denotes  `m:msg`

Moreover, a string constant `'c'` denotes a public name in `pub`,
which is a fixed, global constant. We have a top sort `msg` and three
incomparable subsorts `fresh`, `pub` and `nat` of that top sort. Timepoint
variables of sort `temporal` are unconnected.

The above rule can therefore be read as follows. First, generate
a fresh name `~ltk` (of sort fresh), which is the new private (long-term) key, and
non-deterministically choose a public name `A`, for the agent for whom we
are generating the key-pair.  Afterward, generate the fact `!Ltk($A, ~ltk)`
(the exclamation mark `!` denotes that the fact is persistent, i.e., it
can be consumed arbitrarily often), which
denotes the association between agent `A` and its private key `~ltk`,
and generate the fact `!Pk($A, pk(~ltk))`, which associates
agent `A` and its public key `pk(~ltk)`.

In the example, we allow the adversary to retrieve any public key
using the following rule. Essentially, it reads a public-key database
entry and sends the public key to the network using the built-in fact
`Out`, which denotes sending a message to the network (see the section on 
[Model Specification](005_protocol-specification-rules.html#sec:model-specification)
for more information).

~~~~ {.tamarin slice="code/FirstExample.spthy" lower=23 upper=26}
~~~~

We model the dynamic compromise of long-term private keys using the
following rule. Intuitively, it reads a private-key database entry and
sends it to the adversary. This rule has an observable `LtkReveal`
action stating that the long-term key of agent `A` was compromised. Action facts 
are just like facts, but unlike the other facts do not appear in state, 
but only on the trace. The security properties are specified on the traces, and 
the action `LtkReveal` is used below to determine which agents are compromised. 
The rule now has a premise, conclusion, and action facts within the arrow: `--[ 
ACTIONFACT ]->`:

~~~~ {.tamarin slice="code/FirstExample.spthy" lower=28 upper=31}
~~~~

Modeling the protocol
---------------------

Recall the Alice-and-Bob notation of the protocol we want to model:

    C -> S: aenc(k, pkS)
    C <- S: h(k)

We model it using the following three rules.

~~~~ {.tamarin slice="code/FirstExample.spthy" lower=33 upper=59}
~~~~

Here, the first rule models the client sending its message, while the second
rule models it receiving a response. The third rule models the server,
both receiving the message and responding in one single rule.

Several explanations are in order. First, Tamarin uses C-style comments, so 
everything between  `/*` and `*/` or the line following `//` is a comment. 
Second, we log the session-key setup requests received by servers using an 
action to allow the formalization of the authentication property for the
client later.

Modeling security properties
----------------------------

Security properties are defined over traces of the action facts of
a protocol execution.

We have two properties that we would like to evaluate. In the Tamarin framework,
properties to be evaluated are denoted by lemmas. The first of these is on the
secrecy of the session key from the client point of view. The lemma
`Client_session_key_secrecy` says that it cannot be that a client has set up a
session key `k` with a server `S` and the adversary learned that `k` unless the
adversary performed a long-term key reveal on the server `S`. The second lemma
`Client_auth` specifies client authentication.  This is the statement that, for
all session keys `k` that the clients have setup with a server `S`, there must
be a server that has answered the request or the adversary has previously
performed a long-term key reveal on `S`.

~~~~ {.tamarin slice="code/FirstExample.spthy" lower=62 upper=86}
~~~~

Note that we can also strengthen the authentication property to a version of
injective authentication. Our formulation is stronger than the standard
formulation of injective authentication as it is based on uniqueness instead
of counting. For most protocols that guarantee injective authentication, one
can also prove such a uniqueness claim, as they agree on appropriate fresh
data. This is shown in lemma `Client_auth_injective`.

~~~~ {.tamarin slice="code/FirstExample.spthy" lower=88 upper=102}
~~~~

To ensure that our lemmas do not just hold vacuously because the model
is not executable, we also include an executability lemma that shows
that the model can run to completion. This is given as a regular lemma,
but with the `exists-trace` keyword, as seen in the lemma
`Client_session_key_honest_setup` below. This keyword says that the
lemma is true if there *exists* a trace on which the formula holds; this
is in contrast to the previous lemmas where we required the formula to
hold on *all* traces. When modeling protocols, such existence proofs are useful 
sanity checks.


~~~~ {.tamarin slice="code/FirstExample.spthy" lower=104 upper=109}
~~~~

Graphical User Interface {#sec:gui}
------------------------

How do you now prove that your lemmas are correct? If you execute the
command line

    tamarin-prover interactive FirstExample.spthy

you will then see the following output on the command line:

    GraphViz tool: 'dot'
     checking version: dot - graphviz version 2.39.20150613.2112 (20150613.2112). OK.
    maude tool: 'maude'
     checking version: 2.7. OK.
     checking installation: OK.
    
    The server is starting up on port 3001.
    Browse to http://127.0.0.1:3001 once the server is ready.
    
    Loading the security protocol theories './*.spthy' ...
    Finished loading theories ... server ready at 
    
        http://127.0.0.1:3001

    21/Jun/2016:09:16:01 +0200 [Info#yesod-core] Application launched @(yesod_83PxojfItaB8w9Rj9nFdZm:Yesod.Core.Dispatch ./Yesod/Core/Dispatch.hs:157:11)

At this point, if there were any syntax or wellformedness errors (for example if
the same fact is used with different arities an error would be displayed) they
would be displayed. See the part on [Modeling
Issues](009_modeling-issues.html#sec:modeling-issues) for details on how to deal
with such errors.

However, there are no such errors in our example, and thus the above command
will start a web-server that loads all security protocol theories in the same
directory as FirstExample.spthy. Point your browser to

<http://localhost:3001>

and you will see the following welcome screen:

![Tamarin Web Interface](../images/tamarin-welcome.jpg "Welcome 
Screen"){width=80%}\

The table in the middle shows all loaded theories. You can either
click on a theory to explore it and prove your security properties, or
upload further theories using the upload form at the bottom. Do note
that no warnings will be displayed if you use the GUI in such a manner
to load further theories, so we do recommend starting Tamarin from the
command line in the appropriate directory.

If you click on the 'FirstExample' entry in the table of loaded theories, you 
should see the following:

![FirstExample Theory 
Overview](../images/tamarin-tutorial-overview.jpeg "FirstExample Theory 
Overview"){width=100%}\

On the left hand side, you see the theory: links to the message theory
describing the adversary, the multiset rewrite rules and restrictions describing
your protocol, and the raw and refined sources, followed by the
lemmas you want to prove. We will explain each of these in the following.

On the right hand side, you have a quick summary of the available
commands and keyboard shortcuts you can use to navigate inside the
theory. In the top right corner there are some links: `Index` leads
back to the welcome page, `Download` allows you to download the
current theory (including partial proofs if they exist), `Actions` and
the sub-bullet `Show source` shows the theory's source code,
and `Options` allows you to configure the level of details in the
graph visualization (see below for examples).

If you click on `Message theory` on the left, you should see the following:

![FirstExample Message Theory](../images/tamarin-tutorial-message-theory.jpeg
 "FirstExample Message Theory"){width=100%}\

On the right side, you can now see the message theory, starting with
the so-called *Signature*, which consists of all the functions and equations. 
These can be either user-defined or imported using the built-ins, as in our 
example. Note that Tamarin automatically adds a function `pair` to
create pairs, and the functions `fst` and `snd` together with two
equations to access the first and second parts of a pair. There is a
shorthand for the `pair` using `<` and `>`, which is used here for
example for `fst(<x.1, x.2>)`.

Just below come the *Construction rules*. These rules describe the functions
that the adversary can apply. Consider, for example, the following rule:

    rule (modulo AC) ch:
     [ !KU( x ) ] --[ !KU( h(x) ) ]-> [ !KU( h(x) ) ]

Intuitively, this rule expresses that if the adversary knows `x` (represented by
the fact `!KU(x)` in the premise), then he can compute `h(x)` (represented by
the fact `!KU(h(x))` in the conclusion), i.e., the hash of `x`. The action fact
`!KU(h(x))` in the label also records this for reasoning purposes.

Finally, there are the *Deconstruction rules*. These rules
describe which terms the 
adversary can extract from larger terms by applying functions. Consider for 
example the following rule:

    rule (modulo AC) dfst:
     [ !KD( <x.1, x.2> ) ] --> [ !KD( x.1 ) ]

In a nutshell, this rule says that if the adversary knows the pair `<x.1, x.2>` 
(represented by the fact `!KD( <x.1, x.2> )`), then he can extract the first 
value `x.1` (represented by the fact `!KD( x.1 )`) from it. This results from 
applying `fst` to the pair and then using the equation 
`fst(<x.1, x.2>) = x.1`. The precise difference between `!KD( )` and `!KU( )` 
facts is not important for now, and will be explained below. As a first 
approximation, both represent the adversary's knowledge and the distinction is 
only used to make the tool's reasoning more efficient.

Now click on *Multiset rewriting rules* on the left.

![FirstExample Multiset Rewriting 
Rules](../images/tamarin-tutorial-multiset-rules.jpeg
 "FirstExample Multiset Rewriting Rules"){width=100%}\

On the right side of the screen are the protocol's 
rewriting rules, plus two additional rules:  `isend` and `irecv`^[The 'i'
historically stems from "intruder", but here we use "adversary".].
These two extra rules provide an interface between the protocol's output and input
and the adversary deduction.
The rule `isend` takes a fact `!KU(x)`, i.e., a value `x` that the adversary knows, 
and passes it to a protocol input `In(x)`. The rule `irecv` takes a protocol 
output `Out(x)` and passes it to the adversary knowledge, represented by the 
`!KD(x)` fact. Note that the rule `Serv_1` from the protocol has two 
*variants (modulo AC)*. The precise meaning of this is unimportant right now 
(it stems from the way Tamarin deals with equations) and will be explained in 
the 
[section on cryptographic messages](004_cryptographic-messages.html#sec:cryptographic-messages).

Now click on `Refined sources (10 cases, deconstructions complete)` to see 
the following:

<!-- FIX: When we switch to raw/refined sources, change this whole thing to look
at the second set (refined/type case distinctions) also in the pictures, since
those are the ones actually used in the proof, and 'raw' is just an
uninteresting intermediate result. -->

![FirstExample Case Distinctions 
Rules](../images/tamarin-tutorial-case-distinctions.jpeg
 "FirstExample Case Distinctions"){width=100%}\
 
To improve the efficiency of its internal reasoning, Tamarin precomputes case 
distinctions. A case distinction gives all possible sources for a fact, i.e., 
all rules (or combinations of rules) that produce this fact, and can then be 
used during Tamarin's backward search. These case distinctions are 
used to avoid repeatedly computing the same things. On the right hand 
side is the result of the precomputations for our FirstExample theory.

For example, here Tamarin tells us that there is one possible source of the 
fact `!Ltk( t.1, t.2 )`, namely the rule `Register_pk`. The image shows the 
(incomplete) graph representing the execution. The green box symbolizes the 
instance of the `Register_pk` rule, and the trapezoid on the bottom stands for 
the "sink" of the `!Ltk( t.1, t.2 )` fact. Here the case distinction consists 
of only one rule instance, but there can be potentially multiple rule 
instances, and multiple cases inside the case distinction, as in the following 
images.

The technical information given below the image is unimportant for now, it 
provides details about how the case distinction was computed and if there are 
other constraints such as equations or substitutions that still must be 
resolved.

![FirstExample Case Distinctions 1 of 
3](../images/tamarin-tutorial-case-distinctions-1.jpg 
 "FirstExample Case Distinctions 1 of 3"){width=60%}\
 
Here the fact `!KU( ~t.1 )` has three sources, the first one is the rule 
`Reveal_ltk`, which requires an instance of the rule `Register_pk` to create 
the necessary `!Ltk` fact. The other two sources are given below.
 
![FirstExample Case Distinctions 2 of 
3](../images/tamarin-tutorial-case-distinctions-2.png 
 "FirstExample Case Distinctions 2 of 3"){width=70%}\

![FirstExample Case Distinctions 3 of 
3](../images/tamarin-tutorial-case-distinctions-3.jpg 
 "FirstExample Case Distinctions 3 of 3"){width=40%}\
 
Now we will see how to prove lemmas in the interactive mode. For that, click on 
`sorry` (indicating that the proof has not been started) after the first 
lemma in the left frame to obtain the following screen:

![FirstExample Lemma 1](../images/tamarin-tutorial-lemma-1.jpeg
 "FirstExample Lemma 1"){width=100%}\

Tamarin proves lemmas using constraint solving.
Namely, it refines the knowledge 
it has about the property and the protocol (called a *constraint system*) until 
it can either conclude that the property holds in all possible cases, or until 
it finds a counterexample to the lemma.

On the right, we now have the possible proof steps at the top, and the current 
state of the constraint system just below (which is empty, as we have not 
started the proof yet). A proof always starts with either a simplification step 
(`1. simplify`), which translates the lemma into an initial constraint system 
that needs to be resolved, or an induction setup step (`2. induction`), which 
generates the necessary constraints to prove the lemma using induction on the 
length of the trace. Here we use the default strategy, i.e., a simplification 
step by clicking on `1. simplify`, to obtain the following screen:
 
![FirstExample Lemma 1 Step 1](../images/tamarin-tutorial-lemma-1-simplify.jpeg
 "FirstExample Lemma 1 Step 1"){width=100%}\

Tamarin has now translated the lemma into a constraint system. Since
Tamarin looks for counterexamples to the lemma, it looks for a protocol
execution that contains a `SessKeyC( S, k )` and a `K( k )` action, but
does not use an `LtkReveal( S )`. This is visualized in the graph as
follows. The only way of getting a `SessKeyC( S, k )` action is using an
instance of the `Client_2` rule on the left, and the `K( k )` rule is
symbolized on the right using a round box (adversary reasoning is always
visualized using round boxes).  Just below the graph, the formula

    formulas: ∀ #r. (LtkReveal( S ) @ #r) ⇒ ⊥

now states that any occurrence of `LtkReveal( S )` will lead to a contradiction.

To finish the proof, we can either continue manually by selecting the constraint
to resolve next, or by calling the `autoprove` command, which selects the next
steps based on a heuristic. Here we have two constraints to resolve: 
`Client_1( S, k )` and `KU( k )`, both of which are premises for the rules in 
the unfinished current constraint system.

Note that the proof methods in the GUI are sorted according to the same 
heuristic as is used by the `autoprove` command. Any proof found by always 
selecting the first proof method will be identical to the one constructed by 
the `autoprove` command. However, because the general problem is
undecidable, the algorithm may not terminate for every protocol and property.

In this example, both by clicking multiple times on the first constraint or by 
using the autoprover, we end with the following final state, where the constructed 
graph leads to a contradiction as it contains `LtkReveal( S )`:

![FirstExample Lemma 1 
Finished](../images/tamarin-tutorial-lemma-1-finished.jpeg
 "FirstExample Lemma 1 Finished"){width=100%}\
 
The lemma is now colored in green as it was successfully proven. If we had 
found a counterexample, it would be colored in red. You can prove the other 
lemmas in the same way.

As you may have noticed, there can be lots of different types of arrows, which additionally can be colored differently.

There are normal (solid) arrows (in black or gray), which are used to represent the origins of protocol facts (for linear or persistent facts).
There are also solid red orange arrows, which represent steps where the adversary extracts values from a message he received.

Then there dashed arrows, representing ordering constraints between two actions, and their colors indicate the reasons for the constraint : 

- Black dashed arrows represent an ordering constraint stemming from formulas, for example from the current lemma or a restriction.
- Dark blue indicates an ordering constraint deduced from a fresh value: since fresh values are unique, all rule instances using a fresh value must appear after the instance that created the value.
- Red dashed arrows are used to represent steps where the adversary composes values.
- Dark orange represents an ordering constraint implied by Tamarin's normal form conditions.
- Purple denotes an ordering constraint originating from an injective fact instance, see [injective-instances](011_advanced-features.html#reasoning-about-exclusivity-facts-symbols-with-injective-instances) . 

Dashed edges can be colored with multiple colors at a time, which means that there are several ordering constraints at the same time.

For example, a black and blue dashed arrow indicates that there are two constraints: one deduced from a formula, and one deduced from a fresh value appearing in the rule instances.

Finally, in intermediate proof steps, there can also be dotted green arrows, which are used during Tamarin's proof search to represent incomplete adversary deduction steps.

Note that by default Tamarin does not show all rules and arrows to simplify the graphs, but this can be adjusted using the Options button on the top right of the page.

Another option is whether to render abbreviations in the graph as shown in the picture below.
When abbreviations are enabled Tamarin will construct abbreviations for terms, list them in a legend at the bottom of the image and replace the original terms in the graph.
A maximum on 10 abbreviations are generated and terms are prioritized based on their length and how often they appear in the graph.
Note that abbreviations can appear in other abbreviations, as for example "PK1" appears in the expanded term of "AE1" below.
The legend is sorted so that it can be read top to bottom.

![FirstExample Lemma 1 Abbreviations](../images/tamarin-tutorial-lemma-1-abbrev.png 
 "FirstExample Lemma 1 Abbreviations"){width=100%}\

Running Tamarin on the Command Line
-----------------------------------

The call

    tamarin-prover FirstExample.spthy

parses the `FirstExample.spthy` file, checks its wellformedness, 
and pretty-prints the theory. The declaration of the signature and the 
equations can be found at the top of the pretty-printed theory.

Proving all lemmas contained in the theory using the automatic prover is as 
simple as adding the flag `--prove` to the call; i.e.,

    tamarin-prover FirstExample.spthy --prove

This will first output some logging from the constraint solver and
then the FirstExample security protocol theory with the lemmas and their
attached (dis)proofs:

    summary of summaries:
    
    analyzed: FirstExample.spthy
    
      Client_session_key_secrecy (all-traces): verified (5 steps)
      Client_auth (all-traces): verified (11 steps)
      Client_auth_injective (all-traces): verified (15 steps)
      Client_session_key_honest_setup (exists-trace): verified (5 steps)

It is possible to select lemmas by having multiple `--prove` flags and by
specifying a common prefix followed by a wildcard, e.g.,
`--prove=Client_auth*`. **Note:** In most shells, the `*` needs to be escaped
to `\*`.

### Quit on Warning

As referred to in ["Graphical User Interface"](#sec:gui), in larger models, one
can miss wellformedness errors (when writing the Tamarin file, and when running
the `tamarin-prover`): in many cases, the web-server starts up correctly, making
it harder to notice that something's not right either in a rule or lemma.

To ensure that your provided `.spthy` file is free of any errors or warnings
(and to halt pre-processing and other computation in the case of errors), it can
be a good idea to use the `--quit-on-warning` flag at the command line. E.g.,

    tamarin-prover interactive FirstExample.spthy --quit-on-warning

This will stop Tamarin's computations from progressing any further, and leave
the error or warning causing Tamarin to stop on the terminal.


Complete Example
----------------

Here is the complete input file:

~~~~ {.tamarin include="code/FirstExample.spthy"}
~~~~



