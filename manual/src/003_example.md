Initial Example
===============

We will start with a simple example of a protocol that only consists
of two messages (given in Alice-and-Bob notation):

    C -> S: aenc{k}pk(S)
    C <- S: h(k)

In this protocol, a client C generates a fresh symmetric key 'k', encrypts it
with the public key of a server 'S' and sends it to 'S'. The server confirms
the receipt of the key by sending its hash back to the client.

This protocol is artificial and satisfies only very weak security
guarantees.  We will use it to illustrate the general Tamarin workflow
by proving that from the perspective of the client, the freshly
generated key is secret provided that the server is uncompromised.

The Tamarin modeling of this protocol and the security properties are given in 
the file [Tutorial](code/Tutorial.spthy) presented here:

~~~~ {.tamarin include="code/Tutorial.spthy"}
~~~~

Note that Tamarin uses C-style comments. The Tamarin file starts with
`theory` followed by the name, here 'Tutorial'.  After the keyword
`begin`, we first declare function symbols, and equations that these
function symbols must satisfy. Then we declare multiset rewriting
rules that model the protocol, and finally we write lemmas that
specify the security properties. Moreover, we also inserted comments,
to structure the theory. Now, we describe these elements while
modeling this simple protocol in detail.


Function Signature and Equational Theory
----------------------------------------

We are working in the symbolic model of security protocol
verification, which means that we model the messages as terms, built
from functions, satisfying an underlying equational theory. This will
be explained in detail later, but for now note that there are function
names which we explicitly declare together with their arity, and
equalities that define the semantic equivalence of terms, e.g., the
decryption of an encrypted ciphertext is the original message, when
the correct keys are used. We generally use lower-case for function names.

We model hashing using the unary function 'h'.
We model asymmetric encryption by declaring

  * a binary function 'aenc' denoting the encryption algorithm,
  * a binary function 'adec' denoting the decryption algorithm, and
  * a unary function 'pk' denoting the algorithm computing a public
  key from a private key.

This is done by declaring the function symbols:

~~~~ {.tamarin slice="code/Tutorial.spthy" lower=15 upper=15}
~~~~

The equation 

~~~~ {.tamarin slice="code/Tutorial.spthy" lower=16 upper=16}
~~~~

models the interaction between calls to these three algorithms. All
such user-specified equations must be subterm-convergent rewriting
rules, when oriented from left to right. This means that the
right-hand-side must be a subterm of the left-hand-side or a nullary
function symbol (a constant), see the section on [Equational
Theory](004_cryptographic-messages).


Modeling the Public Key Infrastructure
--------------------------------------

Now, we introduce multiset rewriting rules modeling a public key
infrastructure (PKI). In these rules we use facts to store information
about the state in their arguments. The rules have a premise and a
conclusion, separated by the arrow `-->`:

~~~~ {.tamarin slice="code/Tutorial.spthy" lower=19 upper=22}
~~~~

The above rule models registering a public key. It makes use of the
following syntax.

Facts always start with an upper-case letter and do not have to be
declared.  If their name is prefixed with an exclamation mark `!`,
then they are persistent. Otherwise, they are linear. Note that every
fact name must be used consistently; i.e., it must always be used with
the same arity, casing, and multiplicity. Otherwise, Tamarin complains
that the theory is not wellformed.

The `Fr` fact is a built-in fact. It denotes a freshly generated fresh
name, used to model random numbers, i.e., nonces or keys. See later in this
manual for details.

We denote the sort of variables using prefixes:

 *    `~x`  denotes  `x:fresh`
 *    `$x`  denotes  `x:pub`
 *    `#i`  denotes  `i:temporal`
 *    `i`   denotes  `i:msg`

 and a string constant `'c'` denotes a public name `'c \in PN'`; i.e., a
 fixed, global constant

Thus, the above rule can be read as follows. First, freshly generate a
fresh name `~ltk`, the new private key, and nondeterministically choose
a public name `A`, the agent for which we are generating the key-pair.
Then, generate the persistent fact `!Ltk($A, ~ltk)`, which denotes the
association between agent `A` and its private key `~ltk`, and generate
the persistent fact `!Pk($A, pk(~ltk))`, which denotes the association
between the agent `A` and its public key `pk(~ltk)`.

We allow the adversary to retrieve any public key using the following
rule.  Intuitively, it just reads a public-key database entry and
sends the public key to the network using the built-in fact `Out`
denoting a message sent to the network. See later for more
information:

~~~~ {.tamarin slice="code/Tutorial.spthy" lower=24 upper=27}
~~~~

We model the dynamic compromise of long-term private keys using the
following rule. Intuitively, it reads a private-key database entry and
sends it to the adversary. This rule has an observable `LtkReveal`
action stating that the long-term key of agent `A` was compromised. We
will use this action in the security property below to determine which
agents are compromised. Action facts are just like facts, but *should*
be from a different namespace, though this is not enforced. The rule
now has a premise, conclusion, and action facts within the arrow: `-[
FACT ]->`:

~~~~ {.tamarin slice="code/Tutorial.spthy" lower=29 upper=32}
~~~~

Modeling the protocol
----------------------

Recall the Alice-and-Bob notation of the protocol we want to model:

    C -> S: aenc{k}pk(S)
    C <- S: h(k)

We model it using the following three rules.

~~~~ {.tamarin slice="code/Tutorial.spthy" lower=34 upper=65}
~~~~

The first rule models the client sending its message, while the second
rule models it receiving a response. The third rule models the server,
both receiving the message and responding in one single rule.

Note that we model all applications of cryptographic algorithms
explicitly.  Call `tamarin-prover Tutorial.spthy` to inspect the
finite variants of the `Serv_1` rule, which list all possible
interactions of the destructors used, or see below for detail. In our
proof search, we will consider all these interactions.


We also model that the server explicitly checks that the first
component of the request is equal to `'1'`. We model this by logging
the claimed equality and then adapting the security property such that
it only considers traces where all `Eq` actions occur with two equal
arguments. Note that `Eq` is NOT a built-in fact, but one can pick any
name. Note that inequalities can be modeled analogously.

We log the session-key setup requests received by servers to allow
formalizing the authentication property for the client.


Modeling the security properties
--------------------------------

The security properties are defined over traces of the action facts of
a protocol execution.

First, note that we can specify additional axioms that restrict the
set of considered traces. In this example, we restrict our attention
to traces where all equality checks succeed. In detail the axiom says
that for all parameters `x`, `y` to the `Eq` action fact at some time
point `i` it has to be the case that `x=y`.

~~~~ {.tamarin slice="code/Tutorial.spthy" lower=68 upper=68}
~~~~

Note that the order between axioms and lemmas does not matter. All
axioms are always available/assumed in the proofs of all security
properties. Now we have two lemmas, the first on the secrecy of
session key secrecy from the client point of view. The lemma
`Client_session_key_secrecy` says that it cannot be that a client has
set up a session key `k` with a server `S` and the adversary learned
that `k` unless the adversary performed a long-term key reveal on the
server `S`. The second lemma `Client_auth` specifies client authentication, which is
that for all session keys `k` that the clients have setup with a
server `S` there must be a server that has answered the request, or
the adversary has performed a long-term key reveal on `S` previously
in time.

~~~~ {.tamarin slice="code/Tutorial.spthy" lower=70 upper=95}
~~~~

Note that we can also strengthen the authentication property to a version of
injective authentication. Our formulation is stronger than the standard
formulation of injective authentication, as it is based on uniqueness instead
of counting. For most protocols, that guarantee injective authentication one
can also prove such a uniqueness claim, as they agree on appropriate fresh
data. This is shown in lemma `Client_auth_injective`.


~~~~ {.tamarin slice="code/Tutorial.spthy" lower=97 upper=111}
~~~~


To ensure that our lemmas do not just hold vacuously because the model
is not executable, we make it a point to always have an executability
lemma, that shows that the model can run to completion. This is given
as a regular lemma, but with the `exists-trace` keyword, as seen in
the lemma `Client_session_key_honest_setup` below

~~~~ {.tamarin slice="code/Tutorial.spthy" lower=113 upper=118}
~~~~

Note that when adding inconsistent axioms, you can prove any
property. To check that there still exist traces, we always want an
`exists-trace` lemma.  When modeling protocols such existence proofs
are very useful sanity checks.



Running Tamarin on Tutorial
---------------------------


The call `tamarin-prover Tutorial.spthy` parses the `Tutorial.spthy`
file, computes the variants of the multiset rewriting rules, checks
their wellformedness (explained below), and pretty-prints the
theory. The declaration of the signature and the equations can be
found at the top of the pretty-printed theory.

Proving all lemmas contained in the theory is as simple as adding the
flag `--prove` to the call; i.e.,

  `tamarin-prover Tutorial.spthy --prove`

This will first output some logging from the constraint solver and
then the Tutorial security protocol theory with the lemmas and their
attached (dis)proofs.




Graphical User Interface
------------------------

Just call

    tamarin-prover interactive Tutorial.spthy

you will then see the following output on the command line

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

If there were any syntax errors you would see them at this point, but
there are none in the 'Tutorial'. See later for details on how to deal
with such errors.
    
This will start a web-server that loads all security protocol theories in the
same directory as Tutorial.spthy. Point your browser to

<http://localhost:3001>

and you will see the following welcome screen:

![Tamarin Web Interface](../images/tamarin-welcome.jpg "Welcome Screen")

The table in the middle shows all loaded theories. You can either click on a 
theory to explore it and prove your security properties, or upload further 
theories using the upload form below.

If you click on the 'Tutorial' entry in the table of loaded theories, you 
should see the following:

![Tutorial Theory Overview](../images/tamarin-tutorial-overview.jpg "Tutorial 
Theory Overview")

On the left hand side you see the theory: links to the message theory 
describing the intruder, the multiset rewrite rules and axioms describing your 
protocol, and the typed and untyped case distinctions, followed by the lemmas 
you want to prove. We will explain each of these points in the following.

On the right hand side, you have a quick summary of the available
commands and keyboard shortcuts you can use to navigate inside the
theory. In the top right corner there are some links: `Index` leads
back to the welcome page, `Download` allows you to download the
current theory (including partial proofs if they exist), `Actions` and
then the sub-bullet `Show source` shows the source code of the theory,
and `Options` allows you to configure the level of details in the
graph visualisation (see below for examples).

If you click on `Message theory` on the left, you should see the following:

![Tutorial Message Theory](../images/tamarin-tutorial-message-theory.jpg 
 "Tutorial Message Theory")
 
On the right side you can now see the message theory, starting with
the so-called *Signature*, i.e., all functions and equations you
defined. Note that Tamarin automatically added a function `pair` to
create pairs, and functions `fst` and `snd` together with two
equations to access the first and second value of a pair. There is a
shorthand for the `pair` using `<` and `>` which is used here for
example for `fst(<x.1, x.2>)`.

Just below you have the *Construction rules* which describe which functions the 
intruder can apply. Consider for example the following rule:

    rule (modulo AC) ch:
     [ !KU( x ) ] --[ !KU( h(x) ) ]-> [ !KU( h(x) ) ]

Essentially this rule says that if the intruder knows `x` (represented
by the fact `!KU(x)` in the premise), then he can compute `h(x)`
(represented by the fact `!KU(h(x))` in the conclusion), i.e., the
hash of `x`. The action fact `!KU(h(x))` in the label also notes this
for reasoning purposes.

Finally, there are the *Deconstruction rules* which describe which terms the 
intruder can extract from larger terms by applying functions. Consider for 
example the following rule:

    rule (modulo AC) dfst:
     [ !KD( <x.1, x.2> ) ] --> [ !KD( x.1 ) ]

In a nutshell this rule says that if the intruder knows the pair `<x.1, x.2>` 
(represented by the fact `!KD( <x.1, x.2> )`), then he can extract the first 
value `x.1` (represented by the fact `!KD( x.1 )`) from it. This stems from 
the applying `fst` to the pair and then using the equation 
`fst(<x.1, x.2>) = x.1`. The precise difference between `!KD( )` and `!KU( )` 
facts is not important for now, and will be explained below. As a first 
approximation, both represent they intruder's knowledge and are only used to 
make the tool's reasoning more efficient.

Now click on *Multiset rewriting rules and axioms* on the left.

![Tutorial Multiset Rewriting 
Rules](../images/tamarin-tutorial-multiset-rules.jpg 
 "Tutorial Multiset Rewriting Rules")

On the right side of the screen you should now see your protocol's 
rewriting rules, plus two additional rules: the `isend` and `irecv` rules, 
which interface the protocols output and input with the intruder deduction.
The rule `isend` takes a fact `!KU(x)`, i.e., a value `x` the intruder knows, 
and passes it to a protocol input `In(x)`. The rule `irecv` takes a protocol 
output `Out(x)` and passes it to the intruder knowledge, represented by the 
`!KD(x)` fact. Note that the rule `Serv_1` from the protocol has three 
*variants (modulo AC)*. The precise meaning of this is not important right now 
(it stems from the way Tamarin deals with equations) and will be explained in 
the [section on cryptographic
messages](004_cryptographic-messages.html#sec:cryptographic-messages).

Just below you have the list of all axioms. In this example there is
only the one axiom `Equality_Checks_Succeed`.

Now click on `Untyped case distinctions (10 cases, all chains solved)` to see 
the following:

![Tutorial Case Distinctions 
Rules](../images/tamarin-tutorial-case-distinctions.jpg 
 "Tutorial Case Distinctions")
 
To improve the efficiency of its internal reasoning, Tamarin precomputes case 
distinctions. A case distinction gives all possible sources for a fact, i.e., 
all rules (or combinations of rules) that produce this fact, and can then be 
used during Tamarin's backward search. These case distinctions are 
then used to avoid computing the same thing again and again. On the right hand 
side you can now see the result of the precomputations for our Tutorial theory.

For example, here Tamarin tells us that there is one possible source of the 
fact `!Ltk( t.1, t.2 )`, namely the rule `Register_pk`. The image shows the 
(incomplete) graph representing the execution. The green box symbolizes the 
instance of the `Register_pk` rule, and the trapezoid on the bottom stands for 
the "sink" of the `!Ltk( t.1, t.2 )` fact. Here the case distinction consists 
of only one rule instance, but there can be potentially multiple rule 
instances, and multiple cases inside the case distinction, as in the following 
images.

The technical information given below the image is not important for now, it 
gives details about how the case distinction was computed and if there are 
other constraints such as equations or substitutions which still need to be 
resolved.

![Tutorial Case Distinctions 1 of 
3](../images/tamarin-tutorial-case-distinctions-1.jpg 
 "Tutorial Case Distinctions 1 of 3")
 
Here the fact `!KU( ~t.1 )` has three sources, the first one is the rule 
`Reveal_ltk`, which requires an instance of the rule `Register_pk` to create 
the necessary `!Ltk` fact. The other two sources are given below.
 
![Tutorial Case Distinctions 2 of 
3](../images/tamarin-tutorial-case-distinctions-2.jpg 
 "Tutorial Case Distinctions 2 of 3")

![Tutorial Case Distinctions 3 of 
3](../images/tamarin-tutorial-case-distinctions-3.jpg 
 "Tutorial Case Distinctions 3 of 3")
 
Now we will see how to prove lemmas in the interactive mode. For that, click on 
the `sorry` (indicating that the proof has not been started) after the first 
lemma in the left frame to obtain the following screen:

![Tutorial Lemma 1](../images/tamarin-tutorial-lemma-1.jpg 
 "Tutorial Lemma 1")

Tamarin proves lemmas using constraint solving, i.e., by refining the knowledge 
it has about the property and the protocol (called a *constraint system*) until 
it can either conclude that the property holds in all possible cases, or until 
it finds a counterexample invalidating the lemma.

On the right we now have the possible proof steps at the top, and the current 
state of the constraint system just below (which is empty, as we haven't 
started the proof yet). A proof always starts with either a simplification step 
(`1. simplify`) which translates the lemma into an initial constraint system 
that needs to be resolved, or an induction setup step (`2. induction`) which 
generates the necessary constraints to prove the lemma using induction on the 
length of the trace. Here we use the default strategy, i.e., a simplification 
step by clicking on `1. simplify`, to obtain the following screen:
 
![Tutorial Lemma 1 Step 1](../images/tamarin-tutorial-lemma-1-simplify.jpg 
 "Tutorial Lemma 1 Step 1")

Tamarin has now translated the lemma into a constraint system. Since it looks 
for counterexamples to the lemma, it looks for a protocol execution that 
contains a `SessKeyC( S, k )` and a `K( k )` action, but does not use an 
`LtkReveal( S )`. This is visualized in the graph as follows. The only way of 
getting a `SessKeyC( S, k )` action is using an instance of the `Client_2` 
rule on the left, and the `K( k )` rule is symbolized on the right using a 
round box (intruder reasoning is always visualized using round boxes).
Just below the graph, the formula

    formulas: ∀ #r. (LtkReveal( S ) @ #r) ⇒ ⊥

now states that any occurrence of `LtkReveal( S )` will lead to a contradiction.

To finish the proof we can either continue manually by selecting the constraint 
to resolve next, or by calling the `autoprove` command which selects the next steps 
based on a heuristic. Note that that the proof methods in the GUI are also 
sorted according to the same heuristic. Always selecting the first proof method 
will result in the same proof as the one constructed by the 'autoprover'.

In both cases we end with the following final state, where the constructed 
graph leads to a contradiction as it contains `LtkReveal( S )`:

![Tutorial Lemma 1 Finished](../images/tamarin-tutorial-lemma-1-finished.jpg 
 "Tutorial Lemma 1 Finished")
 
The lemma is now colored in green, as it was successfully proven. If we had 
found a counterexample, it would be colored in red.

All other properties in the 'Tutorial' can also be proven by Tamarin, just run

     $ tamarin-prover Tutorial.spthy --prove

and you will see this output:

    ==============================================================================
    summary of summaries:
    
    analyzed: Tutorial.spthy
    
      Client_session_key_secrecy (all-traces): verified (5 steps)
      Client_auth (all-traces): verified (11 steps)
      Client_auth_injective (all-traces): verified (15 steps)
      Client_session_key_honest_setup (exists-trace): verified (5 steps)

meaning all properties have been verified indeed.