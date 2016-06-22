Precomputation
============== 

In this section we will explain some of the aspects of the precomputation
performed by Tamarin.  This is relevant for users that model complex protocols,
because they may run into so-called [open chains](#sec:openchains) that can be
problematic for verification.

To illustrate the concepts, consider the example of the Needham-Schroeder-Lowe
Public Key Protocol, given here in Alice&Bob notation:

~~~~ {.tamarin slice="code/NSLPK3.spthy" lower=24 upper=29}
~~~~

It is specified in Tamarin by the following rules:

~~~~ {.tamarin slice="code/NSLPK3.spthy" lower=32 upper=71}
~~~~

We want to examine if the following lemma holds:

~~~~ {.tamarin slice="code/NSLPK3.spthy" lower=105 upper=118}
~~~~



Open Chains {#sec:openchains}
-----------

In the precomputation phase, Tamarin goes through all rules and inspects their
premises. For each of these facts, Tamarin will precompute a set of possible
sources. Each such source is referred to as a *chain* and represents
combinations of rules from which the fact could be obtained.  For each fact,
this leads to a set of possible sources and we refer to these sets as the *case
distinctions*.

However, for some rules Tamarin cannot resolve where a fact must have come from.
We call such a chain an *open chain*, and we will explain them in more detail
below.

The existence of open chains complicates the automatic proof generation and
often (but not always) means that no proof will be found automatically.  For
this reason, it is useful for users to be able to find open chains and examine
if it is possible to remove them.

In the interactive mode you can find open chains as follows.  On the top left,
under "Untyped case distinction", one can find the chains that were precomputed
by Tamarin.

![Tamarin GUI](../images/FindOpenChains1.png "Untyped case distinctions")

The unsolved chains can be identified by the light green arrows as in the
following example:

![Open chain visible in green](../images/FindOpenChains2.png "Open chain visible")

The green arrow indicates that Tamarin cannot exclude the possibility that the
adversary can derive any fresh term `~t.1` with this rule `I_2`.  As we are
using an untyped protocol model, the tool cannot determine that `nr.7` should be
a fresh nonce, but that it could be any message. For this reason Tamarin
concludes that it can derive any message with this rule.

**FIX Cas: In the above, we mention untyped protocol model. Did we explain
this?**

### Why open chains complicate proofs

To get a better understanding of the problem we can look at what happens if
we try to prove the lemma `nonce_secrecy`.  If we manually always choose
the first case for the proof, we can see that Tamarin derives the secret key to
decrypt the output of rule `I_2` by repeatedly using this rule `I_2`.

![Secret derived by using `I_2`](../images/FindOpenChains3.png "`I_2` repeatedly")

As Tamarin is not able to conclude that the secret key could not have come from
the rule `I_2`, the algorithm derives the secret key that is needed. The proof
uses the same strategy recursively but will not terminate.



Using Typing Lemmas to Mitigate Open Chains
-------------------------------------

Once we identified the rules and cases in which open chains occur, we
can try to avoid them. A good mechanism to get rid of open chains is the use of
so-called *typing lemmas*.

Typing lemmas are a special case of lemmas, and are applied in a particular
phase of Tamarin's pre-computation. Roughly, verification in Tamarin involves
the following steps:

  1. It first determines the possible sources of all premises. We call these the
     untyped case distinctions.

  2. Next, the algorithm uses the automatic proof mode to discharge any typing lemmas using induction.

  3. The typing lemmas are applied to the untyped case distinctions, yielding a
     new set of sources, which we call the typed case distinctions.

  4. Depending on the mode, the other (non-typing) lemmas are now considered
     manually or automatically using the typed case distinctions.

For full technical details, we refer the reader to [@meierthesis].

In our example we can add the following lemma:

~~~~ {.tamarin slice="code/NSLPK3.spthy" lower=86 upper=102}
~~~~

This typing lemma is applied to the untyped case distinctions to compute the
typed case distinctions. All non-typing lemmas are proven with the resulting
typed case distinctions, while typing lemmas of course need to be proved with
the untyped case distinctions.

This lemma relates the point of instantiation to the point of sending by either
the adversary or the communicating partner. In other words, it says that
whenever the responder receives the first nonce, either the nonce was known to
the adversary or the initiator sent the first message prior to that moment.
Similarly, the second part states that whenever the initiator receives the
second message, either the adversary knew the corresponding nonce or the
responder has sent the second message before.

This typing lemma can be automatically proven by Tamarin. With the typing lemma,
Tamarin can then automatically prove the lemma `nonce_secrecy`.


Another possibility is that the open chains only occur in an undesired
application of a rule that we do not want to consider in our model.
In such a case we can explicitly exclude this application of the rule
with an axiom. But, we need to ensure that the resulting model is the
one we want, so use this with care.


TODO:
      * Typing lemmas in particular - how to tell when one would help, the
        best way to write one, and what you can’t prove in a typing lemma
