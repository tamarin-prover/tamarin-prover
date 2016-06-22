
Advanced Features
=================

Here we discuss advanced features for advanced users.
Namely manual proofs, custom
heuristics, encoding tricks, induction, channel models, internal
preprocessor, and how to do timings

Manual Exploration using GUI
----------------------------

TODO: Cas?


Heuristics
----------

TODO: python "oracle" script? [Benedikt/Sasa]

How to Improve your Encoding
----------------------------

to encoding using alternative more efficient descriptions



Different Channel Models
-------------------------

Tamarin's built-in adversary model is the classical Dolev-Yao
adversary that has complete control of the communication network.  In
particular, this adversary can eavesdrop on, block, and
modify messages sent over the network and inject any message
from his knowledge (the messages he has learned or can construct
from learned messages) into the network.

The Dolev-Yao adversary's control over the communication network is
modeled with the following two built-in rules:

1.  
```
rule irecv:
   [ Out( x ) ] --> [ !KD( x ) ]
```

2.  
```
rule isend:
   [ !KU( x ) ] --[ K( x ) ]-> [ In( x ) ]
```

The `irecv` rule states that any message sent by an agent using the
`Out` fact is learned by the adversary. Such messages are then
analyzed with the adversary's message deduction rules that depend on
the specified equational theory.

The `isend` rule states that any message received by
an agent by means of the `In` fact has been constructed by the
adversary.

We can limit the adversary's control over the protocol agents'
communication channels by specifying channel rules.  In the following,
we illustrate the modelling of confidential, authentic, and secure
channels.
Consider for this purpose the following protocol, where an initiator generates a 
fresh nonce and sends it to a receiver.

~~~~ {.tamarin slice="code/ChannelExample.spthy" lower=5 upper=6}
~~~~

We can model this protocol as follows.

~~~~ {.tamarin slice="code/ChannelExample.spthy" lower=10 upper=31}
~~~~

We state the nonce secrecy property for the 
initiator and responder with the `nonce_secret_initiator` and the
`nonce_secret_receiver` lemma, respectively. The lemma
`message_authentication` specifies a [message authentication](006_property-specification.html#sec:message-authentication) property for the responder role. 

If we analyze the protocol with insecure channels, none of the
properties hold because the adversary can learn the nonce sent by the
initiator and send his own one to the receiver.

#### Confidential Channel Rules

Let us now modify the protocol such that the same message is sent over a
confidential channel. By confidential we mean that only the intended receiver
can read the message but anybody, including the adversary, can send a message
on this channel.

~~~~ {.tamarin slice="code/ChannelExample_conf.spthy" lower=11 upper=38}
~~~~

The first three rules denote the channel rules for a confidential channel.
They specify that whenever a message `x` is sent on a confidential channel 
from `$A` to `$B`, a fact `!Conf($B,x)` can be derived. This fact binds the 
receiver `$B` to the  message `x`, because only he will be able to read
the message. The rule `ChanIn_C` models that at the incoming end of a
confidential channel, there must be a `!Conf($B,x)` fact, but any apparent
sender `$A` from the adversary knowledge can be added. This models 
that a confidential channel is not authentic, and anybody could have sent the message.

Note that the fact `!Conf($B,x)` is persistent. With this we model that a
message that was sent confidentially to `$B` can be replayed by the adversary at
a later point in time.
The last rule, `ChanIn_CAdv`, denotes that the adversary can also directly
send a message from his knowledge on a confidential channel.

Finally, we need to given protocol rules specifying that the message `~n` is
sent and received on a confidential channel. We do this by changing the `Out` 
and `In` facts to the `Out_C` and `In_C` facts, respectively.

In this modified protocol, the lemma `nonce_secret_initiator` holds. 
As the initiator sends the nonce on a confidential channel, only the intended
receiver can read the message, but the adversary cannot learn it.

#### Authentic Channel Rules

Unlike a confidential channel, an adversary can read messages sent on an
authentic channel. However, on an authentic channel, the adversary cannot
modify the messages or their sender.
We modify the protocol again to use an authentic channel for sending the 
message.

~~~~ {.tamarin slice="code/ChannelExample_auth.spthy" lower=11 upper=33}
~~~~

The first channel rule binds a sender `$A` to a message `x` by the 
fact `!Auth($A,x)`. Additionally, the rule produces an `Out` fact that models
that the adversary can learn everything sent on an authentic channel.
The second rule says that whenever there is a fact `!Auth($A,x)`, the message
can be sent to any receiver `$B`. This fact is again persistent, which means 
that the adversary can replay it several times, potentially to different 
receivers.

Again, if we want the nonce in the protocol to be sent over the authentic 
channel, the corresponding `Out` and `In` facts in the protocol rules must
be changed to `Out_A` and `In_A`, respectively.
In the resulting protocol, the lemma `message_authentication` is proven 
by Tamarin. The adversary can neither change the sender of the message nor 
the message itself. For this reason, the receiver can be sure that the agent in 
the initiator role indeed sent it.

#### Secure Channel Rules

The final kind of channels that we consider in detail are secure 
channels. Secure channels are both confidential and authentic. Hence
an adversary can neither modify nor learn messages that are sent over it.
However, an adversary can store a message sent over a secure channel for replay
at a later point in time.

The protocol to send the messages over a secure channel can be modeled as
follows.

~~~~ {.tamarin slice="code/ChannelExample_sec.spthy" lower=11 upper=33}
~~~~

The channel rules bind both the sender `$A` and the receiver `$B` to the
message `x` by the fact `!Sec($A,$B,x)`, which cannot be modified by the 
adversary.
As `!Sec($A,$B,x)` is a persistent fact, it can be reused several times as the
premise of the rule `ChanIn_S`. This models that an adversary can replay
such a message block arbitrary many times.

For the protocol sending the message over a secure channel, Tamarin proves
all the considered lemmas. The nonce is secret from the perspective of both
the imitator and the receiver because the adversary cannot read anything on
a secure channel. 
Furthermore, as the adversary cannot send his own messages on the secure channel
nor modify the messages, the receiver can be sure that the nonce was sent by
the agent who he believes to be in the initiator role.


Similarly, one can define other channels with other properties.
For example, we can model a secure channel with the additional property
that it does not allow for replay. This could be done by changing the secure
channel rules above by chaining `!Sec($A,$B,x)` to be a linear fact 
`Sec($A,$B,x)`. Consequently, this fact can only be consumed once and not be
replayed by the adversary at a later point in time.
In a similar manner, the other channel properties can be changed and additional
properties can be imagined.




Induction
---------

Let us first motivate the need for an inductive proof method on a simple example with two rules and one lemma:

~~~~ {.tamarin slice="code/InductionExample.spthy" lower=5 upper=23}
~~~~

If we try to prove this with Tamarin without using induction (comment
out the `[use_induction]` to try) the tool will loop on the backwards
search over the repeating `A(x)` fact. That `A(x)` fact can have two
sources, either the `start` rule, which ends the search, or another
instantiation of the `loop` rule, which continues.

The induction method works by distinguishing the last timepoint `#i`
in the trace, as `last(#i)`, from all other timepoints. It assumes the
property holds for all timepoints but this one (*wellfounded induction*).

The induction hypothesis then becomes another constraint during the
constraint solving phase. Essentially trace induction allows to prove
slightly more properties.

**FIXME:** adjust the induction section


Integrated Preprocessor {#sec:integrated-preprocessor}
-----------------------

You can use the integrated preprocessor to activate or deactivate
particular of your file. We use this mostly when we are interested in
only a subset of lemmas. You do this by putting the relevant part of
your file within an `#ifdef` block with a keyword `KEYWORD`

```
#ifdef KEYWORD
...
#endif
```

and then running Tamarin with the option `-DKEYWORD` to have this part included.

If you use this feature to exclude typing lemmas, your case
distinctions will change, and you may not be able to find proofs that
were found previously anymore. Similarly, if you have `reuse` marked
lemmas that are removed, other following lemmas may not be provable anymore.


See this code for a lemma that will be included when `timethis` is
given as parameter to `-D`:

~~~~ {.tamarin slice="code/TimingExample.spthy" lower=20 upper=24}
~~~~

while at the same time this would be excluded:

~~~~ {.tamarin slice="code/TimingExample.spthy" lower=26 upper=30}
~~~~


How to do Timings in Tamarin
----------------------------

If you want to time the verification duration of a particular lemma
you can use the previously described integrated preprocessor to mark
each lemma, and only include the one you are timing. For example, wrap
the relevant lemma within `#ifdef timethis`. Also make sure to include
`reuse` and `typing` lemmas in this.  All other lemmas should be
covered under a different keyword, in the example here we use `nottimed`.

You then run

```
time tamarin-prover -Dtimethis TimingExample.spthy --prove
```

to get the timing for only those lemmas of interest. Here is the
complete input file, with an entirely artificial protocol:

~~~~ {.tamarin include="code/TimingExample.spthy"}
~~~~

