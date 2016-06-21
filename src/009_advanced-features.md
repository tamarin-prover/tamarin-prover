Advanced Features
=================

Advanced features for advanced users: manual proofs, custom heuristics, encod-
ing tricks, induction, channel models, internal preprocessor, how to do timings

Manual Exploration using GUI
----------------------------

TODO: Cas?


Heuristics
----------

TODO: python "oracle" script? [Benedikt/Sasa]

How to Improve your encoding
----------------------------

to encoding using alternative more efficient descriptions



Different Channel Models
-------------------------
Generally, the Dolev-Yao adversary that we consider can read and modify
all messages sent over the network and also inject his own messages.
If we want to achieve authentication or confidentiality properties, we
use cryptography to sign or encrypt messages sent over the insecure network.
 
Alternatively, we can assume that a channel between two roles already has
some properties and abstract away from the fact how this property is achieved.
For example, we can assume that a channel between two roles is confidential
without considering how this property is achieved. The adversary can then not 
learn messages that are sent over this channel. 
For modeling such properties we can define channel rules.

Let us consider the following protocol, where an initiator generates a new 
fresh nonce and sends it to a receiver.

~~~~ {.tamarin include="code/ChannelExample.spthy" lower=3 upper=8}
~~~~

We can model this protocol with the following Tamarin rules.

~~~~ {.tamarin include="code/ChannelExample.spthy" lower=12 upper=33}
~~~~

We want to examine whether the nonce remains secret from the perspective 
of both the initiator, with lemma `nonce_secret_initiator`, and the
receiver, with lemma `nonce_secret_receiver`. Further, with lemma
`message_authentication` we examine if the receiver can be sure that the
agent who he thinks is in the initiating role really is the one who sent the
nonce.

If we consider the protocol with insecure channels, none of the properties
hold, because the adversary can learn the nonce but also send his own one
to the receiver.

Let us now modify the protocol such that the same message is sent over a
confidential channel. By confidential we mean that only the intended receiver
can read the message but anybody, including the adversary, can send a message
on this channel.

~~~~ {.tamarin include="code/ChannelExample_conf.spthy" lower=11 upper=40}
~~~~

The first three rule denote the channel rules for a confidential channel.
They specify that whenever a message `x` is sent on a confidential channel 
from `$A` to `$B`, a fact `!Conf($B,x)` can be derived. This fact binds the 
receiver `$B` to the to the message `x`, because only he will be able to read
the message. The rule `ChanIn_C` models that at the incoming end of a
confidential channel, there must be a `!Conf($B,x)` fact but any apparent
sender `$A` from the adversary knowledge can be added. This models the fact
that a confidential channel is not authentic, and anybody could have sent it.

Note that the fact `!Conf($B,x)` is persistent. With this we model that a
message once sent confidentially to `$B` can be replayed by the adversary at
a later point of time.
The last rule `ChanIn_CAdv` denotes that the adversary can also directly
send a message from his knowledge on a confidential channel.

Finally, we need to specify in the protocol rules that the message `~n` is
sent and received on a confidential channel. We do this by changing the `Out` 
and `In` fact to a  `Out_C` and `In_C` fact, respectively.

In this modified protocol the lemma `nonce_secret_initiator` holds. 
As the initiator sends the nonce on a confidential channel, only the intended
receiver can read the message, but the adversary cannot learn it.


Unlike a confidential channel, an adversary can read messages sent on an
authentic channel. However, on an authentic channel, the adversary cannot
modify the messages or the sender of it.
We modify the protocol again to use an authentic channel for sending the 
message.

~~~~ {.tamarin include="code/ChannelExample_auth.spthy" lower=11 upper=35}
~~~~

The first channel rule binds the sender `$A` of a message `x` to it, by the 
fact `!Auth($A,x)`. Additionally, the rule produces an `Out` fact, which models
that the adversary can learn everything sent on an authentic channel.
The second rule says that whenever there is a fact `!Auth($A,x)`, the message
can be sent to any receiver `$B`. This fact is again persistent, which means 
that the adversary can replay it several times, potentially to different 
receivers.

Again, if we want the nonce in the protocol to be sent over the authentic 
channel, the corresponding `Out` and `In` facts in the protocol rules have to 
be changed to `Out_A` and `In_A`, respectively.
In the resulting protocol, the lemma `message_authentication` is proven to hold
by Tamarin. The adversary cannot change the sender of the message nor 
the message itself. For this reason the receiver can be sure that the agent in 
the initiator role indeed sent it.

The final kind of channels that we want to consider in detail are secure 
channels. Secure channels are both confidential and authentic. This means that 
an adversary can neither modify nor learn messagages that are sent over it.
However, an adversary can store a message sent over a secure channel to replay
it in a later point of time.
The protocol to send the messages over a secure channel can be modeled as
follows.

~~~~ {.tamarin include="code/ChannelExample_sec.spthy" lower=13 upper=35}
~~~~

The channel rules bind both the sender `$A` and the receiver `$B` to the
message `x` by the fact `!Sec($A,$B,x)`, which cannot be modified by the 
adversary.
As `!Sec($A,$B,x)` is a persistent fact, it can be reused several times as the
premise of the rule `ChanIn_S`. This models that an adversary can replay
such a message block arbitrary many times.

With the protocol sending the message over a secure channel, Tamarin proves
all the considered lemmas. The nonce is secret from the perspective of both
the initator and the receiver because the adversary cannot read anything on
a secure channel. 
Further, as the adversary cannot send his own messages on the secure channel
nor modify the messages, the receiver can be sure that the nonce was sent by
the agent who he thinks to be in the initiator role.


Similarly, other channels with yet different properties can be defined. 
For example, we can model a secure channel with the additional property
that it does not allow for replay. This could be done by changing the secure
channel rules above by chaning `!Sec($A,$B,x)` to be a linear fact 
`Sec($A,$B,x)`. Consequently, this fact can only be consumed once and not be
replayed by the adversary at a later point of time.
In a similar mannor, the other channel properties can be changed or more 
properties can be imagined.






































Induction
---------



Integrated Preprocessor
-----------------------



How to do Timings in Tamarin
----------------------------
