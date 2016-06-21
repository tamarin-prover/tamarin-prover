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
then use cryptography to sign or encrypt messages sent over these insecure
channels.
 
Alternatively, we can assume that a channel between two roles already has
some properties and abstract away from the fact how this property is achieved.
For example, we can assume that a channel between two roles is confidential
and the adversary cannot learn what is sent over this channel. 
For modeling such properties we can define new channel rules.

Let us consider the following protocol, where an initiator generates a new 
fresh nonce and sends it to a receiver.

~~~~ {.tamarin include="code/ChannelExample.spthy" lower=47 upper=67}
~~~~

We want to examine whether the nonce remains secret from the perspective 
of both the initiator and the receiver. Further, we examine if the receiver
can be sure that the agent who he thinks is in the initiating role really is
the one who sent the nonce.
If we consider the protocol with insecure channels, none of the properties
hold, because the adversary can learn the nonce but also send his own one
to the receiver.


* authentic channel:

~~~~ {.tamarin include="code/ChannelExample.spthy" lower=11 upper=21}
~~~~

* confidential channel:

~~~~ {.tamarin include="code/ChannelExample.spthy" lower=21 upper=36}
~~~~


* secure channel:

~~~~ {.tamarin include="code/ChannelExample.spthy" lower=36 upper=46}
~~~~




*maybe not only auth,conf,sec but also say that with same idea can do several things: no replay = not persistent fact ..*




Induction
---------



Integrated Preprocessor
-----------------------



How to do Timings in Tamarin
----------------------------