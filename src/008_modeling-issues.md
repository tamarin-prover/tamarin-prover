Modeling Issues
===============

TODO: Explain common errors and misconceptions and how to avoid them

First-time users
----------------
In this section we discuss some problems that a first-time user might face.
This includes some error messages and what you can do in order to fix them. 
Also, we discuss how you can find out that your rule do not model the protocol
that you wanted and how you can avoid this with `exists-trace` lemmas.

For illustrating these concepts, consider the following protocol, where an
initiator `$I` and a receiver `$R` share a symmetric key. `$I` then sends the
message `~m`, encrypted with their shared key `~k` to `$R`.

~~~~ {.tamarin slice="code/FirstTimeUser.spthy" lower=12 upper=33}
~~~~

With the lemma `nonce_secret` we examine if the message is secret from the
perspective of the receiver.


### Exists lemma ### 
Imagine that you forgot in the setup the agent state fact for the receiver
`AgSt($R,~k)` as follows:

~~~~ {.tamarin slice="code/FirstTimeUser_Error1.spthy" lower=16 upper=20}
~~~~

If you then use Tamarin to prove the lemma `nonce_secret` it will be verified.
The lemma says that whenever the action `Secret(R,m)` is reached in a trace,
then the adversary does not learn `m`. However, with this error, the rule `R_1`
will never be executed, and consequently there will never be an action 
`Secret(R,m)` in the trace. For this reason the lemmas is always true.
To avoid the case of proving a lemma but with an empty protocol, we define
`exist-trace` lemmas.

With such a lemma we define what functionality we want to achieve in a protocol.
In the above example the goal is that first an initiator sends a message and 
that then the receiver receives the same message. 
We express this with the following lemma:

~~~~ {.tamarin slice="code/FirstTimeUser.spthy" lower=34 upper=38}
~~~~

If we evaluate this lemma with Tamarin it will be falsified. This indicates
that there exists no trace where the initiator sends a message to the receiver.
Often, this is the case if we forget to add a fact that connects several rules 
and some rules can never be reached. 
So it is generally recommended to add a `exists-trace` lemma from the beginning
to make sure the protocol provides the functionality you want.

### Error Messages ###
In this section we will intentionally add some mistakes to the above protocol 
to go through some common error messages of Tamarin.
We will always present one changed rule and a corresponding error message and 
then explain what the error message means. 
In practice, this should help in understanding error messages that one gets
when specifying a new protocol.








unexpected"(" : if 
	forgot to built in or if 
	forgot to define this function

wellformedness check failed: go up and look at more detailed msg

arity
fact of different arity: gives errors
functional lemma,


error fresh vs public (no tilde vs tilde with same name)

### why not doing anything ###
open chains


### else ###
function-> where does it go? doesn have support:
local to rule with "let"

 






Using rewrite rules to 'share'
------------------------------

TODO: Katriel?
