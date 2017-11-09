# Summary of case studies

Build of Tamarin:
 - Git revision: 73593dd9747f3320384227ff086f7fca0f75c488, branch: develop
 - Compiled at: 2017-11-09 08:34:57.786964 UTC

For properties: automatically proven  by default, see precisions otherwise.

## LAK06.spthy
Model:
 - LAK stateless (no key-chaining, abstracted away by shared nonce)
 - one pair of tag-reader
 - each tag, reader can have an unbounded number of sessions

Property (reachability):
 - executability
 - helping lemma: secrecy of key k
 - injective agreement of Tag
 - injective agreement of Reader (falsified)
 
 Result:
 ==============================================================================
 summary of summaries:
 
 analyzed: build09_LAK06_3600.spthy
 
   executable (exists-trace): verified (9 steps)
   helpingSecrecy (all-traces): verified (2 steps)
   noninjectiveagreementTAG (all-traces): verified (2148 steps)
   noninjectiveagreementREADER (all-traces): falsified - found trace (13 steps)
		 
 ==============================================================================
tamarin-prover --prove build09_LAK06_3600.spthy  3094.16s user 411.29s system 2617% cpu 2:13.90 total
		 

## LAK06_state.spthy
Model:
 - LAK stateful (with key-chaining, reader stores 2 last keys, tag stores 1 last key, + key updates)
 - one pair of tag-reader
 - each tag, reader can have an unbounded number of sessions

Property (reachability):
 - helping lemma: key use implies key updates -> autoproof with oracle
 - helping lemma: keys stored are of the form h(k') -> autoproof with oracle
 - helping lemma: secrecy of stored keys -> manual proof but we get huge help from the oracle
 - executability -> manual proof (see comments on weird, additional proofs discharge)
 - injective agreement of Tag -> manual proof but we get huge help from the oracle, oracle could be improved
 - injective agreement of Reader (falsified) -> attack found automatically !!!

Note:
In a sense, the manual proofs are "semi-automatic".
Because of XOR, there are so many cases one would have to inspect (for good reasons) making fully manual proofs kind of impractical. Tamarin+Oracle is of great help here: many sub-cases are proven fully automatically. One just needs to be clever about the very high-level proof structure. That's maybe something we can explain in the paper.
