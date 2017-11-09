# Summary of case studies

Build of Tamarin:
 - Git revision: 73593dd9747f3320384227ff086f7fca0f75c488, branch: develop
 - Compiled at: 2017-11-09 08:34:57.786964 UTC

## LAK06.spthy
Model:
 - LAK stateless (no key-chaining, abstracted away by shared nonce),
 - one pair of tag-reader
 - each tag, reader can have an unbounded number of sessions.

Property (reachability):
 - executability
 - helping lemma (secrecy of key k)
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
		 
