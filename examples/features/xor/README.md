# OBSOLETE!

Everything in this folder (except 'basicfunctionality') is obsolete,
for current versions see the folder examples/csf18-xor instead!

# Summary of case studies

Build of Tamarin:
 - Git revision: 73593dd9747f3320384227ff086f7fca0f75c488, branch: develop
 - Compiled at: 2017-11-09 08:34:57.786964 UTC

For properties: automatically proven by default, see precisions otherwise.

## Reachability properties

### LAK06.spthy
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


### LAK06_state.spthy
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

## Equivalence Properties

### CH07-untrac-weak.spthy
Model:
 - CH07 with only one pair of Tag-Reader (stateless as in the spec)
 - each agent can play at most one session --> finite scenario

Property: weak UK of tag:
 - two tages T1 T2 in a guessing phase
 - one tag T_i in the learning phase, i=1 on the left and i=2 on the right.
 - No restriction to implement phases as the property can be proven without it (see comments in the file).

 ==============================================================================
 summary of summaries:

 analyzed: CH07-untrac-weak_checkingProof.spthy
   [...]
   DiffLemma:  Observational_equivalence : verified (3118 steps)

 ==============================================================================
 ~/.local/bin/tamarin-prover --prove=Observ*  --diff +RTS -N14 -RTS  675.47s user 109.34s system 906% cpu 1:26.59 total
