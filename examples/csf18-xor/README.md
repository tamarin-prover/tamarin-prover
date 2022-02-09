README
======

## Automatic prover
To run the examples, use

tamarin-prover --prove FILENAME

for the trace properties (secrecy, non-injective agreement), and

tamarin-prover --diff --prove FILENAME

for the equivalence properties (anonymity, untraceability).


## Interactive prover
To use the interactive mode, run

tamarin-prover interactive FILENAME

for the trace properties (secrecy, non-injective agreement), and

tamarin-prover --diff interactive FILENAME

for the equivalence properties (anonymity, untraceability).

and direct your browser to: http://127.0.0.1:3001


## Using oracles

For some theories an oracle is required. This is the case, when there is a file with the ".oracle" ending with the same prefix of the name. To use the oracle, first rename the appropriate oracle file to just "oracle". Then start Tamarin and give the extra parameter --heuristic=O like so:

tamarin-prover --prove --heuristic=O FILENAME


DETAILS
=======

Oracles are needed only for the chaum_offline_anonymity.spthy and
LAK06_state.spthy. For LAK06_state additional care must be taken to
analyze each lemma separately, as documented in the CSF paper in
Fig. 12. The following commands will complete the analysis for
LAK06_state:

tamarin-prover --prove=helpingUpdateKey* --heuristic=O --oraclename=LAK06_state.oracle LAK06_state.spthy

tamarin-prover --prove=helpingStackHash* LAK06_state.spthy

tamarin-prover --prove=helpingSecrecy* LAK06_state_proof-secrecy.spthy

tamarin-prover --prove=noninjectiveagreementTAG* LAK06_state_proof-nonInjectiveAgreementTag.spthy

tamarin-prover --prove=noninjectiveagreementREADER* --stop-on-trace=BFS LAK06_state.spthy
