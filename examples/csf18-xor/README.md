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
