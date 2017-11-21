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
