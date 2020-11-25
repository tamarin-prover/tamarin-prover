See ../README.md for an overview. All files in this folder must be
opened by Tamarin with the option "--diff" used. All files not
mentioned below can be proven as usual with --prove --diff used
without any extra arguments.


DETAILS
=======

Extra care must be taken for CH07 property UK3, to only run the
diff-equivalence by itself:

tamarin-prover --prove=Observ* --diff CH07-UK1.spthy


For KCL07 BFS must be used for property UK1. For property UK3 the
stored attack must be loaded without the parameter --prove.

tamarin-prover --prove --diff --stop-on-trace=BFS KCL07-UK1.spthy

tamarin-prover         --diff KCL07-UK3_attack.spthy



For OTYT06 for UK1 the file must be loaded in interactive mode, the lemma Observational_equivalence must be opened, after one step the goal Rule_equality needs to be chosen, and after the next step one is automatically in the LHS goal, on which the autoprover can be started. (For UK3 a 'nicer' attack is found by following these steps, but a basic attack is found without.) Alternatively, the stored proofs can be loaded without --prove:

tamarin-prover interactive --diff OTYT06*

tamarin-prover --diff OTYT06_UK1_proof.spthy

tamarin-prover --diff OTYT06_UK3_proof.spthy
