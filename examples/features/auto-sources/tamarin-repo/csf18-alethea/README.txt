This directory contains the Tamarin files that model the protocol and the properties of the following paper:
[1] Alethea: A Provably Secure Random Sample Voting Protocol, David Basin, Sasa Radomirovic, and Lara Schmid, CSF 2018.

FILE TYPES:
----------
There are three types of files: protocol model files, proof files, and oracle files. 
Protocol files model a version of the protocol, proof files show certain finished proofs found by Tamarin, and oracle files are used as input to Tamarin, to use more efficient heuristics.

PROTOCOL MODELS:
---------------
Each protocol model file first defines which version of the protocol is tested (e.g. with an honest / corrupted server) and gives an Alice & Bob specification of the protocol it models.

Then, it contains a list of the results of the evaluation, also stating with which oracle the automated proofs succeeded.
Where we model observational equivalence, LHS and RHS denotes the lemmas' results in the left and right system, respectively.
For universal and end-to-end verifiability properties, where something must hold if the verification of the zero knowledge proof is true, we must check each possible permutation that evaluates to true. Instead of listing them all as a series of disjunctions in the precondition of one lemma, we give separate lemmas for each case. Whenever the proofs of all of these lemmas go through, the corresponding verifiability property is satisfied.

Finally, the files contain the protocol rules first and then the lemmas.
Each protocol is instantiated with a setup rule. 
We model the fact that an agent cannot perform several roles, for example a voter cannot be the same as a device, by assigning constant public variables to the agent names in the setup rule.


LIST OF ALL FILES WITH DESCRIPTION
-----------------------------------
Protocol Model Files
---------------------
- alethea_selectionphase_anonymity.spthy:
	models Alethea's selection phase with an honest server
- alethea_selectionphase_malS.spthy: 	 
	models Alethea's selection phase with a malicious server.
- alethea_votingphase_malS.spthy: 	
	models Alethea's voting phase with a malicious server.
- alethea_votingphase_malS_abstain.spthy:
	models Alethea's voting phase with a malicious server where one voter votes and one voter abstains from voting.
- alethea_votingphase_Privacy.spthy: 	
	models Alethea's voting phase with an honest server.
- alethea_votingphase_RF.spthy: 	
	models Alethea's voting phase with an honest server and a changed human role to consider receipt-freeness (see [1], Definition 12).

Proof Files
---------------
- alethea_votingphase_malS_Proof_functional.spthy: 
	the proof produced by Tamarin for "lemma functional" in the model alethea_votingphase_malS.spthy

Oracle Files
------------
- oracle_alethea_votingphase_abstain:
	the oracle file used in the proofs of alethea_votingphase_malS_abstain.spthy
- oracle_alethea_votingphase_malS:     	
	the oracle file used in the proofs of alethea_votingphase_malS.spthy
- oracle_alethea_votingphase_Privacy:
	the oracle file used in the proofs of alethea_votingphase_Privacy.spthy
- oracle_alethea_votingphase_RF:  
	the oracle file used in the proofs of alethea_votingphase_RF.spthy

PROVE THE FILES WITH TAMARIN
-----------------------------
to prove a protocol file X(=one of the Protocol Model Files) with the heuristic Y(=one of the Oracle Files), use the following command in the directory where X and Y are stored:

tamarin-prover --diff X --heuristic=o --oraclename=Y --prove

to open the same file X in interactive mode, use the following command:

tamarin-prover interactive . --diff  --heuristic=o --oraclename=Y 


For more details, we refer to the official Tamarin Manual at https://tamarin-prover.github.io/manual/




