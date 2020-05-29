
This directory contains the Tamarin files that model the protocols and the properties of 
the paper [1] "Dispute Resolution in Voting", David Basin, Sasa Radomirovic, and Lara Schmid, CSF20.


All the Tamarin proofs were successfully proved with the Tamarin prover version 1.5.1, Git revision: 5c569d9ff08e32b449a6d28acf0efe55fa2ba18b.

### FILE TYPES
There are three types of files: protocol model files, proof files, and oracle files (starting with o_). 
Protocol files model a version of a protocol, proof files show certain finished proofs found by Tamarin, and oracle files are used as input to Tamarin, to use more efficient heuristics.

### PROTOCOL MODELS
Note that, in contrast to [1], we denote the authority Auth by the "(server) S" for brevity.

The name of each protocol model file denotes (1) which protocol is analyzed and (2) under which adversary model.
(1) PRi, i ={1,2,3,4,5,6,7} refers to the seven protocols in Figures 7--13 in [1], where the same numbering is used as in [1], and mixvote refers to the protocol MixVote in Figure 15 in [1].
(2) We denote the three considered adversary models from [1] by the following shortcuts:
- ShHh denotes that the authority and the voter are honest
- ShHm denotes that the authority is honest
- SmHh denotes that the voter is honest

Each protocol model first contains a list of the results of the evaluation.
Then, the files contain the protocol specification rules first, including the channel rules, and then the lemmas.
Each protocol is instantiated with a setup rule. We model the fact that an agent cannot perform several roles, for example a voter cannot be the same as a device, by assigning constant public variables to the agent names in the setup rule.
Also, we model Assumption 1 from [1] (i.e., that honest agents and agents instantiating partially trusted agents always proceed in the protocol) by expressing a role's receive events and subsequent send events in one atomic protocol rule.

### LIST OF ALL PROTOCOL MODEL FILES WITH DESCRIPTION

#### Protocol Model Files

- PR1_ShHh.spthy: 	models the protocol Pr_1 with an honest authority and an honest voter
- PR1_ShHm.spthy: 	models the protocol Pr_1 with an honest authority and a dishonest voter
- PR1_SmHh.spthy: 	models the protocol Pr_1 with a dishonest authority and an honest voter
- PR2_ShHh.spthy: 	models the protocol Pr_2 with an honest authority and an honest voter
- PR2_ShHm.spthy: 	models the protocol Pr_2 with an honest authority and a dishonest voter
- PR2_SmHh.spthy: 	models the protocol Pr_2 with a dishonest authority and an honest voter
- PR3_ShHh.spthy: 	models the protocol Pr_3 with an honest authority and an honest voter
- PR3_ShHm.spthy: 	models the protocol Pr_3 with an honest authority and a dishonest voter
- PR3_SmHh.spthy: 	models the protocol Pr_3 with a dishonest authority and an honest voter
- PR4_ShHh.spthy: 	models the protocol Pr_4 with an honest authority and an honest voter
- PR4_ShHm.spthy: 	models the protocol Pr_4 with an honest authority and a dishonest voter
- PR4_SmHh.spthy: 	models the protocol Pr_4 with a dishonest authority and an honest voter
- PR5_ShHh.spthy: 	models the protocol Pr_5 with an honest authority and an honest voter
- PR5_ShHm.spthy: 	models the protocol Pr_5 with an honest authority and a dishonest voter
- PR5_SmHh.spthy: 	models the protocol Pr_5 with a dishonest authority and an honest voter
- PR6_ShHh.spthy: 	models the protocol Pr_6 with an honest authority and an honest voter
- PR6_ShHm.spthy: 	models the protocol Pr_6 with an honest authority and a dishonest voter
- PR6_SmHh.spthy: 	models the protocol Pr_6 with a dishonest authority and an honest voter
- PR7_ShHh.spthy: 	models the protocol Pr_7 with an honest authority and an honest voter
- PR7_ShHm.spthy: 	models the protocol Pr_7 with an honest authority and a dishonest voter
- PR7_SmHh.spthy: 	models the protocol Pr_7 with a dishonest authority and an honest voter
- mixvote_ShHh.spthy: 	models the protocol MixVote with an honest authority and an honest voter
- mixvote_ShHm.spthy: 	models the protocol MixVote with an honest authority and a dishonest voter
- mixvote_SmHh.spthy:	models the protocol MixVote with a dishonest authority and an honest voter
- mixvote_ShHh_RF.spthy:models the protocol MixVote with an honest server and a changed human role to consider receipt-freeness (see [1], Definition 14)
- mixvote_ShHh_RF_reuseAsRestriction.spthy:*
			models the protocol MixVote with an honest server and a changed human role to consider receipt-freeness (see [1], Definition 14)

\* Tamarin allows the use of "reuse lemmas", i.e., lemmas labeled with [reuse]. These lemmas are such that other lemmas can use their statements, however they do not just assume that the stated property holds, as the reuse-lemmas are also proven correct.
The files mixvote_ShHh_RF.spthy and mixvote_ShHh_RF_reuseAsRestriction.spthy model the same protocol under the same adversary model. The only difference is that the reuse lemmas in mixvote_ShHh_RF.spthy are modeled as restrictions in mixvote_ShHh_RF_reuseAsRestriction.spthy. 
We proved all reuse lemmas as well as lemmas in mixvote_ShHh_RF.spthy, except for observational equivalence which we proved in mixvote_ShHh_RF_reuseAsRestriction.spthy. 
As we proved in the former that all reuse lemmas hold, we can safely use them as restrictions in the latter (the reuse lemmas and restrictions exclude the same set of traces), which helps in proving the observational equivalence property.

#### Proof Files

- mixvote_ShHh_RF_functionalLHS.spthy:
	the proof produced by Tamarin for "lemma functional" in the model mixvote_ShHh_RF.spthy, in the left system when using the diff-mode
- mixvote_ShHh_RF_functionalRHS.spthy:
	the proof produced by Tamarin for "lemma functional" in the model mixvote_ShHh_RF.spthy, in the right system when using the diff-mode

#### Oracle Files

- o_mixvote_ShHh: 	the oracle file used in the proofs of mixvote_ShHh.spthy
- o_mixvote_ShHm: 	the oracle file used in the proofs of mixvote_ShHm.spthy
- o_mixvote_SmHh: 	the oracle file used in the proofs of mixvote_SmHh.spthy
- o_mixvote_ShHh_RF: 	the oracle file used in the proofs of mixvote_ShHh_RF.spthy and mixvote_ShHh_RF_reuseAsRestriction.spthy

### PROVING THE FILES WITH TAMARIN

In almost all protocol files, all properties can be automatically proven by Tamarin.
The only exception is the functional property in the model mixvote_ShHh_RF.spthy, which we proved by hand and whose proof we provide in the proof files.

#### Proving the protocol files: 

- for all files starting with PR, to prove the protocol file P(=one of the Protocol Model Files)'s lemma L(=one of the Lemmas in P), use the following command in the directory where P is stored:

    ```
    tamarin-prover P --prove=L
    ```

- to open the same file P in interactive mode, use the following command:

    ```
    tamarin-prover interactive . 
    ```

- for all files starting with mixvote, except those including _RF, to prove the protocol file P(=one of the Protocol Model Files)'s lemma L(=one of the Lemmas in P), with the heuristic H(=one of the Oracle Files), use the following command in the directory where P and H are stored. 
(For P=X.spthy for some name X, the oracle named H=o_X should be used.)

    ```
    tamarin-prover P --heuristic=O --oraclename=H --prove=L
    ```

- to open the same file P in interactive mode, use the following command:

    ```
    tamarin-prover interactive . --heuristic=O --oraclename=H
    ```
    
- for all files starting with mixvote and including _RF, to prove the protocol file P(=one of the Protocol Model Files)'s lemma L(=one of the Lemmas in P), use the following command in the directory where P and H are stored:

    ```
    tamarin-prover P --diff --heuristic=O --oraclename=o_mixvote_ShHh_RF --prove=L
    ```

- to open the same file P in interactive mode, use the following command:

    ```
    tamarin-prover interactive . --diff --heuristic=O --oraclename=o_mixvote_ShHh_RF
    ```


For more details, we refer to the official Tamarin Manual at https://tamarin-prover.github.io/manual/



