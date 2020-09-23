This directory contains the Tamarin models of the following thesis:
[1] Advancing the Formal Foundations for Voting Protocols, Lara Schmid, ETH Zürich, 2020.

The directory consists of three sub-directories, respectively containing the Tamarin files that model the protocols and the properties of Chapters 3 to 5 in [1]. 
All files have been modeled by Lara Schmid and were successfully proved with the Tamarin prover version 1.5.1, Git revision: 1b68093f5d9c98771e71daea8befdd345387ae32


We first describe some notation and other conventions, then we list all the files in each sub-directory, and finally we describe how the protocols can be proven using Tamarin.
As the models of the phone-based authentication protocols from Section 5.3 [1] require different explanations, they are in a separate folder [chapter5_HumanErrors/AuthenticationProtocols](chapter5_HumanErrors/AuthenticationProtocols) together with a [README](chapter5_HumanErrors/AuthenticationProtocols/README.md) file explaining these protocols.


### NOTATION / CONVENTIONS


#### File Types

There are three types of files: protocol model files, proof files, and oracle files (starting with o_). 
Protocol files model a version of a protocol, proof files show certain finished proofs found by Tamarin, and oracle files are used as input to Tamarin, to use more efficient heuristics.

We use the following conventions:

- When using the shortcuts ShHh, ShHm, and SmHh, we mean the three considered adversary models from Definition 22 [1]:
   - ShHh denotes that the server/authority and the voter are honest
   - ShHm denotes that the server/authority is honest and the voter is dishonest
   - SmHh denotes that the server/authority is dishonest and the voter is honest 

- Each proof file and oracle file is associated with a protocol model file:
   - a proof file that proves lemma L for the protocol model file P.spthy, is denoted by P_A.spthy
   - an oracle file that should be used in the proofs of a protocol model file P.spthy, is denoted by o_P

#### Protocol Model Files

Each protocol model first contains a list of the results of the evaluation.
Then, the files contain the protocol rules first, including the channel rules (and the untrained human rules for the human error models), and then the lemmas.
Each protocol is instantiated with a setup rule. 

In the voting protocols for which we only model one instantiation of the setup, we often model the fact that an agent cannot perform several roles, for example a voter cannot be the same as a device, by assigning constant public variables to the agent names in the setup rule.

In contrast to the thesis, some variables, functions, and signals are denoted by a slightly different name. We list here the most important ones:

- We often use the term sskX to refer to the signing key of agent X, spkX to refer to the corresponding verification key, eskX to refer to the private decryption key of X, and epkX to refer to the corresponding public encryption key ('s' stands for signing and 'e' for encryption).

- We denote the terms in (all variants of) Alethea that consist of the ballots but without signatures by 'bPrime', which corresponds to the term '\tilde(b)' in [1].

- We use constants to distinguish different messages that are written to and read from the bulletin board.
Thereby, we use both the constant 'b' and 'bs' to denote the ballots (similarly with 'v' and 'vs' for the votes and with other terms). Especially, when modeling human errors, we often need the tag 'b' to refer to one ballot of H and thus we use 'bs' as the tag for the list of ballots (corresponding to ['b'] in [1]).  

- We use the function verzkp() to denote the function Ver_zk() from the thesis.

- In protocol model files involving fallible humans, we often use the signal H(H) in all untrained human rules instantiated by the human agent H and H_role(H) in all agent rules instantiated by H. Together, they model the signal Hact(H) from [1].

- We model the fact AgSt(A,C,i) from [1] in Tamarin by the fact AgSt_C(), where the state C that an agent is at is part of the name. This allows for faster proofs in Tamarin.


### LIST OF FILES WITH DESCRIPTION IN [chapter3_Alethea/](chapter3_Alethea)

#### Protocol Model Files

- alethea_sel_ShHh.spthy:
 	models Alethea's selection phase with 2 voters where 1 is selected,
	with an honest server
- alethea_sel_SmHh.spthy: 	
	models Alethea's selection phase with 2 voters where 1 is selected,
	with a dishonest server
- alethea_sel_ShHh_A.spthy:	
	models Alethea's selection phase with 2 voters where 1 is selected,
	with an honest server, in a simplified model to show anonymity
- alethea_vot_ShHh.spthy:	
	models Alethea's voting phase with 2 voters who both vote, 
	with an honest server
- alethea_vot_SmHh.spthy:	
	models Alethea's voting phase with 2 voters who both vote, 		
	with a dishonest server
- alethea_vot_ShHh_RF.spthy:	
	models Alethea's voting phase with 2 voters who both vote, 
	with an honest server, with a changed human role to model receipt-freeness
- alethea_vot_abst_ShHh.spthy:	
	models Alethea's voting phase with 1 voter who abstains,
	with an honest server
- alethea_vot_abst_SmHh.spthy:	
	models Alethea's voting phase with 1 voter who abstains,
	with a dishonest server

- aletheaD_sel_ShHh.spthy: 	
	models Alethea-D's selection phase with 2 voters where 1 is selected,
	with an honest server
- aletheaD_sel_SmHh.spthy:		
	models Alethea-D's selection phase with 2 voters where 1 is selected,
	with a dishonest server
- aletheaD_sel_ShHh_A.spthy:  	
	models Alethea-D's selection phase with 2 voters where 1 is selected,
	with an honest server, in a simplified model to show anonymity
- aletheaD_vot_ShHh.spthy:		
	models Alethea-D's voting phase with 2 voters who both vote, 
	with an honest server
- aletheaD_vot_SmHh.spthy:		
	models Alethea-D's voting phase with 2 voters who both vote,
	with a dishonest server
- aletheaD_vot_ShHh_RF.spthy:		
	models Alethea-D's voting phase with 2 voters who both vote, 
	with an honest server, with a changed human role to model receipt-freeness

#### Proof Files

- alethea_vot_ShHh_RF_functional.spthy:
	the proof produced by Tamarin for "lemma functional" in the model alethea_vot_ShHh_RF.spthy
- alethea_vot_SmHh_functional.spthy:
	the proof produced by Tamarin for "lemma functional" in the model alethea_vot_SmHh.spthy
- aletheaD_vot_ShHh_functional.spthy:
	the proof produced by Tamarin for "lemma functional" in the model aletheaD_vot_ShHh.spthy
- aletheaD_vot_ShHh_RF_functional.spthy:
	the proof produced by Tamarin for "lemma functional" in the model aletheaD_vot_ShHh_RF.spthy
- aletheaD_vot_SmHh_functional.spthy
	the proof produced by Tamarin for "lemma functional" in the model aletheaD_vot_SmHh.spthy

#### Oracle Files

- o_alethea_vot_ShHh:	the oracle file used in the proofs of alethea_vot_ShHh.spthy
- o_alethea_vot_ShHh_RF:the oracle file used in the proofs of alethea_vot_ShHh_RF.spthy
- o_alethea_vot_SmHh:	the oracle file used in the proofs of alethea_vot_SmHh.spthy
- o_aletheaD_sel_ShHh_A:the oracle file used in the proofs of aletheaD_sel_ShHh_A.spthy	
- o_aletheaD_vot_ShHh: 	the oracle file used in the proofs of aletheaD_vot_ShHh.spthy
- o_aletheaD_vot_ShHh_RF:the oracle file used in the proofs of aletheaD_vot_ShHh_RF.spthy
- o_aletheaD_vot_SmHh:	the oracle file used in the proofs of aletheaD_vot_SmHh.spthy



### LIST OF FILES WITH DESCRIPTION IN [chapter4_DisputeResolution/](chapter4_DisputeResolution)

#### Protocol Model Files

- aletheaDR_ShHh.spthy: 		
	models Alethea-DR with 1 voter who votes, with an honest server and an honest voter
- aletheaDR_SmHh.spthy:
	models Alethea-DR with 1 voter who votes, with a dishonest server and an honest voter
- aletheaDR_ShHm.spthy:
	models Alethea-DR with 1 voter who votes, with an honest server and a dishonest voter
- aletheaDR_ShHh_RF.spthy:	
	models Alethea-DR with 2 voters who both vote, with an honest server and an honest but
	changed human role to consider receipt-freeness	
- aletheaDR_ShHh_RF_reuseAsRestriction.spthy:*
	models Alethea-DR with 2 voters who both vote, with an honest server and an honest but
	changed human role to consider receipt-freeness	

- PR1_ShHh.spthy: models the protocol Pr_1 with an honest authority and an honest voter
- PR1_ShHm.spthy: models the protocol Pr_1 with an honest authority and a dishonest voter
- PR1_SmHh.spthy: models the protocol Pr_1 with a dishonest authority and an honest voter
- PR2_ShHh.spthy: models the protocol Pr_2 with an honest authority and an honest voter
- PR2_ShHm.spthy: models the protocol Pr_2 with an honest authority and a dishonest voter
- PR2_SmHh.spthy: models the protocol Pr_2 with a dishonest authority and an honest voter
- PR3_ShHh.spthy: models the protocol Pr_3 with an honest authority and an honest voter
- PR3_ShHm.spthy: models the protocol Pr_3 with an honest authority and a dishonest voter
- PR3_SmHh.spthy: models the protocol Pr_3 with a dishonest authority and an honest voter
- PR4_ShHh.spthy: models the protocol Pr_4 with an honest authority and an honest voter
- PR4_ShHm.spthy: models the protocol Pr_4 with an honest authority and a dishonest voter
- PR4_SmHh.spthy: models the protocol Pr_4 with a dishonest authority and an honest voter
- PR5_ShHh.spthy: models the protocol Pr_5 with an honest authority and an honest voter
- PR5_ShHm.spthy: models the protocol Pr_5 with an honest authority and a dishonest voter
- PR5_SmHh.spthy: models the protocol Pr_5 with a dishonest authority and an honest voter
- PR6_ShHh.spthy: models the protocol Pr_6 with an honest authority and an honest voter
- PR6_ShHm.spthy: models the protocol Pr_6 with an honest authority and a dishonest voter
- PR6_SmHh.spthy: models the protocol Pr_6 with a dishonest authority and an honest voter
- PR7_ShHh.spthy: models the protocol Pr_7 with an honest authority and an honest voter
- PR7_ShHm.spthy: models the protocol Pr_7 with an honest authority and a dishonest voter
- PR7_SmHh.spthy: models the protocol Pr_7 with a dishonest authority and an honest voter

 \* Tamarin allows the use of "reuse lemmas", i.e., lemmas labeled with [reuse]. These lemmas are such that other lemmas can use their statements, however they do not just assume that the stated property holds, as the reuse-lemmas are also proven correct. The files aletheaDR_ShHh_RF.spthy and aletheaDR_ShHh_RF_reuseAsRestriction.spthy model the same protocol under the same adversary model. The only difference is that the reuse lemmas in aletheaDR_ShHh_RF.spthy are modeled as restrictions in aletheaDR_ShHh_RF_reuseAsRestriction.spthy. We proved all reuse lemmas as well as lemmas in aletheaDR_ShHh_RF.spthy, except for observational equivalence which we proved in aletheaDR_ShHh_RF_reuseAsRestriction.spthy. As we proved in the former that all reuse lemmas hold, we can safely use them as restriction in the latter (the reuse lemmas and restrictions exclude the same set of traces), which helps in proving the observational equivalence property.

#### Proof Files

- aletheaDR_ShHh_RF_functional_LHS.spthy: 
	the proof produced by Tamarin for "lemma functional" in the model aletheaDR_ShHh_RF.spthy,
	in the left system when using the diff-mode
- aletheaDR_ShHh_RF_functional_RHS.spthy:
	the proof produced by Tamarin for "lemma functional" in the model aletheaDR_ShHh_RF.spthy,
	in the right system when using the diff-mode

#### Oracle Files

- o_aletheaDR_ShHh:	the oracle file used in the proofs of aletheaDR_ShHh.spthy
- o_aletheaDR_ShHh_RF:	the oracle file used in the proofs of aletheaDR_ShHh_RF.spthy
- o_aletheaDR_ShHm:	the oracle file used in the proofs of aletheaDR_ShHm.spthy
- o_aletheaDR_SmHh:	the oracle file used in the proofs of aletheaDR_SmHh.spthy


### LIST OF FILES WITH DESCRIPTION IN [chapter5_HumanErrors/](chapter5_HumanErrors/)

- AuthenticationProtocol/:
	this directory contains all Tamarin files that model the different authentication protocols analyzed in Section 5.3. We refer to AuthenticationProtocol/README.txt for more details.

#### Protocol Model Files

- aletheaD_vot_HE_ShHh.spthy:
	models Alethea-D's voting phase with 1 voter who votes, with human errors,
	with an honest server	
- aletheaD_vot_HE_SmHh:
	models Alethea-D's voting phase with 1 voter who votes, with human errors,
	with a dishonest server
- HPagree.spthy:
	models the protocol HPagree from Example 7


### PROVING THE FILES WITH TAMARIN

In almost all protocol files, all properties can be automatically proven by Tamarin.
The only exception are some functional properties, which we proved by hand and whose proof we provide in a proof files (see proof files listed above).

#### Proving the protocol files: 

In all of the following cases, when X is a name, in all proofs concerning a protocol model P=X.spthy, use oracle H=o_X. If no such oracle exists, omit "--heuristic=O --oraclename=H" in the following instructions.

* for all protocol files P ending in _RF or _A, proceed as follows: 
    To prove the protocol file P(=one of the Protocol Model Files)'s lemma L(=one of the Lemmas in P), with the heuristic H(=one of the Oracle Files), use the following command in the directory where P and H are stored.

    ```
    tamarin-prover P --diff --heuristic=O --oraclename=H --prove=L
    ```

* to open the same file P in interactive mode, use the following command:

    ```
    tamarin-prover interactive . --diff --heuristic=O --oraclename=H
    ```

* for all other protocol files, proceed as follows: To prove the protocol file P(=one of the Protocol Model Files)'s lemma L(=one of the Lemmas in P), with the heuristic H(=one of the Oracle Files), use the following command in the directory where P and H are stored.

    ```
    tamarin-prover P --heuristic=O --oraclename=H --prove=L
    ```

* to open the same file P in interactive mode, use the following command:

    ```
    tamarin-prover interactive . --heuristic=O --oraclename=H
    ```

* for all protocol files P used with the human error model (i.e., in the directory chapter5_HumanErrors/), proceed as follows: To prove the protocol file P(=one of the Protocol Model Files)'s lemma L(=one of the Lemmas in P), with the human model HM(=infallible, =untrained or =ruleBased), use the following command in the directory where P is stored:

    ```
    tamarin-prover P --prove=L -D=HM
    ```

* to open the same file P in interactive mode, use the following command:

    ```
    tamarin-prover interactive . -D=HM 
    ```

For more details, we refer to the official Tamarin Manual at https://tamarin-prover.github.io/manual/

