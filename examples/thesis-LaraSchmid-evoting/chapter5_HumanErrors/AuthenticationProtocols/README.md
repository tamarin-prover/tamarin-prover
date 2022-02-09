This directory contains the Tamarin models of the different authentication protocols analyzed in Section 5.3. of the following thesis:
[1] Advancing the Formal Foundations for Voting Protocols, Lara Schmid, ETH Zürich, 2020.

As these Tamarin files were modeled for the CSF 2016 paper "Modeling Human Errors in Security Protocols", they are 1) modeled in an old version of Tamarin and 2) contain some optimizations for analyzing protocols with human errors that slightly deviate from the notation used in [1] (as in [1] we aimed for consistent notation in all chapters).
We first present some of most important differences and then list all the files. 

### DIFFERENCES TAMARIN VERSION AND HUMAN ERROR OPTIMIZATIONS

1. Old Tamarin version:

    We stress that even though the files have been modeled in an old version of Tamarin, they can be and were successfully proved with the Tamarin prover version 1.5.1.
    Nevertheless, the files contain some old keywords, which are still supported by Tamarin but have been renamed in the new versions.
    - The keyword "axiom" is the older version of what is now called "restriction"
    - When executing Tamarin for rule-based voters, the current version of Tamarin often issues a warning similar to the following one:

    ```
    ****************************************************
    WARNING: the following wellformedness checks failed!

    Restriction actions:
        restriction `noTell' references action 
          (ProtoFact Linear "Rule3" 3,3,Linear)
        but no rule has such an action.
    *****************************************************
    ```
    Such warnings were not issued in the old version of Tamarin and can safely be ignored as they just mean that certain guidelines will not take effect (see first point in 2.)

2. Optimizations for the human error model:

      - As with the untrained-human rules, the models aim to use the same set of guidelines (which used to be called "rules") for all protocols. Therefore, all considered guidelines are always imported into the Tamarin theory and the "active" guidelines are selected by signals in the setup rule. Thereby, the different guidelines are not distinguished by different signals (i.e., by different names) but by arguments in the signals Rule3 or Rule4.
    (The cause for the warning mentioned in 1) are the guidelines that are imported but are not activated.)

    - To facilitate referring to the human accessible subterms that are contained in a sent or received message, a separate signal Send(H,t,m) (respectively Receive(H,t,m)) is recorded for each such subterm. Whereas the message's tag t is listed as a separate argument in these signals, the signals do not record the intended communication partners. 
        In the relevant cases, the intended communication partner A is denoted in one of the signals To(A) or From(A).

    - Similarly, the facts In_l(A,B,t,m) and Out_l(A,B,t,m) have four arguments, denoting a message's sender (A), recipient (B), tag (t) and value (m), as tags are always needed in the communication with humans.
        If two non-human agents A and B communicate with each other, the tag t (called label l in the theories) can be chosen arbitrarily as long as it is consistent in A and B.

    - We use the signal H(H) in untrained human rules instantiated by the human agent H (in contrast to the signal Untrained(H) used in other files) and H_role(H) in all agent rules instantiated by H (in contrast to Infallible(H)). These signals are collectively denoted by Hact(H) in [1].

    - The signal D(D) denotes the signal Dact(D) from [1], which records that the device D is active.

    - The signal Sstart(S) denotes the signal FirstStep(S) from [1].

### LIST OF FILES

#### File types

There are two types of files: protocol model files and oracle files (starting with o_). 
Protocol files model a version of a protocol and oracle files are used as input to Tamarin, to use more efficient heuristics.

#### Protocol Model Files

The protocols can be analyzed with respect to infallible, rule-based or untrained types of humans (see below).

Each protocol model contains the following parts:

1. A list of the results of the evaluation..
2. Axioms that select the proper set of rules for the considered type of human.
3. The untrained-human rules.
4. The channel rules.
5. The setup and agent rules.
6. Axioms specifying the guidelines for rule-based humans.
7. Axioms stating further assumptions (documented in the .spthy file). 
8. The lemmas stating the analyzed security properties.

Parts 3., 4., and 6. are identical in all files (although 6. is omitted in some files where it is not needed).

#### List of all protocol model files with description

File		|	Protocol Name in Paper 		| Analyzed Property
--------|---------------------------|-------------------------------------------------------------
Cronto_EA.spthy			|Cronto|				Entity and Device Authentication	
Cronto_MA.spthy			|Cronto_MA|			Message Authentication
Google2Step_EA.spthy		|Google 2-Step|			Entity and Device Authentication	
Google2Step_MA.spthy		|Google 2-Step|			Message Authentication
MPAuth_EA.spthy			|MP-Auth| 			Entity and Device Authentication	
MPAuth_MA.spthy			|MP-Auth_MA|			Message Authentication	
MPAuth_MA_NoTellExceptOK.spthy	|MP-Auth_MA|			Func_Commit (for Lemma 55 in [1])
MPAuth_MA_NoTellOK.spthy	|MP-Auth_MA|			Func_Commit (for Lemma 53 in [1])
MPAuth_VC.spthy			|MP-Auth_VC|			Message Authentication	
OTPOverSMS_EA.spthy		|OTP over SMS|			Entity and Device Authentication
OTPOverSMS_MA.spthy		|OTP over SMS|			Message Authentication	
Phoolproof_EA.spthy		|Phoolproof|			Entity and Device Authentication
Phoolproof_MA.spthy		|Phoolproof|			Message Authentication	
Soundproof_EA.spthy		|Sound-Proof|			Entity and Device Authentication

#### Oracle Files

- o_MPAuth_VC: 		the oracle file used in the proofs of MPAuth_VC.spthy
- o_Phoolproof_MA: 	the oracle file used in the proofs of Phoolproof_MA.spthy

All other models can automatically be proven without an oracle.
   


