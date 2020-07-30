Analysis of 5G-AKA
==================

Organization
------------

 - `5G-AKA-nonBindingChannel`: analysis of 5G-AKA as specified in TS 33.501 v15.0.0. We also give a model implementing our fix (see Section 5.3.3).
 - `5G-AKA-bindingChannel`: analysis of 5G-AKA as specified in TS 33.501 v15.0.0, with the additional assumption that the channel between SN and HN is binding.  We also give a model implementing our fix (see Section 5.3.3).
 - `5G-AKA-untraceability`: privacy analysis of 5G-AKA.

How to reproduce the results (authentication and secrecy properties)
--------------------------------------------------------------------

This analysis uses version 1.4.0 of the [Tamarin-prover](https://github.com/tamarin-prover/tamarin-prover). Instructions for the installation and usage can be found in chapter 2 of the [manual](https://tamarin-prover.github.io/manual/book/002_installation.html).


Due to the complexity of the proofs, oracle files that guide the proof search are required. These files need to be passed as argument as shown below:
```
$ tamarin-prover interactive --heuristic=O --oraclename=5G_AKA.oracle .
```
Once an interactive Tamarin session is launched, one can select and load the appropriate Tamarin file (`5G_AKA.spthy`) and navigate through the model and the different lemmas.

Lemmas that are annotated (in the Tamarin models) with `proof (automatic)` or `attack (automatic)` can be proven (or disproven) automatically using our oracle (clicking 'a'). Lemmas that are annotated with `attack (stored)` cannot be disproven automatically, due to a bug in the Tamarin-prover. This bug forces the user to carry out the proof in the interactive mode (see below) and to click '1' until the attack is found. We both provide an oracle that allows to semi-automatically find the attack this way (oracle automatically selects the goal that should be solved first at each step of the proof), and stored proofs that can be used to quickly see and check our attacks.

The stored attack can be reloaded with the tool. Corresponding proof scripts are provided in `5G-AKA-nonBindingChannel/proofs` and `5G-AKA-bindingChannel/proofs`. For loading, e.g., the lemma `noninjectiveagreement_seaf_ue_kseaf_keyConf_noRev`, the following command can be used:
```
$ tamarin-prover interactive --heuristic=O --oraclename=5G_AKA.oracle proofs/5G_aka_attack_noninjectiveagreement_seaf_ue_kseaf_keyConf_noRev.spthy	
```
The following command automatically verifies that the stored proof is complete and valid (without showing the attack trace):	
```
$ tamarin-prover --heuristic=O --oraclename=5G_AKA.oracle proofs/5G_aka_attack_noninjectiveagreement_seaf_ue_kseaf_keyConf_noRev.spthy
```


How to reproduce the results (privacy)
--------------------------------------

The untraceability property is modeled as an observational equivalence property and therefore relies on the *diff-equivalence mode* of Tamarin. The command that should be used is:
```
$ tamarin-prover interactive --heuristic=O --oraclename=5G_AKA.oracle --diff .
```

The lemma stating observational equivalence is called "Observational_equivalence". For the active attack, the attack traces (on the full model and on a simplified model) are stored in proof scripts `5G-AKA-untraceability/proofs/5G_AKA_*-attack.spthy` and the corresponding models are in `5G-AKA-untraceability/5G_AKA_*.spthy`. 

For the passive adversary model, the proof of untraceability is split across three files `5G-AKA-untraceability/proofs/` and the corresponding model is in `5G-AKA-untraceability/5G_AKA_passive_privacy_game.spthy`. The proof can be found automatically using the oracle `5G_AKA_passive_privacy_game.oracle`. The command that should be used is:
```
$ tamarin-prover interactive --heuristic=O --oraclename=5G_AKA_passive_privacy_game.oracle --diff .
```
