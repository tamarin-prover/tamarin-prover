Organization
============

 - `5G_AKA_priv.spthy`: Tamarin model of 5G-AKA for untraceability (active attacker)
 - `5G_AKA_simplified_privacy_active.spthy`: Much simplified Tamarin model of 5G-AKA for untraceability that considers only the three messages exchanged between UE and SN (active attacker)
 - `5G_AKA_passive_privacy_game.spthy`: Tamarin model of 5G-AKA for untraceability that considers the three messages exchanged between UE and SN (passive attacker)

 - `proofs/5G_AKA_priv-attack.spthy`: proof script showing the untraceability attack trace for an active attacker
 - `proofs/5G_AKA_simplified_privacy_active-attack.spthy`: proof script showing the untraceability attack trace for an active attacker in a much simplified model 
 - `proofs/5G_AKA_passive_privacy_game__*.spthy`: Three parts of the untraceability proof against a passive attacker. Due to the size of the automatically generated proof, the proof was split into these three parts. 

 - `5G_AKA.oracle`: Tamarin oracle for the proofs of `5G_AKA_simplified_privacy_active.spthy` and `5G_AKA_priv.spthy`
 - `5G_AKA_passive_privacy_game.oracle`: Tamarin oracle for the proof of `5G_AKA_passive_privacy_game.spthy`
