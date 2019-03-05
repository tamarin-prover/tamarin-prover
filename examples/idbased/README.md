Companion of the paper:
	Symbolic Analysis of Identity-Based Protocols.
	David Basin, Lucca Hirschi, Ralf Sasse.
	CathyFest 2019, LNCS volume (TBD). Springer, 2019.

## Reproducibility

Our analyses can be reproduced. We used Tamarin v1.5.0, compiled from develop@0df3d09fca76fd9d ([https://github.com/tamarin-prover/tamarin-prover/commit/0df3d09fca76fd9d340bd37b0151d71dea6ad106](commit)); latest version as of writing. The commands to use are:
```
tamarin-prover --prove --heuristic=O --oraclename=<oracleName> <model.spthy>
```
when an oracle is needed, and
```
tamarin-prover --prove <model.spthy>
```
otherwise. It is also possible to conduct the proofs or falsifications interactively in a browser using `interactive` instead of `--prove`.
For convenience, we also provide stored proofs and falsifications in the folder `proofs/`.


## Identity-Based Authentication Key Exchange with Session Escrow Based on Bilinear Pairing
Source: see Figure 10 from the paper. Original model: `BP_IBS_0.spthy`. Fixed model: `BP_IBS_4.spthy`.

### Modeling
**Bilinear Pairing**:
Bilinear pairing is modeled in Tamarin using the built in theory 'bilinear-pairing'.

**Private Key Generators** (Private Key Generator (PKG) = Key Generation Center (KGC)):
We model two independent KGCs (Key Generation Centers) providing two Key Escrows Setups:
 - The first one 'AUTH' is in charge of the escrow of authentication sessions. The master public key MUST be pmult(master_secret_key, 'P').
 - The second one 'SIGN' provides an identity-based PKI that will be used to verify signatures. No constraint on the master public key.
Note that the same identities will be used for both KGCs. However, security properties are conditioned by the honesty of both KGCs, because:
 - when 'SIGN' is compromised, then the attacker can impersonate any honest user
 - when 'AUTH' is compromised, then the attacker can escrow any session and learn any session key.

*Tamarin file*: the initial model corresponding the most closely to the specification we were given is `BP_IBS_0.spthy`.


### Results
We found several critical attacks on the initial protocol that defeat all of its security goals. We propose a serie of fixes and prove that the fixed protocol is secure in our model. The attacks were found automatically and the security properties were established automatically (with Tamarin). You may want to use the oracle `oracle_BP_IBS`.
We used the following command:

```
tamarin-prover --prove --heuristic=O --oraclename=oracle_BP_IBS <model.spthy>
```

#### Attack 1: Empty Share 
When Initiator chooses the share 'P', the responder builds a weak key that anyone can build knowing:
 - the public master key of 'AUTH' and
 - the responder's share.

*Implications*: All security goals of the protocol are broken (the attack on weak secrecy is not found automatically though).
*Tamarin file*: The attacks are found automatically with Tamarin from the inital model. See the attack files in `proofs/`.
*Remedies*:
It suffices for the responder to check that the initiator's share MUST be different from 'P'.
The model in the file `BP_IBS_1.spthy` implements this fix.

#### Attack 2: Confusion Attack
The signatures sent by the responder and the initiator can be confused. As a direct consequence, one can use the signature produced by an initiator that has received a dishonest shares to forge a message that is accepted by another initiator as coming from a legitimate responder.
One can use this weakness to mount attacks against secrecy of session keys and weak agreement properties for both sides.

*Implications*: All security goals of the protocol are broken.
*Taamarin file*: The attacks are found automatically with Tamarin from the (fixed) model `BP_IBS_1.spthy`. See the attack and proof files: `proofs/`.
*Remedies*: It suffices to add to the two signed messages a constant describing the role that is signing the message (i.e., 'Responder' and 'Initiator'). The model in the file `BP_IBS_2.spthy` implements this fix.

#### Attack 3: Initiator fails to commit on Responder's identity
The signed message sent by the Initiator does not contain the responder identity. Therefore, one can man in the middle an honest session between an honest initator I and an honest responder R but replacing the responder's identity R by a dishonest one D. At the end, the initiator view (myself, I, agreed on the key with D) does not match with the responder view (myself, R, has agreed with I).
This breaks weak agreement authentication property of the responder towards the initiator.

*Implications*: Basic authentication properties are broken.
*Taamarin file*: The attacks are found automatically with Tamarin from the (fixed) model `BP_IBS_2.spthy`. See the attack and proof files: `proofs/`.
*Remedies*: It suffices to add the responder's identity in the messages signed by the initiator. The model in the file `BP_IBS_3.spthy` implements this fix.

#### Similar with Responder ID: `BP_IBS_3.spthy`

#### Fixed version
The model in  `BP_IBS_4.spthy` implements all previous fixes and meets secrecy and agreement properties.


## Toy Example and Different Modelings of IBS and IBE
- `BP_ABSTRACT_IBE_toyExample.spthy` contains a modeling of our running example (Example 2) for our abstract modeling of IBE schemes (Section 4.1),
- `BP_ABSTRACT_IBS_toyExample.spthy` contains a modeling of our running example (Example 1) for our abstract modeling of IBS schemes (Section 4.1),
- `BP_PRECISE_IBE_toyExample.spthy` contains a modeling of our running example (Example 2) for our precise IBE modeling (Section 4.2),
- `badIBSmodeling_BPIBS-4-simplified.spthy` contains a simplified modeling of `BP_IBS_4.spthy` for our *flawed* precise IBS modeling based on bilinear-pairing (Section 4.2). See `proofs/badIBSmodelingAttackSecrecy_BPIBS-4-simplified.spthy` for a trace showing why our modeling is flawed.
