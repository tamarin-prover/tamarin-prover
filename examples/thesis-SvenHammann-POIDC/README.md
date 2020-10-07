These are the models associated with the doctoral thesis of Sven Hammann, titled "Secure, Private, and Personal: Advancing Digital Identity",
in particular with Chapter 4: "Privacy-Preserving OpenID Connect". The protocols are an extended version of those presented in asiaccs20-POIDC.
In particular, we generalize the proposal from the asiaccs20 paper by introducing a generic masking function used to compute the "private audience" field
in the id_token. This function can be instantiated in different ways to enable additional functional properties. The details are explained in the thesis.

The main directory contains the theories, and the proofs/ subdirectory contains the proven models, which can be loaded into Tamarin to reproduce the proofs we obtained.

It contains the following theories:

- OIDC_Implicit.spthy: Standard OpenID Connect implicit flow
- OIDC_CodeFlow_no_ClientSecret.spthy: Standard OpenID Connect code flow without client authentication
- OIDC_CodeFlow_with_ClientSecret.spthy: Standard OpenID Connect code flow with client authentication using a client_secret

- POIDC_H.spthy: Privacy-preserving OpenID Connect (POIDC) using public subject identifiers and a cryptographic hash function as masking function
- POIDC_enc_U.spthy: POIDC using public subject identifiers and an encryption under a user-controlled public key as masking function
- POIDC_enc_A.spthy: Privacy-preserving OpenID Connect (POIDC) using public subject identifiers and an encryption under a public key controlled by a third party, called the aggregator, as a masking function
- POIDC_CMB.spthy: Privacy-preserving OpenID Connect (POIDC) using public subject identifiers, using as masking function a concatentation of the encryptions used in enc_U and in enc_A

- Pairwise_POIDC_H.spthy: Pairwise POIDC, i.e., POIDC using _pairwise_ subject identifiers and a cryptographic hash function as masking function
- Pairwise_POIDC_enc_A.spthy: Privacy-preserving OpenID Connect (POIDC) using _pairwise_ subject identifiers and an encryption under a public key controlled by a third party, called the aggregator, as a masking function

We obtained the proofs using Tamarin version 1.4.1, git revision d2e1c57311ce4ed0ef46d0372c4995b8fdc25323, the current release version as of 23.09.2020.

The proofs were computed automatically on a server with 2 CPUs of type Intel(R) Xeon(R) E5-2650 v4 @ 2.2 GHz, 256 GB of RAM, running Ubuntu 16.04.3 LTS. 
Each CPU has 12 cores, but we limited our computation to use 10 cores only.

All proofs completed automatically without providing additional arguments, i.e., using only the standard heuristic, in the following amounts of time,
obtained by running "time tamarin-prover --prover <theory_name>.spthy":

- OIDC_Implicit.spthy: 14s
- OIDC_CodeFlow_no_ClientSecret.spthy: 34min 41s 
- OIDC_CodeFlow_with_ClientSecret.spthy: 3min 52s   
- POIDC_H.spthy: 31min 44s
- POIDC_enc_U.spthy: 31min 59s  
- POIDC_enc_A.spthy: 34min 8s   
- POIDC_CMB.spthy: 60min 42s    
- Pairwise_POIDC_H.spthy: 28min 32s 
- Pairwise_POIDC_enc_A.spthy: 29min 59s