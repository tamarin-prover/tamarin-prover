Privacy-Preserving OpenID Connect
=========================================================================================

Authors:
- Sven Hammann, Department of Computer Science, ETH Zurich
- Ralf Sasse, Department of Computer Science, ETH Zurich
- David Basin, Department of Computer Science, ETH Zurich

These are the models associated with the paper "Privacy-Preserving OpenID Connect" 
accepted to ASIACCS 2020.

The main directory contains the theories, and the proofs/ subdirectory
contains the proven models, which can be loaded into Tamarin to reproduce
the proofs we obtained.

It contains the following theories:

OIDC_Implicit.spthy: Standard OpenID Connect implicit flow
OIDC_CodeFlow_no_ClientSecret.spthy: Standard OpenID Connect code flow without client authentication
OIDC_CodeFlow_with_ClientSecret.spthy: Standard OpenID Connect code flow with client authentication using a client_secret

POIDC.spthy: POIDC using public subject identifiers
POIDC_pairwise.spthy: Pairwise POIDC, i.e., POIDC using pairwise subject identifiers

We obtained the proofs using Tamarin version 1.4.1, git revision d2e1c57311ce4ed0ef46d0372c4995b8fdc25323.