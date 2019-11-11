Formal Analysis and Implementation of a TPM 2.0-based Direct Anonymous Attestation Scheme
=========================================================================================

Authors:
- Liqun Chen, Surrey Centre for Cyber Security, University of Surrey
- Christoper J.P. Newton, Surrey Centre for Cyber Security, University of Surrey
- Ralf Sasse, Department of Computer Science, ETH Zurich
- Helen Treharne, Surrey Centre for Cyber Security, University of Surrey
- Stephan Wesemeyer, Surrey Centre for Cyber Security, University of Surrey
- Jorden Whitefield, Ericsson AB, Finland


These are the models associated with the paper "Formal
Analysis and Implementation of a TPM 2.0-based Direct
Anonymous Attestation Scheme" accepted to ASIACCS 2020.

The different models are contained with the following 3
folders:

1) SIGN: This folder contains the 6 models and associated
   oracles required for the sign context.

1) QUOTE: This folder contains the 6 models and associated
   oracles required for the quote PCR context.

1) CERTIFY: This folder contains the 6 models and associated
   oracles required for the certify key context.

Note that in each folder, the models dealing with the
observational equivalence security properties SP5 and SP6
can be found in a separate folder called SP5_SP6_ObsEqui.

At the top of each file containing a Tamarin model (files
with the .spthy extension), the details of how to prove it
using Tamarin are included together with the timings.

Note that all these models were proven on a server with 2
Intel (R) Xeon(R) CPU E5-2667 v3 @ 3.20GHz processeor
(16 cores/32 vCPUs) and 378GB of RAM.
