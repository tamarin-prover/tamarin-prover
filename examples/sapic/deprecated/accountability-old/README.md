This directory contains the Tamarin models of the following paper:
[1] "Automated Verification of Accountability in Security Protocols", Robert Künnemann, Ilkan Esiyok, and Michael Backes, CSF19.

## Verification

The translation of the accountability lemmas is done by the now deprecated [SAPiC plugin](https://github.com/tamarin-prover/tamarin-prover/tree/develop/plugins/sapic).
If the `sapic` binary is not available, it can be built by `make sapic`.

The `.sapic` files can then be translated to `.spthy` files and analyzed by Tamarin:

```
sapic <filename>.sapic > <filename>.spthy
tamarin-prover <filename>.spthy
```

## Deprecated Notice

The accountability implementation was superseded by a new implementation presented in the following paper:
[2] "Verifying Accountability for Unbounded Sets of Participants", Kevin Morio, and Robert Künnemann, CSF21.

The following models in this directory have been ported to the new implementation which can be found [here](https://github.com/tamarin-prover/tamarin-prover/tree/develop/examples/accountability/csf21-acc-unbounded/previous):

- (./CertificateTransparency_extended.sapic)
- (./OCSPS.sapic)
- (./WhoDunit_Fixed.sapic)
