# Automated Security Analysis of Exposure Notification Systems

## Authors

- Kevin Morio, *CISPA Helmholtz Center for Information Security*
- Ilkan Esiyok, *CISPA Helmholtz Center for Information Security*
- Dennis Jackson, *Mozilla*
- Robert Künnemann, *CISPA Helmholtz Center for Information Security*

The paper has been accepted for *USENIX Security '23*.

## Preprint

A preprint of the full version of the paper is available on arXiv: [2210.00649](https://arxiv.org/abs/2210.00649)

## Models

### CWA (`cwa.spthy`)

This is a model of a modified DP-3T design 1 following the CWA proposal with Google/Apple-style keys and authorisation scheme 3 (device bound authorisation).

- Run as `tamarin-prover --prove cwa.spthy` in the terminal for automated mode,
- Run as `tamarin-prover interactive cwa.spthy` for interactive mode.

The oracle `oracle-cwa` is directly imported by the model.

### DP3T (`dp3t.spthy`)

This is a model of DP-3T design 3 with authorisation scheme 3 (device bound authorisation).

- Run as `tamarin-prover --prove dp3t.spthy` in the terminal for automated mode,
- Run as `tamarin-prover interactive dp3t.spthy` for interactive mode.

The oracle `oracle-dp3t` is directly imported by the model.

## ROBERT (`robert.spthy`)

This is a model of ROBERT (ROBust and privacy-presERving proximity Tracing) / TousAntiCovid.

- Run as `tamarin-prover --prove robert.spthy` in the terminal for automated mode,
- Run as `tamarin-prover interactive robert.spthy` for interactive mode.

The oracle `oracle-robert` is directly imported by the model.

