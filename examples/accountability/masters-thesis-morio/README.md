# Master's Thesis: Verifying Accountability for Unbounded Sets of Participants

This is the artifact for the Master's thesis *Verifying Accountability for Unbounded Sets of Participants* by Kevin Morio.

## Models

```
.
├── CentralizedMonitor.spthy
├── OCSPS-untrusted.spthy
├── OCSPS.spthy
└── WhoDunit.spthy
```

The models were ported from [Künnemann et al. (2019)](https://doi.org/10.1109/CSF.2019.00034) to the new implementation presented in the thesis.

### Changes to the original version

The models have been adapted to the new SAPiC semantic in November 2023.
The tactic feature is now used for the OCPS models to speed up the verification.
