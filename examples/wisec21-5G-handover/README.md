# Tamarin Models of 5G Handovers
In 5G networks, a handover protocol is used to transfer a User Equipment (UE), such as a mobile phone, from one Radio Access Network (RAN) to another. It can also be used as a fallback method to transfer a UE from a 5G to a 4G network (or vice versa).  

This directory contains four [Tamarin](https://tamarin-prover.github.io/) models of 5G handover protocols - two inter, and two intra-system variations.

## Structure
```bash
models
├── inter-5G
│   ├── 5GS_to_EPS_over_N26
│   │   ├── 5G_handover.oracle    # Oracle
│   │   └── 5G_handover.spthy     # 5GS to EPS handover over N26
│   └── EPS_to_5GS_over_N26
│       ├── 5G_handover.oracle    # Oracle
│       └── 5G_handover.spthy     # EPS to 5GS handover over N26
├── intra-5G
│   ├── n2
│   │   ├── 5G_handover.oracle    # Oracle
│   │   └── 5G_handover.spthy     # N2-based inter NG-RAN handover
│   └── xn
│       ├── 5G_handover.oracle    # Oracle
│       └── 5G_handover.spthy     # Xn-based inter NG-RAN handover
└── README.md
```

## Reproducing The Results
The models have been tested with version 1.5.1 (git revision: 57056945acf0d3aa91784a4cf93e37270cc97dc6, branch: develop) of the [Tamarin prover](https://github.com/tamarin-prover/tamarin-prover). Instructions for installation and usage can be found in Chapter 2 of the [manual](https://tamarin-prover.github.io/manual/book/002_installation.html). Results can be reproduced in one of two ways.


Interactive mode:
```bash
$ tamarin-prover interactive --heuristic=o --oraclename=5G_handover.oracle 5G_handover.spthy
```

Command line:
```bash
$ tamarin-prover --heuristic=o --oraclename=5G_handover.oracle 5G_handover.spthy --prove
```

### Flags

In the Xn model, four additional executability lemmas for three consecutive handovers can be enabled with flags. Note that the first handover over the Xn interface must always use horizontal key derivation [TS 33.501, Sec. 6.9].

__hkd__ = horizontal key derivation  
__vkd__ = vertical key derivation


| Key derivation | Flag                |
| -------------- | ------------------- |
| hkd-hkd-hkd    | -D=exec_hkd_hkd_hkd |
| hkd-hkd-vkd    | -D=exec_hkd_hkd_vkd |
| hkd-vkd-hkd    | -D=exec_hkd_vkd_hkd |
| hkd-vkd-vkd    | -D=exec_hkd_vkd_vkd |

e.g.
```bash
$ tamarin-prover --heuristic=o --oraclename=5G_handover.oracle -D=exec_hkd_hkd_hkd 5G_handover.spthy --prove
```

### Execution times
The following are approximate execution times for proving all lemmas in each of the models. The times presented here are based on runs with an Intel(R) Xeon(R) CPU E5-2650 v4 @ 2.20GHz using 10 cores and 20GB of memory:

```bash
$ tamarin-prover --heuristic=o --oraclename=5G_handover.oracle 5G_handover.spthy +RTS -N10 -M20G -RTS --prove
```

Execution times for individual lemmas can be found in the comments of each model.

| Model      | (Approximate) Execution time      |
| ---------- | --------------------------------- |
| 5GS to EPS | 30 s                              |
| EPS to 5GS | 30 s                              |
| Xn         | 30 min (1h 40 min with all flags) |
| N2         | 4h 30min                          |

Due to the complexity of the models, running tests for the intra-5G handovers (Xn and N2) on a laptop is not recommended, even when using oracles. The inter-5G variations, however, are testable in a reasonable time (< 2min) on a standard laptop.

5GS to EPS:

```bash
$ (cd inter-5G/5GS_to_EPS_over_N26/ && tamarin-prover --heuristic=o --oraclename=5G_handover.oracle 5G_handover.spthy --prove)
```

EPS to 5GS:

```bash
$ (cd inter-5G/EPS_to_5GS_over_N26/ && tamarin-prover --heuristic=o --oraclename=5G_handover.oracle 5G_handover.spthy --prove)
```
