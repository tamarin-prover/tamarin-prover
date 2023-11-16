# Verifying Accountability for Unbounded Sets of Participants

This is the artifact for the paper *Verifying Accountability for Unbounded Sets of Participants* accepted for *CSF '21*.

## Authors

- Kevin Morio, *CISPA Helmholtz Center for Information Security*
- Robert Künnemann, *CISPA Helmholtz Center for Information Security*

## Paper

The published version of the paper is available under DOI [10.1109/CSF51468.2021.00032](https://doi.org/10.1109/CSF51468.2021.00032).
The preprint of the full version of the paper is available on arXiv: [2006.12047](https://arxiv.org/abs/2006.12047).

## Models

```
.
├── README.md
├── mixnets
│   ├── basic
│   │   ├── dmn-basic.spthy
│   │   └── oracle-dmn-basic
│   └── message-tracing
│       ├── dmn-message-tracing-all-1.spthy
│       ├── dmn-message-tracing-all-2.spthy
│       ├── dmn-message-tracing-all-3.spthy
│       ├── dmn-message-tracing-all-4.spthy
│       ├── dmn-message-tracing-all-5.spthy
│       ├── dmn-message-tracing-first-1.spthy
│       ├── dmn-message-tracing-first-2.spthy
│       ├── dmn-message-tracing-first-3.spthy
│       ├── dmn-message-tracing-first-4.spthy
│       ├── dmn-message-tracing-first-5.spthy
│       └── oracle-dmn-message-tracing
├── mixvote
│   └── mixvote_SmHh-multi-session.spthy
└── previous
    ├── ct.spthy
    ├── ocsps-msr-untrusted.spthy
    ├── ocsps-msr.spthy
    └── whodunit.spthy
```

### [mixnets/basic](./mixnets/basic)

This directory contains a case study modeling basic decryption mixnets in the limited case where corrupted senders and mix servers can only repost already posted messages.

### [mixnets/message-tracing](./mixnets/message-tracing)

This directory contains two sets of case studies implementing decryption mixnets with the message tracing technique.
In the models with the name `dmn-message-tracing-all-<i>.spthy`, the audit continues after detecting the first unexpected message on the bulletin board.
In the models with the name `dmn-message-tracing-first-<i>.spthy`, the audit stops after detecting the first unexpected message on the bulletin board.
The number of mix servers in the model is indicated by `<i>`.

### [mixvote](./mixvote)

This directory contains a variant of the MixVote protocol extended to unbounded sessions for the indicated number of allowed server identities.
The case study is based on the MixVote model [mixvote_SmHh.spthy](https://github.com/tamarin-prover/tamarin-prover/blob/develop/examples/csf20-disputeResolution/mixvote_SmHh.spthy) by Lara Schmid.

### [previous](./previous)

This directory contains the case studies of [Künnemann et al. (2019)](https://doi.org/10.1109/CSF.2019.00034), which were ported from the now deprecated accountability implementation provided by the [SAPiC plugin](https://github.com/tamarin-prover/tamarin-prover/tree/be0214d5ea0516f1398744ec44590b5bdff2386a) to the new implementation presented in this paper.
