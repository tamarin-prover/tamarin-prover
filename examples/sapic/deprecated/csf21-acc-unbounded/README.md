This directory contains Tamarin models of the following paper, which were ported to the now deprecated accountability implementation provided by the [SAPiC plugin](https://github.com/tamarin-prover/tamarin-prover/tree/be0214d5ea0516f1398744ec44590b5bdff2386a):
[1] "Verifying Accountability for Unbounded Sets of Participants", Kevin Morio, and Robert Künnemann, CSF21.

## Generation of lemmas

Since the initial models are specified using MSRs which are not supported by the old accountability implementation, the lemmas had to be generated separately and then added to the models manually.
The verdict functions and accountability lemmas used for the generation are included in comments.

## Models

```
.
├── README.md
├── mixnets
│   └── message-tracing
│       ├── dmn-message-tracing-all-1-fixed.spthy
│       ├── dmn-message-tracing-all-2-fixed.spthy
│       ├── dmn-message-tracing-all-3-fixed.spthy
│       ├── dmn-message-tracing-all-4-fixed.spthy
│       ├── dmn-message-tracing-all-5-fixed.spthy
│       ├── dmn-message-tracing-first-1-fixed.spthy
│       ├── dmn-message-tracing-first-2-fixed.spthy
│       ├── dmn-message-tracing-first-3-fixed.spthy
│       ├── dmn-message-tracing-first-4-fixed.spthy
│       ├── dmn-message-tracing-first-5-fixed.spthy
│       └── oracle-dmn-message-tracing
└── mixvote
    ├── mixvote_SmHh-multi-session-1-fixed.spthy
    ├── mixvote_SmHh-multi-session-2-fixed.spthy
    ├── mixvote_SmHh-multi-session-3-fixed.spthy
    ├── mixvote_SmHh-multi-session-4-fixed.spthy
    └── mixvote_SmHh-multi-session-5-fixed.spthy
```

The directory [mixnets/message-tracing](./mixnets/message-tracing) contains two sets of case studies implementing decryption mixnets with the message tracing technique.
In the models with the name `dmn-message-tracing-all-<i>.spthy`, the audit continues after detecting the first unexpected message on the bulletin board.
In the models with the name `dmn-message-tracing-first-<i>.spthy`, the audit stops after detecting the first unexpected message on the bulletin board.
The number of mix servers in the model is indicated by `<i>`.

The directory [mixvote](./mixvote) contains a variant of the MixVote protocol extended to unbounded sessions for the indicated number of allowed server identities.
The case study is based on the MixVote model [mixvote_SmHh.spthy](https://github.com/tamarin-prover/tamarin-prover/blob/develop/examples/csf20-disputeResolution/mixvote_SmHh.spthy) by Lara Schmid.
