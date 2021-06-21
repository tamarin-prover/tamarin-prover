This directory contains the Tamarin models of the following paper:
[1] "Verifying Accountability for Unbounded Sets of Participants", Kevin Morio, and Robert Künnemann, CSF21.

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

The directory [mixnets/basic](./mixnets/basic) contains a case study modeling basic decryption mixnets in the limited case where corrupted senders and mix servers can only repost already posted messages.

The directory [mixnets/message-tracing](./mixnets/message-tracing) contains two sets of case studies implementing decryption mixnets with the message tracing technique.
In the models with the name `dmn-message-tracing-all-<i>.spthy`, the audit continues after detecting the first unexpected message on the bulletin board.
In the models with the name `dmn-message-tracing-first-<i>.spthy`, the audit stops after detecting the first unexpected message on the bulletin board.
The number of mix servers in the model is indicated by `<i>`.

The directory [mixvote](./mixvote) contains a variant of the MixVote protocol extended to unbounded sessions for the indicated number of allowed server identities.
The case study is based on the MixVote model [mixvote_SmHh.spthy](https://github.com/tamarin-prover/tamarin-prover/blob/develop/examples/csf20-disputeResolution/mixvote_SmHh.spthy) by Lara Schmid.

The directory [previous](./previous) contains the case studies of the following paper, which were ported from the now deprecated acccountability implementation provided by the [SAPiC plugin](https://github.com/tamarin-prover/tamarin-prover/tree/develop/plugins/sapic) to the new implementation presented in [1]:
[2] "Automated Verification of Accountability in Security Protocols", Robert Künnemann, Ilkan Esiyok, and Michael Backes, CSF19.
