# Example files for the Paper "TAMARIN Unchained: Handling User-Defined AC Operators" by Jannik Dreier, Elise Klein and Steve Kremer, at CSF26

This directory contains the case studies used in the paper.

## Experiments

The examples are split into he following sub-folders:

- `ccs18-5G-multiset-UD`: Models for AKA-5G using the built-in version of XOR and the user-defined version of multiset. These are modified versions of the `ccs18-5G` models from the Tamarin repository.
- `ccs18-5G-xor-UD`: Models for AKA-5G using the built-in version of multiset and the user-defined version of XOR. These are modified versions of the `ccs18-5G` models from the Tamarin repository.
- `exponential_mixnet`: Models of the exponentiation mixnet presented in the paper, written by us by adapting the ProVerif version[^0].
- `jcs19-xor-multiset-UD`: Models from `jcs19-xor` modified to use a user-defined version of multiset and a built-in version of XOR.
- `jcs19-xor-UD`: Models from `jcs19-xor` modified to use a user-defined version of XOR and a built-in version of multiset.
- `multiset-UD`: Models from `multiset` modified to use a user-defined version of multiset.
- `okamoto-UD`: Models for Okamoto's e-voting protocol using a user-defined multiset. These are modified versions of the files in `okamoto`.
- `toy-voting-system`: Models of the toy voting system presented in the paper, written by us.

The modified versions were obtained by simply replacing the built-in symbol with a user-defined one. In this process all comments were removed from the file.

### Individual Execution

In `experiments/files/fast`, you will find proofs that finish in less than 15 minutes on a standard laptop with 32GB of RAM. To run a proof:

```bash
cd experiments/files/fast
tamarin-prover <chosen_file>.spthy --prove +RTS -N3 -RTS
```

For files in `experiments/files/fast/diff`, use this command:

```bash
cd experiments/files/fast/diff
tamarin-prover <chosen_file>.spthy --prove=Observ* --diff +RTS -N3 -RTS
```

### Toy Voting System

To run proofs for the toy voting system run:

```bash
cd experiments/files/toy_voting_system/
tamarin-prover toy_voting_system_not_diff.spthy +RTS -N3 -RTS --auto-sources --prove=eligibility
tamarin-prover toy_voting_system_not_diff.spthy +RTS -N3 -RTS --auto-sources --prove=exec
tamarin-prover toyVotingSystem_semi_manual.spthy +RTS -N3 -RTS --auto-sources --prove=AUTO_typing --heuristic={sourceLemmas}
```

The proofs take between 5 and 10 minutes on a standard laptop for eligibility and executability, but for the source lemma, it can take 30 minutes on a standard laptop.
The file `toyVotingSystem_semi_manual.spthy` contains the entire proof.

### Exponential Mixnet

To run proofs for the exponential mixnet run:

```bash
cd experiments/files/exponential_mixnet/
tamarin-prover exponential_mixnet_V2.spthy --prove --diff --stop-on-trace=BFS +RTS -N3 -RTS
```

The proof for `exponential_mixnet_V2.spthy` will find an attack in 3008 steps in BFS in one or two minutes on a standard laptop.

## References

[^0]: https://gitlab.limos.fr/dhmahmoud/usenix24-632
