DIFF: ISO/IEC 20008 mechanism 4, ECC DAA in TAMARIN
===================================================

This is the README for the Tamarin files associated with the
IEEE EuroS&P 2019 submission "A Symbolic Analysis of ECC-based Direct
Anonymous Attestation" using Observational Equivalence. 

Additionally, we have stored the proved model in the `../analysed/ObservationalEquiv` folder. 

Tamarin Installation
--------------------

To run these files, you will need the Tamarin Prover tool installed, git hash `44d5ecbc2097ee99a22a01876e445047f2a31c54` or later, and its dependencies.

Please follow the [instructions within the Tamarin Manual (link)](https://tamarin-prover.github.io/manual/book/002_installation.html).

Running Tamarin on the model
----------------------------

To run the verification on the model from within this folder it in the GUI mode and run the proofs:
```bash
$ tamarin-prover interactive . --diff --heuristic=o --oraclename=ISOIEC_20008_2013_2_ECC_DAA.unlinkability.oracle
```
and then point your browser to [http://localhost:3001/](http://localhost:3001/). There are a number of cases that will not autoprove using our oracle, and
these can be seen in the partial proof file `../analysed/ObservationalEquiv/ISOIEC_20008_2013_2_ECC_DAA.unlinkability.partial.spthy`. The partial proof then needs to be downloaded, and then run using Tamarin's defaults by entering the following command in the folder where the partial proof is stored:
```bash
$ tamarin-prover interactive . --diff 
```
