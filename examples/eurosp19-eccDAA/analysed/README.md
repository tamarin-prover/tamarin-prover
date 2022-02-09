ISO/IEC 20008 mechanism 4, ECC DAA in TAMARIN
=============================================

This is the README for the Tamarin files associated with the
IEEE EuroS&P 2019 submission "A Symbolic Analysis of ECC-based Direct
Anonymous Attestation". This folder contains the proved theories.

Please see the sub-directory `observatonalEquiv`
for the partial and proved model with the `diff` terms which performs
the observational equivalence analysis. 

Tamarin Installation
--------------------

To run these files, you will need the Tamarin Prover tool installed, git hash `44d5ecbc2097ee99a22a01876e445047f2a31c54` or later, and its dependencies.

Please follow the [instructions within the Tamarin Manual (link)](https://tamarin-prover.github.io/manual/book/002_installation.html).

Running Tamarin on the models
-----------------------------

To load the proved models from within this folder load the models in the GUI mode:
```bash
$ tamarin-prover interactive .
```
and then point your browser to [http://localhost:3001/](http://localhost:3001/).

* To load the observational equivalence model see the README in the `observationalEquiv` folder. 
