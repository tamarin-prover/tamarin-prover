# Automated Security Analysis of Exposure Notification Systems

This is the artifact for the paper *Automated Security Analysis of Exposure Notification Systems* accepted for *USENIX Security '23*.

## Authors

- Kevin Morio, *CISPA Helmholtz Center for Information Security*
- Ilkan Esiyok, *CISPA Helmholtz Center for Information Security*
- Dennis Jackson, *Mozilla*
- Robert Künnemann, *CISPA Helmholtz Center for Information Security*

## Preprint

A preprint of the full version of the paper is available on arXiv: [2210.00649](https://arxiv.org/abs/2210.00649).

## Models

The artifact consists of the Tamarin model files with the corresponding oracles for the three exposure notification systems ROBERT, DP3T, and the CWA presented in the paper.

### ROBERT (`robert.spthy`)

This is a model of the French deployment of the ROBust and privacy-presERving proximity Tracing (ROBERT) protocol as used by the TousAntiCovid app.
This model uses the oracle `oracle-robert`.

### DP3T (`dp3t.spthy`)

This is a model of the Decentralized Privacy-Preserving Proximity Tracing (DP3T) protocol with authorisation scheme 3 (device bound authorisation).
This model uses the oracle `oracle-dp3t`.

### CWA (`cwa.spthy`)

This is a model of the German Corona-Warn App (CWA).
This model uses the oracle `oracle-cwa`.

## Installation

This artifact can be evaluated with a local Tamarin installation or using the provided Docker container.

Tamarin and its dependencies can be installed following the instruction from the [Tamarin manual](https://tamarin-prover.github.io/manual/book/002_installation.html).

Installation instruction for Docker are available in the [Docker documentation](https://docs.docker.com/engine/install).
The Docker container can be obtained by executing

    docker pull kevinmorio/usenix23-ens

## Usage

The lemmas of the models can be automatically verified by executing

    tamarin-prover --prove <model>

for a local installation of Tamarin or

    docker run kevinmorio/usenix23-ens tamarin-prover --prove <model>

for using the Docker container, where `<model>` can be one of `robert.spthy`, `dp3t.spthy`, or `cwa.spthy`.

Alternatively, the models can be inspected in Tamarin's interactive mode by executing

    tamarin-prover interactive .

or

    docker run -it -p 3001:3001 kevinmorio/usenix23-ens tamarin-prover interactive --interface='*4' .

Tamarin's web interface is then accessible on the host under [localhost:3001](http://localhost:3001).
