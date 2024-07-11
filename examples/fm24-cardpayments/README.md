# Tamarin Models of C8
These are the Tamarin models of the new EMV kernel, C8 for the FM 2024 paper *Getting Chip Card Payments Right*.

The models are based on our previous models, available at https://github.com/EMVrace/EMVerify-PAN-routing.

## Authors
* David Basin, *Department of Computer Science, ETH Zurich*
* Xenia Hofmeier, *Department of Computer Science, ETH Zurich*
* Ralf Sasse, *Department of Computer Science, ETH Zurich*
* Jorge Toro-Pozo, *SIX Digital Exchange*

## Folder Layout
* [offlineAndOnlineAuthorized](./offlineAndOnlineAuthorized/): contains the Tamarin models allowing for both, offline and online authorization.
* [onlineAuthorized](./onlineAuthorized/): contains the Tamarin models requiring online authorization.

Both folders contain the following folders and files:
* [Makefile](./offlineAndOnlineAuthorized/Makefile): script to generate the target models and run the Tamarin analysis of them.
* [tools](./offlineAndOnlineAuthorized/tools/): contains useful scripts:
	* [`collect`](./offlineAndOnlineAuthorized/tools/collect): Python script that summarizes the proofs in an human-readable HTML file. It also generates LaTeX code of the summary table.
	* [`decomment`](./offlineAndOnlineAuthorized/tools/decomment): Python script that prints a comment-free copy of the input model.
* [oracle](./offlineAndOnlineAuthorized/oracle/C8.oracle): proof-support oracles.

The folders differ in the following files:
* [C8.spthy](./offlineAndOnlineAuthorized/C8.spthy) (offlineAndOnlineAuthorized) and [C8.spthy](./onlineAuthorized/C8.spthy) (onlineAuthorized): generic model of the C8 kernel with all the configurations.
* [models-n-proofs](./offlineAndOnlineAuthorized/models-n-proofs/) (offlineAndOnlineAuthorized) and [models-n-proofs](./onlineAuthorized/models-n-proofs/) (onlineAuthorized): contains the auto-generated, target models and their proofs (`.proof`).
* [results](./offlineAndOnlineAuthorized/results/) (offlineAndOnlineAuthorized) and [results](./onlineAuthorized/results/) (onlineAuthorized): contains the analysis results in HTML format.

## Configurations
We consider four configuration options, each consisting of a parameter and possible values:
* `localAuth` (`Yes`/`No`): determines whether local authentication is performed, i.e. whether the terminal verified the certificates and the blinding factor.
* `copyIAD` (`Yes`, `No`): determines whether the IAD-MAC is copied into the IAD itself and whether the IAD-MAC is included in the AC.
* `CVM` (`NoCVM`/`OnlinePIN`/`CDCVM`): the CVM used in the transaction.
* `value` (`Low`/`High`): determines whether the transaction amount is below (low) or above (high) the CVM Required Limit.

We call a combination of these four parameters *configuration*. We model transactions arising from all configurations running and interacting in parallel. In our formalization of the security properties though, we consider each configuration separately. To do this, for each configuration we generate a so-called target model that we analyze with Tamarin. 

## Analysis with Tamarin
The analysis of the models requires a recent installation of the Tamarin prover. We used Tamarin version 1.9.0 (git revision: 57e619fef32033293e4a83c0be67cc6e296bf166, branch: develop). Installation instructions can be found at https://tamarin-prover.com/manual/master/book/002_installation.html.

The two model versions are analyzed separately. Thus, execute the following instructions either in folder [offlineAndOnlineAuthorized](./offlineAndOnlineAuthorized/) or [onlineAuthorized](./onlineAuthorized/).

The full analysis of all the configurations can be performed with:
```shell
make ceight
```
This generates the target models for all configurations and runs Tamarin on each target model. These files and the proofs (`.proof`) are saved in the folder `models-n-proofs`.

A single target model can be generated and its analysis can be performed using the following `make` command, where for each placeholder ``<X/Y>``, one value ``X`` or ``Y`` has to be chosen:
```shell
make localAuth=<Yes/No> copyIAD=<Yes/No> CVM=<NoCVM/OnlinePIN/NoCVM> value=<Low/High>
```


## Results
The results of our analysis can be found in the folders [offlineAndOnlineAuthorized/models-n-proofs](./offlineAndOnlineAuthorized/models-n-proofs/) and [onlineAuthorized/models-n-proofs](./onlineAuthorized/models-n-proofs/). These are summarized in the files in the folders [offlineAndOnlineAuthorized/results](./offlineAndOnlineAuthorized/results/) and [onlineAuthorized/results](./onlineAuthorized/results/). We used Tamarin version 1.9.0 (git revision: 57e619fef32033293e4a83c0be67cc6e296bf166, branch: develop) on a computing server running Ubuntu 20.04.3 with two Intel(R) Xeon(R) E5-2650 v4 @ 2.20GHz CPUs (with 12 cores each) and 256GB of RAM. We used 14 threads
and at most 32GB of RAM per target model.
