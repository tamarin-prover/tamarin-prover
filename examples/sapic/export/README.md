This repository contains the case studies performed using the export feature of tamarin, which allows to export to ProVerif (with GSVerif) and DeepSec.

# First basic example

On the `ex1.spthy` file written in pure sapic, running `tamarin-prover ex1.spthy --prove` classically verifies the file using tamarin.

One can use `tamarin-prover -m=proverif ex1.spthy` to automatically translate this file to ProVerif. Exporting and using ProVerif can be done for instance with:
`tamarin-prover -m=proverif ex1.spthy > ex1.pv; proverif ex1.pv`

# Convenience scripts

If you are inside the docker image, or have installed on your path the scripts from `tamarin-prover/etc/docker/res`, you should have access to some convenience scripts, one-liners that perform the export with tamarin and run the desired tool on the file.
 * ProVerif-tamarin
 * progsverif-tamarin
 * ProVerif-tamarin-diff
 * deepsec-tamarin

One can thus do `proverif-tamarin ex1.spthy` and directly see the ProVerif results.

# Case-Studies from the paper

 The case studies mentionned in the paper are:
  * KEMTLS -> ./KEMTLs/kemtls.spthy
  * KEMTLS-CA -> ./KEMTLS/kemtls-clientauth.spthy
  * KEMTLS-NOAEAD -> ./KEMTLS/kemtls-noaead.spthy
  * LAKE -> ./LAKE/lake-edhoc.spthy
  * LAKE-DH-KCI -> ./LAKE/lake-edhoc-DHmode-KCI.spthy
  * LAKE-DH-FS ->./LAKE/lake-edhoc-DHmode-FS.spthy
  * SSH -> ./SSH/ssh-without-forwarding.spthy
  * SSH-NEST -> ./SSH/ssh-with-one-forwarding.spthy
  * SSH-NEST-X -> ./SSH/ssh-with-forwarding-bounded.spthy
  * Privacy-Pass -> ./privacypass.spthy
  * AC -> ./ExistingSapicModels/AC.spthy
  * AC-F-SID -> ./ExistingSapicModels/AC_sid_with_attack.spthy
  * AKE -> ./ExistingSapicModels/AKE.spthy
  * SOC -> tamarin-prover/examples/sapic/fast/feature-locations/SOC.spthy
  * OTP -> ./ExistingSapicModels/OTP.spthy
  * NSL -> ./ExistingSapicModels/nsl-no_as-untagged.spthy
  * Scytl -> ./States/scytl-voting-system.spthy
  * SD -> ./States/secure-device.spthy

On all of them, `progsverif-tamarin myfile.spthy` export to ProVerif, applies GSVerif and then run ProVerif. Remark that all examples in the folders `KEMTLS|LAKE|SSH` are pure sapic files without states that can be executed simply with:
 * `tamarin-prover file.spthy --prove`
 * `proverif-tamarin file.spthy`, which is essentially doing `tamarin-prover -m=proverif file.spthy > file.pv; proverif file.pv`

## Running everything

From the docker image, one can execute either `run-tamarin-CS.sh` or `run-proverif-CS.sh` to run all the case studies in a batch, and store the final results and timings inside either `res-tam.csv` or `res-proverif.csv`.

# A complete example with diff

To see all the features on a single file, one can check out `toy-example.spthy`.

Its header shows the full process that allows to export to the multiple tools. We use a single file to export to ProVerif for a reachability query and diff-equivalence queries.
