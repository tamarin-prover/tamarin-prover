This repository contains the case-studies performed using the export feature of tamarin, that allows to export to proverif (with gsverif) and deepsec.

# First basic example

On the `ex1.spthy` file written in pure sapic, running `tamarin-prover ex1.spthy --prove` classicaly verifies the file using tamarin.

One can use `tamarin-prover -m=proverif ex1.spthy` to autoamtically translate this file to proverif. Exporting and using proverif can be done for instance with:
`tamarin-prover -m=proverif ex1.spthy > ex1.pv; proverif ex1.pv`

# Convenience scripts

If you are inside the docker image, or have installed on your path the scripts from `tamarin-prover/etc/docker/res`, you should have access to some convenience scripts, one-liners that perform the export with tamarin and run the desired tool on the file.
 * proverif-tamarin
 * progsverif-tamarin
 * proverif-tamarin-diff
 * deepsec-tamarin

One can thus do `proverif-tamarin ex1.spthy` and directly see the proverif results.

# Case-Studies from the paper

 The case-studies mentionned in the paper are:
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

On all of them, `progsverif-tamarin myfile.spthy` export to proverif, applies gsverif and then run proverif. Remark that all examples in the folders `KEMTLS|LAKE|SSH` are pure sapic files without states that can be executed simply with:
 * `tamarin-prover file.spthy --prove`
 * `proverif-tamarin file.spthy`, which is essentially doing `tamarin-prover -m=proverif file.spthy > file.pv; proverif file.pv`

## Running everything

From the docker image, one can execute either `run-tamarin-CS.sh` or `run-proverif-CS.sh` to run all the case-studies in a batch, and store the final results and timings inside either `res-tam.csv` or `res-proverif.csv`.

# A complete example with diff

To see all the features on a single file, one can checkout `toy-example.spthy`.

Its headers shows the full process that allows to export to the multiple tools. We use a single file to export to proverif for a reachability query and two distinct diff-equivalence query, we thus use `#ifdef` flags to instantiate with the pre-processing of Tamarin mutliple versions of the file, based on some command line arguments. Remark that it may be simpler for new users to at first simply create multiple `.spthy` files.

The convienence scripts above and thus our more complex example files use:

    REACH .. for output to proverif / gsverif / tamarin-prover
    PROVERIFEQUIV .. for output only to ProVerif
    DEEPSECEQUIV  .. for output only to  DeepSec

If tamarin is used directly, the `-D` flag needs to be used to set the  macros accordingly, see above. Those are of course arbitrarily chosen.

See e.g., KEMTLS-CA, NSL and Privacy-Pass for the more complex examples using diff.
