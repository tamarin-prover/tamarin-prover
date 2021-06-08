This repository contains the case-studies performed using the export feature of tamarin.

# A first example

To see all the features on a single file, one can checkout `toy-example.spthy`.

It's heaeder shows the full process that allows to export to the multiple tools. If you are inside the docker, or have installed on your path the scripts from `tamarin-prover/etc/docker/res`, you can run it using:
 * proverif-tamarin
 * proverif-tamarin-diff
 * deepsec-tamarin

 Or classically run it using tamarin.

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

# Running everything

From the docker image, one can execute either `run-tamarin-CS.sh` or `run-proverif-CS.sh` to run all the case-studies.
