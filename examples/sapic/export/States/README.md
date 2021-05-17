The examples of this folder are taken from the benchmark of

A little more conversation, a little less action, a lot moresatisfaction: Global states in ProVerifVincent Cheval, Véronique Cortier, Mathieu Turuani

We did not import all examples, because some of the files in the benchmark were broken.

For instance, in the original gs-benchmark archive:
 * in [Sapic]scytl-voting-system.sapic, the model did not execute because an equation was missing.
 * in [GSVerif]secure-device.pv, the model does not run
 * in the tpm files, we cannot make any reachability test terminate, and removing the extend process (we should make the reachability query false trivially does not change the answer of the tool).
 * same goes for the security API, no sanity check query provable.
 * [Sapic]tpm-toy.sapic does not run, and proverif proves it in a few seconds.
