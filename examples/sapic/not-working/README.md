The following case studies are in the repository, but cannot be proven automatically:

- (./PKCS11/pkcs11-dynamic-policy.spthy): This model is an experiment that never concluded
- (./envelope): These examples were never completed and are here for reference only.
- (./fairexchange-???/) The examples used a lot of syntactic trickery pre-SAPIC+
  that is now forbidden. They should be translateable, but considerable effort is needed:
    - the let-construct were used to encode parts of patterns, these need to be inlined
    - matched and bound variables need to be referenced explicitely
    - at the experiments ran for hours, re-validation is costly
