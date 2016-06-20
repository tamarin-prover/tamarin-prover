Equational Theories
===================



Certain equational theories are used very often when modeling
cryptographic messages. We therefore provide builtins definitions for
them, using the keyword 'builtins'. The above theory could also be
enabled using the declaration

  builtins: hashing, asymmetric-encryption

We support the following builtins theories:

  diffie-hellman, signing, asymmetric-encryption, symmetric-encryption,
  hashing



Note that the theory for hashing only introduces the function symbol 'h/1'
and contains no equations.
Apart from 'diffie-hellman', all of these theories are subterm-convergent and
can therefore also be declared directly, as above. You can inspect their
definitions by uncommenting the following two line-comments and calling

  tamarin-prover Tutorial.spthy

// builtins: diffie-hellman, signing, asymmetric-encryption, 
symmetric-encryption,
//          hashing
