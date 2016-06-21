Cryptographic Messages {#sec:cryptographic-messages}
====================================================

A cryptographic message is either a constant `c` or a message `f(m1,...,mN)`
corresponding to the application of the `N`-ary function `f` to `N` cryptographic
messages `m1`, ..., `mN`.

FIX: `crypto messages => semantics`, `message patterns => specification of rules`

Message patterns can additionally contain (typed) message
variables that can be instantiated with arbitrary cryptographic messages of the
correct type.


Constants
---------

We distinguish between two types of constants:

* Public constants model publicly known atomic messages such as agent
  identities and labels. We use the notation `'some_identifier'` to denote public
  constants in Tamarin.
* Fresh constants model random values such as secret keys or random
  nonces. We use the notation `~'some_identifier'` to denote fresh
  constants in Tamarin. Note that fresh *constants* are seldomly used, a fresh
  *variable* is almost always the right choice.

Function Symbols
----------------

Tamarin supports a fixed set of builtin function symbols and additional user-defined
function symbols. The builtin function symbols are included in signatures. To include
a signature `some-sig`, include the line `builtins: some-sig` in your file. The
builtin message theories are given in Section [Builtin message theories](#sec:linux).

Sorts/Types
-----------

Variables
---------

Equational theories
-------------------

Builtin message theories {#subsec:builtin-sigs}
------------------------

In the following, we write `f/n` to denote that the function symbol `f` is
`n`-ary.


`hashing`:

: This theory models a hash function. It defines the function symbol
  `h/1` and no equations.

`asymmetric-encryption`:

: This theory models a public key encryption scheme. It defines the
  function symbols `aenc/2`, `adec/2`, and `pk/1`. These function symbols are
  related by the equation `adec(aenc(m, pk(sk)), sk) = m`.

`signing`:

: This theory models a signature scheme. It defines the function symbols
  `sign/2`, `verify/3`, `pk/1`, and `true`. These function symbols are related by
  the equation `verify(sign(m,sk),m,pk(sk)) = true`.

`symmetric-encryption`:

: This theory models a symmetric encryption scheme. It defines the function symbols
  `senc/2`  and `sdec/2`. These function symbols are related by the equation
  ` sdec(senc(m,k),k) = m`.

`diffie-hellman`:

: This theory models one or multiple Diffie-Hellman group. 

`bilinear-pairing`:

: FIXME

`multiset`:

: FIXME


OLD
---




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




