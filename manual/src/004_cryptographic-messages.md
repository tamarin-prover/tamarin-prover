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
`n`-ary. **FIXME: Also explain pairing, which is always included.**


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

: This theory models Diffie-Hellman groups. **FIXME**

`bilinear-pairing`:

: This theory models Pairing groups. **FIXME**

`multiset`:

: This theory introduces associative operators which can be used to model
  multisets. **FIXME**



