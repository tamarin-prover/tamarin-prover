
Cryptographic Messages {#sec:cryptographic-messages}
====================================================

Tamarin analyzes protocols with respect to a symbolic model of cryptography.
This means cryptographic messages are modeled as terms [^1] rather than
bit strings..
The properties of the employed cryptographic algorithms are
modeled by equations.
More concretely, a cryptographic message is either a constant `c` or a
message `f(m1,...,mN)` corresponding to the application of the `N`-ary
function symbol `f` to `N` cryptographic messages `m1`, ..., `mN`.
To specify equations, we also allow for variables in addition to constants.

Constants
---------

We distinguish between two types of constants:

* Public constants model publicly known atomic messages such as agent
  identities and labels. We use the notation `'ident'` to denote public
  constants in Tamarin.
* Fresh constants model random values such as secret keys or random
  nonces. We use the notation `~'ident'` to denote fresh
  constants in Tamarin. Note that fresh *constants* are seldomly used
  in protocol specifications. A fresh *variable* is almost always the
  right choice.

Function Symbols
----------------

Tamarin supports a fixed set of builtin function symbols and additional user-defined
function symbols. The only function symbols available in every Tamarin file are for
pairing and projection. The binary function symbol `pair` models the pair of two
messages and the function symbols `fst` and `snd` model the projections of the first
and second argument. The properties of projection are captured by the following
equations:

    fst(pair(x,y)) = x
    snd(pair(x,y)) = y

Tamarin also supports `<x,y>` as syntactic sugar for `pair(x,y)` and
`<x1,x2,...,xN-1,xN>` as syntactic sugar for `<x1,<x2,..,<xN-1,xN>...>`.

Additional builtin function symbols can be activated by including one of the
following message theories:
`hashing`,
`asymmetric-encryption`,
`signing`,
`symmetric-encryption`,
`diffie-hellman`,
`bilinear-pairing`, and
`multiset`.

To activate message theories `t1`, ..., `tN`, include the line 
`builtins: t1, ..., tN` in your file.
The definitions of the builtin message theories are given in Section
[Builtin message theories](#sec:builtin-theories).

To define function symbols `f1`, ..., `fN` with arity `n1`,...,`nN` include the
  following line in your file:

    functions: f1/n1, ..., fN/nN

Tamarin also supports *private function symbols*. In contrast to regular function
symbols, Tamarin assumes that private function symbols cannot be applied by the adversary.
Private functions can be used to model functions that implicitly use some secret
that is shared between all (honest) users. To make a function private, append the
attribute `[private]`. For example, the line

    functions: f/3, g/2 [private], h/1

defines the private function `g` and the public functions `f` and `h`.
We will describe in the next section how you can define equations that capture
properties of functions.

Equational theories {#sec:equational-theories}
-------------------

Equational theories can be used to model properties of functions, e.g., that
symmetric decryption is the inverse of symmetric encryption whenever both use
the same key. The syntax for adding equations to the context is:

    equations: lhs1 = rhs1, ..., lhsN = rhsN

Both `lhs` and `rhs` can contain variables.
The symbolic proof search used by Tamarin only supports a restricted class of
user-defined equations.
Concretely, the right-hand-side must be either a ground term (i.e., it does not contain
any variables) or a proper subterm of the left-hand-side.
Note that the equations modeled by the builtin message theories `diffie-hellman`,
`bilinear-pairing`, and `multiset` do not belong to this restricted class since they
include for example associativity and commutativity. All other builtin message theories
can be equivalently defined by using `functions: ...` and `equations: ...` and
we will therefore see some examples of allowed equations in the next section.


Builtin message theories {#sec:builtin-theories}
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

: This theory models Diffie-Hellman groups. **FIXME: add function symbols and equations**

`bilinear-pairing`:

: This theory models Pairing groups. **FIXME: add functions symbols and equations**

`multiset`:

: This theory introduces associative operators which can be used to model
  multisets. **FIXME: add function symbols and equations**

[^1]: FIXME: Should we write more about terms and equations.


