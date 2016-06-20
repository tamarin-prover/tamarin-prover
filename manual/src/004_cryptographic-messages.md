Cryptographic Messages
======================

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
a signature `some-sig`, include the line `builtin: some-sig` in your file. The
builtin signatures are.

diffie-hellman

: FIXME

bilinear-pairing

: FIXME

some more

: FIXME




Sorts/Types
-----------

Variables
---------

Equational theories
-------------------

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




TODO: THIS SHOULD GO TO EQUATIONAL THEORY, OR LATER TO DEFINING LEMMAS

The syntax for specifying security properties is defined as follows:

 *  `All`      for universal quantification, temporal variables are prefixed with #
 *  `Ex`       for existential quantification, temporal variables are prefixed with #
 *  `==>`      for implication
 *  `&`        for conjunction
 *  `|`        for disjunction
 *  `not`      for  negation

*  `f @ i`    for action constraints, the sort prefix for the temporal variable 'i'
           is optional

 * `i < j`    for temporal ordering, the sort prefix for the temporal variables 'i'
           and 'j' is optional

 * `#i = #j`  for an equality between temporal variables 'i' and 'j'
 * `x = y`    for an equality between message variables 'x' and 'y'



Note that apart from public names (delimited using single-quotes), no terms
may occur in guarded trace properties. Moreover, all variables must be
guarded. The error message for an unguarded variable is currently not very
good.

For universally quantified variables, one has to check that they all
occur in an action constraint right after the quantifier and that the
outermost logical operator inside the quantifier is an implication.
For existentially quantified variables, one has to check that they all
occur in an action constraint right after the quantifier and that the
outermost logical operator inside the quantifier is a conjunction.
Note also that currently the precedence of the logical connectives is
not specified. We therefore recommend to use parentheses, when in
doubt.
