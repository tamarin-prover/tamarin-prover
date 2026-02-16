
Cryptographic Messages {#sec:cryptographic-messages}
====================================================

Tamarin analyzes protocols with respect to a symbolic model of cryptography.
This means cryptographic messages are modeled as terms rather than
bit strings.

<!--  
[^1]: FIXME: Should we write more about terms and equations.
-->

The properties of the employed cryptographic algorithms are
modeled by equations.
More concretely, a cryptographic message is either a constant `c` or a
message `f(m1,...,mn)` corresponding to the application of the `n`-ary
function symbol `f` to `n` cryptographic messages `m1`, ..., `mn`.
When specifying equations, we also allow for variables in addition to constants.

Constants
---------

We distinguish between these types of constants:

* *Public constants* model publicly known atomic messages such as agent
  identities and labels. We use the notation `'ident'` to denote public
  constants in Tamarin. Such constants are of sort `pub` and can hence be
  unified with public variables. They are always known by the adversary.
* *Functions* of arity 0 (see below). A function is always of sort `msg`, and
  hence cannot be unified with a public variable. By default the function is
  public and known by the adversary. If the function is declared private, it is
  not known by the adversary. However, *fresh* values are usually a more
  appropriate modeling of secret values.
* *Natural Numbers* have only one constant which is written `%1` or `1:nat` and models the number one.

Function Symbols
----------------

Tamarin supports a fixed set of built-in function symbols and additional user-defined
function symbols. The only function symbols available in every Tamarin file are for
pairing and projection. The binary function symbol `pair` models the pair of two
messages and the function symbols `fst` and `snd` model the projections of the first
and second argument. The properties of projection are captured by the following
equations:

    fst(pair(x,y)) = x
    snd(pair(x,y)) = y

Tamarin also supports `<x,y>` as syntactic sugar for `pair(x,y)` and
`<x1,x2,...,xn-1,xn>` as syntactic sugar for `<x1,<x2,..,<xn-1,xn>...>`.

Additional built-in function symbols can be activated by including one of the
following message theories:
`hashing`,
`asymmetric-encryption`,
`signing`,
`revealing-signing`,
`symmetric-encryption`,
`diffie-hellman`,
`bilinear-pairing`,
`xor`, and
`multiset`.

To activate message theories `t1`, ..., `tn`, include the line
`builtins: t1, ..., tn` in your file.
The definitions of the built-in message theories are given in Section
[Built-in message theories](#sec:builtin-theories).

To define function symbols `f1`, ..., `fn` with arity `a1`,...,`an` include the
  following line in your file:

    functions: f1/a1, ..., fn/an

Tamarin also supports *private function symbols*. In contrast to regular function
symbols, Tamarin assumes that private function symbols cannot be applied by the adversary.
Private functions can be used to model functions that implicitly use some secret
that is shared between all (honest) users. To make a function private,
simply add the attribute `[private]` after the function declaration. For example, the line

    functions: f/3, g/2 [private], h/1

defines the private function `g` and the public functions `f` and `h`.
We will describe in the next section how you can define equations that formalize
properties of functions.

Equational theories {#sec:equational-theories}
-------------------

Equational theories can be used to model properties of functions, e.g., that
symmetric decryption is the inverse of symmetric encryption whenever both use
the same key. The syntax for adding equations to the context is:

    equations: lhs1 = rhs1, ..., lhsn = rhsn

Both `lhs` and `rhs` can contain variables, but no public constants, and all variables on the right hand
side must also appear on the left hand side. The symbolic proof search
used by Tamarin supports a certain class of user-defined equations, namely
*convergent* equational theories that have the *finite variant property*
[@Comon-LundhD05]. Note that Tamarin does *not* check whether the given equations
belong to this class, so writing equations outside this class can cause
non-termination or incorrect results *without any warning*.

Also note that Tamarin's reasoning is particularly efficient when considering only
subterm-convergent equations, i.e., if the right-hand-side is either a ground
term (i.e., it does not contain any variables) or a proper subterm of the
left-hand-side. These equations are thus preferred if they are sufficient to model
the required properties. However, for example the equations modeled by the
built-in message theories `diffie-hellman`, `bilinear-pairing`, `xor`, and `multiset`
do not belong to this restricted class since they include for example
associativity and commutativity. All other built-in message theories can
be equivalently defined by using `functions: ...` and `equations: ...`
and we will see some examples of allowed equations in the next
section.


Built-in message theories and other built-in features {#sec:builtin-theories}
------------------------

In the following, we write `f/n` to denote that the function symbol `f` is
`n`-ary.

`hashing`:

: This theory models a hash function. It defines the function symbol
  `h/1` and no equations.

`asymmetric-encryption`:

: This theory models a public key encryption scheme. It defines the
  function symbols `aenc/2`, `adec/2`, and `pk/1`, which are
  related by the equation `adec(aenc(m, pk(sk)), sk) = m`.
  Note that as described in [Syntax Description](016_syntax_description.html),
  `aenc{x,y}pkB` is syntactic sugar for `aenc(<x,y>, pkB)`.
  <!-- This is otherwise not mentioned until Ch14: Syntax Description -->

`signing`:

: This theory models a signature scheme. It defines the function symbols
  `sign/2`, `verify/3`, `pk/1`, and `true`, which are related by
  the equation `verify(sign(m,sk),m,pk(sk)) = true`.

`revealing-signing`:

: This theory models a message-revealing signature scheme. It defines the function
  symbols `revealSign/2`, `revealVerify/3`, `getMessage/1`, `pk/1`, and
  `true`, which are related by the equations
  `revealVerify(revealSign(m,sk),m,pk(sk)) = true`
  and `getMessage(revealSign(m,sk)) = m`.

`symmetric-encryption`:

: This theory models a symmetric encryption scheme. It defines the function symbols
  `senc/2`  and `sdec/2`, which are related by the equation
  ` sdec(senc(m,k),k) = m`.

`diffie-hellman`:

: This theory models Diffie-Hellman groups. It defines the function symbols
  `inv/1`, `1/0`, `DH_neutral/0`, and the symbols `^` and `*`. We use `g ^ a` to
  denote exponentiation in the group and `*`, `inv` and `1` to model the
  (multiplicative) abelian group of exponents (the integers modulo the group
  order). The set of defined equations is:

~~~
(x^y)^z  = x^(y*z)
x^1      = x
x*y      = y*x
(x*y)*z  = x*(y*z)
x*1      = x
x*inv(x) = 1
DH_neutral^x = DH_neutral
~~~

`bilinear-pairing`:

: This theory models bilinear groups. It extends the `diffie-hellman` theory with
  the function symbols `pmult/2` and `em/2`. Here, `pmult(x,p)` denotes the
  multiplication of the point `p` by the scalar `x` and `em(p,q)` denotes
  the application of the bilinear map to the points `p` and `q`. The additional
  equations are:

~~~
pmult(x,(pmult(y,p)) = pmult(x*y,p)
pmult(1,p)           = p
em(p,q)              = em(q,p)
em(pmult(x,p),q)     = em(p,q)^x
~~~

`xor`:

: This theory models the exclusive-or operation. It adds the function
  symbols `⊕/2` (also written as `XOR/2`) and `zero/0`. `⊕` is
  associative and commutative and satisfies the cancellation
  equations:

~~~
x ⊕ y       = y ⊕ x
(x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)
x ⊕ zero    = x
x ⊕ x       = zero
~~~

`multiset`:

: This theory introduces the associative-commutative operator `++` which is usually used to model multisets^[In earlier versions of Tamarin, this operator was `+` which is still supported but deprecated. The reason for this change is that in the end, we want to use `+` for addition on natural numbers (instead of the current `%+`).].

`natural-numbers`:
: This theory introduces the associative-commutative operator `%+` and the public constant `%1` which are used to model counters. It also introduces the sort `nat` with which variables can be annotated like the sort `pub $`: `n:nat` or `%n`. Furthermore, the operator `%+` only accepts terms of sort `nat` and is the only one to produce `nat` terms. This guarantees, that any term of sort `nat` is essentially a sum of `%1`. So all natural numbers are public knowledge which speeds up Tamarin as no attacker construction of a number has to be searched for.

Note that these `nat` terms are only suited to model small natural numbers like counters that are assumed to be guessable by the attacker. To model big random numbers, it is advised to use `fresh` variables.

In some protocols such as WPA-2, big natural numbers are increased as a counter with a random start-point. For such models, it is advised to use a pair `<~x, %n>` where `~x` is the random start point and `%n` is the guessable counter.

`reliable-channel`:

: This theory introduces support for reliable channel in the [process
calculus](006_protocol-specification-processes.html).
Messages on the channel (i.e., public name) `'r'` are guaranteed to arrive
eventually. There is only one other channel, the public and unreliable channel
`'c'`. Note that multiple reliable channels can be modelled using pattern matchting:
```
  out('r',<'channelA','Hello')              
| out('r',<'channelB','Bonjour')
| in('r',<'channelA',x); event PrepareTea()
| in('r',<'channelB',x); event PrepareCoffee()
```

Reserved function symbol names {#sec:reserved-names}
------------------------

Due to their use in built-in message theories, the following function
names cannot be user-defined: `mun`, `one`, `exp`, `mult`, `inv`, `pmult`, `em`.

If a theory contains any of these as user-defined function symbol the
parser will reject the file, stating which reserved name was redeclared.
