User manual for the Tamarin prover
==================================

Date:    2012/09/28
Authors: Simon Meier <iridcode@gmail.com>,
         Benedikt Schmidt <beschmi@gmail.com>


Installation
============

See the [installation instructions](../INSTALL.md).

Subscribe to https://groups.google.com/group/tamarin-prover for receiving news
on updates and new releases of the Tamarin prover.

Syntax highlighting
-------------------

We provide syntax highlighting files for the 'vim' text editor. Here, we
describe how to install them. Let DATA_PATH be the parent directory of the
examples directory output in Tamarin's help message.  The 'vim' syntax
highlighting files are found at

  DATA_PATH/etc/

To install them, copy 'DATA_PATH/etc/filepath.vim' to the '~/.vim' directory
and copy 'DATA_PATH/etc/spthy.vim' to the '~/.vim/syntax directory'. If one of
these directories does not exist, then just create it.

We also provide a syntax highlighting file for Notepad++
(http://notepad-plus-plus.org/). This is a great text editor for Windows. See

  DATA_PATH/notepad_plus_plus_stphy.xml

for the syntax highlighting file.


Usage
=====

Once you have installed the 'tamarin-prover' executable, calling it without
any arguments will print a help message explaining its different modes and the
paths to example files. We suggest that you first have a look at the
'Tutorial.spthy' file referenced there.

Once, you have done that, you probably want to start modeling your own
protocols. We normally use the following workflow to do that.

  1. Copy the example protocol that is most similar to the one your are
     modeling. Let us assume that this copy is named 'myproto.spthy'.

  2. Modify the protocol piece by piece and call 'tamarin-prover
     myproto.spthy' to ensure that it still parses and all well-formedness
     checks pass. This way you get immediate feedback on your changes.
     Moreover, you can see the expansions of syntactic sugar like the built-in
     signatures for hashing or asymmetric encryption.

  3. Once you are satisfied with your model, check if the automated prover
     succeeds in analyzing your protocol by calling

       'tamarin-prover myproto.spthy --prove'

  4. If the Tamarin prover does not terminate, then you can either bound the
     proof-depth using the '--bound' flag or you can switch to the interactive
     GUI to analyze what is going wrong. Call

       'tamarin-prover interactive myproto.spthy'

     and try to construct the proof interactively. If you want to bound the
     proof depth of the autoprover in interactive mode, you can call the
     Tamarin prover as follows.

       'tamarin-prover interactive myproto.spthy --bound=7'

     Note that you can also use the GUI to sanity check your model. Just go
     through the message theory and check that it really models what you
     intent to model. Moreover, the precomputed case distinctions, described
     below, give a good overview about the behavior/specification of your
     protocol. If something is wrong with your model, then it is likely that
     you can see it already from the precomputed case distinctions.

  5. If you have constructed a proof by hand and want to store it for later
     usage, then you can just copy it from the GUI to your input file. The
     Tamarin prover will parse and re-check this proof when loading this
     security protocol theory.


Heuristics and Non-Termination
------------------------------

The problems tackled by the Tamarin prover are undecidable in general. Thus
there will always be protocols satisfying properties that cannot be proven
using the constraint-reduction rules implemented in the Tamarin prover.
However, sometimes there would exist a proof, but the heuristic employed by
the Tamarin prover does not select the right goals to solve. In this case you
have two options: (1) construct your proof interactively in the GUI or (2) try
to twiddle with the '--heuristic' flag.

Option (1) has already been described above. Option (2) is currently
experimental. The argument of the '--heuristic' flag is a word built from the
alphabet '{s,S,c,C}'. Each of these letters describes a different way to rank
the open goals of a constraint system.

  s: the 'smart' ranking is the ranking described in the extended version of
     our CSF'12 paper. It is the default ranking and works very well in a wide
     range of situations.

  S: is like the 'smart' ranking, but does not delay the solving of premises
     marked as loop-breakers. What premises are loop breakers is determined
     from the protocol using a simple under-approximation to the vertex
     feedback set of the conclusion-may-unify-to-premise graph. We require
     these loop-breakers for example to guarantee the termination of the case
     distinction precomputation. You can inspect which premises are marked as
     loop breakers in the 'Multiset rewriting rules' page in the GUI.

  c: is the 'consecutive' or 'conservative' ranking. It solves goals in the
     order they occur in the constraint system. This guarantees that no goal
     is delayed indefinitely, but often leads to large proofs because some
     of the early goals are not worth solving.

  C: is like 'c' but without delaying loop breakers.

If several rankings are given for the heuristic flag, then they are employed
in a round-robin fashion depending on the proof-depth. For example, a flag
'--heuristic=ssC' always uses two times the smart ranking and then once the
'Consecutive' goal ranking. The idea is that you can mix goal rankings easily
in this way.

Note that it might be the case that your case studies require a different goal
ranking that the ones give above. If you have concrete suggestions on
how to compute your required ranking from a constraint system, then we would
love to hear about it: https://github.com/tamarin-prover/tamarin-prover/issues.
Note that your ranking may depend on *all* the information present in a
constraint system. Scroll down in the constraint system visualization page in
the GUI to see what information that is.

Marking facts to be solved preferentially or delayed
----------------------------------------------------

By starting a fact name with "F_" the tool will solve instances of
that fact earlier than normal, while putting "L_" as the prefix will
delay solving the fact. This can have a performance impact.


Additional Theory
=================

Most of the theory underlying the Tamarin prover is described in the submitted
draft of Meier's PhD thesis available from

  http://www.infsec.ethz.ch/research/software/tamarin

or directly at

  http://dx.doi.org/10.3929/ethz-a-009790675

Some of the missing pieces will be described in Schmidt's PhD thesis. His
thesis explains the notion of an equation store and design of the normal form
message deduction rules used to reason about Diffie-Hellman explanation,
bilinear pairings, and multiset union. Note that this version of Tamarin does
not yet support bilinear pairings and multiset union. It does support
Diffie-Hellman exponentiation as described in our CSF'12 paper,
and it uses equation stores as explained below.

Our preliminary support for reasoning about protocols that make use of
exclusive access to linear facts is not yet described as part of a research
paper. It is explained in the following subsection.


Reasoning about Exclusivity: Facts Symbols with Injective Instances
-------------------------------------------------------------------

We say that a fact symbol 'f' has *injective instances* with respect to a
multiset rewriting system 'R', if there is no reachable state of
the multiset rewriting system 'R' with more than one instance of an f-fact
with the same term as a first argument. Injective facts typically arise from
modeling databases using linear facts. An example of an fact with injective
instances, is the 'Store'-fact in the following multiset rewriting system.

  rule CreateKey: [ Fr(handle), Fr(key) ] --> [ Store(handle, key) ]

  rule NextKey:   [ Store(handle, key) ] --> [ Store(handle, h(key)) ]

  rule DelKey:    [ Store(handle,key) ] --> []

When reasoning about the above multiset rewriting system, we exploit that
'Store' has injective instances to prove that after the 'DelKey' rule no other
rule using the same handle can be applied. This proof uses trace induction and
the following constraint-reduction rule that exploits facts with unique
instances.

Let 'f' be a fact symbol with injective instances. Let i, j, and k be temporal
variables ordered according to

  i < j < k

and let there be an edge from (i,u) to (k,w) for some indices u and v.
Then, we have a contradiction, if the premise (k,w) requires a fact 'f(t,...)'
and there is a premise (j,v) requiring a fact 'f(t,...)'.  These two premises
must be merged because the edge (i,u) >-> (k,w) crosses 'j' and the state at
'j' therefore contains 'f(t,...)'. This merging is not possible due to the
ordering constraints 'i < j < k'.

Note that computing the set of fact symbols with injective instances is
undecidable in general. We therefore compute an under-approximation to this
set using the following simple heuristic. A fact tag is guaranteed to have
injective instance, if

  1. the fact-symbol is linear,
  2. every introduction of such a fact is protected by a Fr-fact of the
     first term, and
  3. every rule has at most one copy of this fact-tag in the conclusion and
     the first term arguments agree.

We exclude facts that are not copied in a rule, as they are already handled
properly by the naive backwards reasoning.

Note that this support for reasoning about exclusivity was sufficient for our
case studies, but it is likely that more complicated case studies require
additional support. For example, that fact symbols with injective instances
can be specified by the user and the soundness proof that these symbols have
injective instances is constructed explicitly using the Tamarin prover.
Please tell us, if you encounter limitations in your case studies:
https://github.com/tamarin-prover/tamarin-prover/issues.


Equation Store
--------------

We store equations in a special form to allow delaying case splits on them.
This allows for example to determine the shape of a signed message without case
splitting on its variants. In the GUI, you can see the equation store being
pretty printed as follows.

  free-substitution

  1. fresh-substitution-group
  ...
  n. fresh substitution-group

The free-substitution represents the equalities that hold for the free
variables in the constraint system in the usual normal form, i.e., a
substitution. The variants of a protocol rule are represented as a group of
substitutions mapping free variables of the constraint system to terms
containing only fresh variables. The different fresh-substitutions in a group
are interpreted as a disjunction.

Logically, the equation store represents expression of the form

      x_1 = t_free_1
    & ...
    & x_n = t_free_n
    & ( (Ex y_111 ... y_11k. x_111 = t_fresh_111 & ... & x_11m = t_fresh_11m)
      | ...
      | (Ex y_1l1 ... y_1lk. x_1l1 = t_fresh_1l1 & ... & x_1lm = t_fresh_1lm)
      )
    & ..
    & ( (Ex y_o11 ... y_o1k. x_o11 = t_fresh_o11 & ... & x_o1m = t_fresh_o1m)
      | ...
      | (Ex y_ol1 ... y_olk. x_ol1 = t_fresh_ol1 & ... & x_1lm = t_fresh_1lm)
      )



Security Protocol Theories
==========================

A security protocol theory specifies a signature, an equational theory, a
security protocol, and several lemmas, which formalize security properties.
The formal definition of security protocol theories is given in Meier's thesis
available from

  http://www.infsec.ethz.ch/research/software/tamarin

Here, we explain the formal syntax of the security protocol theory format that
is processed by Tamarin. We recommend first reading the 'Tutorial.spthy'
example before delving into the following section.

Comments are C-style:

    /* for a multi-line comment */
    // for a line-comment

All security protocol theory are named and delimited by 'begin' and 'end'.
We explain the non-terminals of the body in the following paragraphs.

    security_protocol_theory := 'theory' ident 'begin' body 'end'
    body := (signature_spec | rule | axiom | lemma | formal_comment)+

Here, we use the term signature more liberally to denote both the defined
function symbols and the equalities describing their interaction.  Note that
our parser is stateful and remembers what functions have been defined. It will
only parse function applications of defined functions.

    signature_spec := functions | equations | built_in
    functions      := 'functions' ':' (ident '/' arity) list
    equations      := 'equations' ':' (term '=' term) list
    arity          := digit+

Note that the equations must be subterm-convergent. Tamarin provides built-in
sets of function definitions and subterm convergent equations. They are
expanded upon parsing and you can therefore inspect them by pretty printing
the file using 'tamarin-prover your_file.spthy'. The built-in 'diffie-hellman'
is special. It refers to the equations given in the paper. You need to enable
it to parse terms containing exponentiations, e.g.,  g ^ x.

    built_in       := 'builtins' ':' built_ins list
    built_ins      := 'diffie-hellman'
                    | 'hashing' | 'symmetric-encryption'
                    | 'asymmetric-encryption' | 'signing'

Multiset rewriting rules are specified as follows. The protocol corresponding
to a security protocol theory is the set of all multiset rewriting rules
specified in the body of the theory.

    rule := 'rule' ident ':'
            [let_block]
            '[' facts ']' ( '-->' | '--[' facts ']->') '[' facts ']'

    let_block := 'let' (ident '=' term)+ 'in'

The let-block allows more succinct specifications. The equations are applied
in a bottom-up fashion. For example,

    let x = y
        y = <z,x>
    in [] --> [ A(y)]    is desugared to    [] --> [ A(<z,y>) ]

This becomes a lot less confusing if you keep the set of variables on the
left-hand side separate from the free variables on the right-hand side ;-)

Axioms specify restrictions on the set of traces considered, i.e., they filter
the set of traces of a protocol. The formula of an axiom is available as an
assumption in the proofs of *all* security properties specified in this
security protocol theory.

    axiom := 'axiom' ident ':' '"' formula '"'

Lemmas specify security properties. By default, the given formula is
interpreted as a property that must hold for all traces of the protocol of the
security protocol theory. You can change this using the 'exists-trace' trace
quantifier.

    lemma := 'lemma' ident [lemma_attrs] ':'
             [trace_quantifier]
             '"' formula '"'
             proof
    lemma_attrs      := '[' ('typing' | 'reuse' | 'use_induction') ']'
    trace_quantifier := 'all-traces' | 'exists-trace'
    proof            := ... a proof as output by the Tamarin prover ..


Formal comments are used to make the input more readable. In contrast
to /*...*/ and //... comments, formal comments are stored and output
again when pretty-printing a security protocol theory.

    formal_comment := ident '{*' ident* '*}'

For the syntax of terms, you best look at our examples. A common pitfall is to
use an undefined function symbol. This results in an error message pointing to
a position slightly before the actual use of the function due to some
ambiguity in our grammar.

We provide special syntax for tuples, multiplications, exponentiation, nullary
and binary function symbols. An n-ary tuple <t1,...,tn> is parsed as n-ary,
right-associative application of pairing. Multiplication and exponentiation
are parsed left-associatively. For a binary operator 'enc' you can write
'enc{m}k' or 'enc(m,k)'. For nullary function symbols, there is no need to
write 'nullary()'. Note that the number of arguments of an n-ary function
application must agree with the arity given in the function definition.

    tupleterm := multterm list
    multterm  := expterm ('*' expterm)*
    expterm   := term    ('^' term   )*
    term      := '<' tupleterm '>'     // n-ary right-associative pairing
               | '(' multterm ')'      // a nested term
               | nullary_fun
               | binary_app
               | nary_app
               | literal

    nullary_fun := <all-nullary-functions-defined-up-to-here>
    binary_app  := binary_fun '{' tupleterm '}' term
    binary_fun  := <all-binary-functions-defined-up-to-here>
    nary_app    := nary_fun '(' multterm* ')'

    literal := "'"  ident "'"      // a fixed, public name
             | '$'  ident          // a variable of sort 'pub'
             | "~'" ident "'"      // a fixed, fresh name
             | "~"  ident          // a variable of sort 'fresh'
             | "#"  ident          // a variable of sort 'temp'
             | ident               // a variable of sort 'msg'

Facts do not have to be defined up-front. This will probably change once we
implement user-defined sorts. Facts prefixed with '!' are persistent facts.
All other facts are linear. There are six reserved fact symbols: In, Out, KU,
KD, and K. KU and KD facts are used for construction and deconstruction
rules. KU-facts also log the messages deduced by construction rules. Note that
KU-facts have arity 2. Their first argument is used to track the
exponentiation tags. See the 'loops/Crypto_API_Simple.spthy' example for more
information.

    facts := fact list
    fact := ['!'] ident '(' multterm list ')'

Formulas are trace formulas as described in our paper. Note that we are a bit
more liberal with respect to guardedness. We accept a conjunction of atoms as
guards.

    formula   := atom | '(' iff ')' | ( 'All' | 'Ex' ) ident+ '.' iff
    iff       := imp '<=>' imp
    imp       := disjuncts '==>' disjuncts
    disjuncts := conjuncts ('|' disjuncts)+  // left-associative
    conjuncts := negation  ('|' conjuncts)+  // left-associative
    negation  := 'not' formula

    atom := tvar '<' tvar              // ordering of temporal variables
          | '#' ident '=' '#' ident    // equality between temporal variables
          | multterm  '=' multterm     // equality between terms
          | fact '@' tvar              // action
          | 'T'                        // true
          | 'F'                        // false
          | '(' formula ')'            // nested formula

    // Where unambiguous the '#' sort prefix can be dropped.
    tvar := ['#'] ident

Identifiers always start with a character. Moreover, they must not be one of the
reserved keywords 'let', 'in', or 'rule'.

    ident := alpha (alpha | digit)*



Developing Tamarin
==================

The Tamarin prover is under active development. We are grateful to receive
bug-reports at 'https://github.com/tamarin-prover/tamarin-prover/issues'. If
you consider building on top of Tamarin, then you might consider integrating
your idea into the main source repository. Please feel free to contact us such
that we can discuss the next steps towards fully verified systems :-)

