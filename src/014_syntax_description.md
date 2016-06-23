Syntax Description
==================

Here, we explain the formal syntax of the security protocol theory format that
is processed by Tamarin.

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
is special. It refers to the equations given in Section [Cryptographic
Messages](004_cryptographic-messages.html#equational-theories). You need to 
enable it to parse terms containing exponentiations, e.g.,  g ^ x.

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
left-hand side separate from the free variables on the right-hand side.

Axioms specify restrictions on the set of traces considered, i.e., they filter
the set of traces of a protocol. The formula of an axiom is available as an
assumption in the proofs of *all* security properties specified in this
security protocol theory.

    axiom := 'axiom' ident ':' '"' formula '"'

In observational equivalence mode, axioms can be associated to one side.

    axiom := 'axiom' ident [axiom_attrs] ':' '"' formula '"'
    axiom_attrs      := '[' ('left' | 'right') ']'

Lemmas specify security properties. By default, the given formula is
interpreted as a property that must hold for all traces of the protocol of the
security protocol theory. You can change this using the 'exists-trace' trace
quantifier.

    lemma := 'lemma' ident [lemma_attrs] ':'
             [trace_quantifier]
             '"' formula '"'
             proof
    lemma_attrs      := '[' ('typing' | 'reuse' | 'use_induction' | 
                             'hide_lemma=' ident) ']'
    trace_quantifier := 'all-traces' | 'exists-trace'
    proof            := ... a proof as output by the Tamarin prover ..

In observational equivalence mode, lemmas can be associated to one side.

    lemma_attrs      := '[' ('typing' | 'reuse' | 'use_induction' | 
                             'hide_lemma=' ident | 'left' | 'right') ']'

Formal comments are used to make the input more readable. In contrast
to /*...*/ and //... comments, formal comments are stored and output
again when pretty-printing a security protocol theory.

    formal_comment := ident '{*' ident* '*}'

For the syntax of terms, you best look at our examples. A common pitfall is to
use an undefined function symbol. This results in an error message pointing to
a position slightly before the actual use of the function due to some
ambiguity in the grammar.

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

Formulas are trace formulas as described previously. Note that we are a bit
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

