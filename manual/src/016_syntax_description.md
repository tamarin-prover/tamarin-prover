Syntax Description
==================

Here, we explain the formal syntax of the security protocol theory format that
is processed by Tamarin.

Comments are C-style:

    /* for a multi-line comment */
    // for a line-comment

All security protocol theory are named and delimited by `begin` and `end`.
We explain the non-terminals of the body in the following paragraphs.

    security_protocol_theory := 'theory' ident 'begin' body 'end'
    body := (signature_spec | global_heuristic | tactic | rule |
                restriction | lemma | formal_comment)*

Here, we use the term signature more liberally to denote both the defined
function symbols and the equalities describing their interaction.  Note that
our parser is stateful and remembers what functions have been defined. It will
only parse function applications of defined functions.

    signature_spec := functions | equations | built_in
    functions      := 'functions' ':' function_sym (',' function_sym)* [',']
    function_sym   := ident '/' arity ['[private]']
    arity          := digit+
    equations      := 'equations' ':' equation (',' equation)* [',']
    equation       := (term '=' term)

Note that the equations must be convergent and have the
Finite Variant Property (FVP), and do not allow the use
of fixed public names in the terms. Tamarin provides built-in
sets of function definitions and equations. They are
expanded upon parsing and you can therefore inspect them by pretty printing
the file using `tamarin-prover your_file.spthy`. The built-in `diffie-hellman`
is special. It refers to the equations given in Section [Cryptographic
Messages](004_cryptographic-messages.html#sec:equational-theories). You need to
enable it to parse terms containing exponentiations, e.g.,  g ^ x.

    built_in       := 'builtins' ':' built_ins (',' built_ins)* [',']
    built_ins      := 'diffie-hellman'
                    | 'hashing' | 'symmetric-encryption'
                    | 'asymmetric-encryption' | 'signing'
                    | 'bilinear-pairing' | 'xor'
                    | 'multiset' | 'revealing-signing'

A global heuristic sets the default heuristic that will be used when autoproving
lemmas in the file. The specified goal ranking can be any of those discussed in
Section [Heuristics](010_advanced-features.html#sec:heuristics).

    global_heuristic      := 'heuristic' ':' goal_ranking+
    goal_ranking          := standard_goal_ranking | oracle_goal_ganking
    standard_goal_ranking := 'C' | 'I' | 'P' | 'S' | 'c' | 'i' | 'p' | 's'
    oracle_goal_ranking   := 'o' '"' [^'"']* '"' | 'O' '"' [^'"']* '"'

The tactics allow the user to write their own heuristics based on the lemmas there are trying to prove. Their use is descibed in in Section [Using a Tactic](010_advanced-features.html#sec:fact-annotations#subsec:tactic).

    tactic                := 'tactic' ':' ident
                             [presort]
                             (prio)+ (deprio)* | (prio)* (deprio)+
    presort               := 'presort' ':' 'standard_goal_ranking
    prio                  := 'prio' ':' ['{'post_ranking'}']
                                 (function)+
    deprio                := 'deprio' ':' ['{'post_ranking'}']
                                 (function)+
    standard_goal_ranking := 'C' | 'I' | 'P' | 'S' | 'c' | 'i' | 'p' | 's'
    post_ranking          := 'smallest' | 'id'                   
    function              := and_function [ '|' and_function]*
    and_function          := not_function [ '&' not_function]*
    not_function          := (not)? function_name ['"' param '"']*
    function_name         :=   'regex' | 'isFactName' | 'isInFactTerms' | 'dhreNoise'
                             | 'defaultNoise' | 'reasonableNoncesNoise' | 'nonAbsurdGoal'

Multiset rewriting rules are specified as follows. The protocol corresponding
to a security protocol theory is the set of all multiset rewriting rules
specified in the body of the theory. Rule variants can be explicitly given, as
well as the left and right instances of a rule in diff-mode.
(When called with `--diff`, Tamarin will parse `diff_rule` instead of `rule`).

    rule        := simple_rule [variants]
    diff_rule   := simple_rule ['left' rule 'right' rule]
    simple_rule := 'rule' [modulo] ident [rule_attrs] ':'
            [let_block]
            '[' facts ']' ( '-->' | '--[' facts ']->') '[' facts ']'
    variants    := 'variants' simple_rule (',' simple_rule)*
    modulo      := '(' 'modulo' ('E' | 'AC') ')'
    rule_attrs  := '[' rule_attr (',' rule_attr)* [','] ']'
    rule_attr   := ('color=' | 'colour=') hexcolor
    let_block   := 'let' (msg_var '=' msetterm)+ 'in'
    msg_var     := ident ['.' natural] [':' 'msg']

Rule annotations do not influence the rule's semantics. A color is represented
as a triplet of 8 bit hexadecimal values optionally
preceded by '#', and is used as the background color of the rule when it is
rendered in graphs.

The let-block allows more succinct specifications. The equations are applied
in a bottom-up fashion. For example,

    let x = y
        y = <z,x>
    in [] --> [ A(y)]    is desugared to    [] --> [ A(<z,y>) ]

This becomes a lot less confusing if you keep the set of variables on the
left-hand side separate from the free variables on the right-hand side.

Macros works similarly to let-blocks, but apply globally to all rules.

    macros      := 'macros' ':' macro (',' macro)*
    macro       := ident '(' [(var) (',' var)*] ')' '=' term

Restrictions specify restrictions on the set of traces considered, i.e., they filter
the set of traces of a protocol. The formula of a restriction is available as an
assumption in the proofs of *all* security properties specified in this
security protocol theory.

    restriction := 'restriction' ident ':' '"' formula '"'

In observational equivalence mode, restrictions can be associated to one side.

    restriction := 'restriction' ident [restriction_attrs] ':' '"' formula '"'
    restriction_attrs      := '[' ('left' | 'right') ']'

Lemmas specify security properties. By default, the given formula is
interpreted as a property that must hold for all traces of the protocol of the
security protocol theory. You can change this using the 'exists-trace' trace
quantifier.

    lemma := 'lemma' [modulo] ident [lemma_attrs] ':'
             [trace_quantifier]
             '"' formula '"'
             proof_skeleton
    lemma_attrs      := '[' lemma_attr (',' lemma_attr)* [','] ']'
    lemma_attr       := 'sources' | 'reuse' | 'use_induction' |
                             'hide_lemma=' ident | 'heuristic=' goalRanking+
    trace_quantifier := 'all-traces' | 'exists-trace'

In observational equivalence mode, lemmas can be associated to one side.

    lemma_attr      := '[' ('sources' | 'reuse' | 'use_induction' |
                            'hide_lemma=' ident | 'heuristic=' heuristic |
                            'left' | 'right') ']'

A proof skeleton is a complete or partial proof as output by the Tamarin prover.
It indicates the proof method used at each step, which may include multiple cases.

    proof_skeleton :=  'SOLVED' | 'by' proof_method
                    | proof_method proof_skeleton
                    | proof_method 'case' ident proof_skeleton
                        ('next 'case' ident proof_skeleton)* 'qed'
    proof_method   := 'sorry' | 'simplify' | 'solve '(' goal ')' |
                      'contradiction' | 'induction'
    goal           :=  fact "▶" natural_subscr node_var
                    | fact '@' node_var
                    | '(' node_var ',' natural ')' '~~>' '(' node_var ',' natural ')'
                    | formula ("∥" formula)*
                    | 'splitEqs' '(' natural ')'
    node_var       := ['#'] ident ['.' natural]      // temporal sort prefix
                    | ident ['.' natural] ':' 'node' // temporal sort suffix
    natural        := digit+
    natural_sub    := ('₀'|'₁'|'₂'|'₃'|'₄'|'₅'|'₆'|'₇'|'₈'|'₉')+

Formal comments are used to make the input more readable. In contrast
to `/*...*/` and `//...` comments, formal comments are stored and output
again when pretty-printing a security protocol theory.

    formal_comment := ident '{*' ident* '*}'

For the syntax of terms, you best look at our examples. A common pitfall is to
use an undefined function symbol. This results in an error message pointing to
a position slightly before the actual use of the function due to some
ambiguity in the grammar.

We provide special syntax for tuples, multisets, xors, multiplications,
exponentiation, nullary and binary function symbols. An n-ary tuple
`<t1,...,tn>` is parsed as n-ary, right-associative application of pairing.
Multiplication and exponentiation are parsed left-associatively. For a binary
operator `enc` you can write `enc{m}k` or `enc(m,k)`. For nullary function
symbols, there is no need to write `nullary()`. Note that the number of
arguments of an n-ary function application must agree with the arity given in
the function definition.

    tupleterm := '<' msetterm (',' msetterm)* '>'
    msetterm  := xorterm ('+' xorterm)*
    xorterm   := multterm (('XOR' | ⊕) multterm)*
    multterm  := expterm ('*' expterm)*
    expterm   := term    ('^' term   )*
    term      := tupleterm             // n-ary right-associative pairing
               | '(' msetterm ')'      // a nested term
               | nullary_fun
               | binary_app
               | nary_app
               | literal

    nullary_fun := <all-nullary-functions-defined-up-to-here>
    binary_app  := binary_fun '{' tupleterm '}' term
    binary_fun  := <all-binary-functions-defined-up-to-here>
    nary_app    := nary_fun '(' multterm* ')'

    literal     := "'"  ident "'" // a fixed, public name
                 | "~'" ident "'" // a fixed, fresh name
                 | nonnode_var    // a non-temporal variable
    nonnode_var := ['$'] ident ['.' natural]         // 'pub' sort prefix
                 | ident ['.' natural] ':' 'pub'     // 'pub' sort suffix
                 | ['~'] ident ['.' natural]         // 'fresh' sort prefix
                 | ident ['.' natural] ':' 'fresh'   // 'fresh' sort suffix
                 | msg_var                                // 'msg' sort

Facts do not have to be defined up-front. This will probably change once we
implement user-defined sorts. Facts prefixed with `!` are persistent facts.
All other facts are linear. There are six reserved fact symbols: In, Out, KU,
KD, and K. KU and KD facts are used for construction and deconstruction
rules. KU-facts also log the messages deduced by construction rules. Note that
KU-facts have arity 2. Their first argument is used to track the
exponentiation tags. See the `loops/Crypto_API_Simple.spthy` example for more
information.

    facts := fact (',' fact)*
    fact  := ['!'] ident '(' [msetterm (',' msetterm)*] ')' [fact_annotes]
    fact_annotes := '[' fact_annote (',' fact_annote)* ']'
    fact_annote  := '+' | '-' | 'no_precomp'

Fact annotations can be used to adjust the priority of corresponding
goals in the heuristics, or influence the precomputation step performed by
Tamarin, as described in
Section [Advanced Features](010_advanced-features.html#sec:fact-annotations).

Formulas are trace formulas as described previously. Note that we are a bit
more liberal with respect to guardedness. We accept a conjunction of atoms as
guards.

    formula     := imp [('<=>' | '⇔') imp]
    imp         := disjunction [('==>' | '⇒') imp]
    disjunction := conjunction (('|' | '∨') conjunction)* // left-associative
    conjunction := negation (('&' | '∧') negation)*       // left-associative
    negation    := ['not' | '¬'] atom
    atom        := '⊥' | 'F' | '⊤' | 'T'        // true or false
                 | '(' formula ')'          // nested formula
                 | 'last' '(' node_var ')'  // 'last' temporal variable for induction
                 | fact '@' node_var        // action
                 | node_var '<' node_var    // ordering of temporal variables
                 | msetterm '=' msetterm    // equality of terms
                 | node_var '=' node_var    // equality of temporal variables
                 | ('Ex' | '∃' | 'All' | '∀') // quantified formula
                        lvar+ '.' formula

    lvar        := node_var | nonnode_var

Identifiers always start with a letter or number, and may contain underscores
after the first character. Moreover, they must not be one of the
reserved keywords `let`, `in`, or `rule`. Although identifiers beginning with
a number are valid, they are not allowed as the names of facts (which
must begin with an upper-case letter).
    ident := alphaNum (alphaNum | '_')*
