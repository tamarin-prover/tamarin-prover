Syntax Description
==================

Here, we explain the formal syntax of the security protocol theory format that
is processed by Tamarin.

Comments are C-style and are allowed to be nested:

    /* for a multi-line comment */
    // for a line-comment

All security protocol theory are named and delimited by `begin` and `end`.
We explain the non-terminals of the body in the following paragraphs.


~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="theory,_body_item"}
~~~~

Here, we use the term signature more liberally to denote both the defined
function symbols and the equalities describing their interaction.  Note that
our parser is stateful and remembers what functions have been defined. It will
only parse function applications of defined functions.

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="_signature_spec,function,_function_sym,function_pub,function_private,function_destructor,equations,equation"}
~~~~

Note that the equations must be convergent and have the
Finite Variant Property (FVP), and do not allow the use
of fixed public names in the terms. Tamarin provides built-in
sets of function definitions and equations. They are
expanded upon parsing and you can therefore inspect them by pretty printing
the file using `tamarin-prover your_file.spthy`. The built-in `diffie-hellman`
is special. It refers to the equations given in Section [Cryptographic
Messages](004_cryptographic-messages.html#sec:equational-theories). You need to
enable it to parse terms containing exponentiations, e.g.,  g ^ x.

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="built_ins,built_in"}
~~~~

A global heuristic sets the default heuristic that will be used when autoproving
lemmas in the file. The specified proof method ranking can be any of those discussed in
Section [Heuristics](010_advanced-features.html#sec:heuristics).

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="global_heuristic,_goal_ranking,standard_goal_ranking,oracle_goal_ranking,tactic_goal_ranking,param"}
~~~~

The tactics allow the user to write their own heuristics based on the lemmas there are trying to prove. Their use is descibed in in Section [Using a Tactic](010_advanced-features.html#sec:fact-annotations#subsec:tactic).

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="tactic,presort,prio,deprio,standard_goal_ranking,post_ranking,_function,and_function,not_function,function_name"}
~~~~

Multiset rewriting rules are specified as follows. The protocol corresponding
to a security protocol theory is the set of all multiset rewriting rules
specified in the body of the theory. Rule variants can be explicitly given, as
well as the left and right instances of a rule in diff-mode.
(When called with `--diff`, Tamarin will parse `diff_rule` instead of `rule`).

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="_rule,rule,diff_rule,simple_rule,variants,modulo,rule_attrs,rule_attr,rule_let_block,rule_let_term,msg_var,msg_var_or_nullary_fun,hexcolor"}
~~~~

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

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="macros,macro,macro_identifier,_non_temporal_var"}
~~~~

Configuration blocks allow the specification of certain Tamarin command line options
in the model file itself. Options passed over the command line override options given
in a configuration block.

    configuration := 'configuration' ':' '"' option (' ' option)* '"'
    option          := '--auto-sources' | ('--stop-on-trace' '=' search_method)
    search_method := 'DFS' | 'BFS' | 'SEQDFS' | 'NONE'

Restrictions specify restrictions on the set of traces considered, i.e., they filter
the set of traces of a protocol. The formula of a restriction is available as an
assumption in the proofs of *all* security properties specified in this
security protocol theory. In observational equivalence mode, restrictions can be associated to one side.

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="restriction,restriction_attr"}
~~~~

Lemmas specify security properties. By default, the given formula is
interpreted as a property that must hold for all traces of the protocol of the
security protocol theory. You can change this using the 'exists-trace' trace
quantifier.
When exporting, one may indicate which lemmas should only be included in certain output formats.

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="_lemma,lemma,lemma_attrs,lemma_attr,trace_quantifier"}
~~~~

In observational equivalence mode, lemmas can be associated to one side.

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="diff_lemma,diff_lemma_attrs,diff_lemma_attr"}
~~~~

A proof skeleton is a complete or partial proof as output by the Tamarin prover.
It indicates the proof method used at each step, which may include multiple cases.

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="_proof_skeleton,_proof_methods,proof_method,goal,premise_goal,nod_var,solved,mirrored,by_method,method_skeleton,cases,premise_goal,action_goal,chain_goal,disjunction_split_goal,eq_split_goal,node_var,natural,natural_subscript"}
~~~~

Formal comments are used to make the input more readable. In contrast
to `/*...*/` and `//...` comments, formal comments are stored and output
again when pretty-printing a security protocol theory.

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="formal_comment"}
~~~~

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

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="tupleterm,mset_term,nat_term,xor_term,mult_term,exp_term,_term"}
~~~~

Tamarin's parser checks that functions were previously defined and are used with the correct arity.

~~~~
    nullary_fun := <all-nullary-functions-defined-up-to-here>
    binary_app  := binary_fun '{' tupleterm '}' term
    binary_fun  := <all-binary-functions-defined-up-to-here>
    nary_app    := nary_fun '(' multterm* ')'
~~~~

External tools may instead use the following grammar and check these conditions after parsing.

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="nulllary_fun,binary_app,binary_fun,nary_app"}
~~~~

Literals and variables appear in many forms.

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="_literal,_non_temporal_var"}
~~~~

When appearing in formulas or rules, they have an identifier and a sort.

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="fresh_name,_non_temporal_var,pub_var,fresh_var,msg_var_or_nullary_fun,nat_var"}
~~~~

SAPIC processes also have (optional) types. Moreover, literals in pattern can signify with a `=` if they are matched or bound.

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="comp_var,_custom_type_var,custom_var"}
~~~~

Facts do not have to be defined up-front. This will probably change once we
implement user-defined sorts. Facts prefixed with `!` are persistent facts.
All other facts are linear. There are six reserved fact symbols: In, Out, KU,
KD, Fr, and K. KU and KD facts are used for construction and deconstruction
rules. KU-facts also log the messages deduced by construction rules. Note that
KU-facts have arity 2. Their first argument is used to track the
exponentiation tags. See the `loops/Crypto_API_Simple.spthy` example for more
information.

~~~~ {.tamarin grammar="grammar/grammar.ebnf" rules="_facts,_fact,fact_annotes,fact_annote"}
~~~~
    facts := fact (',' fact)*
    fact  := ['!'] ident '(' [msetterm (',' msetterm)*] ')' [fact_annotes]
    fact_annotes := '[' fact_annote (',' fact_annote)* ']'
    fact_annote  := '+' | '-' | 'no_precomp'

Fact annotations can be used to adjust the priority of corresponding
proof methods in the heuristics, or influence the precomputation step performed by
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
    atom        := '⊥' | 'F' | '⊤' | 'T'           // true or false
                 | '(' formula ')'                 // nested formula
                 | 'last' '(' node_var ')'         // 'last' temporal variable for induction
                 | fact '@' node_var               // action
                 | node_var '<' node_var           // ordering of temporal variables
                 | msetterm '=' msetterm           // equality of terms
                 | msetterm ('<<' | '⊏') msetterm  // subterm relation
                 | node_var '=' node_var           // equality of temporal variables
                 | ('Ex' | '∃' | 'All' | '∀')      // quantified formula
                        lvar+ '.' formula

    lvar        := node_var | nonnode_var

Identifiers always start with a letter or number, and may contain underscores
after the first character. Moreover, they must not be one of the
reserved keywords `let`, `in`, or `rule`. Although identifiers beginning with
a number are valid, they are not allowed as the names of facts (which
must begin with an upper-case letter).

Full syntax
-----------

The following [Treesitter](https://tree-sitter.github.io/tree-sitter/)-generated eBNF is regularly tested against the files in `examples`. It includes the aforementioned rules, and those concerning the [process calculus SAPIC+](006_protocol-specification-processes.html).

~~~~ {.tamarin include="grammar/grammar.ebnf"}
~~~~
