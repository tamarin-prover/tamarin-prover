/**
 * @file spthy grammar for tree-sitter
 * @author Lennard Tworeck
 */

module.exports = grammar({
  name: 'spthy',

  // Tokens that may appear anywhere in the language
  extras: $ => [
      $.multi_comment,
      $.single_comment,
      /\s|\\\r?\n|\u00A0/
  ],

  conflicts: $ => [
      // Conflict between quantifiers and variables:
      // e.g. ∀ msg_var #temp_var.5. T
      [$.pub_var], [$.fresh_var], [$.msg_var_or_nullary_fun], [$.temporal_var], [$.nat_var],
      [$.pub_var, $.fresh_var, $.msg_var_or_nullary_fun, $.temporal_var, $.nat_var],
      [$.pub_var, $.fresh_var, $.msg_var_or_nullary_fun, $.nat_var],

      // All Lemmas can use just 'lemma' as a keyword
      [$.accountability_lemma, $.diff_lemma],
      [$.lemma, $.diff_lemma],

      // Conflict since both look alike, but they don't appear in the same scenarios.
      [$.nary_app, $.predicate_ref],

      // Conflict since parser cannot decide how to parse ident
      [$.nullary_fun, $.nary_app, $.msg_var_or_nullary_fun]
  ],

  externals: $ => [
      $.multi_comment,
      $.single_comment
  ],

  precedences: $ => [
      [
          // Term
          'NESTED',
          'FUNCTION',
          'VARIABLE',
          'EXPONENTIAL',
          'MULTIPLY',
          'ADD',
          'MUL_SET',
          'TUPLE',
          'NULLARY_FUN',

          // Formula
          'ATOM',
          'LOGICAL_NOT',
          'EXCLUSIVE_OR',
          'LOGICAL_AND',
          'LOGICAL_OR',
          'LOGICAL_IMPLICATION',
          'LOGICAL_IFF',
          'CHAIN_GOAL',
      ],
      // Diff
      [
          'NON_DIFF',
          'DIFF'
      ],
      [
          'REPLICATION',
          'EVENT',
          'CHOICE',
          'PROCESS_LET',
          'LOOKUP',
          'CONDITIONAL'
      ]
  ],

  word: $ => $.ident,

  rules: {
      theory: $ => seq(
          'theory',
          field('theory_name', $.ident),
          'begin',
          repeat($._body_item),
          'end',
          repeat(
              /./
          )
      ),

      _body_item: $ => choice(
          $.preprocessor,
          $._signature_spec,
          $.global_heuristic,
          $.tactic,
          $.process,  // SAPIC+
          $.let,
          $.export,
          $._rule,
          $.restriction,
          $.case_test,
          $._lemma,
          $.formal_comment
      ),


      /*
       * Preprocessor:
       */
      preprocessor: $ => choice(
          $.ifdef,
          $.define,
          $.include
      ),

      ifdef: $ => seq(
          '#ifdef',
          $._ifdef_formula,
          repeat($._body_item),
          optional(seq(
              '#else',
              repeat($._body_item)
          )),
          '#endif'
      ),

      define: $ => seq(
          '#define',
          $.ident
      ),

      include: $ => seq(
          '#include',
          '"', alias($.param, $.path), '"'
      ),

      _ifdef_formula: $ => choice(
          $.ifdef_nested,
          $.ifdef_or,
          $.ifdef_and,
          $.ifdef_not,
          $.ident
      ),

      ifdef_nested: $ => prec('NESTED', seq(
          '(', $._ifdef_formula, ')'
      )),

      ifdef_or: $ => prec.left('LOGICAL_OR', seq(
          $._ifdef_formula, '|', $._ifdef_formula
      )),

      ifdef_and: $ => prec.left('LOGICAL_AND', seq(
          $._ifdef_formula, '&', $._ifdef_formula
      )),

      ifdef_not: $ => prec('LOGICAL_NOT', seq(
          'not', $._ifdef_formula
      )),


      /*
       * Signature specification:
       */
      _signature_spec: $ => choice(
          $.built_ins,
          $.functions,
          $.equations,
          $.predicates,
          $.macros,
          $.options
      ),

      // Builtins:
      built_ins: $ => seq(
          'builtins',
          ':',
          $.built_in,
          repeat(seq(
              ',',
              $.built_in
          )),
          optional(',')
      ),

      built_in: $ => choice(
          'diffie-hellman',
          'hashing',
          'symmetric-encryption',
          'asymmetric-encryption',
          'signing',
          'bilinear-pairing',
          'xor',
          'multiset',
          'natural-numbers',
          'revealing-signing',
          'locations-report',
          'reliable-channel',
          'dest-pairing',
          'dest-signing',
          'dest-symmetric-encryption',
          'dest-asymmetric-encryption'
      ),

      // Functions:
      functions: $ => prec.right(seq(
          'functions',
          ':',
          $._function_sym,
          repeat(seq(
              ',',
              $._function_sym
          )),
          optional(',')
      )),

      _function_sym: $ => choice(
          $.function_pub,
          $.function_private,
          $.function_destructor,
          $.function_custom
      ),

      function_pub: $ => seq(
          field('function_identifier', $.ident),
          '/',
          field('arity', $.natural)
      ),

      function_private: $ => seq(
          field('function_identifier', $.ident),
          '/',
          field('arity', $.natural),
          '[', 'private', ']'
      ),

      function_destructor: $ => seq(
          field('function_identifier', $.ident),
          '/',
          field('arity', $.natural),
          '[', 'destructor', ']'
      ),

      function_custom: $ => seq(
          field('function_identifier', $.ident),
          '(', optional($.arguments), ')',
          ':', field('function_type', $.ident)
      ),

      // Equations:
      equations: $ => prec.right(seq(
          'equations',
          ':',
          $.equation,
          repeat(seq(
             ',',
             $.equation
          )),
          optional(',')
      )),

      equation: $ => seq(
          field('left', $._term),
          '=',
          field('right', $._term)
      ),

      // Predicates:
      predicates: $ => seq(
          choice('predicate', 'predicates'), ':',
          $.predicate,
          repeat(seq(
              ',', $.predicate
          ))
      ),

      predicate: $ => seq(
          alias($.predicate_def, ''),
          '<=>',
          field('formula', $._formula)
      ),

      predicate_def: $ => seq(
          field('predicate_identifier', $.ident),
          '(', optional($.arguments), ')'
      ),

      // Options:
      options: $ => seq(
          'options',
          ':',
          $.option,
          repeat(seq(
              ',',
              $.option
          )),
          optional(',')
      ),

      option: $ => choice(
          'translation-state-optimisation',
          'translation-progress',
          'translation-asynchronous-channels',
          'translation-compress-events',
          'translation-allow-pattern-lookups'
      ),


      /*
       * Global heuristic:
       */
      global_heuristic: $ => seq(
          'heuristic',
          ':',
          field('goal_ranking', repeat1($._goal_ranking))
      ),

      _goal_ranking: $ => choice(
          $.standard_goal_ranking,
          $.oracle_goal_ranking,
          $.tactic_goal_ranking
      ),

      standard_goal_ranking: $ => /[CISPcisp][CISPcisp]?[CISPcisp]?[CISPcisp]?/,

      oracle_goal_ranking: $ => seq(
          choice('O', 'o'),
          optional(seq('"', $.param, '"'))
      ),

      tactic_goal_ranking: $ => seq(
          '{', $.ident, '}' // in this case ident has to be a tactic name
      ),


      /*
       * Tactic:
       */
      tactic: $ => seq(
          'tactic', ':',
          $.ident,
          optional($.presort),
          choice(
              seq(
                  repeat1($.prio),
                  repeat($.deprio)
              ),
              seq(
                  repeat($.prio),
                  repeat1($.deprio)
              )
          )
      ),

      presort: $ => seq(
          'presort', ':',
          $.standard_goal_ranking
      ),

      prio: $ => seq(
          'prio', ':',
          optional(seq(
              '{', $.post_ranking, '}'
          )),
          repeat1($._function)
      ),

      deprio: $ => seq(
          'deprio', ':',
          optional(seq(
              '{', $.post_ranking, '}'
          )),
          repeat1($._function)
      ),

      post_ranking: $ => choice(
          'smallest', 'id'
      ),

      _function: $ => choice(
          $.or_function,
          $.and_function,
          $.not_function,
          $.std_function
      ),

      or_function: $ => prec.left('LOGICAL_OR', seq(
          $._function, '|', $._function
      )),

      and_function: $ => prec.left('LOGICAL_AND', seq(
          $._function, '&', $._function
      )),

      not_function: $ => prec('LOGICAL_NOT', seq(
          'not', $._function
      )),

      std_function: $ => seq(
          $.function_name,
          repeat(seq(
              '"', $.param, '"'
          ))
      ),

      function_name: $ => choice(
          'regex',
          'isFactName',
          'isInFactTerms',
          'dhreNoise',
          'defaultNoise',
          'reasonableNoncesNoise',
          'nonAbsurdGoal'
      ),


      /*
       * SAPIC+
       */
      process: $ => seq(
          'process', ':',
          $._process
      ),

      _process: $ => choice(
          $._elementary_process,
          $._extended_process,
          $._stateful_process,
          $.inline_msr_process,
          $._nested_process,
          $.location_process,
          $.predefined_process

      ),

      _elementary_process: $ => choice(
          $.binding,
          $.output,
          $.input,
          $.conditional,
          $.process_let,
          $.deterministic_choice,
          $.non_deterministic_choice,
          $.null
      ),

      _extended_process: $ => choice(
          $.event,
          $.replication
      ),

      _stateful_process: $ => choice(
          $.set_state,
          $.delete_state,
          $.read_state,
          $.set_lock,
          $.remove_lock
      ),

      location_process: $ => seq(
          '(',
          $._process,
          ')', '@',
          field('location_identifier', choice($._literal, $.tuple_term))
      ),

      inline_msr_process: $ => prec.right(seq(
          $.premise,
          choice(
              '-->',
              $.action_fact
          ),
          $.conclusion,
          optional(seq(';', $._process))
      )),

      // represents processes that have been defined and named in let-blocks:
      _nested_process: $ => seq(
          '(', $._process, ')'
      ),

      predefined_process: $ => prec.left(-1, $._term),

      // elementary processes:
      binding: $ => prec.right(seq(
          'new', $._literal,
          optional(seq(';', $._process))
      )),

      output: $ => prec.right(choice(
          seq(
              'out', '(', $._term, ',', $._term, ')',
              optional(seq(';', $._process))
          ),
          seq(
              'out', '(', $._term, ')',
              optional(seq(';', $._process))
          )
      )),

      input: $ => prec.right(choice(
          seq(
              'in', '(', $._term, ',', $._term, ')',
              optional(seq(';', $._process))
          ),
          seq(
              'in', '(', $._term, ')',
              optional(seq(';', $._process))
          )
      )),

      conditional: $ => prec.right('CONDITIONAL', seq(
          'if', field('condition', $._condition),
          'then', field('then', $._process),
          optional(seq('else', field('else', $._process)))
      )),

      process_let: $ => prec.right('PROCESS_LET', seq(
          'let',  repeat1($.term_eq),
          'in', field('in', $._process),
          optional(seq('else', field('else', $._process)))
      )),

      deterministic_choice: $ => prec.left('CHOICE', seq(
          $._process,
          choice('|', '||'),
          $._process
      )),

      non_deterministic_choice: $ => prec.left('CHOICE', seq(
          $._process,
          choice('+'),
          $._process
      )),

      null: $ => '0',

      // extended processes:
      event: $ => prec.right('EVENT', seq(
          'event', $._fact,
          optional(seq(';', $._process))
      )),

      replication: $ => prec.right('REPLICATION', seq(
          '!', $._process,
          optional(seq(';', $._process))
      )),

      // stateful processes:
      set_state: $ => prec.right(seq(
          'insert',
          field('from', $._term), ',',
          field('to', $._term),
          optional(seq(';', $._process))
      )),

      delete_state: $ => prec.right(seq(
          'delete', $._term,
          optional(seq(';', $._process))
      )),

      read_state: $ => prec.right('LOOKUP', seq(
          'lookup', field('from', $._term),
          'as', field('to',$._lvar),
          'in', field('in', $._process),
          optional(seq('else', field('else', $._process))),
          optional(seq(';', $._process))
      )),

      set_lock: $ => prec.right(seq(
          'lock', $._term,
          optional(seq(';', $._process))
      )),

      remove_lock: $ => prec.right(seq(
          'unlock', $._term,
          optional(seq(';', $._process))
      )),

      _condition: $ => choice(
          $.equality_check,
          $.lesser_check,
          $.predicate_ref
      ),

      equality_check: $ => seq(
          choice($._term, $._formula), token(prec(1, '=')), choice($._term, $._formula)
      ),

      lesser_check: $ => seq(
          $._term, choice('(<)', '<<'), $._term
      ),


      /*
       * Top-level let-block:
       */
      let: $ => seq(
          'let',
          field('let_identifier', $._term), '=',
          $._process
      ),

      /*
       * Export:
       */
      export: $ => seq(
          'export',
          field('export_identifier', $.ident),
          ':', '"', $.export_query, '"'
      ),

      /*
       * Rule:
       */
      _rule: $ => choice(
          $.rule,
          $.diff_rule
      ),

      rule: $ => seq(
          $.simple_rule,
          optional($.variants)
      ),

      diff_rule: $ => seq(
          $.simple_rule,
          'left', field('left', $.rule),
          'right', field('right', $.rule)
      ),

      simple_rule: $ => seq(
          'rule',
          optional($.modulo),
          field('rule_identifier', $.ident),
          optional($.rule_attrs),
          ':',
          optional($.rule_let_block),
          $.premise,
          choice(
              '-->',
              $.action_fact
          ),
          $.conclusion
      ),

      premise: $ => seq(
          '[', optional($._facts), ']'
      ),

      action_fact: $ => seq(
          '--[', optional($._facts_restrictions), ']->'
      ),

      conclusion: $ => seq(
          '[', optional($._facts), ']'
      ),

      variants: $ => seq(
          'variants',
          $.simple_rule,
          repeat(seq(
              ',',
              $.simple_rule
          ))
      ),

      modulo: $ => seq(
          '(',
          'modulo',
          choice('E', 'AC'),
          ')'
      ),

      rule_attrs: $ => seq(
          '[',
          $.rule_attr,
          repeat(seq(
              ',',
              $.rule_attr
          )),
          optional(','),
          ']'
      ),

      rule_attr: $ => seq(
          choice(
              'color=',
              'colour='
          ),
          $.hexcolor
      ),

      rule_let_block: $ => seq(
          'let',
          repeat1($.rule_let_term),
          'in'
      ),

      rule_let_term: $ => seq(
          field('left', choice($.msg_var_or_nullary_fun, $.nat_var)),
          '=',
          field('right', $._term)
      ),

      macros: $ => seq(
          'macros',
          ':',
          $.macro,
          repeat(seq(
              ',',
              $.macro
          ))
      ),

      macro: $ => seq(
          field('macro_identifier', $.ident),
          '(',
          optional(seq(
              $._non_temporal_var,
              repeat(seq(
                  ',',
                  $._non_temporal_var
              ))
          )),
          ')',
          '=',
          field('term', $._term)
      ),

      embedded_restriction: $ => seq(
          '_restrict',
          '(', field('formula', $._formula), ')'
      ),

      // Fact:
      _facts_restrictions: $ => prec.left(seq(
          choice($._fact, $.embedded_restriction),
          repeat(seq(
              ',',
              choice($._fact, $.embedded_restriction)
          ))
      )),

      _facts: $ => prec.left(seq(
          $._fact,
          repeat(seq(
              ',',
              $._fact
          ))
      )),

      _fact: $ => choice(
          alias($.fact, $.linear_fact),
          seq(
              '!',
              alias($.fact, $.persistent_fact)
          )
      ),

      fact: $ => prec.left(seq(
          field('fact_identifier', $.ident),
          '(',
          optional($.arguments),
          ')',
          optional($.fact_annotes)
      )),

      fact_annotes: $ => seq(
          '[',
          $.fact_annote,
          repeat(seq(
              ',',
              $.fact_annote
          )),
          ']'
      ),

      fact_annote: $ => choice(
          '+',
          '-',
          'no_precomp'
      ),


      /*
       * Restriction:
       */
      restriction: $ => seq(
          // 'axiom' is a retired notation and is exchanged to 'restriction' by Tamarin
          choice('restriction', 'axiom'),
          field('restriction_identifier', $.ident),
          optional($.restriction_attr),
          ':',
          '"', field('formula', $._formula), '"'
      ),

      restriction_attr: $ => seq(
          '[',
          choice(
              'left',
              'right'
          ),
          ']'
      ),


      /*
       * Case test:
       */
      case_test: $ => seq(
          'test',
          field('test_identifier', $.ident), ':',
          '"', field('formula', $._formula), '"'
      ),


      /*
       * Lemma:
       */
      _lemma: $ => choice(
          $.lemma,
          $.diff_lemma,
          $.accountability_lemma,
          $.equiv_lemma,
          $.diff_equiv_lemma
      ),

      lemma: $ => seq(
          'lemma',
          optional($.modulo),
          field('lemma_identifier', $.ident),
          optional($.lemma_attrs),
          ':',
          optional($.trace_quantifier),
          '"', field('formula', $._formula), '"',
          optional(field('proof_skeleton', $._proof_skeleton))
      ),

      lemma_attrs: $ => seq(
          '[',
          $.lemma_attr,
          repeat(seq(
              ',',
              $.lemma_attr
          )),
          optional(','),
          ']'
      ),

      lemma_attr: $ => choice(
          'sources',
          'reuse',
          'use_induction',
          seq('output=', '[', $.language, repeat(seq(',', $.language)), ']'),
          seq('hide_lemma=', $.ident),
          seq('heuristic=', field('goal_ranking', repeat1($._goal_ranking)))
      ),

      language: $ => choice(
          'spthy',
          'spthytyped',
          'msr',
          'proverif',
          'deepsec'

      ),

      diff_lemma: $ => seq(
          choice('diffLemma', 'lemma'),
          optional($.modulo),
          field('lemma_identifier', $.ident),
          optional($.diff_lemma_attrs),
          ':',
          optional($.trace_quantifier),
          optional(seq(
              '"', field('formula', $._formula), '"'
          )),
          optional(field('proof_skeleton', $._proof_skeleton))
      ),

      diff_lemma_attrs: $ => seq(
          '[',
          repeat(prec.right(seq($.lemma_attr, ','))),
          optional($.diff_lemma_attr),
          repeat(prec.right(seq(',', $.lemma_attr))),
          optional(','),
          ']'
      ),

      diff_lemma_attr: $ => choice(
          'left',
          'right'
      ),

      accountability_lemma: $ => seq(
          'lemma',
          field('lemma_identifier', $.ident), ':',
          field('test_identifier', $.ident), repeat(seq(',', field('test_identifier', $.ident))),
          choice('account', 'accounts'), 'for',
          '"', field('formula', $._formula), '"'
      ),

      equiv_lemma: $ => seq(
          'equivLemma', ':',
          field('first', $._process),
          field('second', $._process)
      ),

      diff_equiv_lemma: $ => seq(
          'diffEquivLemma', ':',
          $._process
      ),

      trace_quantifier:  $ => choice(
          'all-traces',
          'exists-trace'
      ),


      /*
       * Proof:
       */
      _proof_skeleton: $ => choice(
          $.solved,
          $.mirrored,
          $.by_method,
          $.method_skeleton,
          $.cases
      ),

      solved: $ => 'SOLVED',

      mirrored: $ => 'MIRRORED',

      by_method: $ => seq(
          'by',
          $._proof_methods
      ),

      method_skeleton: $ => seq(
          $._proof_methods,
          field('proof_skeleton', $._proof_skeleton)
      ),

      cases: $ => seq(
          $.case,
          repeat(seq(
              'next', $.case
          )),
          'qed'
      ),

      case: $ => seq(
          'case',
          field('case_identifier', $.ident),
          field('proof_skeleton', $._proof_skeleton)
      ),

      _proof_methods: $ => prec.right(choice(
          $.proof_method,
          repeat1($.step)
      )),

      proof_method: $ => choice(
          'sorry',
          'simplify',
          seq(
              'solve', '(', $.goal, ')'
          ),
          'contradiction',
          'induction',
          'rule-equivalence',
          'backward-search',
          'ATTACK'
      ),

      step: $ => seq(
        'step', '(', $.proof_method, ')'
      ),

      goal: $ => choice(
          $.premise_goal,
          $.action_goal,
          $.chain_goal,
          $.disjunction_split_goal,
          $.eq_split_goal
      ),

      premise_goal: $ => seq(
          $._fact,
          '▶',
          $.natural_subscript,
          $.temporal_var
      ),

      action_goal: $ => seq(
          $._fact,
          '@',
          $.temporal_var
      ),

      chain_goal: $ => seq(
          '(', $.temporal_var, ',', $.natural, ')',
          '~~>',
          '(', $.temporal_var, ',', $.natural, ')'
      ),

      disjunction_split_goal: $ => prec('CHAIN_GOAL', seq(
          field('formula', $._formula),
          repeat1(seq(
              choice('||', '∥'),
              field('formula', $._formula)
          ))
      )),

      eq_split_goal: $ => seq(
          'splitEqs',
          '(', $.natural, ')'
      ),


      /*
       * Term:
       */
      _term: $ => choice(
          $.tuple_term,
          $.mset_term,
          $.nat_term,
          $.xor_term,
          $.mul_term,
          $.exp_term,
          $.nested_term,
          $.nullary_fun,
          $.binary_app,
          $.nary_app,
          $._literal
      ),

      tuple_term: $ => prec('TUPLE', seq(
          '<',
          field('term', choice($._term)),
          repeat(seq(
              ',',
              field('term', $._term)
          )),
          '>'
      )),

      mset_term: $ => prec.left('MUL_SET', seq(
          field('left', $._term),
          choice('++', '+'),
          field('right', $._term)
      )),

      nat_term: $ => prec.left('ADD', seq(
          field('left', $._term),
          '%+',
          field('right', $._term)
      )),

      xor_term: $ => prec.left('EXCLUSIVE_OR', seq(
          field('left', $._term),
          choice('XOR', '⊕'),
          field('right', $._term)
      )),

      mul_term: $ => prec.left('MULTIPLY', seq(
          field('left', $._term),
          '*',
          field('right', $._term)
      )),

      exp_term: $ => prec.right('EXPONENTIAL', seq(
          field('base', $._term),
              '^',
          field('exponent', $._term)
      )),

      nested_term: $ => prec('NESTED', seq(
          '(', $._term, ')'
      )),

      nullary_fun: $ => prec('NULLARY_FUN', choice(
          field('function_identifier', $.ident),
          seq(
              field('function_identifier', $.ident), '(', ')'
          )
      )),

      binary_app: $ => prec('FUNCTION', seq(
          field('function_identifier', $.ident),
          '{',
          field('argument', $._term),
          optional(repeat(seq(',', field('argument', $._term)))),
          '}',
          field('argument', $._term)
      )),

      nary_app: $ => prec('FUNCTION', seq(
          field('function_identifier', $.ident),
          '(', $.arguments, ')'
      )),

      arguments: $ => seq(
          field('argument', choice($._term, $.temporal_var)),
          repeat(seq(
              ',', field('argument', $._term)
          ))
      ),

      // Variable:
      _literal: $ => choice(
          $.pub_name,
          $.fresh_name,
          $._non_temporal_var, // non-temporal variable
          $.comp_var, // compare variable for pattern matching
          $._custom_type_var // variable with custom type
      ),

      _non_temporal_var: $ => choice(
          $.pub_var,
          $.fresh_var,
          $.msg_var_or_nullary_fun,
          $.nat_var
      ),

      pub_var: $ => prec('VARIABLE', choice(
          seq( //'pub' sort prefix
              '$',
              field('variable_identifier', $.ident),
              optional(seq(
                  '.', $.natural
              ))
          ),
          seq( //'pub' sort suffix
              field('variable_identifier', $.ident),
              optional(seq(
                  '.', $.natural
              )),
              ':', 'pub'
          ),
      )),

      fresh_var: $ => prec('VARIABLE', choice(
          seq( //'fresh' sort prefix
              '~',
              field('variable_identifier', $.ident),
              optional(seq(
                  '.', $.natural
              ))
          ),
          seq( //'fresh' sort suffix
              field('variable_identifier', $.ident),
              optional(seq(
                  '.', $.natural
              )),
              ':', 'fresh'
          )
      )),

      msg_var_or_nullary_fun: $ => prec('VARIABLE' ,seq(
          field('variable_identifier', $.ident), // 'msg' sort prefix
          optional(seq(
              '.',
              $.natural
          )),
          optional(seq( // 'msg' sort suffix
              ':',
              'msg'
          ))
      )),

      temporal_var: $ => choice(
          seq( // 'temporal' sort prefix
              '#',
              field('variable_identifier', $.ident),
              optional(seq(
                  '.', $.natural
              ))
          ),
          seq( // 'temporal' sort suffix
              field('variable_identifier', $.ident),
              optional(seq(
                  '.', $.natural
              )),
              ':', 'node'
          )
      ),

      nat_var: $ => choice(
          seq( // 'natural' sort prefix
              '%',
              field('variable_identifier', $.ident),
              optional(seq(
                  '.', $.natural
              )),
              optional(seq(
                  ':', 'nat'
              ))
          ),
          seq( // 'natural' sort suffix
              field('variable_identifier', $.ident),
              optional(seq(
                  '.', $.natural
              )),
              ':', 'nat'
          )
      ),

      // compared variable for pattern matching
      comp_var: $ => seq(
          '=',
          $._literal
      ),

      _custom_type_var: $ => choice(
          $.custom_var,
          $.any_var
      ),

      custom_var: $ => prec(-1, seq(
          $._literal,
          ':', field('variable_type', $.ident)
      )),

      any_var: $ => prec(-1, seq(
          $._literal,
          ':', 'ANY'
      )),

      // temporal prefix is optional for action constraints and temporal ordering
      temporal_var_optional_prefix: $ => prec('NULLARY_FUN', choice(
          seq(
              optional('#'),
              field('variable_identifier', $.ident),
              optional(seq(
                  '.', $.natural
              ))
          ),
          seq(
              field('variable_identifier', $.ident),
              optional(seq(
                  '.', $.natural
              )),
              ':', 'temporal'
          )
      )),

      pub_name: $ =>  seq( // fixed, public name
          "'",
          /[^\n']+/,
          "'"
      ),

      fresh_name: $ => seq( // fixed, fresh name
          "~'",
          /[^\n']+/,
          "'"
      ),


      /*
       * Formula:
       */
      _formula: $ => choice(
          $.iff,
          $.imp,
          $.disjunction,
          $.conjunction,
          $.negation,
          $.nested_formula,
          $._temporal_variable_operation,
          $.action_constraint,
          $.term_eq,
          $.subterm_rel,
          $.quantified_formula,
          $.atom,
          $.predicate_ref,
          $.pre_defined
      ),

      iff: $ => prec.left('LOGICAL_IFF', seq(
          field('left', $._formula),
          choice('<=>', '⇔'),
          field('right', $._formula)
      )),

      imp: $ => prec.left('LOGICAL_IMPLICATION', seq(
          field('left', $._formula),
          choice(token(prec(1, '==>')), '⇒'),
          field('right', $._formula)
      )),

      disjunction: $ => prec.left('LOGICAL_OR', seq(
          field('left', $._formula),
          choice('|', '∨'),
          field('right', $._formula)
      )),

      conjunction: $ => prec.left('LOGICAL_AND', seq(
          field('left', $._formula),
          choice('&', '∧'),
          field('right', $._formula)
      )),

      negation: $ => prec('LOGICAL_NOT', seq(
          choice('not', '¬'),
          field('formula', $._formula),
      )),

      nested_formula: $ => prec('ATOM', seq(
          '(', $._formula, ')'
      )),

      _temporal_variable_operation: $ => choice(
          $.temp_var_induction,
          $.temp_var_order,
          $.temp_var_eq
      ),

      temp_var_induction: $ => prec('ATOM', seq(
          'last', '(', $.temporal_var, ')'
      )),

      temp_var_order: $ => prec('ATOM', seq(
          field('left', alias($.temporal_var_optional_prefix, $.temporal_var)),
          '<',
          field('right', alias($.temporal_var_optional_prefix, $.temporal_var))
      )),

      temp_var_eq: $ => prec('ATOM', seq(
          field('left', alias($.temporal_var_optional_prefix, $.temporal_var)),
          '=',
          field('right', alias($.temporal_var_optional_prefix, $.temporal_var))
      )),

      action_constraint: $ => prec('ATOM', seq(
          field('fact', $._fact),
          '@',
          field('variable', alias($.temporal_var_optional_prefix, $.temporal_var))
      )),

      term_eq: $ => prec('ATOM', seq(
          field('left', $._term),
          '=',
          field('right', $._term)
      )),

      subterm_rel: $ => prec('ATOM', seq(
          field('left', $._term),
          choice('<<', '⊏'),
          field('right', $._term)
      )),

      quantified_formula: $ => prec('ATOM', seq(
          choice('Ex', '∃', 'All', '∀'),
          field('variable', repeat1($._lvar)),
          '.',
          field('formula', $._formula)
      )),

      atom: $ => prec('ATOM', choice(
          '⊥', 'F', '⊤', 'T', // True, False
      )),

      _lvar: $ => choice(
          $.temporal_var,
          $._non_temporal_var
      ),

      // predicate reference that is substituted with the predicate by Tamarin
      predicate_ref: $ => prec('FUNCTION', seq(
          field('predicate_identifier', $.ident),
          '(', optional($.arguments), ')'
      )),

      // some predefined function, let_block, ...
      pre_defined: $ => prec('NULLARY_FUN', $.ident),


      /*
       * Terminals:
       */
      hexcolor: $ => choice(
          seq(
              "'",
              optional(token("#")),
              token(/[0-9a-fA-F]{1,6}/),
              "'"),
          seq(
              optional(token("#")),
              token(/[0-9a-fA-F]{1,6}/)
          )
      ),

      ident: $ => /[A-Za-z0-9]\w*/,

      param: $ => /[^"]*/,

      export_query: $ => /(\\"|[^"])*/,

      natural: $ => /[0-9]+/,

      natural_subscript: $ => repeat1(choice(
          '₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉'
      )),


      /*
       * Comment:
       */
      formal_comment: $ => seq(
          field('comment_identifier', $.ident),
          token(seq(
              '{*',
              /[^*]*\*+([^}*][^*]*\*+)*/,
              '}'
          ))
      )

  }
});
