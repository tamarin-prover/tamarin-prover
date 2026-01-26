; Tamarin syntax highlight

; File structure
[
  "theory"
  "begin"
  "end"
] @keyword
(theory theory_name: (ident) @module)

; builtins
"builtins" @keyword
(built_in) @module.builtin

; rule
[
  "rule"
  "let"
  "in"
  "color="
  "colour="
  "role"
] @keyword
(simple_rule rule_identifier: (ident) @function)
(rule_role role_identifier: (ident) @string)

; lemma
"lemma" @keyword
(lemma lemma_identifier: (ident) @function)
[
  "All"
  "∀"
  "Ex"
  "∃"
  "all-traces"
  "exists-trace"
] @property

; other keywords
"equations" @keyword

(nary_app function_identifier: (ident) @function.builtin)

(temporal_var) @variable.temporal
(fresh_var) @variable.fresh
(pub_var) @constant
(nat_var) @variable.natural
(msg_var_or_nullary_fun) @variable

; operators
[
  "&"
  "<"
  "="
  "==>"
  ">"
  "@"
  "^"
  "|"
  "¬"
  "not"
] @operator

; facts
(linear_fact fact_identifier: (ident) @function)
"!" @punctuation.special
(persistent_fact fact_identifier: (ident) @function)

; comments
(single_comment) @comment.line
(multi_comment) @comment.block

; brackets
[
  "["
  "]"
  "--["
  "]->"
  "-->" ; not a bracket, but shuld be the same color
] @punctuation.bracket

; literal
(pub_name) @string.public
(fresh_name) @string.fresh
