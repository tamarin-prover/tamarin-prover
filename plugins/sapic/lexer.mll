{
open Printf
open Sapic (* Assumes the parser file is "sapic.mly". *) 
open Char
let fc = ref ""
}


rule token = parse
     | [' ' '\t' ]    { token lexbuf }   (* ignore whitespace, line breaks, ... *)
     | ['\n']    { Lexing.new_line lexbuf; token lexbuf }   (* increase line_counter *)
     | "//" [^'\n']* '\n' { Lexing.new_line lexbuf; token lexbuf }   (* ignore one-line comments *)
     | "/*"        { commentslash lexbuf }        (* begin of multi-line comment; switch to "comment" rule *)
     | "(*"        { commentparent lexbuf }        (* begin of multi-line comment; switch to "comment" rule *)
     (* | '\n'        { NEWLINE } *)
     | '.'         { POINT }
     | "theory"    { THEORY }
     | "rule"      { RULE }
     | "begin"     { BEGIN }
     | "end"       { END }
     | "builtins"  { BUILTINS }
     | "diffie-hellman" as theory	 { BUILTIN_THEORY (theory) }
     | "hashing" as theory 		 { BUILTIN_THEORY (theory) }
     | "symmetric-encryption" as theory  { BUILTIN_THEORY (theory) }
     | "asymmetric-encryption" as theory { BUILTIN_THEORY (theory) }
     | "multiset" as theory { BUILTIN_THEORY (theory) }
     | "signing" as theory     	  	 { BUILTIN_THEORY (theory) }
     | "functions" { FUNCTIONS }
     | "equations" { EQUATIONS }
     | "predicates" { PREDICATES }
     | "options" { OPTIONS }
     | "progress" { PROGRESS }
     | "lemma"     { LEMMA }
     | "axiom"       { Printf.eprintf "\"axiom\" is deprecated, replace with \"restriction\".\n"; RESTRICTION }
     | "restriction" { RESTRICTION }
     | "verdictfunction" { VERDICTFUNCTION }
     | "private" as attr     { FUNCTION_ATTR(attr) }
     | "typing" 			{ Printf.eprintf "Option \"typing\" is deprecated, replace with \"sources\".\n";  LEMMA_ATTR ("sources") } 
     | "sources"    as attr		{ LEMMA_ATTR (attr) } 
     | "reuse"	as attr			{ LEMMA_ATTR (attr) } 
     | "inductive" as attr		{ LEMMA_ATTR (attr) } 
     | "invariant" as attr		{ LEMMA_ATTR (attr) } 
     | "use_induction" as attr		{ LEMMA_ATTR (attr) } 
     | "hide_lemma" { HIDE_LEMMA }
     | "all-traces" { ALL_TRACES ('A') }
     | "exists-trace" { EXISTS_TRACE ('E') }
     | "All"	   { ALL }
     | "Ex"	   { EXISTS }
     | "<=>"	   { IFF }
     | "==>"	   { IMP }
     | "not"	   { NOT}
     | "T"	   { TRUE }
     | "F"	   { FALSE }
     | "|"	   { OR }
     | "&"	   { AND }
     | "@"	   { AT }
     | "otherwise"	   { OTHERWISE }
     | "empty"	   { EMPTY }
     | "accounts" { ACCOUNTS }
     | "coarse" { COARSE }
     | "cases" { CASES }
     | "control" { CONTROL }
     | "control-equivalence" { CONTROLEQUIVALENCE }
     | "control-subset" { CONTROLSUBSET }
     | "for" { FOR }
     | "parties" { PARTIES }
     | "->"	   { RIGHTARROW }
     | "-->"	   { TRANSIT }
     | "--["	   { OPENTRANS }
     | "]->"	   { CLOSETRANS }
     | "{*"	   { fc:=""; formalcomment lexbuf; FORMALCOMMENT (!fc) }
     | '('	   { LP }
     | ')'	   { RP }
     | '{'	   { LCB }
     | '}'	   { RCB }
     | '['	   { LSB }
     | ']'	   { RSB }
     | '*'	   { STAR }
     | '^'	   { EXP }
     | '<'	   { LEQ }
     | '>'	   { GEQ }
     | '$'	   { DOLLAR }
     | '\''	   { QUOTE }
     | '"'	   { DQUOTE }
     | '~'	   { TILDE }
     | '#'	   { SHARP }
     | '+'	   { PLUS }
     | '0'         { NULL } 
     | "new" 	   { NEW }
     | "in"	   { IN }
     | "out"	   { OUT }
     | "if"	   { IF }
     | "then"	   { THEN }
     | "else"	   { ELSE }
     | "event"	   { EVENT }
     | "insert"	   { INSERT }
     | "delete"	   { DELETE }
     | "lookup"	   { LOOKUP }
     | "lock"	   { LOCK }
     | "unlock"	   { UNLOCK }
     | "as"	   { AS }
     | "="	   { EQ }
     | '!' 	   { REP }
     | "let" 	   { LET }
     | "report"    { REPORT }
     | ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']*  as symbol  { IDENTIFIER (symbol)}
     | '\'' ['a'-'z' 'A'-'Z' '0'-'9' '-' '_']* '\'' as symbol  { QUOTED_IDENTIFIER (symbol)}
     | ['0'-'9']+  as num  { NUM (num)}
     | ';'	   { SEMICOLON }
     | ':'	   { COLON }
     | ','	   { COMMA }
     | '/'	   { SLASH }
     | "||"	   { PARALLEL }
     | eof	   { raise End_of_file }
     
and commentslash = parse
    | "*/" { token lexbuf }   (* end of comment; switch back to "token" rule *)
    | '\n' { Lexing.new_line lexbuf ; commentslash lexbuf }
    | _    { commentslash lexbuf } (* skip comments *)

and commentparent = parse
    | "*)" { token lexbuf }   (* end of comment; switch back to "token" rule *)
    | '\n' { Lexing.new_line lexbuf ; commentparent lexbuf }
    | _    { commentparent lexbuf } (* skip comments *)

	
and formalcomment = parse
    | "*}"     { }
    | '\n'     {fc:=(!fc)^"\n"; Lexing.new_line lexbuf; formalcomment lexbuf }
    | _	 as c  {fc:=(!fc)^(escaped c); formalcomment lexbuf }
