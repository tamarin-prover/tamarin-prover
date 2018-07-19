%{
open Printf
open Exceptions
open Btree
open Tamarin
open Formula
open Fact
open Action
open Var
open Verdict
open Atomformulaaction
open Sapicaction
open Sapicvar
open Sapicterm
open Lemma

module TermSet = Set.Make( Term );;

let reswords= ["Init"; "Insert"; "Delete"; "IsIn"; "IsNotSet"; "Lock"; "Unlock"; "Out"; "Fr"; "In"; "Msg"; "ProtoNonce"; "Event"; "InEvent"; "ExecId"] 
let reswords_pref = ["State_"; "Pred_"; "Pred_not_"; "n_"; "lock_"; "prog_" ]

let reserved symbol =
  (List.mem symbol reswords) ||
    ( let len_sym=String.length symbol in
      List.exists (fun x ->
	let len_x = String.length x in
	if (len_x <= len_sym )
	then
	  (
	    let prefix = String.sub symbol 0 len_x in
	    prefix = x
	  )
	else  false
      ) reswords_pref )
  
module VarSet = Set.Make( Var );;
let (@@) (a:VarSet.t) (b:VarSet.t) = VarSet.union a b

type options = { progress: bool; accountability:bool}
let defaultop= {progress=false; accountability=false}
let mergeopt a b = { 
    progress=(a.progress || b.progress);
    accountability=(a.accountability || b.accountability)
}

type inp = {sign : string;
            pred : string list;
            op   : options;
            rules: rule list;
            proc : sapic_action btree;
            lem  : lemma list;
}

type fct_attr =
  Public
| Private
| Pred of string

let proc_table = Hashtbl.create 10;;
let verdictf_table = Hashtbl.create 10;;

let varlist n =
  let rec work i =
    if i < n then  
      Term.Var(Var.Msg( ("x"^(string_of_int i)) )) :: (work (i+1))
    else [Term.Var(Var.Msg( ("x"^(string_of_int i)) ))]
  in
  if n < 1 then []
  else work 1
    
let function_declare id arity attr =
  match attr with
  | Public -> id ^"/"^ (string_of_int arity)
  | Private
  | Pred(_) -> id ^"/"^ (string_of_int arity) ^ "[private]"

let rule_declare id arity attr =
  match attr with
  | Public 
  | Private -> []
  | Pred(p) ->
    if arity = 0 then
      [{ identifier="function_"^id; let_block=""; rule_body= 
	  ([],
	   [Action("Pred_"^p, [])],
	   [LFact("Out",[Term.App(id,[])])])
       }]

    else
      [{ identifier="function_"^id; let_block=""; rule_body= 
	  ([LFact("In",[Term.List(varlist arity)])],
	   [Action("Pred_"^p, varlist arity)],
	   [LFact("Out",[Term.App(id,varlist arity)])])
       }]


let location_sign=
  "functions: rep/2 [private], check_rep/2, get_rep/1\nequations: check_rep(rep(m,loc),loc)=m, get_rep(rep(m,loc))=m\n"

let location_rule=
  { identifier="function_rep"; let_block=""; rule_body= 
      ([LFact("In",[Term.List(varlist 2)])],
       [Action("Pred_pred_rep", varlist 2)],
       [LFact("Out",[Term.App("rep",varlist 2)])])
  }

%}


%token <char> ALL_TRACES EXISTS_TRACE
%token <string> IDENTIFIER NUM BUILTIN_THEORY FUNCTION_ATTR LEMMA_ATTR FORMALCOMMENT QUOTED_IDENTIFIER 
%token THEORY BEGIN END BUILTINS FUNCTIONS EQUATIONS PREDICATES OPTIONS PROGRESS RESTRICTION VERDICTFUNCTION LEMMA REUSE INDUCTIVE INVARIANT 
%token ALL EXISTS IFF IMP NOT TRUE FALSE AT OR AND HIDE_LEMMA RIGHTARROW OTHERWISE EMPTY ACCOUNTS FOR PARTIES
%token COARSE CASES CONTROL CONTROLEQUIVALENCE CONTROLSUBSET
%token NULL NEW IN OUT IF THEN ELSE EQ REP LET EVENT INSERT DELETE LOOKUP AS LOCK UNLOCK REPORT
%token SLASH LP RP COMMA SEMICOLON COLON POINT PARALLEL NEWLINE LCB RCB LSB RSB DOLLAR QUOTE DQUOTE TILDE SHARP STAR EXP LEQ GEQ RULE TRANSIT OPENTRANS CLOSETRANS PLUS

/* define associativity and operator precedence */
%left PARALLEL
%left REP
%left SEMICOLON

%right ALL EXISTS 
%right IFF IMP  
%right OR
%right AND
%nonassoc NOT


/* entry point */
%start input

/* types*/
%type <inp> input
%type <sapic_action btree> process
%type <sapic_action btree> optprocess
%type <sapic_action> sapic_action
%type <inp> body
%type <string * rule list> signature_spec 
%type <string> builtins 
%type <string> builtin_theory_seq
%type <VarSet.t> varseq
%type <string * rule list> fctseq
%type <string * int * fct_attr> fct
%type <options> optionseq
%type <options> opt
%type <string> eqseq
%type <string> eq
%type <Term.termlist> termseq
%type <term> multterm
%type <term> expterm
%type <term> term
%type <var> literal
%type <string> restriction_header
%type <lemma> lemma
%type <string*string> lemma_header
%type <string> lemma_attr
%type <string> lemma_attr_seq
%type <formula> formula
%type <atom> atom
%type <var> tvar
%type <fact list> factseq
%type <fact> fact
%type <rule> rule
%type <actionlist> transition
%type <string> letblock
%type <(string * Term.term) list> id_eq_termseq
%type <string> identifierseq
%type <string> formal_comment
%type <string> id_not_res


%% /* Grammar rules and actions follow */

input: 	       
    |   THEORY IDENTIFIER BEGIN body END {{sign="theory "^$2^"\nbegin\n\n"^location_sign^$4.sign; pred=$4.pred; op=$4.op; rules=location_rule::$4.rules; proc=$4.proc; lem=$4.lem}}

;

body: 
    | /* empty*/           {{sign=""; pred=[]; op=defaultop; rules=[]; proc=Empty; lem=[]}}
    | signature_spec body  {let (s,rl)=$1 in {sign=(s^$2.sign); pred=$2.pred; op=$2.op; rules=rl@$2.rules; proc=$2.proc; lem=$2.lem}}
    | let_process body     {{sign=$2.sign; pred=$2.pred; op=$2.op; rules=$2.rules; proc=$2.proc; lem=$2.lem}} 
    | verdictf body     {{sign=$2.sign; pred=$2.pred; op=$2.op; rules=$2.rules; proc=$2.proc; lem=$2.lem}} 
    | predicates body   {{sign=$2.sign; pred=($2.pred @ $1); op=$2.op; rules=$2.rules; proc=$2.proc; lem=$2.lem}}
    | options body   {{sign=$2.sign; pred=$2.pred; op=(mergeopt $1 $2.op); rules=$2.rules; proc=$2.proc; lem=$2.lem}}
    | process body 	      {{sign=$2.sign; pred=$2.pred; op=$2.op; rules=$2.rules; proc=$1; lem=$2.lem}}
    | lemma body 	      {{sign=$2.sign; pred=$2.pred; 
                                op=(mergeopt {progress=false; accountability=isAccLemma_with_control $1} $2.op);
                                rules=$2.rules; proc=$2.proc; lem=($1::$2.lem)}}
    | rule body 	          {{sign=$2.sign; pred=$2.pred; op=$2.op; rules=($1::$2.rules); proc=$2.proc; lem=$2.lem}}
    | formal_comment body  {{sign=($1^$2.sign); pred=$2.pred; op=$2.op; rules=$2.rules; proc=$2.proc; lem=$2.lem}}
;

signature_spec: 
    | /* empty */ {("",[])}
    | builtins signature_spec  {let (s,rl)=$2 in ($1^s,rl)}
    | functions signature_spec {let (s1,rl1)=$1 in let (s2,rl2)=$2 in (s1^s2,rl1@rl2)}
    | equations signature_spec {let (s,rl)=$2 in ($1^s,rl)}
  ;


builtins :
	 |    BUILTINS COLON builtin_theory_seq {"\nbuiltins: "^$3^"\n"}
;

builtin_theory_seq :
	 | BUILTIN_THEORY			   {$1}
         | BUILTIN_THEORY COMMA builtin_theory_seq {$1^", "^$3}


functions :
	 |    FUNCTIONS COLON fctseq {let (f,rl) = $3 in ("\nfunctions: "^f^"\n",rl)}


equations :
	 |    EQUATIONS COLON eqseq {"\nequations: "^$3^"\n"}

predicates :
	 |    PREDICATES COLON predicate_seq {$3}
;

options :
	 |    OPTIONS COLON optionseq {$3}
;

optionseq :
         |    opt			{$1}
	 |    optionseq COMMA opt       {mergeopt $1 $3}
;

fctseq :
    |    fct			        { let (id, arity, attr) = $1 in
						  ( function_declare  id arity attr,
						    rule_declare id arity attr ) }
    |    fctseq COMMA fct		{ let (fseq, ruleseq) = $1 in
							  let (id, arity, attr) = $3 in
							  ( fseq^", "^(function_declare  id arity attr) , ruleseq@(rule_declare id arity attr))}
  ;

eqseq :
         |    eq			{$1}
	 |    eqseq COMMA eq		{$1^","^$3}
;

predicate_seq :
    |    predicate {$1}
    |    predicate_seq COMMA predicate		{$3@$1}
;


fct :
         |    fct_decl function_attr {let (id, arity)=$1 in (id,arity,$2)}
;


fct_decl :
    |    IDENTIFIER SLASH NUM	{($1, (int_of_string $3) )}
    |    IDENTIFIER SLASH NULL	{($1, 0)}
;

opt:
  |    PROGRESS	{ {progress=true; accountability = false} }
;

eq :
         |    term EQ term	{(Term.term2string $1)^"="^(Term.term2string $3)}
;

predicate :
         |    IDENTIFIER LP varseqstring RP IFF cond_predicate
                { ["All #i "^(String.concat " " $3)^". Pred_"^$1^"("^(String.concat "," $3)^")@i ==> "^(formula2string $6);
                  "All #i "^(String.concat " " $3)^". Pred_not_"^$1^"("^(String.concat "," $3)^")@i ==> "^(formula2string ((Not($6):Formula.formula))) ]
                }
;

varseqstring :  
    |    messagevar		{ [$1] }
    |    varseqstring COMMA messagevar	{$1 @ [$3]}
;

messagevar :
    | IDENTIFIER			{$1}
;

id_not_res :
		    | IDENTIFIER			{
		      if reserved $1 then (Printf.eprintf ": \"%s\" is a reserved word. \n"
					     $1;  raise Parsing.Parse_error)
		      else      $1}
  ;

let_process:
	 |    LET id_not_res EQ process			 {Hashtbl.add proc_table $2 $4; ()} 

verdictf:
	|     VERDICTFUNCTION IDENTIFIER COLON caseseq {Hashtbl.add verdictf_table $2 $4; ()} 
;

caseseq:
    |	/* empty */		{[]}
    |     case			{[$1]}
    |     case COMMA caseseq	{$1::$3}
    |     case COMMA OTHERWISE RIGHTARROW verdict	{[$1;Otherwise($5)]} /*otherwise needs to be at the very end*/
;

case:
  | DQUOTE formula DQUOTE RIGHTARROW verdict {Case($2,$5)}
  | DQUOTE formula DQUOTE RIGHTARROW LET IDENTIFIER EQ LEQ singleton_verdict GEQ {RefCase($6,$2,[$9])}
;

verdict:
  | EMPTY  {[]} 
  | LEQ singleton_verdict GEQ  {[$2]}
  | LEQ singleton_verdict GEQ OR verdict {$2::$5}
  ;

singleton_verdict:
    | pvarseq { VerdictPart(VarSet.of_list $1) } 
    | IDENTIFIER {  Ref($1) }
;

pvarseq:
    |	/* empty */		{[]}
    |     pvar			{[$1]}
    |     pvar COMMA pvarseq	{$1::$3}
;

process:
    | LP process RP                                  { $2 }
    | LP process RP AT multterm                      { substitute "_loc_" $5 $2 }
    | process PARALLEL process                       { Node(Par, $1, $3) }
    | process PLUS process                           { Node(NDC, $1, $3) }
    | NULL                                           { Node(Null, Empty, Empty)}
    | sapic_action optprocess                        { Node($1, $2, Empty) }
    | REP process                                    { Node(Rep, $2, Empty) }
    | IF if_cond THEN process ELSE process           { Node(Cond($2), $4, $6) }
    | IF if_cond THEN process                        { Node(Cond($2), $4, Node(Null, Empty, Empty)) }
    | LOOKUP term AS literal IN process ELSE process { Node(Lookup($2,Term.Var($4)), $6 , $8) }
    | LOOKUP term AS literal IN process              { Node(Lookup($2,Term.Var($4)), $6, Node(Null,Empty,Empty)) }
    | LET id_eq_termseq IN process          { List.fold_right (fun (x,y) p -> substitute x y p) $2 $4 }
    | LET id_not_res EQ REPORT LP multterm RP IN process { substitute
							     $2
							     (Term.App("rep", [$6;Term.Var(Var.Msg("_loc_"))]))
							     $9 }
    | IDENTIFIER                                     { try Hashtbl.find proc_table $1
            with Not_found -> Printf.eprintf "The process: %s is undefined. \n " $1; raise Parsing.Parse_error }
     |    rule_body optprocess { Node(MSR($1), $2, Empty) }
;

if_cond:
    | IDENTIFIER LP termseq RP  {Action($1,$3)}
    | multterm EQ multterm  {Action("eq",[$1;$3])}

cond_predicate:
	|     cond_atom				{Atom($1)}
	|     NOT cond_predicate			{Not($2)}
	|     cond_predicate OR cond_predicate		{Or ($1,$3)}
	|     cond_predicate AND cond_predicate		{And($1,$3)}
	|     cond_predicate IMP cond_predicate		{Imp($1,$3)}
	|     cond_predicate IFF cond_predicate		{Iff($1,$3)}
	|     ALL literalseq POINT cond_predicate 	{All($2,$4)}
	|     EXISTS literalseq POINT cond_predicate 	{Ex($2,$4)}
	|     LP cond_predicate RP    	     		{ $2 }
;

cond_atom:
	|    multterm EQ multterm       { Eq($1,$3)}
	|    TRUE    			{True}
	|    FALSE    			{False}
;

literalseq :  
 	 |    literal		{ (VarSet.add $1 VarSet.empty )}
	 |    literalseq literal	{VarSet.add $2 $1}
;

optprocess:
     /* empty */  { Node(Null,Empty,Empty) }
     | SEMICOLON process   { $2}
 ;

sapic_action:
     |    NEW literal	                 { New($2)}
     |    IN LP multterm RP 	         { Msg_In($3) }
     |    IN LP multterm COMMA multterm RP   { Ch_In($3,$5) }
     |    OUT LP multterm RP 	         { Msg_Out($3) }
     |    OUT LP multterm COMMA multterm RP  { Ch_Out($3,$5) }
     |    EVENT id_not_res LP termseq RP     { Event(Action($2,$4)) }
     |    INSERT term COMMA term                  { Insert($2,$4) } 
     |    DELETE term                  { Delete($2) } 
     |    LOCK term                  { Lock($2) } 
     |    UNLOCK term                  { Unlock($2) } 
;

termseq:
    |	/* empty */		{[]}
    |     multterm			{[$1]}
	|     multterm COMMA termseq	{$1::$3}
;

multterm:
	|     expterm			{$1}
	|     expterm STAR multterm	{ Term.Mult($1,$3) }
;

expterm:
	|     term			{$1}
	|     term EXP expterm          {Term.Exp($1,$3)}

;

        

term:
	|     LEQ termseq GEQ			{ Term.List($2)}
    |     LP multterm RP			{ $2 }
    |     IDENTIFIER LCB termseq RCB term 	{Term.App($1,($3@[$5])) }
    |     IDENTIFIER LP termseq RP		{Term.App($1,$3)}
    |     term PLUS term        {Term.Plus($1,$3)}
	|     literal				{Term.Var($1)}
;

literal:
        | pvar                                  {$1}
	|     TILDE QUOTE IDENTIFIER QUOTE	{Var.FreshFixed($3)}
    |     TILDE IDENTIFIER	     		{Var.Fresh($2)}
	|     SHARP IDENTIFIER			{Var.Temp($2)}
	|     IDENTIFIER			{Var.Msg($1)}
;

pvar:
	/*|     QUOTE IDENTIFIER QUOTE		{Var.PubFixed($2)}  */
    /* tamarin does actually not respect its grammar and accepts e.g. '1'*/
        |     QUOTED_IDENTIFIER
        {let unquoted_id=String.sub $1 1 (String.length $1 - 2 ) in
        if reserved unquoted_id
        then  (Printf.eprintf ": \"%s\" is a reserved word. \n"
        unquoted_id;  raise Parsing.Parse_error)
                    else
                        Var.PubFixed(unquoted_id)
        } 
	|     DOLLAR IDENTIFIER			{Var.Pub($2)}
;

lemma:
	|     lemma_header ALL_TRACES DQUOTE formula DQUOTE	{ ForallLemma($1, $4) }
	|     lemma_header EXISTS_TRACE DQUOTE formula DQUOTE	{ ExistsLemma($1, $4) }
	|     lemma_header DQUOTE formula DQUOTE	{ ForallLemma($1, $3) }
	|     restriction_header DQUOTE formula DQUOTE	{ Restriction($1, $3) }
	|     lemma_header IDENTIFIER ACCOUNTS account_attr_col FOR DQUOTE formula DQUOTE FOR PARTIES LEQ pvarseq GEQ {  try 
            AccLemma($4, $1, Hashtbl.find verdictf_table $2, $7,( VarSet.of_list $12))
            with Not_found -> Printf.eprintf "The verdict: %s is undefined. \n " $2; raise Parsing.Parse_error }
;

lemma_header:
	|     LEMMA IDENTIFIER lemma_attr_col COLON  {($2,$3)}
;

restriction_header:
	|     RESTRICTION IDENTIFIER COLON  {$2}
;



function_attr:
     |     /* empty */ { Public }
     |     LSB FUNCTION_ATTR RSB { Private }
     |     LSB IDENTIFIER RSB { Pred($2) }
;

lemma_attr_col:
	|     /* empty */ {""}
	|     LSB lemma_attr_seq RSB {"["^$2^"]"}
;

lemma_attr_seq:
	|     lemma_attr			{$1}
	|     lemma_attr COMMA lemma_attr_seq	{$1^", "^$3}
;

lemma_attr:
	|     LEMMA_ATTR			{$1}
	|     HIDE_LEMMA EQ IDENTIFIER	{"hide_lemma="^$3}
;

account_attr_col:
	|     /* empty */ { Coarse }
	|     LSB account_attr RSB { $2 }
;

account_attr:
	|     COARSE			{Coarse}
	|     CASES			{Cases}
	|     CONTROL			{ControlEquivalence} // (* Default *)
	|     CONTROLEQUIVALENCE	{ControlEquivalence}
	|     CONTROLSUBSET		{ControlSubset}
;


formula:
	|     atom				{Atom($1)}
	|     NOT formula			{Not($2)}
	|     formula OR formula		{Or($1,$3)}
	|     formula AND formula		{And($1,$3)}
	|     formula IMP formula		{Imp($1,$3)}
	|     formula IFF formula		{Iff($1,$3)}
	|     ALL varseq POINT formula 	{All($2,$4)}
	|     EXISTS varseq POINT formula 	{Ex($2,$4)}
	|     LP formula RP    	     		{$2}
;

atom:
	|    tvar LEQ tvar		{TLeq($1,$3)}
	|    SHARP IDENTIFIER EQ SHARP IDENTIFIER 	{TEq(Temp($2),Temp($5))}
	|    multterm EQ multterm       {Eq($1,$3)}
	|    action AT tvar 		{At($1,$3)}
	|    TRUE    			{True}
	|    FALSE    			{False}
;

tvar:
	|    SHARP IDENTIFIER	{Temp($2)}
	|    IDENTIFIER		{Temp($1)}
;

varseq :  
 	 |    literal		{VarSet.singleton $1}
	 |    varseq literal	{VarSet.add $2 $1}
;


factseq:
    |    /* empty */ {[]}
    |    fact		{[$1]}
	|    fact COMMA factseq	{$1::$3}
;


fact:
    |    lfact  { $1 }
    |    pfact  { $1 }
;

pfact:
	|    REP IDENTIFIER LP termseq RP	{ PFact($2,$4) }
    ;

lfact:
	|    IDENTIFIER LP termseq RP		{ LFact($1,$3) }
;

actionseq:
    |    /* empty */ {[]}
    |    action		{[$1]}
	|    action COMMA actionseq	{$1::$3}
;

action:
	|    IDENTIFIER LP termseq RP		{ Action($1,$3) }
;

rule:
    | RULE IDENTIFIER COLON letblock rule_body {{identifier=$2; let_block=$4; rule_body=$5}}
;

rule_body:
     |  LSB factseq RSB transition LSB factseq RSB { ($2,$4,$6) }
 ;
transition:
    | TRANSIT			{[]}
    | OPENTRANS actionseq CLOSETRANS	{$2}
;

letblock:
	| /* empty */ {""}
	| LET id_eq_termseq IN		{  let to_str (x,y) =  x^"="^(Term.term2string y) in
                                           let eq_list l =  String.concat " " (List.map to_str l) in
                                                "\t let "^(eq_list $2)^" in\n"}
;	

id_eq_termseq:
        | id_not_res EQ multterm { [($1,$3)] }
	| id_not_res EQ multterm id_eq_termseq { ($1,$3)::$4}
;

identifierseq:
       | /* empty */ {""}
       | IDENTIFIER identifierseq {$1^$2}
;

formal_comment:
       | IDENTIFIER FORMALCOMMENT {$1^"{*"^$2^"*}\n"}
;


%%
