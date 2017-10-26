open Printf
open Sapic
open List
open Formula
open Annotatedrule
open Annotatedsapicaction
open Annotatedsapictree
open Atomformulaaction
open Btree
open Lemma
open Term
open Var
open Verdict

let rec lemma2string = function
    ForallLemma((id,op),formula) -> "lemma "^id^" "^op^":\n all-traces\n\""^(formula2string formula)^"\"\n"
    | ExistsLemma((id,op),formula) -> "lemma "^id^" "^op^":\n exists-trace\n\""^(formula2string formula)^"\"\n"
    | Restriction(id,formula) -> "restriction "^id^":\n \""^(formula2string formula)^"\"\n"
    | AccLemma(kind, header, verdictf,formula,parties) -> print_lemmas (Sufficient.sufficient_conditions kind header parties verdictf formula )
    | ManualLemma(id,s) -> "/* lemma: "^id^". The following needs to be shown manually:\n"^s^" */ \n"
and print_lemmas lemlist =
    (String.concat "\n") (List.map lemma2string lemlist)

let rec contains_lookup t = 
    match t with
      Empty -> false
    |   Node(Lookup _, left, right) -> true
    |   Node(_,left,right) -> (contains_lookup left) || (contains_lookup right)

let rec contains_delete t = 
    match t with
      Empty -> false
    |   Node(Delete _, left, right) -> true
    |   Node(_,left,right) -> (contains_delete left) || (contains_delete right)

let rec contains_locking t = 
    match t with
      Empty -> false
    |   Node(AnnotatedLock _, left, right)
    |   Node(AnnotatedUnlock _, left, right) -> true
    |   Node(_,left,right) -> (contains_locking left) || (contains_locking right)

let rec contains_eq t = 
    match t with
      Empty -> false
    |   Node(Cond(Action("eq",_)), _, _) -> true
    |   Node(_,left,right) -> (contains_eq left) || (contains_eq right)

let rec contains_resilient_io t = 
    match t with
      Empty -> false
    |   Node(Ch_In(Var(PubFixed("r")),_), _, _) 
    |   Node(Ch_Out(Var(PubFixed("r")),_), _, _)  -> true
    |   Node(_,left,right) -> (contains_eq left) || (contains_eq right)








