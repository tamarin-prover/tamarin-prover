open Printf
open Sapic
open List
open Formula
open Annotatedrule
open Annotatedsapicaction
open Annotatedsapictree
open Atomformulaaction
open Btree

let lemma2string = function
    ForallLemma(header,formula) -> header^"\n all-traces\n\""^(formula2string formula)^"\"\n"
    |ExistsLemma(header,formula) -> header^"\n exists-trace\n\""^(formula2string formula)^"\"\n"
    |ForallRestriction(header,formula) -> header^"\n all-traces\n\""^(formula2string formula)^"\"\n"
    |ExistsRestriction(header,formula) -> header^"\n exists-trace\n\""^(formula2string formula)^"\"\n"

let rec print_lemmas lemlist =
    (String.concat "\n") (List.map lemma2string lemlist)

let rec contains_lookup t = 
    match t with
      Empty -> false
    |   Node(Lookup _, left, right) -> true
    |   Node(_,left,right) -> (contains_lookup left) || (contains_lookup right)

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





