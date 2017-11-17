open Exceptions
open Formula 
open Verdict
open Var

module VarSet = Set.Make( Var );;

type acckind = Coarse | Cases | Control

type lemma = ForallLemma of (string * string) * formula (* string is used for header and options *)
           | ExistsLemma of (string * string) * formula
           | AccLemma of acckind * (string * string)* proto_verdictf * formula * (VarSet.t)
           | Restriction of string * formula 
           | ManualLemma of string * string

let isAccLemma = function AccLemma(_) -> true
                        | _ -> false 

let isAccLemma_with_control = function AccLemma(Control,_,_,_,_) -> true
                        | _ -> false 

let contains_accountability  = List.exists isAccLemma
let contains_control  = List.exists isAccLemma_with_control

let add_antecedent f = function
    ForallLemma(hd,f') -> ForallLemma(hd,Atomformulaaction.Imp(f,f'))
  | ExistsLemma(hd,f') -> ExistsLemma(hd,Atomformulaaction.Imp(f,f'))
  | _ -> raise (ImplementationError "add_antecedent is only meant to be called on lemmas.")

let rec lemma2string_base sufficient_conditions = function
    ForallLemma((id,op),formula) -> "lemma "^id^" "^op^":\n all-traces\n\""^(formula2string formula)^"\"\n"
    | ExistsLemma((id,op),formula) -> "lemma "^id^" "^op^":\n exists-trace\n\""^(formula2string formula)^"\"\n"
    | Restriction(id,formula) -> "restriction "^id^":\n \""^(formula2string formula)^"\"\n"
    | AccLemma(kind, header, verdictf,formula,parties) -> print_lemmas_base sufficient_conditions (sufficient_conditions kind header parties verdictf formula )
    | ManualLemma(id,s) -> "/* lemma: "^id^". The following needs to be shown manually:\n"^s^" */ \n"
and print_lemmas_base sufficient_conditions lemlist =
    (String.concat "\n") (List.map (lemma2string_base sufficient_conditions) lemlist)

let lemma2string_noacc = lemma2string_base (fun k h p v f -> []) (* no translation for acclemma *)
