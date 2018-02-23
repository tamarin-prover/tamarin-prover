open Exceptions
open Formula 
open Verdict
open Var
open Atomformulaaction

module VarSet = Set.Make( Var );;

type acckind = Coarse | Cases | ControlEquivalence | ControlSubset

type lemma = ForallLemma of (string * string) * formula (* string is used for header and options *)
           | ExistsLemma of (string * string) * formula
           | AccLemma of acckind * (string * string)* proto_verdictf * formula * (VarSet.t)
           | Restriction of string * formula 
           | ManualLemma of string * string

let isAccLemma = function AccLemma(_) -> true
                        | _ -> false 

let isAccLemma_with_control = function 
                      AccLemma(ControlEquivalence,_,_,_,_) -> true
                     |AccLemma(ControlSubset,_,_,_,_) -> true
                        | _ -> false 

let contains_accountability  = List.exists isAccLemma
let contains_control  = List.exists isAccLemma_with_control

let add_antecedent f = function
    ForallLemma(hd,f') -> ForallLemma(hd,Atomformulaaction.Imp(f,f'))
  | ExistsLemma(hd,f') -> ExistsLemma(hd,Atomformulaaction.And(f,f'))
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

let  lemma_map f = function
    ForallLemma((id,op),formula) -> ForallLemma((id,op),f formula) 
    | ExistsLemma((id,op),formula) -> ExistsLemma((id,op),f formula)  
    | Restriction(id,formula) -> Restriction(id,f formula)  
    | AccLemma(kind, header, verdictf,formula,parties) -> AccLemma(kind, header, verdictf,f formula,parties)  
    | ManualLemma(id,s) -> raise (NotImplementedError "Function cannot be applied to manual lemmas.")


let rec bind_to_session (id:var) phi = match phi with 
    (* Atom(At(InitEmpty,v))    ->  InitId *)
    Atom(At(s,v))    ->  
               And (Atom(At(s,v)),Atom(At(Action("Event",[Term.Var id]),v)))
  | Atom (_) -> phi
  |Not(f)     -> Not (bind_to_session id f)
  |Or(f1,f2)  -> Or(bind_to_session id f1,bind_to_session id f2)
  |And(f1,f2) -> And(bind_to_session id f1,bind_to_session id f2)
  |Imp(f1,f2) -> Imp(bind_to_session id f1,bind_to_session id f2)
  |Iff(f1,f2) -> Iff(bind_to_session id f1,bind_to_session id f2)
  |All(vs,f)  -> All(vs,bind_to_session id f)
  |Ex(vs,f)   -> Ex(vs,bind_to_session id f)

let bind_lemma_to_session (id:var) l =
    let f phi = All(VarSet.of_list [id], bind_to_session id phi)
    in
        lemma_map f l

