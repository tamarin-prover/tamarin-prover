open Exceptions
open Var
open Term
open Position
open Atomformulaaction

type action=Atomformulaaction.action

type actionlist = action list

let id_ExecId = "ExecId"
let var_ExecId = Fresh "ExecId"

let action2string = function 
    InitEmpty -> "Init()"
  | InitId -> "Init("^(var2string (var_ExecId))^")"
  | StopId -> "Stop("^(var2string (var_ExecId))^")"
  | EventEmpty -> "Event()"
  | EventId -> "Event("^(var2string (var_ExecId))^")"
  | Action(name,t) -> name^"("^(flatten_termlist t)^")"   
  | Predicate(p,vs,_) -> "Predicate"^pos2string(p)^"("^(flatten_termlist ( List.map (fun v ->  Var(v)) (
      VarSet.elements vs)))^")"   
  | NegPredicate(p,vs,_) -> "NegPredicate"^pos2string(p)^"("^(flatten_termlist ( List.map (fun v ->  Var(v)) (
      VarSet.elements vs)))^")"   
  | ProgressFrom(p) ->  "ProgressFrom_"^(pos2string p)^"(~prog_"^(pos2string p)^")"
  | ProgressTo(p,pf) -> "ProgressTo_"^(pos2string p)^"(~prog_"^(pos2string pf)^")"
  | Listen(p,v) -> "Listen_"^(pos2string p)^"("^(var2string v)^")"
  | Receive(p,t) -> "Receive(mid_"^(pos2string p)^","^(term2string t)^")"
  | Send(p,t) -> "Send(mid_"^(pos2string p)^","^(term2string t)^")" 


let rec substitute_a v t (a:action) = 
        let f = (subs_t v t) in
        match a with
            | Action(name,t) -> Action(name, List.map f t)
            | InitEmpty
            | InitId
            | StopId
            | EventEmpty
            | EventId
            | Predicate(_,_,_) 
            | NegPredicate(_,_,_) 
            | ProgressFrom(_)
            | ProgressTo(_)
            | Listen(_)
            | Receive(_)
            | Send(_)
            -> raise Parsing.Parse_error 

(* let rec subs_a v t (a:action) = *) 
(*         let f = (subs_t v t) in *)
(*         match a with *)
(*             | Action(name,t) -> Action(name, List.map f t) *)
(*   | InitId -> InitId *) 
(*   | StopId -> StopId *) 
(*   | EventEmpty -> EventEmpty *) 
(*   | EventId -> EventId *) 
(*   | Predicate(p,vs,_) -> Predicate(p,VarSet.map vs,_) *) 
(*   | NegPredicate(p,vs,_) -> NegPredicate(p,vs,_) *) 
(*   | ProgressFrom(p) -> ProgressFrom(p) *) 
(*   | ProgressTo(p,pf) -> ProgressTo(p,pf) *) 
(*   | Listen(p,v) -> Listen(p,v) *) 
(*   | Receive(p,t) -> Receive(p,t) *) 
(*   | Send(p,t) -> *) 

let rec vars_action  = function
    InitEmpty -> VarSet.empty 
  | Action(name,tl) -> List.fold_left 
   (fun a x -> VarSet.union (vars_t x) a)
   VarSet.empty tl
   | _  -> raise ( NotImplementedError "Not implemented.")


type t = action
let compare (s1:action) (s2:action) = String.compare (action2string s1) (action2string s2)
