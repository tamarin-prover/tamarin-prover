open Var
open Term
open Position
open Atomformulaaction

type action=Atomformulaaction.action

type actionlist = action list

let action2string = function 
    Init -> "Init()"
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

let rec subs_a id t (a:action) = 
        let f = (subs_t id t) in
        match a with
            | Action(name,t) -> Action(name, List.map f t)
            | Init
            | Predicate(_,_,_) 
            | NegPredicate(_,_,_) 
            | ProgressFrom(_)
            | ProgressTo(_)
            | Listen(_)
            | Receive(_)
            | Send(_)
            -> raise Parsing.Parse_error 

type t = action
let compare (s1:action) (s2:action) = String.compare (action2string s1) (action2string s2)
