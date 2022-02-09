open Term
open Var
open List
open Position

module VarSet = Set.Make( Var );;

type fact = K of term | Fr of var | In of term 
            | Out of term
            | Message of term * term
            | Ack of term * term
            | State of position * (VarSet.t)
            | PState of position * (VarSet.t)
            | Semistate of position * (VarSet.t)
            | PSemistate of position * (VarSet.t)
            | MessageIDSender of position
            | MessageIDReceiver of position
            | PFact of string * termlist  | LFact of string * termlist 

type factlist = fact list

let vars_fact = function
    K(t)
  |        In(t)
  |       Out(t)-> vars_t(t)
  |        Fr(v)-> VarSet.singleton v
  |    PFact(_,tl)
  |    LFact(_,tl)-> fold_left (fun a t -> VarSet.union a (vars_t t)) VarSet.empty tl
  |    State(_,s)
  |   PState(_,s) 
  |   Semistate(_,s) 
  |   PSemistate(_,s) -> s
  |  MessageIDSender _
  |  MessageIDReceiver _ -> VarSet.empty
  |Message(t1,t2)-> (vars_t t1)  @@ (vars_t  t2) 
  |Ack(t1,t2)-> (vars_t t1)  @@ (vars_t  t2) 

let vars_factlist (fl:factlist) = fold_left (fun a t -> VarSet.union a (vars_fact t)) VarSet.empty fl

let fact2string (f:fact) = match f with 
    K(t) ->  "K("^(term2string t)^")"
  |        Fr(t) ->  "Fr("^(term2string (Var t))^")"
  |        In(t) ->  "In("^(term2string t)^")"
  |       Out(t) ->  "Out("^(term2string t)^")"
  |Message(t1,t2)->  "Message("^(term2string t1)^","^(term2string t2)^")"
  | Ack(t1,t2)->  "Ack("^(term2string t1)^","^(term2string t2)^")"
  |    State(p,t)->  "State_"^(pos2string p)^"("^(flatten_varlist_comma (VarSet.elements t))^")" 
  |   PState(p,t)->  "!State_"^(pos2string p)^"("^(flatten_varlist_comma (VarSet.elements t))^")" 
  |    Semistate(p,t)->  "Semistate_"^(pos2string p)^"("^(flatten_varlist_comma (VarSet.elements t))^")" 
  |    PSemistate(p,t)->  "!Semistate_"^(pos2string p)^"("^(flatten_varlist_comma (VarSet.elements t))^")" 
  |  MessageIDSender p -> "MID_Sender(mid_"^(pos2string p)^")"
  |  MessageIDReceiver p -> "MID_Receiver(mid_"^(pos2string p)^")"
  |    PFact(s,t)->  "!"^s^"("^ (flatten_termlist t) ^ ")"
  |    LFact(s,t)->  s^"("^ (flatten_termlist t) ^ ")"
