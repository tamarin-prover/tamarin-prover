open Exceptions
open Btree
open Sapicterm
open Sapicvar
open Action
open Tamarin
open Term


type sapic_action = Null 
                 | Par
                 | Rep
                 | NDC
                 | New of sapic_var
                 | Msg_In of sapic_term
                 | Ch_In of sapic_term * sapic_term
                 | Msg_Out of sapic_term
                 | Ch_Out of sapic_term * sapic_term
                 | Insert of sapic_term * sapic_term
                 | Delete of sapic_term 
                 | Lock of sapic_term 
                 | Unlock of sapic_term 
                 | Lookup of sapic_term * sapic_term
                 | Event of action
                 | Cond of action
                 | MSR of msr 

let sapic_action2string = function
     Null -> "Zero"
    | Par -> "Parallel"
    | Rep  -> "Rep"
    | NDC  -> "Non-deterministic choice"
    | New(t) -> "new "^(Term.term2string (Term.Var t))
    | Msg_In(t) -> "in "^(Term.term2string t)
    | Ch_In(t1,t2) -> "in "^(Term.term2string t1)^","^(Term.term2string t2)
    | Msg_Out(t) -> "out "^(Term.term2string t)
    | Ch_Out(t1,t2) -> "out "^(Term.term2string t1)^","^(Term.term2string t2)
    | Insert(t1,t2) -> "insert "^(Term.term2string t1)^","^(Term.term2string t2)
    | Delete(t)  -> "delete "^(Term.term2string t)
    | Lock(t)  -> "lock "^(Term.term2string t)
    | Unlock(t)  -> "unlock "^(Term.term2string t)
    | Lookup(t1,t2) -> "lookup "^(Term.term2string t1)^" as "^(Term.term2string t2)
    | Event(a) -> "event "^action2string(a)
    | Cond(f) -> "if "^action2string(f)
    | MSR(prem,ac,conl) -> "MSR"   

let rec substitute  (id:string) (t:term) process =
  match process with
  | Empty -> Empty
  | Node(a, left, right) ->
    begin
      let v = (Var.Msg id) in
      let f = Term.subs_t v t in
      match a with
      | Null -> Node(a, left, right)
      | Par
      | NDC -> Node(a, substitute id t left, substitute id t right)
      | Rep -> Node(a, substitute id t left, right)
      | New (x) -> Node(a, substitute id t left, right)
      | Delete (u) -> Node(Delete( (f u) ), substitute id t left, right)
      | Lock(u) -> Node(Lock( (f u) ), substitute id t left, right)
      | Unlock(u) -> Node(Unlock( (f u) ), substitute id t left, right)
      | Msg_Out(u) -> Node(Msg_Out( (f u) ), substitute id t left, right)
      | Insert(u1,u2) -> Node(Insert( (f  u1), (f u2)), substitute id t left, right)
      | Ch_Out(u1,u2) -> Node(Ch_Out( (f  u1), (f u2)), substitute id t left, right)
      | Event(a) -> Node(Event(substitute_a v t a), substitute id t left, substitute id t right)
      | Cond(a) -> Node(Cond(substitute_a v t a), substitute id t left, substitute id t right)
      | Msg_In(u) ->
	    Node( Msg_In(f u), substitute id t left, substitute id t right )
      | Ch_In(u1, u2) ->
	    Node( Ch_In(f u1, f u2), substitute id t left, substitute id t right )
      | Lookup(u1,u2) ->
	    Node( Lookup(f u1, f u2), substitute id t left, substitute id t right )
      | MSR(prem,ac,conl) -> raise (NotImplementedError "Substitution cannot be used in embedded MSRs")
    end
    
