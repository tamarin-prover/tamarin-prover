open Exceptions
open Sapic
open Action
open Tamarin
open Term
open Sapicvar
open Sapicterm

type annotated_sapic_action = Null 
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
                         | AnnotatedLock of sapic_term * int
                         | AnnotatedUnlock of sapic_term * int
                         | Lock of sapic_term 
                         | Unlock of sapic_term 
                         | Lookup of sapic_term * sapic_term
                         | Event of action
                         | Cond of action
                         | MSR of msr 
                         | Comment of string

let annotated_sapic_action2string = function
        Null -> "Zero"
        | Par -> "Par"
        | Rep  -> "Rep"
        | NDC  -> "Non-deterministic choice"
        | New(t) -> "new "^(term2string (Var t))
        | Msg_In(t) -> "in "^(term2string t)
        | Ch_In(t1,t2) -> "in "^(term2string t1)^","^(term2string t2)
        | Msg_Out(t) -> "out "^(term2string t)
        | Ch_Out(t1,t2) -> "out "^(term2string t1)^","^(term2string t2)
        | Insert(t1,t2) -> "insert "^(term2string t1)^","^(term2string t2)
        | Delete(t)  -> "delete "^(term2string t)
        | AnnotatedLock(t,a)  -> "lock "^(term2string t)
        | AnnotatedUnlock(t,a)  -> "unlock "^(term2string t)
        | Lookup(t1,t2) -> "lookup "^(term2string t1)^" as "^(term2string t2)
        | Event(a) -> "event "^action2string(a)
        | Cond(s) -> "if "^action2string(s)
        | MSR(prem,ac,conl) -> "MSR"   
        | Comment(s) -> s
        | Lock(_) | Unlock(_)  -> raise (UnAnnotatedLock "There is an unannotated lock in the
             * proces description") 
