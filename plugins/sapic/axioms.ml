open Exceptions
open Progressfunction
open List
open Annotatedsapictree
open Position
open Printf

let ass_set_in = " axiom set_in:
\"All x y #t3 . IsIn(x,y)@t3 ==>
        (Ex #t2 . Insert(x,y)@t2 & #t2<#t3 
                & ( All #t1 . Delete(x)@t1 ==> (#t1<#t2 |  #t3<#t1))
                & ( All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1))
)\"

"

let ass_set_notin = 
"axiom set_notin:
\"All x #t3 . IsNotSet(x)@t3 ==> 
        (All #t1 y . Insert(x,y)@t1 ==>  #t3<#t1 )
  | ( Ex #t1 .   Delete(x)@t1 & #t1<#t3 
                &  (All #t2 y . Insert(x,y)@t2 & #t2<#t3 ==>  #t2<#t1))\"

"

let ass_predicate_not_eq = "
axiom predicate_not_eq:
\"All #i a b. Pred_not_eq(a,b)@i ==> not(a = b)\"

"

let ass_predicate_eq = "
axiom predicate_eq:
\"All #i a b. Pred_eq(a,b)@i ==> a = b\"

"

let ass_immeadiate_in = "
axiom immeadiate_in:
\"All x #t3 . ChannelInEvent(x)@t3
        ==> Ex #t2. K(x)@t2 & #t2<#t3
                & (All #t0. Event()@t0  ==> #t0<#t2 | #t3<#t0)
                & (All #t0 xp . K(xp)@t0  ==> #t0<#t2 | #t0=#t2 | #t3<#t0 )
                             \"
        
"

let ass_locking = "
axiom locking:
\"All l x lp #t1 #t3 . Lock(l,x)@t1 & Lock(lp,x)@t3 
        ==> 
        ( #t1<#t3 
                & (Ex #t2. Unlock(l,x)@t2 & #t1<#t2 & #t2<#t3 
                 & (All  #t0 . Unlock(l,x)@t0 ==> #t0=#t2) 
                 & (All lp #t0 . Lock(lp,x)@t0 ==> #t0<#t1 | #t0=#t1 | #t2<#t0) 
                 & (All lp #t0 . Unlock(lp,x)@t0 ==> #t0<#t1 | #t2<#t0 | #t2=#t0 )
                ))
        | #t3<#t1 | #t1=#t3 \"

"

let ass_single_session = "
axiom single_session: // for a single session
    \"All #i #j. Init()@i & Init()@j ==> #i=#j\"

"

let ass_resilient = "
axiom resilient: 
    \"All #i x y. Send(x,y)@i ==> Ex #j. Receive(x,y)@j & #i<#j \"

"

let print_predicates pred_list =
        match 
    fold_left (fun (s,n) t ->
            ("axiom predicate"^(string_of_int n)^":\n\t\""^t^"\"\n\n"
            ^s
                    ,n+1))
            ("",0) pred_list
    with
        (s,_) -> s

module PositionSet = Set.Make( Position );;

let generate_progress_axioms anP =
  let pf = Progressfunction.generate anP in
  let print_toset a bset = 
    let a'= Position.pos2string a 
    in 
    let pvar = "p "
    in
    let blist = (PSet.elements bset)
    in
    let rule_name_part = String.concat "_or_" (List.map pos2string blist)
    in
    let progress_to =
      List.map (fun p -> (sprintf "(Ex #t2. ProgressTo_%s(%s)@t2)" (pos2string p) pvar)) blist
    in
    sprintf   "
axiom progress_%s_to_%s:
    \"All %s#t1. ProgressFrom_%s(%s)@t1 ==> 
       %s
    \"
" a' (rule_name_part) pvar a' pvar (String.concat "\n\t | " progress_to )
  in
  let print_tosetset a bsetset = 
    PSetSet.fold (fun bset s -> (print_toset a bset) ^ s) bsetset ""
  in
  (PMap.fold (fun a bsetset s -> (print_tosetset a bsetset) ^ s) pf "")
  ^
  "

axiom progress_init:
    \" Ex #t. Init()@t \"
"
