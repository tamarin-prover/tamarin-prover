open Exceptions
open Progressfunction
open List
open Annotatedsapictree
open Position
open Printf
open Var
open Atomformulaaction
open Lemma
open Formula
open Term

(* let res_set_in = "restriction set_in: *)
(* \"All x y #t3 . IsIn(x,y)@t3 ==> *)
(*         (Ex #t2 . Insert(x,y)@t2 & #t2<#t3 *) 
(*                 & ( All #t1 . Delete(x)@t1 ==> (#t1<#t2 |  #t3<#t1)) *)
(*                 & ( All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1)) *)
(* )\" *)

(* " *)

let res_set_in_l =  Restriction("set_in",
        All(VarSet.of_list [Msg "x"; Msg "y"; Temp "t3"],
        Imp(
         Atom ( At (Action("IsIn",[Var (Msg "x"); Var (Msg "y")]),Temp "t3")),
         Ex( VarSet.of_list [Temp "t2"],
           And (Atom ( At (Action("Insert",[Var (Msg "x");Var (Msg "y")]),Temp "t2")),
            And ( Atom (TLeq (Temp "t2", Temp "t3")),
             And (
              All(VarSet.of_list [Temp "t1"],
                Imp( Atom ( At (Action("Delete",[Var (Msg "x")]),Temp "t1")),
                     Or (  Atom (TLeq (Temp "t1", Temp "t2")),
                           Atom (TLeq (Temp "t3", Temp "t1"))))),
              All(VarSet.of_list [Temp "t1"; Msg "yp"],
                Imp( Atom ( At (Action("Insert",[Var (Msg "x");Var (Msg "yp")]),Temp "t1")),
                     Or (  Atom (TLeq (Temp "t1", Temp "t2")),
                       Or ( Atom (TEq (Temp "t1", Temp "t2")), 
                            Atom (TLeq (Temp "t3", Temp "t1")))))))
        )))))
)

let res_set_in = lemma2string_noacc res_set_in_l

(* let res_set_notin = *) 
(* "restriction set_notin: *)
(* \"All x #t3 . IsNotSet(x)@t3 ==> *) 
(*         (All #t1 y . Insert(x,y)@t1 ==>  #t3<#t1 ) *)
(*   | ( Ex #t1 .   Delete(x)@t1 & #t1<#t3 *) 
(*                 &  (All #t2 y . Insert(x,y)@t2 & #t2<#t3 ==>  #t2<#t1))\" *)

(* " *)

let res_set_notin_l =  Restriction("set_notin",
        All(VarSet.of_list [Msg "x"; Temp "t3"],
        Imp(
         Atom ( At (Action("IsNotSet",[Var (Msg "x")]),Temp "t3")),
         Or(
              All(VarSet.of_list [Temp "t1"; Msg "y"],
                Imp( Atom ( At (Action("Insert",[Var (Msg "x");Var (Msg "y")]),Temp "t1")),
                       Atom (TLeq (Temp "t3", Temp "t1")))),
             Ex( VarSet.of_list [Temp "t1"],
                And (Atom ( At (Action("Delete",[Var (Msg "x")]),Temp "t1")), 
                 And ( Atom (TLeq (Temp "t1", Temp "t3")),
                       All( VarSet.of_list [Temp "t2"; Msg "y"],
                        Imp( 
                          And (
                            Atom ( At (Action("Insert",[Var (Msg "x");Var (Msg "y")]),Temp "t2")),
                            Atom (TLeq (Temp "t2", Temp "t3"))),
                          Atom (TLeq (Temp "t2", Temp "t1"))
            ))))))))
)
let res_set_notin = lemma2string_noacc res_set_notin_l

(* let res_set_in_no_delete = "restriction set_in: *)
(* \"All x y #t3 . IsIn(x,y)@t3 ==> *)
(*         (Ex #t2 . Insert(x,y)@t2 & #t2<#t3 *) 
(*                 & ( All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1)) *)
(* )\" *)

(* " *)
let res_set_in_no_delete_l =  Restriction("set_in",
        All(VarSet.of_list [Msg "x"; Msg "y"; Temp "t3"],
        Imp(
         Atom ( At (Action("IsIn",[Var (Msg "x"); Var (Msg "y")]),Temp "t3")),
         Ex( VarSet.of_list [Temp "t2"],
           And (Atom ( At (Action("Insert",[Var (Msg "x");Var (Msg "y")]),Temp "t2")),
            And ( Atom (TLeq (Temp "t2", Temp "t3")),
              All(VarSet.of_list [Temp "t1"; Msg "yp"],
                Imp( Atom ( At (Action("Insert",[Var (Msg "x");Var (Msg "yp")]),Temp "t1")),
                     Or (  Atom (TLeq (Temp "t1", Temp "t2")),
                       Or ( Atom (TEq (Temp "t1", Temp "t2")), 
                            Atom (TLeq (Temp "t3", Temp "t1"))))))
        )))))
)

let res_set_in_no_delete = lemma2string_noacc res_set_in_no_delete_l

(* let res_set_notin_no_delete = *) 
(* "restriction set_notin: *)
(* \"All x #t3 . IsNotSet(x)@t3 ==> *) 
(*         (All #t1 y . Insert(x,y)@t1 ==>  #t3<#t1 )\" *)

(* " *)
let res_set_notin_no_delete_l =  Restriction("set_notin",
        All(VarSet.of_list [Msg "x"; Temp "t3"],
        Imp(
         Atom ( At (Action("IsNotSet",[Var (Msg "x")]),Temp "t3")),
              All(VarSet.of_list [Temp "t1"; Msg "y"],
                Imp( Atom ( At (Action("Insert",[Var (Msg "x");Var (Msg "y")]),Temp "t1")),
                       Atom (TLeq (Temp "t3", Temp "t1")))
            ))))

let res_set_notin_no_delete = lemma2string_noacc res_set_notin_no_delete_l

(* let res_predicate_not_eq = " *)
(* restriction predicate_not_eq: *)
(* \"All #i a b. Pred_not_eq(a,b)@i ==> not(a = b)\" *)
(* " *)

let res_predicate_not_eq_l =  Restriction("predicate_not_eq",
    All(VarSet.of_list [Msg "a"; Msg "b"; Temp "i"],
        Imp(
            Atom ( At (Action("Pred_not_eq",[Var (Msg "a"); Var (Msg "b") ]),Temp "i")),
            Not( Atom( Eq(Var (Msg "a"), Var (Msg "b") )))))
)
let res_predicate_not_eq = lemma2string_noacc res_predicate_not_eq_l

(* let res_predicate_eq = " *)
(* restriction predicate_eq: *)
(* \"All #i a b. Pred_eq(a,b)@i ==> a = b\" *)
(* " *)
let res_predicate_eq_l =  Restriction ("immeadiate_in",
    All(VarSet.of_list [Msg "a"; Msg "b"; Temp "i"],
        Imp(
            Atom ( At (Action("Pred_eq",[Var (Msg "a"); Var (Msg "b") ]),Temp "i")),
             Atom( Eq(Var (Msg "a"), Var (Msg "b") )))))

let res_predicate_not_eq = lemma2string_noacc res_predicate_not_eq_l

(* let res_immeadiate_in = " *)
(* restriction immeadiate_in: *)
(* \"All x #t3 . ChannelInEvent(x)@t3 *)
(*         ==> Ex #t2. K(x)@t2 & #t2<#t3 *)
(*                 & (All #t0. Event()@t0  ==> #t0<#t2 | #t3<#t0) *)
(*                 & (All #t0 xp . K(xp)@t0  ==> #t0<#t2 | #t0=#t2 | #t3<#t0 ) *)
(*                              \" *)
        
(* " *)

(* let res_locking = " *)
(* restriction locking: *)
(* \"All p pp l x lp #t1 #t3 . Lock(p,l,x)@t1 & Lock(pp,lp,x)@t3 *) 
(*         ==> *) 
(*         ( #t1<#t3 *) 
(*                  & (Ex #t2. Unlock(p,l,x)@t2 & #t1<#t2 & #t2<#t3 *) 
(*                  & (All #t0 pp  . Unlock(pp,l,x)@t0 ==> #t0=#t2) *) 
(*                  & (All pp lpp #t0 . Lock(pp,lpp,x)@t0 ==> #t0<#t1 | #t0=#t1 | #t2<#t0) *) 
(*                  & (All pp lpp #t0 . Unlock(pp,lpp,x)@t0 ==> #t0<#t1 | #t2<#t0 | #t2=#t0 ) *)
(*                 )) *)
(*         | #t3<#t1 | #t1=#t3 \" *)

(* " *)

let res_locking_l pos =  Restriction( "locking",
    All(VarSet.of_list [Msg "p"; Msg "l"; Msg "x"; Msg "pp"; Msg "lp"; Temp "t1"; Temp "t3"],
        Imp(
         And(     
             Atom ( At (Action("Lock_"^(string_of_int pos),[Var (Msg "p"); Var (Msg "l"); Var (Msg "x") ]),Temp "t1")),
             Atom ( At (Action("Lock",[Var (Msg "pp"); Var (Msg "lp"); Var (Msg "x") ]),Temp "t3"))),
         Or(
          And(
           Atom(TLeq (Temp "t1", Temp "t3")),
           Ex (VarSet.of_list [Temp "t2"],
             And( Atom ( At (Action("Unlock_"^(string_of_int pos),[Var (Msg "p");Var (Msg "l");Var (Msg "x")]),Temp "t2")),
               And (Atom (TLeq (Temp "t1", Temp "t2")),
               And ( Atom (TLeq (Temp "t2", Temp "t3")),
               And ( All(VarSet.of_list [Temp "t0";Msg "pp"],
                         Imp( Atom ( At (Action("Unlock",[Var (Msg "pp");Var (Msg "l");Var (Msg "x")]),Temp "t0")),
                         Atom (TEq (Temp "t0", Temp "t2")))),
               And ( All(VarSet.of_list [Temp "t0";Msg "pp";Msg "lpp"],
                         Imp( Atom ( At (Action("Lock",[Var (Msg "pp");Var (Msg "lpp");Var (Msg "x")]),Temp "t0")),
                         Or ( Atom (TLeq (Temp "t0", Temp "t1")),
                         Or ( Atom (TEq (Temp "t0", Temp "t1")),
                              Atom (TLeq (Temp "t2", Temp "t0")))))),
                    All(VarSet.of_list [Temp "t0";Msg "pp";Msg "lpp"],
                         Imp( Atom ( At (Action("Unlock",[Var (Msg "pp");Var (Msg "lpp");Var (Msg "x")]),Temp "t0")),
                         Or ( Atom (TLeq (Temp "t0", Temp "t1")),
                         Or ( Atom (TLeq (Temp "t2", Temp "t0")),
                              Atom (TEq (Temp "t2", Temp "t0"))))))
              ))))))),
         Or ( Atom (TLeq (Temp "t3", Temp "t1")),
              Atom (TEq (Temp "t1", Temp "t3")))))))

(* let res_locking = lemma2string_noacc res_locking_l *)

let single_session = 
    let i = Temp "i"
    and j = Temp "j"
    in
    All(VarSet.of_list [i;j],
        Imp(
         And(
          Atom(At(InitEmpty,i)),
          Atom(At(InitEmpty,j))),
         Atom(TEq(i,j))))

let single_session_id = 
    let i = Temp "i"
    and j = Temp "j"
    and id s = Msg (Action.id_ExecId ^ s)
    in
    let init s = Action("Init",[Term.Var (id s)])
    in
    All(VarSet.of_list [i;j; id "1"; id "2"],
        Imp(
         And(
          Atom(At(init "1",i)),
          Atom(At(init "2",j))),
         Atom(TEq(i,j))))

(* let res_single_session = " *)
(* restriction single_session: // for a single session *)
(*     \"All #i #j. Init()@i & Init()@j ==> #i=#j\" *)

(* " *)
let res_single_session = "\n" ^ lemma2string_noacc (Restriction("single_session",single_session)) ^ "\n" 
let res_single_session_l = Restriction("single_session",single_session)

(* let res_resilient = " *)
(* restriction resilient: *) 
(*     \"All #i x y. Send(x,y)@i ==> Ex #j. Receive(x,y)@j & #i<#j \" *)
(* " *)

let res_resilient_l = 
    let i = Temp "i"
    and j = Temp "j"
    and x = Msg "x"
    and y = Msg "y"
    in
    Restriction( "resilient",
    All(VarSet.of_list [i;x;y],
        Imp(
            Atom ( At (Action("Send",[Var x;Var y]),i)),
            Ex (VarSet.of_list [j],
            And(
                Atom ( At (Action("Receive",[Var x;Var y]),j)),
                Atom(TLeq(i,j)))))))

let print_predicates pred_list =
        match 
    fold_left (fun (s,n) t ->
            ("restriction predicate"^(string_of_int n)^":\n\t\""^t^"\"\n\n"
            ^s
                    ,n+1))
            ("",0) pred_list
    with
        (s,_) -> s

module PositionSet = Set.Make( Position );;

let progress_init_lemma = Restriction ("progress_init",
      Ex ( (VarSet.of_list [Temp "t"]), 
                            Atom ( At (Action("Init",[]),Temp "t"))))

let progress_init_lemma_acc = Restriction ("progress_init",
      Ex ( (VarSet.of_list [Temp "t"; Msg "id"]), 
                            Atom ( At (Action("Init",[Var(Msg "id")]),Temp "t"))))

let generate_progress_restrictions anP =
  let pf = Progressfunction.generate anP in
  let rec big_or = function 
                | [f] -> f
                | f::fl -> Or(f,big_or fl)
                | [] -> raise (ImplementationError "There should be at least one to position for every from.")
  in
  let lemma a bset = 
    let a'= Position.pos2string a 
    in 
    let pvar = "p "
    in
    let blist = (PSet.elements bset)
    in
    let rule_name_part = String.concat "_or_" (List.map pos2string blist)
    in
    let progress_to =
      (* List.map (fun p -> (sprintf "(Ex #t2. ProgressTo_%s(%s)@t2)" (pos2string p) pvar)) blist *)
        List.map (fun p -> (Ex ( (VarSet.of_list [Temp "t2"]), 
                            Atom ( At (Action("ProgressTo_"^(pos2string p),[Var (Msg pvar)]),Temp "t2")))))
                  blist
    in
    Restriction ( (sprintf "progress_%s_to_%s" a' (rule_name_part)),
                 All (VarSet.of_list [Msg pvar; Temp "t1"],
                  Imp( Atom ( At (Action("ProgressFrom_"^a',[Var (Msg pvar)]),Temp "t1")),
                       (big_or progress_to))))
  in
  (* let print_tosetset a bsetset = *) 

  (*   PSetSet.fold (fun bset s -> (print_toset a bset) ^ s) bsetset "" *)
  (* in *)
  (* (PMap.fold (fun a bsetset s -> (print_tosetset a bsetset) ^ s) pf "") *)
  let lemmas a bsetset = List.map (lemma a) (PSetSet.elements bsetset) in
        List.flatten (PMap.fold (fun a bsetset s -> (lemmas a bsetset) :: s) pf [])
