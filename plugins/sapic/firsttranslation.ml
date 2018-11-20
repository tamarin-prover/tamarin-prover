open Sapic
open List
open Exceptions
open Formula
open Tamarin
open Btree
open Term
open Fact
open Action
open Position
open Var
open Atomformulaaction
open Annotatedsapicaction
open Annotatedsapictree
open Annotatedrule
open Restrictions
open Translationhelper
open Basetranslation
open Progressfunction

module ActionSet = Set.Make( Action );;

let (@@) (a:VarSet.t) (b:VarSet.t) = VarSet.union a b
let (@::) (a:var) (b:VarSet.t) = VarSet.add a b

let rec gen trans tree p tildex  = match (process_at tree p) with
(* Processes through an annotated process and translates every single action
 * according to trans. It substitutes states by pstates for replication and 
 * makes sure that tildex is updated for the next call. It also performs the 
 * substituion necessary for NDC 
 *)
    Empty -> [] 
  | Node(y, left, right) ->
    let sapic_terms=[y] in
    (* TODO a warning when embedded  msrs are used would be nice *)
    let basemsrs = trans y p tildex in
    let msrs = (* subst_by_pstate_where_needed tree p *) basemsrs in
    let tildex'1 = (try next_tildex (1::p) msrs with
        NoNextState -> match y with
          Null -> VarSet.empty 
        | NDC | Let(_) -> tildex
        | _ -> raise ProgrammingError)
    and tildex'2 = try next_tildex (2::p) msrs with
        NoNextState -> 
            (* If we don't get a new tildex because there is no next state, y should be one of the following *)
         (   match y with
          Null | Let(_) | MSR(_) | Rep | NDC | New (_) | Msg_In(_) 
        | Msg_Out(_) | Ch_In(_) | Ch_Out(_) 
        |  Insert(_) | Delete (_) | Event(_) 
        | Lock _ | Unlock _
        | AnnotatedLock _ | AnnotatedUnlock _
          -> VarSet.empty 
        |_ -> raise (ImplementationError ("msr in translation of "^(annotated_sapic_action2string y) ^"should have state "^(pos2string (2::p))^" on its right-hand side."))
         )
    in
    if y=NDC then
       let  l = gen trans tree (1::p) tildex in
       let  r = gen trans tree (2::p) tildex
       and  s1 = annotated_rules_subst_state tree p (1::p)
       and  s2 = annotated_rules_subst_state tree p (2::p) 
       in 
          s1(l)@s2(r)
    else
       let (l, r) = match (left, right) with
                      (Node(Let(r), ll, Empty), Node(Let(s), rr, Empty)) ->
                        (let new_tree = replace_process_at tree (Node(y, ll, rr)) p in
                        (annotated_rules_update (Some r) (gen trans new_tree (1::p) tildex'1), annotated_rules_update (Some s) (gen trans new_tree (2::p) tildex'2)))
                    | (Node(Let(r), ll, Empty), rr) ->
                        (let new_tree = replace_process_at tree (Node(y, ll, rr)) p in
                        (annotated_rules_update (Some r) (gen trans new_tree (1::p) tildex'1), gen trans new_tree (2::p) tildex'2))
                    | (ll, Node(Let(s), rr, Empty)) ->
                        (let new_tree = replace_process_at tree (Node(y, ll, rr)) p in
                        (gen trans new_tree (1::p) tildex'1, annotated_rules_update (Some s) (gen trans new_tree (2::p) tildex'2)))
                    | (ll, rr) ->
                        (gen trans tree (1::p) tildex'1, gen trans tree (2::p) tildex'2)
       in
       msrs2annotated_rules sapic_terms p msrs @ l @ r

let noprogresstrans anP = 
  let initrule = { 
    process_name = None;
    sapic_terms = [Comment "Init"];
    position=[];
    left= [];
    right=[State([],VarSet.empty)] ;
    actions= [Init]
  }
  in
  initrule::(gen basetrans anP [] VarSet.empty)

let progresstrans anP = (* translation for processes with progress *)
  let pf = Progressfunction.generate anP in
  let trans y p tildex = 
    (* First step: apply custom rules input on (non-)resilient channels *)
    (* progresstrans defines its own version of basetrans, which treats
       message input differently (as we have resilient channels) but otherwise
       calls basetrans for the rules that we also use for "ordinary" processes.
       This is to minimize maintenance for both versions. *)
    let step1msrs = 
      match y with
        Msg_In(_) | Msg_Out(_) -> 
          raise (ProcessNotWellformed 
                   "If progress is activated, the process should not contain in(m) and out(m) actions.")
      (* Actually, we could just allow it and 
       * have in(m) be a synomym for in(c,m) *)
      | Ch_In(Var(PubFixed("c")),t) -> 
        (* [ *)
        (*   ( [State(p,tildex)], [], [Semistate(1::p,tildex)]); *)
        (*   ( [Semistate(1::p,tildex); In(List [Var(PubFixed("c")); t] )], *)
        (*     [Action("ChannelInEvent",[List([Var(PubFixed("c"));t])])], *)
        (*     [ State(1::p,(vars_t t) @@ tildex) ]) *)
        (* ] *)
        [
          ( [State(p,tildex); In(List [Var(PubFixed("c")); t] )],
            [Action("ChannelInEvent",[List([Var(PubFixed("c"));t])])],
            [ State(1::p,(vars_t t) @@ tildex) ])
        ]
      | Ch_Out(Var(PubFixed("c")),t) -> 
        [
          ([State(p,tildex); In(Var(PubFixed("c")))],
           [Action("ChannelInEvent",[Var(PubFixed("c"))])],
           [State(1::p,(vars_t t) @@ tildex);Out(t)])
        ]
      | Ch_In(Var(PubFixed("r")),t) -> 
        (* [ *)
        (*   ( [State(p,tildex)], [], [Semistate(1::p,tildex)]); *)
        (*   ( [Semistate(1::p,tildex); In(t);MessageIDReceiver(p)], *)
        (*     [Receive(p,t)], *)
        (*     [State(1::p,(vars_t t) @@ (tildex))] *)
        (*   ) *)
        (* ] *)
        [
          ( [State(p,tildex); In(t);MessageIDReceiver(p)],
            [Receive(p,t)],
            [State(1::p,(vars_t t) @@ (tildex))]
          )
        ]

      | Ch_Out(Var(PubFixed("r")),t) -> 
        [ ([MessageIDSender(p); State(p,tildex)],[Send(p,t)], [Out(t); State(1::p, tildex)])]
      | Ch_In(_) | Ch_Out(_) -> raise (ProcessNotWellformed 
                                         ("If progress is activated, the process should not contain in(a,m) and out(a,m) actions for a different from 'c' or 'r'. See position"^(pos2string p)))
      | _ -> basetrans y p tildex
    in
    (* The resulting rules
       (step1msrs) do not contain the progress actions, so
        step2 adds ProgressTo actions, and step3 ProgressFrom actions. Step1 and
        step2 try to be clever and only add these actions where a State-fact is
        in the premises, respectively in the conclusions. *)
    let step2 p' somemsrs = (* add ProgressTo events *)
      match (Progressfunction.find_from pf p') with
        Some (q) -> List.map (fun (l,a,r) -> 
          if (List.exists (function State _ | PState _ -> true | _ -> false ) l )
          then 
            (l,(ProgressTo(p',q)::a),r)
          else (l,a,r)
        ) somemsrs
      |None ->  somemsrs
    and step3 p' somemsrs = (* add ProgressFrom events *)
      if (Progressfunction.is_from pf p') then
        List.map (fun (l,a,r) -> 
            if (List.exists (function State _ | PState _ -> true | _ -> false ) r )
            then
              let an=Fresh("prog_"^pos2string p') in
              (Fr(an)::l,(ProgressFrom p'::a),
               List.map (function State(p',v) -> State(p',an @:: v) | bla -> bla) r
              )
            else (l,a,r)
        ) somemsrs
      else
        somemsrs
    in
    step3 (child1 p) ( step2 (child2 p) ( step2 (child1 p) (step1msrs)))
  and messsageidrule = 
    { 
      process_name = None;
      sapic_terms = [Comment "MessageID-rule"];
      position=[];
      left=[Fr(Fresh("x"))];
      right=[LFact("MID_Sender",[Var(Fresh("x"))]);
             LFact("MID_Receiver",[Var(Fresh("x"))])
            ];
      actions= []
    }
  and varset = if (Progressfunction.is_from pf []) then (VarSet.singleton (Fresh("prog_"))) else VarSet.empty
  in
  let initrule =
    { 
      process_name = None;
      sapic_terms = [Comment "Init"];
      position=[];
      left= if (Progressfunction.is_from pf []) then [Fr(Fresh("prog_"))] else [];
      right=[State([],varset)] ;
      actions=
        (if (Progressfunction.is_from pf []) then 
            [Init; ProgressFrom [] ]
         else 
            [Init])
    }
  in
  initrule::messsageidrule::(gen trans anP [] varset )

    
let generate_sapic_restrictions annotated_process =
  if (annotated_process = Empty) then ""
  else 
      (if contains_lookup annotated_process then res_set_in ^ res_set_notin else "")
    (*^ (if contains_locking annotated_process then  List.map res_locking_l (get_lock_positions  annotated_process) else [])*)
    ^ (if contains_eq annotated_process then res_predicate_eq ^ res_predicate_not_eq else "")
    ^ (* Stuff that's always there *)
    res_single_session (*  ^ass_immeadiate_in TODO disabled ass_immeadiate, need to change semantics in the paper *)

let translation input =
  let annotated_process = annotate_locks ( sapic_tree2annotatedtree input.proc) in
  (* Printf.printf "%s\n" (annotatedtree2string annotated_process); *)
  let msr =  
      if input.op.progress 
      then progresstrans annotated_process
      else noprogresstrans annotated_process
  in
  let lemmas_tamarin = print_lemmas input.lem
  and users_restrictions = print_restrictions input.ax
  and predicate_restrictions = print_predicates input.pred
  and sapic_restrictions = 
    if input.op.progress then 
      generate_sapic_restrictions annotated_process
      ^ (generate_progress_restrictions annotated_process)
      ^ res_resilient 
    else 
      generate_sapic_restrictions annotated_process
  (*and sapic_restrictions = List.map print_lemmas (generate_sapic_restrictions annotated_process)*)
  and sapic_restrictions_locks = 
    if contains_locking annotated_process
    then  
      let lock_list = get_lock_positions annotated_process  
      in
      print_lock_restrictions  (remove_duplicates lock_list)
    else ""
  in
  input.sign ^ ( print_msr msr ) ^ users_restrictions ^ sapic_restrictions ^  sapic_restrictions_locks ^
  predicate_restrictions ^ lemmas_tamarin 
  ^ "end"
