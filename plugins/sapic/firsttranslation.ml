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
open Lemma

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
  | Node(y, _, _) -> 
    let sapic_terms=[y] in
    (* TODO a warning when embedded  msrs are used would be nice *)
    let basemsrs = trans y p tildex in
    let msrs = (* subst_by_pstate_where_needed tree p *) basemsrs in
    let tildex'1 = (try next_tildex (1::p) msrs with
        NoNextState -> match y with
          Null ->  VarSet.empty 
        | NDC -> tildex
        | _ -> raise (ImplementationError "ImplementationError"))
    and tildex'2 = try next_tildex (2::p) msrs with
        NoNextState -> 
            (* If we don't get a new tildex because there is no next state, y should be one of the following *)
         (   match y with
          Null | MSR(_) | Rep | NDC | New (_) | Msg_In(_) 
        | Msg_Out(_) | Ch_In(_) | Ch_Out(_) 
        |  Insert(_) | Delete (_) | Event(_) 
        | Lock _ | Unlock _
        | AnnotatedLock _ | AnnotatedUnlock _
          -> VarSet.empty 
        |_ -> raise (ImplementationError ("msr in translation of "^(annotated_sapic_action2string y) ^"should have state "^(pos2string (2::p))^" on its right-hand side."))
         )
    in
    if y=NDC then
       let  l = gen trans tree (1::p) tildex 
       and  r = gen trans tree (2::p) tildex
       and  s1 = annotated_rules_subst_state tree p (1::p)
       and  s2 = annotated_rules_subst_state tree p (2::p) 
       in 
          s1(l)@s2(r)
    else
      msrs2annotated_rules sapic_terms p msrs
      @  (gen trans tree (1::p) tildex'1)
      @  (gen trans tree (2::p) tildex'2)

let noprogresstrans anP = 
  let initrule = { 
    sapic_terms = [Comment "Init"];
    position=[];
    left= [];
    right=[State([],VarSet.empty)] ;
    actions= [InitEmpty]
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
      sapic_terms = [Comment "Init"];
      position=[];
      left= if (Progressfunction.is_from pf []) then [Fr(Fresh("prog_"))] else [];
      right=[State([],varset)] ;
      actions=
        (if (Progressfunction.is_from pf []) then 
            [InitEmpty; ProgressFrom [] ]
         else 
            [InitEmpty])
    }
  in
  initrule::messsageidrule::(gen trans anP [] varset )


(* 
let rec sigma f = function
    | [] -> 0
    | x :: l -> f x + sigma f l;;  


sigma (fun x -> x * x) [1; 2; 3] ;; *)



(* 
let rec fold_bottom f zero = function
    | Empty -> zero
    | Node(y, left, right) -> 
            let res_l = fold_bottom f zero left
            and res_r = fold_bottom f zero right
            in
              f res_l res_r y *)



(*  let match_annotated_lock xp = match (xp:annotated_sapic_action) with
    AnnotatedLock(_,a) -> a
    | _ -> 0 *)

(*   let rec get_lock_positions = function
     _ -> []
    | Node(AnnotatedLock(_,a), l, r) -> a :: get_lock_positions 
 *)

  let rec get_lock_positions x = match x with
   Node(AnnotatedLock(_,a), l, r) -> a :: ( get_lock_positions (l)  @ get_lock_positions (r))
    | _ -> []

    (* Node(AnnotatedLock(,a), l, r) -> a :: ( get_lock_positions (l)  @ get_lock_positions (r)) *)


(* 
  let rec get_lock_positions  = fold_bottom (fun (l:annotated_btree) r y -> match y with 
      _ -> []
      | Node(AnnotatedLock(_,a), l, r) -> a :: fold_bottom l r
     
  )
 *)
    


 
(*   let get_lock_positions = fold_bottom (fun l r y -> match (y:annotated_sapic_action) with
         AnnotatedLock(_,a) -> a::(l @ r)
        | _ -> l @ r 
  )  *)

 (*      match ap with
          Empty -> false
        |   Node(AnnotatedLock _, left, right)
        |   Node(_,left,right) -> (contains_locking left) || (contains_locking right)
 *)

(*   let get_lock_positions = fold_bottom (fun l r y -> match y with
      AnnotatedLock(t,a) -> a::(l @ r)
    | _ -> l @ r
  )
 *)


(*  let rec get_lock_positions ap = 
         match ap with
              Node(AnnotatedLock _, l, r) -> fold_bottom (fun l r y -> match y with
                          AnnotatedLock(_,a) -> a::(l @ r)
                          | _ -> l @ r )
             *)

    
let generate_sapic_restrictions op annotated_process =
    let restrs = 
        if (annotated_process = Empty) then []
      else 
          (if contains_lookup annotated_process then 
              (if  (contains_delete annotated_process) then 
                  [res_set_in_l;  res_set_notin_l]
              else 
                  [res_set_in_no_delete_l; res_set_notin_no_delete_l])
          else [])
          @ (if contains_locking annotated_process then  List.map res_locking_l (get_lock_positions  annotated_process) else [])
          @ (if contains_eq annotated_process then [res_predicate_eq_l; res_predicate_not_eq_l] else [])
          @ (if op.progress then generate_progress_restrictions annotated_process else [])
          @ (if op.progress && contains_resilient_io annotated_process then [res_resilient_l] else [])
          @ (if op.accountability then [] else [res_single_session_l])
        (*  ^ ass_immeadiate_in -> disabled, sound for most lemmas, see liveness paper
         *                  TODO it would be better if we would actually check whether each lemma
         *                  is of the right form so we can leave it out...
         *                  *)
    in
        if op.accountability then
            (* if an accountability lemma with control needs to be shown, we use a 
             * more complex variant of the restritions, that applies them to only one execution *)
            (List.map (bind_lemma_to_session (Msg id_ExecId)) restrs)
            @ (if op.progress then [progress_init_lemma_acc] else [])
        else 
            restrs
             @ (if op.progress then [progress_init_lemma] else [])

let annotate_eventId msr =
    let stop_fact = LFact("Stop",[Var(var_ExecId)]) 
    and has_init = List.exists (function InitId  -> true | _ -> false )
    in
    let fa  = function EventEmpty -> EventId 
                    | InitEmpty -> InitId
                    | o -> o 
    and rewrite_init (l,a,r) = if has_init a then
                    (Fr(var_ExecId)::l,a,stop_fact::r)
                else
                    (l,a,r)
    and add_event_unless_empty = function
        [] -> []
       |l  -> if has_init l then l else EventId::l
    and flr = function 
        State(p,vs) -> State(p,VarSet.add var_ExecId vs)
       |PState(p,vs) -> PState(p,VarSet.add var_ExecId vs)
       |Semistate(p,vs) -> Semistate(p,VarSet.add var_ExecId vs)
       |PSemistate(p,vs) -> PSemistate(p,VarSet.add var_ExecId vs)
                    | o -> o
    and stop_rule = 
        { 
          sapic_terms = [Comment "Stop rule"];
          position=[];
          left=[ stop_fact];
          right=[] ;
          actions= [StopId]
        }
  in
    let f' = function (l,a,r) -> rewrite_init (map flr l,add_event_unless_empty (map fa a),map flr r) in
        stop_rule::(map (msrs_subst f') msr)

let translation input =
  let annotated_process = annotate_locks ( sapic_tree2annotatedtree input.proc) in
  let msr =  
      if input.op.progress 
      then progresstrans annotated_process
      else noprogresstrans annotated_process 
  and lemmas_tamarin = print_lemmas input.lem
  and predicate_restrictions = print_predicates input.pred
  and sapic_restrictions = print_lemmas (generate_sapic_restrictions input.op annotated_process)
  in
  let msr' = if Lemma.contains_control input.lem (* equivalent to op.accountability *)
             then annotate_eventId msr 
             else msr
  in
  input.sign ^ ( print_msr msr' ) ^ sapic_restrictions ^
  predicate_restrictions ^ lemmas_tamarin 
  ^ "end"
