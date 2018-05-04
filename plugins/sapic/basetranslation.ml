open Exceptions
open Annotatedsapicaction
open Annotatedsapictree
open Fact
open Atomformulaaction
open Btree
open Var
open Term
open List
open Position
open Annotatedrule

module VarSet = Set.Make( Var );;

let (@@) (a:VarSet.t) (b:VarSet.t) = VarSet.union a b

let (@::) (a:var) (b:VarSet.t) = VarSet.add a b

module ActionSet = Set.Make( Action );;


let basetrans act p tildex = match act with
    Null  -> [([State(p,tildex)], [], [])] 
  (* | Rep  -> [([PState(p,tildex)], [], [State(1::p,tildex)])] *) 
  | Rep  ->
	[
          ([State(p,tildex)], [], [PSemistate(1::p,tildex)]);
          ([PSemistate(1::p,tildex)], [], [State(1::p,tildex)])
	] 
  | NDC -> []
  | Par  -> [([State(p,tildex)], [], [State(1::p,tildex);State(2::p,tildex)])] 
  | MSR(prems,acts,concls) ->
    let tildex' = tildex @@ (vars_factlist prems)  @@ (vars_factlist concls) in
    [ ( State(p,tildex):: prems, (* EventEmpty::*)acts, State(1::p,tildex')::concls ) ]
  | New(v) -> [([State(p,tildex);Fr(v)], [], [State(1::p, v@::tildex)])]
  | Msg_In(t) -> [([State(p,tildex);In(t)],[],[State(1::p,(vars_t t) @@ tildex)])]
  | Msg_Out(t) -> [([State(p,tildex)],[],[State(1::p,(vars_t t) @@ tildex);Out(t)])]
  | Ch_In(t1,t2) -> let tildex' = tildex @@ (vars_t t1) @@ (vars_t t2) in
    [ ( [State(p,tildex);In(List([t1;t2]))], [Action("ChannelInEvent",[List([t1;t2])])], [State(1::p,tildex')]);
      ( [State(p,tildex);Message(t1, t2)], [], [Ack(t1,t2);State(1::p,tildex')])]
  | Ch_Out(t1,t2) -> [
      ( [State(p,tildex);In(t1)], [Action("ChannelInEvent",[t1])], [Out(t2);State(1::p,tildex)]);
      ( [State(p,tildex) ], [], [Semistate(p,tildex); Message(t1, t2)] );
      ( [Semistate(p, tildex);Ack(t1,t2)], [], [State(1::p,tildex)])]
  | Cond(Action(id,tl)) -> let cond_vars = fold_left (fun vl t -> (vars_t t) @@ vl) VarSet.empty tl
    in
    if VarSet.subset cond_vars tildex then 
      [ ([State(p,tildex)], [Action("Pred_"^id,tl)], [State(1::p,tildex)]);
        ([State(p,tildex)], [Action("Pred_not_"^id,tl)], [State(2::p,tildex)])]
    else
      raise (ProcessNotWellformed 
               ("Condition contains unbound variables: "^(String.concat ", "
                                                            ( List.map var2string (VarSet.elements (VarSet.diff cond_vars tildex))))
                ^" (the bound variables are: "
                ^ (String.concat ", " ( List.map var2string (VarSet.elements ( tildex))))^")" )
            )
  | Cond(_) -> raise (InternalRepresentationError "Cond node should contain Action constructor")
  | Insert(t1,t2) -> [([State(p,tildex)], [Action("Insert",[t1 ; t2])], [State(1::p,tildex)])]
  | Event(a) -> [([State(p,tildex)], [(* EventEmpty;*) a], [State(1::p,tildex)])]
  | Lookup(t1,t2) -> 
    [
      ([State(p,tildex)], [Action("IsIn",[t1; t2])], [State(1::p, tildex @@ (vars_t t2))]);
      ([State(p,tildex)], [Action("IsNotSet",[t1])], [State(2::p,tildex)]) ]
  | AnnotatedUnlock(t,a)  ->
    let str = "lock"^(string_of_int a) in
    let unlock_str = "Unlock_"^(string_of_int a) in
    let nonce=a in
    [([ State(p,tildex)], [Action("Unlock",[Var (Pub (string_of_int nonce));  Var (Fresh str); t ]); Action(unlock_str,[Var (Pub (string_of_int nonce));  Var (Fresh str); t ])], [State(1::p, tildex) ])] 
  | AnnotatedLock(t,a)  ->
    let str = "lock"^(string_of_int a) in
    let lock_str = "Lock_"^(string_of_int a) in
    let nonce=(Fresh str) in
    [([ State(p,tildex); Fr(nonce)], [Action("Lock",[Var (Pub (string_of_int a)); Var (nonce); t ]);Action(lock_str,[Var (Pub (string_of_int a)); Var (nonce); t ])], [State(1::p, nonce @:: tildex)])]
  | Delete(t)  -> [
      ( [ State(p,tildex)], [Action("Delete",[ t ])], [State(1::p, tildex) ])]
  | Lock(_) | Unlock(_) -> raise (UnAnnotatedLock ("There is an unannotated lock (or unlock) in the proces description, at position:"^pos2string p))
  | Comment(s) -> raise (TranslationError "Comments should not be present at this point")



let subst_by_pstate_where_needed tree p msrs = 
  let
    subst a =function
      State(a::p,v) -> PState(a::p,v)
    | x -> x
  in
  let step1msrs = try
      (match (process_at tree (child1 p)) with 
         Node(Rep,_,_)  -> map (function (l,a,r) -> (l,a,map (subst 1) r)) msrs
       | _ -> msrs)
    with InvalidPosition _ -> msrs
  in
  let step2msrs =  try
      (match (process_at tree (child2 p)) with 
         Node(Rep,_,_)  -> map (function (l,a,r) -> (l,a,map (subst 2) r)) step1msrs
       | _ -> step1msrs)
    with InvalidPosition _ -> msrs
  in
  step2msrs


let next_tildex p msrs =
  let is_state = function 
      State(p',_) | PState(p',_) -> p'=p
    |  _ -> false
  in
  let (state_list: fact list) = List.filter is_state (List.flatten (List.map (function (_,_,r) -> r) msrs))
  in
  match state_list  with 
    State(p,v)::_ | PState(p,v)::_ -> v
   | _::_ -> raise (ImplementationError "Should not happen by List.filter")
   |  [] -> raise NoNextState (* If state_list is empty *)
    (* TODO might try to detect inconsistencies *)
     
let annotated_rules_subst_state tree p' p msrs=
  (* Substitute every occurence of  State(p,v) on the left-hand-side
   * of every rule by State(p',v) *)
  let subst = function
      State(p_check,v) -> if p_check = p then 
      (*  match p' with 
          [] ->  State(p',v) 
        | _::parent -> (
            match (process_at tree parent) with 
              Node(Rep,_,_)  -> PState(p',v)
            | _ -> *) State(p',v) 
          (* ) *)
      else State(p_check,v)
    | x ->  x 
  in
  List.map (fun  ar -> 
      {  sapic_terms = ar.sapic_terms ;
         position=ar.position; 
         left=(List.map subst ar.left); 
         actions=ar.actions;
         right=ar.right;}  ) msrs
    
