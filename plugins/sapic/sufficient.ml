open Formula
open Lemma
open List
open Atomformulaaction
open Var
open Term
open Deoptionalize
open Verdict
open Exceptions

module VarSet = Set.Make( Var );;

let exclusiveness id op vf =
(*   (XV) Exclusiveness of φ_1,..: not (φ_i && φ_j) for all i≠j *) 
    let vf' = map (function (f,v) -> f) vf in
    let exclusive i j phi_i phi_j = 
        let label = Printf.sprintf "%s_excl_%n_%n" id i j
        in
            ( ForallLemma ((label,op),Not(And(phi_i,phi_j))))
    in
    let option_list =
        mapi (fun i phi_i ->  
            mapi (fun j phi_j -> if i>=j then None else Some (exclusive i j phi_i phi_j)) vf' )
        vf' 
    in
        deoptionalize (List.flatten option_list)

let exhaustiveness id op vf =
(* (EV) Exhaustiveness: φ_1 && .. && φ_n *)
    let vf' = map (function (f,v) -> f) vf in
    let disj = Verdict.big_or vf' in
    let label = Printf.sprintf "%s_exh" id
    in
        ForallLemma  ((label,op),disj)

let dishonest parties b = 
    let c i = (Temp ("c"^string_of_int(i))) in
    let corrupted_a p i = Atom ( At ( (Action ("Corrupted",[Var p])), c i )) in
    match 
            VarSet.fold (fun p (a,i) -> 
        And (
            (if (VarSet.mem p b) then Ex (VarSet.singleton (c i),corrupted_a p i)
             else All (VarSet.singleton (c i), Imp ((corrupted_a p i),(Atom False))))
            ,a),i+1)
            parties
            (Atom True, 0) 
    with (r,_)->r

(* let dishonest_disj parties v = *) 
(*         List.fold_left (fun a b -> Or(dishonest parties b,a)) (Atom False) v *) 

let corrupted_conj = function [] -> Atom True
| b ->
        let corrupted_a i p = Atom ( At ( (Action ("Corrupted",[Var p])), (Temp ("c"^string_of_int(i))))) in
        let atoms = mapi corrupted_a b in
        let conj = List.fold_left (fun a b -> And(b,a)) (Atom True) atoms in
        Ex (free_vars VarSet.empty conj,conj)


let sufficiency id op parties vf phi = 
(* for the each mapping φ_i → V_i  and V_i non-empty *) 
(* where V_i = B_i^1 | .. | B_i^n *)
(* (suf-i) sufficiency of φ_i and B_i^j :  *) 
(* exists-trace: dishonest( B_i^j) && not (φ) *)
(* TODO could optimize: some lemmas are created twice, if different verdicts have the same part *)
    let sufficient i (f,v) = 
        let sufficient j x = 
            let label = Printf.sprintf "%s_suf_%n_%n" id i j in
            ExistsLemma ((label,op), And(dishonest parties x,Not(phi)))
        in
        match v with
          [] -> None
        | (x::xs)  ->  Some (mapi sufficient v)
    in
    flatten (mapi_opt sufficient vf)

let sufficiencySingleton id op parties vf phi = 
(* for the each mapping φ_i → V_i  and V_i singleton *) 
(* i.e. V_i = B  *)
(* exists-trace: dishonest( B_i^j) && not (φ) & φ_i *)
    let sufficient i (f,v) = 
        let sufficient' x = 
            let label = Printf.sprintf "%s_suf_%n" id i in
            ExistsLemma ((label,op), And(f,And(dishonest parties x,Not(phi))))
        in
        match v with
          [] -> None
        | [x]  ->  Some (sufficient' x)
        | (x::xs)  ->  None
    in
    mapi_opt sufficient vf

let sufficiencyComposite id rel vf = 
(* for the each mapping φ_i → V_i  and V_i not singleton *) 
(* all cases are mapped to a singleton case by R *)
(* rel is the non-reflexive part of R, and an associative list guaranteed to point 
 * to singleton. Hence we only check for presence *)
    mapi_opt (fun i -> function 
        (_,[])
        | (_,[_]) -> None
        | _ ->
        let print_rel rel = 
            String.concat "   " (map (fun (x,y) -> Printf.sprintf "%s |-> %s" (string_of_int x)  (string_of_int y)) rel)
        in
        if mem_assoc i rel 
                         then None 
                         else raise (VerdictNotWellFormed ("Sufficiency of case "^string_of_int(i)^" in "^id^" has |verdict| >= 2. It needs to refer to singleton cases for these sufficient conditions. "^(print_rel rel)))
        ) vf
            
let rec pairwise  = function [] -> []
                   | x::xs -> (List.map (fun x' -> (x,x')) xs) @ ( pairwise xs)

let minimalityComposite id rel vf = 
(* for the each mapping φ_i → V_i  and V_i not singleton *) 
(* all cases are mapped to a singleton case by R *)
(* no two of these should be ubset of each other *)
(* rel is the non-reflexive part of R, and an associative list guaranteed to point 
 * to singleton. Hence we only check for presence *)
    mapi_opt (fun i -> function 
        (_,[])
        | (_,[_]) -> None
        | (f,v) ->
        let subset (j,k) = not (j=k) && ((VarSet.subset j k)) || (not (VarSet.subset k j))
        in
        try (match  find subset (pairwise v) with (j,k) -> 
            let warning = "Minimaliy of case "^string_of_int(i)^" in "^id^" with |verdict| >= 2. verdict need not to be subsets of each other, but "
                           ^(flatten_varlist_comma (VarSet.elements j))
                           ^" and "
                           ^(flatten_varlist_comma (VarSet.elements k))
                           ^" are."
            and labelsym = Printf.sprintf "%s_comp_min_%n" id i 
            in 
                (* raise (VerdictNotWellFormed warning ) *)
                Some (ManualLemma (labelsym, warning^"Exclude the smaller when reading the verdict.") )
            )
            with Not_found -> None
        ) vf
            

let completeness_empty id op vf phi = 
(* for the each mapping φ_i → V_i  and V_i empty *) 
(* For all traces $t$: $φ_i(t) ⇒ φ(t)$. *)
    let complete i (f,v) = 
        let label = Printf.sprintf "%s_compl_empty_%n" id i in
        match v with
          [] -> Some (ForallLemma ((label,op),Imp(f,phi)))
        | (x::cs)  ->  None 
        in
    mapi_opt complete vf 

let completeness_nonempty id op vf phi = 
(* for the each mapping φ_i → V_i  and V_i non-empty *) 
(* For all traces $t$: $φ_i(t) ⇒ ¬φ(t)$. *)
    let complete i (f,v) = 
        let label = Printf.sprintf "%s_compl_nonempty_%n" id i in
        match v with
          [] -> None 
        | (x::cs)  ->  Some (ForallLemma ((label,op),Imp(f,Not(phi))))
        in
    mapi_opt complete vf 

let minimality id op parties vf phi = 
(* for the each mapping φ_i → V_i *) 
(* where V_i = B_i^1 | .. | B_i^n *)
(* and for all strict subsets B' of some B_i^j: *)
(* forall-trace not ( φ && Dishonest(B') ) *)
    (* let rec list_of_subsets b = *) 
    (*     if VarSet.is_empty b then [b] *)
    (*     else List.fold_left (fun a elem -> (list_of_subsets (VarSet.remove elem b))@a ) [b] (VarSet.elements b) *)
    (* in *)
    let list_of_immeadeate_subsets b =
        List.map (fun e -> VarSet.remove e b) (VarSet.elements b)
    in
    let minimal f i j k b' = 
        let label = Printf.sprintf "%s_min_%n_%n_%n" id i j k in
        ForallLemma ((label,op), Not(And(Not(phi),dishonest parties b')))
    in
        List.flatten
        ( List.flatten
        (mapi 
        (fun i (f,v) -> mapi 
            (fun j b -> 
                mapi (minimal f i j) (list_of_immeadeate_subsets b)) 
            v)
        vf))

let cartesian l l' = 
  List.concat (List.map (fun e -> List.map (fun e' -> (e,e')) l') l)


let minimalitySingleton id op rel parties vf phi = 
(* for each mapping φ_i → V_i *) 
(* where V_i = B *)
(* and R_i,j (typically, i=j) *)
(* for all strict subsets B' of some B_i^j: *)
(* forall-trace not ( φ_j && Dishonest(B') ) *)
    let list_of_immeadeate_subsets b =
        List.map (fun e -> VarSet.remove e b) (VarSet.elements b)
    in
    let phi j = match List.nth vf j with (f,_)-> f in
    let related i = (* list of φ_j such that (i,j) in rel or j=i *)
        map_opt (function (i',j) -> if i'=i then Some(phi j ) else None) rel
        @ [phi i]
    in
    let minimal i k (b',f_j) = 
        let label = Printf.sprintf "%s_min_%n_%n" id i k in
        ForallLemma ((label,op), Not(And(f_j,dishonest parties b')))
    in
    let  cart_subsets_related i b =  (cartesian (list_of_immeadeate_subsets b) (related i))
    in
    let compute_singleton i = function 
            (_,[b]) -> Some (mapi (minimal i) (cart_subsets_related i b))
           | _      -> None
    in
        List.flatten (mapi_opt compute_singleton vf)

let uniqueness id op vf = 
(* (uni-i) Uniqueness of V_i *)
(* for the each mapping φ_i → V_i *) 
(* where V_i = B_i^1 | .. | B_i^n  and non-empty *)
(*     For all traces: φ_i ⇒ Corrupt(union over  B_i^j for all j) *)
    let unique i (f,v) = 
        let label = Printf.sprintf "%s_uniq_%n" id i in
        let union = List.fold_left (VarSet.union) VarSet.empty v in
        ForallLemma ((label,op), Imp(f,corrupted_conj (VarSet.elements union)))
    in
    (* TODO I think this filter does not work *)
    mapi unique (filter (function (f,[]) -> false | _ -> true ) vf)

let rec make_list n l = if n = 0 then l else make_list (n - 1) (n-1 :: l);;
let rec listn n = make_list n []
let rec reflexive n = map (fun i -> (i,i)) (listn n)


type lifting = Relate | Unrelate

let manualf task id _ i j phi_i phi_j = 
    let label = Printf.sprintf "%s_rel_%n_%n" id i j
    and phi_i' = formula2string phi_i
    and phi_j' = formula2string phi_j
    in
    let lemma= match task with
        Relate -> Printf.sprintf "
For all contexts u such that traces(P,u) in 
    %s 
and u' such that traces(P,u') in 
    %s
it holds that r(u,u')." phi_i' phi_j'
      | Unrelate -> Printf.sprintf "
For all contexts u such that traces(P,u) in 
    %s 
and u' such that traces(P,u') in 
    %s
it holds that NOT r(u,u')." phi_i' phi_j'
    in 
    ManualLemma (label,lemma)

let axiom_event =  
    (* ( All #i #j #k id pos . Init(id)@i & Stop(id)@j & Event(id)@k ==> #i < #k & #k < #j ) *)
        All(VarSet.of_list [Temp "i"; Temp "j"; Temp "k"; Msg "id"],
        Imp(
         And( Atom ( At (Action("Init",[Var (Msg "id")]),Temp "i")),
          And (Atom ( At (Action("Stop",[Var (Msg "id")]),Temp "j")),
           (Atom ( At (Action("Event",[Var (Msg "id")]),Temp "k"))))),
         And ( 
             Atom (TLeq (Temp "i", Temp "k")),
             Atom (TLeq (Temp "k", Temp "j")))
        ))

let axiom_cluster = 
    (* ( All #i #j #k #l id1 id2 . Init(id1)@i & Stop(id1)@j & Init(id2)@k & Stop(id2)@l ==> (#j < #k & #j < #l) | (#l < #i & #l < #j) | (#i=#k & #j=#l & )) *)
        All(VarSet.of_list [Temp "i"; Temp "j"; Temp "k"; Temp "l"; Msg "id1"; Msg "id2"],
        Imp(
            And ( Atom ( At (Action("Init",[Var (Msg "id1")]),Temp "i")),
             And ( Atom ( At (Action("Stop",[Var (Msg "id1")]),Temp "j")),
              And ( Atom ( At (Action("Init",[Var (Msg "id2")]),Temp "k")),
                    Atom ( At (Action("Stop",[Var (Msg "id2")]),Temp "l"))))),
            Or ( 
             And (
              Atom (TLeq (Temp "j", Temp "k")),
              Atom (TLeq (Temp "j", Temp "l"))),
             Or ( 
              And (
               Atom (TLeq (Temp "l", Temp "i")),
                Atom (TLeq (Temp "l", Temp "j"))),
              And (
               Atom (TEq (Temp "i", Temp "k")),
                Atom (TEq (Temp "j", Temp "l")))))))
let axiom_force =
    (* ( All #i id . Init(id)@i ==> Ex #k . Stop(id)@k & i<k ) *)
        All(VarSet.of_list [Temp "i"; Msg "id"],
        Imp(
            Atom ( At (Action("Init",[Var (Msg "id")]),Temp "i")),
            Ex( VarSet.singleton (Temp "k"),
                And( Atom( At (Action("Stop",[Var (Msg "id")]),Temp "k")),
                     Atom(TLeq (Temp "i", Temp "k"))))))

let controlf_equivalence task id op i j phi_i phi_j = 
    let control_condition = 
      (* All pos1 pos2 #p1 #p2. Control(pos1)@p1 & Event(id1)@p1 & Control(pos2)@p2 & Event(id2)@p2==> pos1 = pos2 *)
      (* All sid 2 pos1 pos2 #p1 #p2. Control(sid,pos1)@p1 & Event(id1)@p1 & Control(sid,pos2)@p2 & Event(id2)@p2==> pos1 = pos2 *)
        All(VarSet.of_list [Temp "p1"; Temp "p2"; Msg "pos1"; Msg "pos2"; Msg "sid"],
        Imp(
             And(Atom ( At (Action("Control",[Var (Msg "sid"); Var (Msg "pos1")]),Temp "p1")),
             And(Atom ( At (Action("Event",[Var (Msg "id1")]),Temp "p1")),
              And(Atom ( At (Action("Control",[Var (Msg "sid"); Var (Msg "pos2")]),Temp "p2")),
               Atom ( At (Action("Event",[Var (Msg "id2")]),Temp "p2"))))),
            Atom (Eq (Var (Msg "pos1") , Var(Msg "pos2")))))
    and formula control_cond = 
            Imp(And(And(axiom_event,axiom_cluster),axiom_force),
            All(VarSet.of_list [Msg "id1"; Msg "id2"; Temp "i"; Temp "j"],
            Imp(
                And ( Atom ( At (Action("Init",[Var (Msg "id1")]),Temp "i")),
                 And( Atom ( At (Action("Init",[Var (Msg "id2")]),Temp "j")),
                      Atom  (TLeq (Temp "i", Temp "j")))),
                Or (  
                      Not (bind_to_session (Msg "id1") phi_i),
                      Or ( Not (bind_to_session (Msg "id2") phi_j),
                              control_cond)))))
    in
    match task with
        Relate -> 
            let label = Printf.sprintf "%s_rel_%n_%n" id i j in
            let labelsym = Printf.sprintf "%s_rel_%n_%n" id j i in
            if i>j then ManualLemma (labelsym, "No need, skipped because of symmetric case.")
            else
                ForallLemma((label,op),(formula control_condition))
       | Unrelate ->
            let label = Printf.sprintf "%s_unrel_%n_%n" id i j in
            let labelsym = Printf.sprintf "%s_unrel_%n_%n" id j i in
            if i>j then ManualLemma (labelsym, "No need, skipped because of symmetric case.")
            else
                ForallLemma((label,op),(formula  (Not (control_condition))))



let controlf_subset task id op i j phi_i phi_j = 
    let control_condition = 
      (* new: All #p2 pos2 sid . (Control(sid, pos2)@#p2 & Event(id2)@#p2) ==> Ex #p1 . (Control(sid, pos2)@#p1 & Event(id1)@#p1) *)
        All(VarSet.of_list [ Temp "p2"; Msg "pos2"; Msg "sid"],
        Imp(
             And(Atom ( At (Action("Control",[Var (Msg "sid"); Var (Msg "pos2")]),Temp "p2")),
              Atom ( At (Action("Event",[Var (Msg "id2")]),Temp "p2"))),
             Ex(VarSet.of_list [Temp "p1";],
              And(Atom ( At (Action("Control",[Var (Msg "sid"); Var (Msg "pos2")]),Temp "p1")),
                  Atom ( At (Action("Event",[Var (Msg "id1")]),Temp "p1"))))))
    and formula control_cond = 
            Imp(And(And(axiom_event,axiom_cluster),axiom_force),
            All(VarSet.of_list [Msg "id1"; Msg "id2"; Temp "i"; Temp "j"],
            Imp(
                And ( Atom ( At (Action("Init",[Var (Msg "id1")]),Temp "i")),
                 And( Atom ( At (Action("Init",[Var (Msg "id2")]),Temp "j")),
                      Atom  (TLeq (Temp "i", Temp "j")))),
                Or (  
                      Not (bind_to_session (Msg "id1") phi_i),
                      Or ( Not (bind_to_session (Msg "id2") phi_j),
                              control_cond)))))
    in
    match task with
        Relate -> 
            let label = Printf.sprintf "%s_rel_%n_%n" id i j in
            (* let labelsym = Printf.sprintf "%s_rel_%n_%n" id j i in *)
            (* if i>j then ManualLemma (labelsym, "No need, skipped because of symmetric case.") *)
            (* else *)
            ForallLemma((label,op),(formula control_condition))
       | Unrelate ->
            let label = Printf.sprintf "%s_unrel_%n_%n" id i j in
            (* let labelsym = Printf.sprintf "%s_unrel_%n_%n" id j i in *)
            (* if i>j then ManualLemma (labelsym, "No need, skipped because of symmetric case.") *)
            (* else *)
            ForallLemma((label,op),(formula  (Not (control_condition))))

let relationLifting f id op (vf:verdictf) rel =
    let phi k     = match List.nth vf k with (f,_)-> f in
    let verdict k = match List.nth vf k with (_,v)-> v in
    let n  = List.length vf in
    let full_rel = rel @ (reflexive n) in
    let f' task (i,j) = f task id op i j (phi i) (phi j) in
    let remove_empty (i,j) = match (verdict i, verdict j) with
         ([],_)
        |(_,[])  -> false
        | _ -> true
    in
    let complement = 
        List.filter
        (fun x -> not (List.mem x full_rel))
        (cartesian (listn n) (listn n))
    in 
        (map (f' Relate) (List.filter remove_empty full_rel))
        @
        (map (f' Unrelate) (List.filter remove_empty complement))


let sufficient_conditions kind (id,op) parties vf' phi =
    let vf = wellformed vf'
    and rel = compute_R vf'
    in
    let cases_axioms =
        (exclusiveness id op vf )
        @
        [exhaustiveness id op vf]
        @
        (sufficiencySingleton id op parties vf phi)
        @
        (sufficiencyComposite id rel vf)
        @
        (completeness_empty id op vf phi)
        @
        (completeness_nonempty id op vf phi)
        @
        (minimalitySingleton id op rel parties vf phi)
        @
        (uniqueness id op vf)
    in
    match kind with
    (* (id,op) -> (1* TODO ignore options for now *1) *)
    Coarse -> 
        (exclusiveness id op vf )
        @
        [exhaustiveness id op vf]
        @
        (sufficiency id op parties vf phi)
        @
        (completeness_empty id op vf phi)
        @
        (completeness_nonempty id op vf phi)
        @
        (minimality id op parties vf phi)
        @
        (uniqueness id op vf)
   | Cases ->
        cases_axioms
        @
        (minimalityComposite id rel vf)
        @
        (relationLifting manualf id op vf rel)
        (* @ Not sure if needed. TODO check in the end. *)
        (* [ManualLemma (id, "r is transitive") ] *)
   | ControlEquivalence ->
        (map (add_antecedent Restrictions.single_session_id) cases_axioms)
        @
        (minimalityComposite id rel vf)
        @
        (relationLifting controlf_equivalence id op vf rel)
   | ControlSubset ->
        (map (add_antecedent Restrictions.single_session_id) cases_axioms)
        @
        (minimalityComposite id rel vf)
        @
        (relationLifting controlf_subset id op vf rel)

