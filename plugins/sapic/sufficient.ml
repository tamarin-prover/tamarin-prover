open Formula
open Lemma
open List
open Atomformulaaction
open Var
open Term

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
        Deoptionalize.deoptionalize (List.flatten option_list)

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

let dishonest_disj parties v = 
        List.fold_left (fun a b -> Or(dishonest parties b,a)) (Atom False) v 

let corrupted_conj = function [] -> Atom True
| b ->
        let corrupted_a i p = Atom ( At ( (Action ("Corrupted",[Var p])), (Temp ("c"^string_of_int(i))))) in
        let atoms = mapi corrupted_a b in
        let conj = List.fold_left (fun a b -> And(b,a)) (Atom True) atoms in
        Ex (free_vars VarSet.empty conj,conj)

let sufficiency id op parties vf phi = 
(* for the each mapping φ_i → V_i *) 
(* where V_i = B_i^1 | .. | B_i^n *)
(* (suf-i) sufficiency of φ_i: exists-trace *) 
(* ( φ_i && ( dishonest(B_i^1) | .. | dishonest(B_i^n)) && not (φ) ) *)
(* unless V_i is empty verdict, then *)
(* ( φ_i && dishonest(empty) && φ ) *)
    let sufficient i (f,v) = 
        let label = Printf.sprintf "%s_suf_%n" id i in
        match v with
          [] -> ExistsLemma ((label,op), And(f,And(dishonest_disj parties v,phi)))
        | v  ->  ExistsLemma ((label,op), And(f,And(dishonest_disj parties v,Not(phi)))) (* Does not work. *)
        in
    mapi sufficient vf 

let minimality id op parties vf phi = 
(* for the each mapping φ_i → V_i *) 
(* where V_i = B_i^1 | .. | B_i^n *)
(* and for all strict subsets B' of some B_i^j: *)
(* (min-i) Minimality of V_i: forall-trace *)
(* not ( φ_i && Dishonest(B') ) *)
(* TODO not sure, maybe instead need *)
(* not ( φ_i && φ && Dishonest(B') ) *)
    (* let rec list_of_subsets b = *) 
    (*     if VarSet.is_empty b then [b] *)
    (*     else List.fold_left (fun a elem -> (list_of_subsets (VarSet.remove elem b))@a ) [b] (VarSet.elements b) *)
    (* in *)
    let list_of_immeadeate_subsets b =
        List.map (fun e -> VarSet.remove e b) (VarSet.elements b)
    in
    let minimal f i j k b' = 
        let label = Printf.sprintf "%s_min_%n_%n_%n" id i j k in
        ForallLemma ((label,op), Not(And(f,dishonest parties b')))
    in
        List.flatten
        ( List.flatten
        (mapi 
        (fun i (f,v) -> mapi 
            (fun j b -> 
                mapi (minimal f i j) (list_of_immeadeate_subsets b)) 
            v)
        vf))

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

let sufficient_conditions header parties vf phi =
    match header with
    (id,op) -> (* ignore options for now *)
    (exclusiveness id op vf )
    @
    [exhaustiveness id op vf]
    @
    (sufficiency id op parties vf phi)
    @
    (minimality id op parties vf phi)
    @
    (uniqueness id op vf)

