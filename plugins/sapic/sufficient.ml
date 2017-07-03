open Formula
open Lemma
open List
open Atomformulaaction
open Var
open Term

module VarSet = Set.Make( Var );;

let exclusiveness id vf =
(*   (XV) Exclusiveness of φ_1,..: not (φ_i && φ_j) for all i≠j *) 
    let vf' = map (function (f,v) -> f) vf in
    let exclusive i j phi_i phi_j = 
        let label = Printf.sprintf "lemma %s_excl_%n_%n" id i j
        in
            ( ForallLemma (label,Not(And(phi_i,phi_j))))
    in
    let option_list =
        mapi (fun i phi_i ->  
            mapi (fun j phi_j -> if i>=j then None else Some (exclusive i j phi_i phi_j)) vf' )
        vf' 
    in
        Deoptionalize.deoptionalize (List.flatten option_list)

let exhaustiveness id vf =
(* (EV) Exhaustiveness: φ_1 && .. && φ_n *)
    let vf' = map (function (f,v) -> f) vf in
    let disj = Verdict.big_or vf' in
    let label = Printf.sprintf "lemma %s_exh" id
    in
        ForallLemma  (label,disj)

let sufficiency id parties vf phi = 
(* for the each mapping φ_i → V_i *) 
(* where V_i = B_i^1 | .. | B_i^n *)
(* (suf-i) sufficiency of φ_i: exists-trace *) 
(* ( φ_i && ( dishonest(B_i^1) | .. | dishonest(B_i^n)) && not (φ) ) *)
    let sufficient i (f,v) = 
        let label = Printf.sprintf "lemma %s_suf_%n" id i in
        let corrupted_a p i = Atom ( At ( (Action ("Corrupted",[Var p])), (Temp ("c"^string_of_int(i))))) in
        let dishonest b = 
            match 
            VarSet.fold (fun p (a,i) -> 
            And ((if (VarSet.mem p b) then (corrupted_a p i) else Not (corrupted_a p i)),a),i+1)
            parties
            (Atom True, 0) 
            with (r,_)->r
        in
        let dishonest_disj v = 
            let disj = List.fold_left (fun a b -> Or(dishonest b,a)) (Atom False) v in
            Ex (free_vars VarSet.empty disj,disj)
        in
        ExistsLemma (label, And(f,And(dishonest_disj v,Not(phi))))
    in
        mapi sufficient vf 

let sufficient_conditions id parties vf phi =
    (exclusiveness id vf )
    @
    [exhaustiveness id vf]
    @
    (sufficiency id parties vf phi)

