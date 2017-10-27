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
            

let completeness id op vf phi = 
(* for the each mapping φ_i → V_i  and V_i empty *) 
(* For all traces $t$: $φ_i(t) ⇒ φ(t)$. *)
    let complete i (f,v) = 
        let label = Printf.sprintf "%s_compl_%n" id i in
        match v with
          [] -> Some (ForallLemma ((label,op),Imp(f,phi)))
        | (x::cs)  ->  None 
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

let rec make_list n l = if n = 0 then l else make_list (n - 1) (n :: l);;
let rec listn n = make_list n []
let rec singletons n = map (fun i -> (i,i)) (listn n)


let relationLifting id (vf:verdictf) rel =
    let phi k = match List.nth vf k with (f,_)-> formula2string f in
    let relate (i,j) = 
        let label = Printf.sprintf "%s_rel_%n_%n" id i j in
        let lemma= Printf.sprintf "
For all contexts u such that traces(P,u) in 
    %s 
and u' such that traces(P,u') in 
    %s
it holds that r(u,u')."
        (phi i) (phi j) in
        ManualLemma (label,lemma)
    in
    let unrelate (i,j) = 
        let label = Printf.sprintf "%s_rel_%n_%n" id i j in
        let lemma= Printf.sprintf "
For all contexts u such that traces(P,u) in 
    %s 
and u' such that traces(P,u') in 
    %s
it holds that NOT r(u,u')."
        (phi i) (phi j) in
        ManualLemma (label,lemma)
    in
    let n  = List.length vf - 1 in
    let full_rel = rel @ (singletons n) in
    let complement = 
        List.filter
        (fun x -> not (List.mem x full_rel))
        (cartesian (listn n) (listn n))
    in 
        (map relate full_rel)
        @
        (map unrelate complement)


let sufficient_conditions kind (id,op) parties vf' phi =
    let vf = wellformed vf'
    and rel = compute_R vf'
    in
    match kind with
    (* (id,op) -> (1* ignore options for now *1) *)
    Coarse -> 
        (exclusiveness id op vf )
        @
        [exhaustiveness id op vf]
        @
        (sufficiency id op parties vf phi)
        @
        (completeness id op vf phi)
        @
        (minimality id op parties vf phi)
        @
        (uniqueness id op vf)
   | Cases ->
        (exclusiveness id op vf )
        @
        [exhaustiveness id op vf]
        @
        (sufficiencySingleton id op parties vf phi)
        @
        (sufficiencyComposite id rel vf)
        @
        (completeness id op vf phi)
        @
        (minimalitySingleton id op rel parties vf phi)
        @
        (relationLifting id vf rel)
        @
        [ManualLemma (id, "r is transitive") ]

