open Var
open Term
open Fact
open Exceptions
open Atomformulaaction
open Atom
open List
open Deoptionalize

module VarSet = Set.Make( Var );;

type causes = VarSet.t
type verdict = causes list

type proto_causes = VerdictPart of VarSet.t | Ref of string
type proto_verdict = proto_causes list

type proto_verdictf_case = RefCase of string * formula * proto_verdict |  Case of formula * proto_verdict | Otherwise of proto_verdict 
type proto_verdictf = proto_verdictf_case list

type verdictf = (formula * verdict) list

let is_wellformed_other vf =
    (* contains otherwise at most once *)
    length (filter (function Case(_,_)|RefCase(_,_,_) -> false | Otherwise(_) -> true) vf) < 2


let rec big_or = function 
                | [f] -> f
                | f::fl -> Or(f,big_or fl)
                | [] -> raise (VerdictNotWellFormed "Verdict should contain at least one case which is not \"otherwise\"")

let deref' vf r = 
    let filter r i = function RefCase(r',_,v) -> if String.equal r r' then Some(i,v) else None
                             | _ -> None
    in
    match mapi_opt (filter r) vf with
                []     -> raise (VerdictNotWellFormed ("Could not find verdict named "^r^"."))
               |[(i,[VerdictPart(vs)])] -> (i,vs)
               |[(_,[Ref(s)])] -> raise (VerdictNotWellFormed ("Reference "^r^"points to another reference "^s^"."))
               |[(_,v)]    -> raise (ImplementationError "Verdicts refered to need to be singleton. Parser should have caught that.")
               |x::xs  -> raise (VerdictNotWellFormed ("More than one verdict named "^r^"."))

(* let rec deref' vf r = (* This version deferences recursively -- might be of future use .. *) *)
(*     let filter r i = function RefCase(r',_,v) -> if String.equal r r' then Some(i,v) else None *)
(*                              | _ -> None *)
(*     in *)
(*     match mapi_opt (filter r) vf with *)
(*                 []     -> raise (VerdictNotWellFormed ("Could not find verdict named "^r^".")) *)
(*                |[(i,[VerdictPart(vs)])] -> (i,vs) *)
(*                |[(i,[Ref(s)])] -> *) 
(*                        (1* raise (VerdictNotWellFormed ("Reference "^r^" points to another reference "^s^".")) *1) *)
(*                        (match deref' vf s with (1* TODO might diverge, add loop detection later *1) *)
(*                        (_,vs) -> (i,vs) ) *)
(*                |[(_,v)]    -> raise (ImplementationError "Verdicts refered to need to be singleton. Parser should have caught that.") *)
(*                |x::xs  -> raise (VerdictNotWellFormed ("More than one verdict named "^r^".")) *)

let deref vf v =
    let f = function VerdictPart(s) -> s
                   | Ref(r) -> match deref' vf r with (i,vs) -> vs
    in
    map f v

let get_verdict = function
    RefCase (_,_,v) | Case(_,v) | Otherwise(v) -> v

let compute_R vf = 
        (* This is computing the relation R_i,j between cases,
         * but not reflexivity
         * *)
    let deref_i r = match deref' vf r with (j,_) -> j
    in
    let iter_verdict i = function Ref(r) -> Some ((i, deref_i r))
                        | _ -> None 
    in
    let iter_case i case = map_opt (iter_verdict i) (get_verdict case)
    in
      flatten (mapi iter_case vf)


let wellformed vf = 
        if not (is_wellformed_other vf) then
            raise (ImplementationError "Otherwise has been used more than once. Parser should have caught that.")
        else 
            map 
            (function Case(f,v) -> (f,deref vf v) 
                    | RefCase(i,f,v) -> (f,deref vf v)
                    | Otherwise(v) -> 
                            let f' = Not( big_or( fold_left (fun l -> function Case(f,_) 
                                                                    | RefCase(_,f,_) -> f::l
                                                                    | Otherwise(_) -> l) [] vf))
                            in
                                (f',deref vf v) ) vf

(* let rec vars_f = function *)
(*      Atom(a)    -> vars_a(a) *)
(*     |Not(f)     -> vars_f(f) *)
(*     |Or(f1,f2) *)  
(*     |And(f1,f2) *) 
(*     |Imp(f1,f2) *)
(*     |Iff(f1,f2) -> VarSet.union (vars_f f1) (vars_f f2) *)
(*     |All(vs,_) *)    
(*     |Ex(vs,_)   -> vs *)

(* let rec formula2string = function *)
(*      Atom(a)    -> atom2string(a) *)
(*     |Not(f)     -> "not("^formula2string(f)^")" *)
(*     |Or(f1,f2)  -> "("^formula2string(f1)^" | "^formula2string(f2)^")" *)
(*     |And(f1,f2) -> "("^formula2string(f1)^" & "^formula2string(f2)^")" *)
(*     |Imp(f1,f2) -> "("^formula2string(f1)^" ==> "^formula2string(f2)^")" *)
(*     |Iff(f1,f2) -> "("^formula2string(f1)^" <=> "^formula2string(f2)^")" *)
(*     |All(vs,f)  -> "All "^flatten_varlist(VarSet.elements vs)^" . (" *)
(*                    ^formula2string(f)^")" *)
(*     |Ex(vs,f)   -> "Ex "^flatten_varlist(VarSet.elements vs)^" . (" *)
(*                    ^formula2string(f)^")" *)

