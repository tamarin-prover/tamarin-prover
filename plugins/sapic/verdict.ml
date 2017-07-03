open Var
open Term
open Fact
open Exceptions
open Atomformulaaction
open Atom
open List

module VarSet = Set.Make( Var );;

type causes = VarSet.t
type verdict = causes list

type proto_verdictf_case = Case of formula * verdict | Otherwise of verdict
type proto_verdictf = proto_verdictf_case list

type verdictf = (formula * verdict) list

let is_wellformed vf = (* contains otherwise at most once *)
    length (filter (function Case(_,_) -> false | Otherwise(_) -> true) vf) < 2

let rec big_or = function 
                | [f] -> f
                | f::fl -> Or(f,big_or fl)
                | [] -> raise (VerdictNotWellFormed "Verdict should contain at least one case which is not \"otherwise\"")

let wellformed vf = 
        if is_wellformed vf then map 
            (function Case(f,v) -> (f,v) 
                    | Otherwise(v) -> 
                            let f' = Not( big_or( fold_left (fun l -> function Case(f,_) -> f::l
                                                                    | Otherwise(_) -> l) [] vf))
                            in
                                (f',v) ) vf
        else raise (ImplementationError "Otherwise has been used more than once. Parser should have caught that.")


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

