open Var
open List

module VarSet = Set.Make( Var );;
let (@@) (a:VarSet.t) (b:VarSet.t) = VarSet.union a b

type funident = string

type term = Mult of term * term
        | Exp of term * term
        | List of term list
        | App of funident * term list
        (*| Var of varident *)
        | Plus of term * term
        | Var of var

type termlist = term list

type t = term

let rec compare s1 s2 =
    match (s1,s2) with
            (Mult(t1,t2), Mult(t3,t4))
        |   (Exp(t1,t2), Exp(t3,t4)  )
        |   (Plus(t1,t2), Plus(t3,t4))
        -> if (compare t1 t3)=0 && (compare t2 t3)=0 then 0
        else -1
        | (List(tl1),List(tl2)) 
        -> 
            (
                try
                    if 
                        List.for_all (fun (t1,t2) -> (compare  t1 t2)=0) (List.combine tl1 tl2)
        then
            0
        else -1
    with
                Invalid_argument(_) (*Lists have different length*) -> -1
            )
        | (App(id1,tl1), App(id2,tl2))
        -> 
            if (String.compare id1 id2 =0) && 
                (compare (List tl1) (List tl2))=0
                    then 0
            else -1
        | (Var(v1),Var(v2)) -> Var.compare v1 v2
        | _ -> -1

let rec vars_t = function 
          Mult(t1,t2) 
        | Exp(t1,t2) 
        | Plus(t1,t2) -> VarSet.union (vars_t t1) (vars_t t2)
        | List(termlist) 
        | App(_,termlist) -> List.fold_left (fun vs t -> VarSet.union t vs)
                                VarSet.empty (List.map vars_t termlist)
        | Var(Msg(l)) -> (VarSet.singleton (Msg l))
        | Var(Temp(l)) -> (VarSet.singleton (Temp l))
        | Var(Fresh(l)) -> (VarSet.singleton (Fresh l))
        | Var(Pub l) -> (VarSet.singleton (Pub l))
        | Var(FreshFixed _)
        | Var(PubFixed _) -> (VarSet.empty)

let rec term2string = function
        Mult(t1,t2) -> "("^(term2string t1) ^") * ("^ (term2string t2)^")"
        | Exp(t1,t2) -> "("^(term2string t1) ^") ^ ("^ (term2string t2)^")"
        | List(termlist) -> "<"^(String.concat ", " (List.map term2string
        termlist))^">"
        | App(ident,termlist) -> ident^"("^( (String.concat ", ") (List.map
        term2string termlist) )^")"
        | Plus(t1,t2) -> "("^(term2string t1) ^") + ("^ (term2string t2)^")"
        | Var(l) -> var2string(l)

let flatten_termlist termlist = (String.concat ", ") (List.map term2string termlist)
let term2termlist s = [s] (* dummy for the moment .. TODO*)

let rec subs_t v t term = 
        let f = (subs_t v t) in
        match term with
            Mult(t1,t2)         -> Mult (f t1, f t2)
            | Exp(t1,t2)        -> Exp(f t1, f t2)
            | Plus(t1,t2)       -> Plus(f t1, f t2)
            | List(termlist)    -> List(List.map f termlist)
            | App(g,termlist)   -> App(g,List.map f termlist)
            | Var(v')       -> if v=v' then t else Var(v')

