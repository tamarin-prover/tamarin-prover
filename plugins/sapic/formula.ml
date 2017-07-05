open Var
open Term
open Fact
open Exceptions
open Atomformulaaction
open Atom

type formula=Atomformulaaction.formula

let rec vars_f = function
     Atom(a)    -> vars_atom(a)
    |Not(f)     -> vars_f(f)
    |Or(f1,f2)  
    |And(f1,f2) 
    |Imp(f1,f2)
    |Iff(f1,f2) -> VarSet.union (vars_f f1) (vars_f f2)
    |All(vs,_)    
    |Ex(vs,_)   -> vs

let rec free_vars bound = function
    Atom(a) -> VarSet.diff (vars_atom a) bound
  | Not(f) -> free_vars bound f
  | Or(f1,f2) | And(f1,f2)|Imp(f1,f2)|Iff(f1,f2) -> VarSet.union (free_vars bound f1) (free_vars bound f2)
  | All(q,f) | Ex(q,f) -> free_vars (VarSet.union bound q) f

let rec formula2string = function
     Atom(a)    -> atom2string(a)
    |Not(f)     -> "not("^formula2string(f)^")"
    |Or(f1,f2)  -> "("^formula2string(f1)^" | "^formula2string(f2)^")"
    |And(f1,f2) -> "("^formula2string(f1)^" & "^formula2string(f2)^")"
    |Imp(f1,f2) -> "("^formula2string(f1)^" ==> "^formula2string(f2)^")"
    |Iff(f1,f2) -> "("^formula2string(f1)^" <=> "^formula2string(f2)^")"
    |All(vs,f)  -> "(All "^flatten_varlist_space(VarSet.elements vs)^" . ("
                   ^formula2string(f)^"))"
    |Ex(vs,f)   -> "(Ex "^flatten_varlist_space(VarSet.elements vs)^" . ("
                   ^formula2string(f)^"))"

