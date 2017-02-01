open Exceptions
open Var
open Term
(* open Formula *)
open Atomformulaaction
open Action

type atom=Atomformulaaction.atom

let atom2string = function 
     TLeq(v1,v2) -> var2string(v1)^" < "^var2string(v2)
    |TEq(v1,v2)  -> var2string(v1)^" = "^var2string(v2)
    |Eq(t1,t2)   -> term2string(t1)^" = "^term2string(t2)
    |At(s,v)     -> action2string(s)^"@"^var2string(v)
    |True        -> "T"
    |False       -> "F"

let vars_a = function 
     TLeq(v1,v2) 
    |TEq(v1,v2) -> VarSet.add v2 (VarSet.singleton v1)
    |Eq(t1,t2)   -> VarSet.union (vars_t t1) (vars_t t2)
    |At(a,v)     -> raise (NotImplementedError "Computing the variables in an action has not been implemented yet, but it should not be necessary")
    |True        
    |False       -> VarSet.empty
