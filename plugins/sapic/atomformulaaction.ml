open Var
open Term
open Position

type atom = TLeq of var * var
           |TEq  of var * var
           |Eq   of term * term
           |At   of action *var
           |True
           |False
and formula = Atom of atom
       |Not of formula
       |Or of formula*formula
       |And of formula*formula
       |Imp of formula*formula
       |Iff of formula*formula
       |All of VarSet.t * formula
       |Ex of VarSet.t * formula
and action = 
    InitEmpty
  | InitId
  | StopId
  | EventEmpty
  | EventId
  | Predicate of position * (VarSet.t) * formula
  | NegPredicate of position * (VarSet.t) * formula
  | Action of string*termlist 
  | ProgressFrom of position 
  | ProgressTo of position * position
  | Listen of position * var 
  | Receive of position * term
  | Send of position * term

