open Formula 
open Verdict
open Var

module VarSet = Set.Make( Var );;

type lemma = ForallLemma of (string * string) * formula (* string is used for header and options *)
           | ExistsLemma of (string * string) * formula
           | AccLemma of (string * string)* verdictf * formula * (VarSet.t)
           | ForallRestriction of string * formula 
           | ExistsRestriction of string * formula 
