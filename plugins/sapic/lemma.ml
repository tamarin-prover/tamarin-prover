open Formula 
open Verdict
open Var

module VarSet = Set.Make( Var );;

type lemma = ForallLemma of string * formula (* string is used for header *)
           | ExistsLemma of string * formula
           | AccLemma of string* verdictf * formula * (VarSet.t)
           | ForallRestriction of string * formula 
           | ExistsRestriction of string * formula 
