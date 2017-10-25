open Formula 
open Verdict
open Var

module VarSet = Set.Make( Var );;

type acckind = Coarse | Cases

type lemma = ForallLemma of (string * string) * formula (* string is used for header and options *)
           | ExistsLemma of (string * string) * formula
           | AccLemma of acckind * (string * string)* proto_verdictf * formula * (VarSet.t)
           | Restriction of string * formula 
