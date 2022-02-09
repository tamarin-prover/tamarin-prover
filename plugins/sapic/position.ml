open List

type position = int list

let pos2string  = List.fold_left (fun s i -> string_of_int(i)^s) "" 

type t = position
let compare (s1:position) (s2:position) = match (s1,s2) with
    (a::ar,b::br) -> if Stdlib.compare a b = 0 then Stdlib.compare ar br else Stdlib.compare a b
  |(a::ar,[]) -> 1
  |([],b::br)-> -1
  |([],[]) -> 0

let prefix a b = 
   let rec suffix = function 
    (a::ar,b::br) -> if a=b then suffix (ar,br) else false
  | ([],_)-> true
  | _ -> false
   in
   suffix (rev a,rev b)

let child1 p = 1::p
let child2 p = 2::p

let parent = function [] -> [] | x::p -> p
