open List

type varident = string

type var =
          PubFixed of varident
        | Pub of varident
        | FreshFixed of varident
        | Fresh of varident
        | Temp of varident
        | Msg of varident 

type t = var

let compare s1 s2 =
    let rank = function
        PubFixed(_) -> 1
                | Pub(_) -> 2
                | FreshFixed(_) -> 3
                | Fresh(_) -> 4
                | Temp(_) -> 5
                | Msg(_) -> 6
    in
            match (s1,s2) with
          (PubFixed(n1),PubFixed(n2)) 
                | (Pub(n1),Pub(n2)) 
                | (FreshFixed(n1),FreshFixed(n2)) 
                | (Fresh(n1),Fresh(n2)) 
                | (Temp(n1),Temp(n2)) 
                | (Msg(n1),Msg(n2)) -> (String.compare n1 n2)
                (* needs to be a total order! *)
        | (a,b)  -> Stdlib.compare (rank a) (rank b)

let var2string = function 
        | PubFixed(name) -> "'"^name^"'"
        | Pub(name)->  "$"^name
        | FreshFixed(name)->  "~$"^name
        | Fresh(name)-> "~"^name
        | Temp(name)-> "#"^name
        | Msg(name) -> name 
                (* List.map (String.to_int c) (String.explode name)*)
                (* "Msg-"^(String.escaped name)^"-End" *)
                (* (string_of_int (Char.code (String.get name 0)))^
                (string_of_int (String.length name)) *)


let flatten_varlist_comma varlist = (String.concat ", ") (List.map var2string varlist)
let flatten_varlist_space varlist = (String.concat " ") (List.map var2string varlist)
