let deoptionalize l =
  let rec deopt acc = function
    | [] -> List.rev acc
    | None::tl -> deopt acc tl
    | Some x::tl -> deopt (x::acc) tl
  in 
  deopt [] l

let map_opt f l = deoptionalize (List.map f l)

let rec mapi_opt i f = function
    [] -> []
  | a::l -> match f i a with
        Some (r) -> r :: mapi_opt (i + 1) f l
       |None ->  mapi_opt (i + 1) f l

let mapi_opt f l = mapi_opt 0 f l
