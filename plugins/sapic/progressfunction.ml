open Exceptions
open Position
open Positionplusinit
open Annotatedsapicaction
open Annotatedsapictree
open Map
open List
open Btree

module PSet = struct
  include Set.Make( Position )
  let (@@) (a:t) (b:t) = union a b
  let (@.:) (a:position) (b:t) = add a b
  let to_string (ps:t) =
    let l = elements ps in
    if List.length l = 0 then "EMPTYSET"
    else
      (List.fold_left (fun xs xp -> xs^"; "^(pos2string xp) )
	 ("{ "^(pos2string (List.hd l))) (List.tl l))^" }"
end;;

module PSetSet = struct
  include Set.Make( PSet )
  let to_string (pss:t) =
    let l = elements pss in
    if List.length l = 0 then "EMPTYSET"
    else
      (List.fold_left (fun xs xp -> xs^"; "^(PSet.to_string xp) )
	 ("{ "^(PSet.to_string (List.hd l))) (List.tl l))^" }"
end;;

let rec (@.) (set:PSet.t) (p:position) = 
    (* suffix list p to each element of set *)
    PSet.of_list (List.map (fun lst -> lst @ p) (PSet.elements set))

let (@@.) (setset:PSetSet.t) p =
    (* suffix list p to each element in a set of set of sets *)
    PSetSet.of_list (List.map (fun set -> set @. p) (PSetSet.elements setset))


module PMap = struct
  include Map.Make( Position )
  let print m = iter (fun p pss -> Printf.printf "%s |-> %s\n" (pos2string p)
    (PSetSet.to_string pss)) m
end;;


let fromP anP =
  let rec blocking = function 
      (* return None if root is non-blocking,
       * and Some (s) if it is, with s being defined as follows:
       * if root is NDC, consider the grand-children the n-ary interpretation of
       * the nesting.
       * if root is in/!, it's the child
       * if root is 0, empty
       *)
      Node(Null   ,l,r) -> Some (PSet.empty)
    | Node(Ch_In _,l,r) 
    | Node(Rep    ,l,r) -> Some (PSet.singleton [1] )
    | Node(NDC    ,l,r) ->
      (match (blocking l) with
	Some (s1) ->
	  (match blocking r with
	    Some (s2) -> Some((s1@.[1]) @@ (s2@.[2]))
	  | _ -> None)
      | _ -> None)
    | _ -> None
  in
  let rec f proc b = match proc with
      Empty 
    | Node(Null,_,_) -> PSet.empty 
    | Node(Rep,l,_)
    | Node(Ch_In _,l,_) -> ( f l true) @. [1]
    | Node(Cond _, l,r) 
    | Node(Lookup _, l,r) -> ( if b then PSet.singleton([]) else  PSet.empty ) @@  ((f l false) @. [1]) @@ ((f r false) @. [2])
    | Node(NDC, l,r) -> ( match (blocking l, blocking r) with
      ( Some (spl) , Some (spr) ) -> 
	(
	  let sp = (spl@.[1]) @@ (spr@.[2]) in 
          (* perform recursive step on (indirect) children of NDC *)
	  PSet.fold (fun pos set -> ((f (process_at proc pos) true) @. pos) @@ set ) sp PSet.empty 
          (* true is set because we come from a blocking NDC (both children are
           * blocking) *)
	)
      | ( Some (spl) , None ) ->
        (if b then PSet.singleton([]) else  PSet.empty )
	@@ (PSet.fold (fun pos set -> ((f (process_at proc pos) false) @. pos) @@ set ) (spl @. [1]) PSet.empty)
	@@  ((f r false) @. [2])

      | ( None, Some (spr) ) ->
        (if b then PSet.singleton([]) else  PSet.empty )
	@@  ((f l false) @. [1])
	@@ (PSet.fold (fun pos set -> ((f (process_at proc pos) false)
				      @. pos) @@ set ) (spr @. [2]) PSet.empty)  

      |  ( None    , None    ) ->
            ( if b then PSet.singleton([]) else  PSet.empty ) @@  ((f l false) @. [1]) @@ ((f r false) @. [2])
    )
    | Node(Par, l,r) -> ( if b then PSet.singleton([]) else  PSet.empty )
        @@  ((f l false) @. [1]) @@ ((f r false) @. [2])
    | Node(Msg_In _,l,_)  ->
        raise (ProcessNotWellformed
                 "If progress is activated, the process should not contain in(m) and out(m) actions.")
    | Node(_,l,_) -> ( if b then PSet.singleton([]) else  PSet.empty )
        @@  (( f  l false) @. [1] ) 
  in
  f anP true

let generate anP =
  let combine_with y x_i set1 =
    PSetSet.fold
      (fun y_i set2 -> PSetSet.add (PSet.union x_i y_i) set2)
      y set1
  in
  let combine x y = PSetSet.fold (combine_with y) x PSetSet.empty
  in

  let rec blocking = function 
      Node(Ch_In _,l,r) 
    | Node(Rep    ,l,r) 
    | Node(Null   ,l,r) -> Some (PSet.singleton [1] )
    | Node(NDC    ,l,r) ->
      (match (blocking l) with
	Some (s1) ->
	  (match blocking r with
	    Some (s2) -> Some((s1@.[1]) @@ (s2@.[2]))
	  | _ -> None)
      | _ -> None)
    | _ -> None
  in

  let rec f proc = match proc with
      Empty -> PSetSet.empty
    | Node(Null,_,_)
    | Node(Rep,_,_)
    | Node(Ch_In _,_,_) -> PSetSet.singleton(PSet.singleton([]))
    | Node(Cond _, l,r)
    | Node(Lookup _, l,r) -> combine (  ( f l  ) @@. [1]   ) (  ( f r  ) @@. [2]   )  
    | Node (NDC, l, r) -> (
      match (blocking l, blocking r) with
        ( Some (psl), Some (psr) ) -> PSetSet.singleton ( PSet.singleton ( [] )  )
      |  ( Some (psl), None ) ->
	  PSet.fold
	    (fun pos pss -> combine (f (process_at proc pos)@@. pos) pss )
	    (psl @. [1])
	    (( f r  ) @@. [2]) 
      |  ( None, Some (psr) ) ->
	  PSet.fold
	    (fun pos pss -> combine (f (process_at proc pos)@@. pos) pss )
	    (psr @. [2])
	    (  ( f l  ) @@. [1]   )
      |  ( None    , None    ) ->
        combine (  ( f l  ) @@. [1]   ) (  ( f r  ) @@. [2]   )
    )
    | Node(Msg_In _,l,_)  ->
      raise (ProcessNotWellformed
               "If progress is activated, the process should not contain in(m) and out(m) actions.")
    | Node(_,l,r) -> PSetSet.union ((f l) @@. [ 1 ]) ((f r) @@. [ 2 ])
  in
  
  let add2map =
    fun x m -> (PMap.add x ((f (process_at anP x))@@. x) m)
  in
  PSet.fold add2map (fromP anP) PMap.empty (*construct map from f function*)  
    
let find_from pf p = 
  let is_in_setset _ bsetset = 
    PSetSet.exists (PSet.mem p) bsetset
  in
  let filtered_map = PMap.filter is_in_setset pf
  in
  match PMap.cardinal filtered_map with
    0 -> None
  | 1 -> let (q,_) = ( PMap.choose filtered_map ) in Some (q)
  | _ ->
    Printf.printf "Progress function is defined as\n";
    PMap.print pf;
    raise (ImplementationError "Progress function faulty") 
	  
let is_from pf q = PMap.mem q pf

