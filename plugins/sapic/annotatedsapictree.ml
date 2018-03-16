open Exceptions
open Annotatedsapicaction
open Btree
open Var
open Position

type annotated_btree = annotated_sapic_action Btree.btree
type sapic_btree = Sapicaction.sapic_action Btree.btree

let rec sapic_tree2annotatedtree (tree:sapic_btree) = fold_bottom (fun (left:annotated_btree) right ->
      function
          Sapicaction.Null -> Node(Null,left,right)
        | Sapicaction.Par -> Node(Par,left,right)
        | Sapicaction.Rep  -> Node(Rep,left,right)
        | Sapicaction.NDC  -> Node(NDC,left,right)
        | Sapicaction.New(t) -> Node(New(t),left,right)
        | Sapicaction.Msg_In(t) -> Node(Msg_In(t),left,right)
        | Sapicaction.Ch_In(t1,t2) -> Node(Ch_In(t1,t2),left,right)
        | Sapicaction.Msg_Out(t) -> Node(Msg_Out(t),left,right)
        | Sapicaction.Ch_Out(t1,t2) -> Node(Ch_Out(t1,t2),left,right)
        | Sapicaction.Insert(t1,t2) -> Node(Insert(t1,t2),left,right)
        | Sapicaction.Delete(t)  -> Node(Delete(t),left,right)
        | Sapicaction.Lock(t)  -> Node(Lock(t),left,right)
        | Sapicaction.Unlock(t)  -> Node(Unlock(t),left,right)
        | Sapicaction.Lookup(t1,t2) -> Node(Lookup(t1,t2),left,right)
        | Sapicaction.Event(a) -> Node(Event(a),left,right)
        | Sapicaction.Cond(a) -> Node(Cond(a),left,right)
        | Sapicaction.MSR(prem,ac,conl) -> Node(MSR(prem,ac,conl) ,left,right)
    ) Empty tree

(* We assume that locks are closed in the order of the following unlocks,
* and that eachone is closed indeed.
* *) 
let annotate_locks (tree:annotated_btree) = 
let rec annotate_each_closest_unlock t annotation tree=
 match tree with  
    Empty -> Empty
  | Node(Unlock(t),l,r) -> Node(AnnotatedUnlock(t,annotation),l,r)
  | Node(Rep,l,r) -> raise ( ProcessNotWellformed "Replication underneath lock")
  | Node(Par,l,r) -> raise (ProcessNotWellformed "Parallel underneath lock")
  | Node(y,l,r) -> Node(y,(annotate_each_closest_unlock t annotation l),
                         (annotate_each_closest_unlock t annotation r))
and 
      max a b = if a> b then a else b
in
let (result,_) = fold_bottom (fun (l,p_l) (r,p_r) a->
             let p=(max p_l p_r)+1 in
             let annotation= p (* Fresh("lock"^string_of_int p) *) in
               match (a:annotated_sapic_action) with
                Lock(t) -> (Node(AnnotatedLock(t,annotation),
                              annotate_each_closest_unlock t annotation l,
                              annotate_each_closest_unlock t annotation r), p)
               | _ -> (Node(a,l,r),p)
    ) (Empty,0) (tree:annotated_btree)
 in
    result


let rec process_at anP = function
    [] -> anP
  |1::xr -> (match (process_at anP xr) with 
        Empty -> raise (InvalidPosition (pos2string (1::xr)))
      | Node(_,l,_) -> l)
  |2::xr -> (match (process_at anP xr) with 
        Empty -> raise (InvalidPosition (pos2string (2::xr)))
      | Node(_,_,r) -> r)
  |p -> raise (InvalidPosition ((pos2string p)))

module PositionSet = Set.Make( Position );;
let (@@) (a:PositionSet.t) (b:PositionSet.t) = PositionSet.union a b
let (@::) (a:position) (b:PositionSet.t) = PositionSet.add a b

let rec filter_positions2 f anP =
  let rec doit p = function
      Empty -> PositionSet.empty
    | Node(x,l,r) -> (
        let rl = doit (1::p) l
        and rr = doit (2::p) r in
        if (f x l r) then p@::(rl @@ rr) else (rl @@ rr) )
  in
  doit [] anP

let filter_positions f = filter_positions2 (fun x _ _ -> f x) 

let valid_pos (anP:'a btree) = filter_positions (fun _ -> true) anP

