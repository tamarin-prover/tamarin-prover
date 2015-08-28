(* start ocaml and load the file with:
   $ ocaml
   # #use "STR.ml";;
   ...
   val test : unit -> 'a = <fun>
   # test ();;
   Log: <$A.1, $gid1, <list($A.1,$A.2,$A.3,$A.4), ($g^(($g^(($g^(~f.439*~f.685))*~f.217))*~f.428))>>
   Log: <$A.3, $gid1, <list($A.1,$A.2,$A.3,$A.4), ($g^(($g^(($g^(~f.439*~f.685))*~f.217))*~f.428))>>
   Log: <$A.2, $gid1, <list($A.1,$A.2,$A.3,$A.4), ($g^(($g^(($g^(~f.439*~f.685))*~f.217))*~f.428))>>
   Log: <$A.4, $gid1, <list($A.1,$A.2,$A.3,$A.4), ($g^(($g^(($g^(~f.439*~f.685))*~f.217))*~f.428))>>
   Log: <$A.1, $gid2, <list($A.1,$A.2), ($g^(~f.14*~f.393))>>
   Log: <$A.2, $gid2, <list($A.1,$A.2), ($g^(~f.14*~f.393))>>

*)
#use "topfind";;
#thread;;

type term = Public of (string * int)
          | Fresh of (string * int)
          | App of (string * (term list))


let rec intercalate sep = function [] -> []
  | b::[] -> [b]
  | b::bs -> b::sep::(intercalate sep bs)


let rec print_term = function
  |  (App ("exp", [a;b])) ->
      Printf.sprintf "(%s^%s)" (print_term a) (print_term b)
  |  (App ("mult", args)) ->
      Printf.sprintf "(%s)" (String.concat "*" (List.map print_term args))
  |  (App ("pair", args)) ->
      let ms = List.concat (List.map (function App ("pair", args) -> args | t -> [t]) args)
      in Printf.sprintf "<%s>" (String.concat ", " (List.map print_term ms))
  |  (App (name, args)) ->
      Printf.sprintf "%s(%s)" name (String.concat "," (List.map print_term args))
  | Public (s,i) -> String.concat "" [ Printf.sprintf "$%s" s;
                                       if i == 0 then "" else Printf.sprintf ".%d" i]
  | Fresh  (s,i) -> String.concat "" [ Printf.sprintf "~%s" s;
                                       if i == 0 then "" else Printf.sprintf ".%d" i]

let rec norm_term t =
  match t with
    (App ("exp", [a;b])) ->
      let (a', b') = (norm_term a, norm_term b) in
      (match a' with
         (App ("exp", [c;d])) -> App ("exp", [c; norm_term (App ("mult", [d;b']))])
       | _ -> (App ("exp", [a';b'])))
  | (App ("mult", args)) ->
      let ms = List.map (function App ("mult", args) -> args | t -> [t])
                        (List.map norm_term args)
      in (App ("mult", List.sort compare (List.concat ms)))
  | _ -> t
      

(** Some undefined functions on terms. *)
let undefined () = failwith "undefined"

let fresh_name () =
  let r = Random.int 1000 in
  Fresh ("f", r)

let (^) a b = norm_term (App ("exp", [a;b]))

let pair (a,b) = App ("pair", [a;b])

let te (a) = App ("te", [a])

let first = function (App ("pair", [a;b])) -> a | _ -> undefined ()

let second = function (App ("pair", [a;b])) -> b | _ -> undefined ()

let g = Public ("g", 0)

let agent a = Public ("A", a)

let agent_list bs = App ("list", List.map (fun x -> agent x) bs)

(* The blinded randomness of the given agent *)
let blinded_random (t,a) = App ("blindRandomOf", [t; agent a])

(* The blinded key of the given agent *)
let blinded_key (t,a) = App ("blindKeyFor", [t; agent a])

(** The fixed functions, just placeholders for now. *)

(* fork a thread that executes the given function *)
let fork f = ignore (Thread.create f ())

let chan_out = Event.new_channel ()

let chan_in  = Event.new_channel ()

let received_messages = ref []

let waiting_channels = ref []

type either = Out of (term * term) | In of (term * term Event.channel)

let rec try_send (chant,t) waiting =
  if List.mem_assoc chant waiting then
    let c = List.assoc chant waiting in
    fork (fun () -> Event.sync (Event.send c t));
    try_send (chant,t) (List.remove_assoc chant waiting)
  else waiting      

let try_receive (chant,c) sent =
  if List.mem_assoc chant sent then
    let t = List.assoc chant sent in
    fork (fun () -> Event.sync (Event.send c t))


let rec net_handler (sent_msgs, waiting_chans) =
  let req = Event.sync (Event.choose [ Event.wrap (Event.receive chan_out) (fun x -> Out x);
                                       Event.wrap (Event.receive chan_in)  (fun x -> In x)])
  in
  match req with
     Out (chant, t) ->
       let waiting_chans' = try_send (chant, t) waiting_chans in
       net_handler (sent_msgs @ [(chant,t)], waiting_chans')
   | In  (chant, c) ->
       try_receive (chant, c) sent_msgs;
       net_handler (sent_msgs, waiting_chans @ [(chant,c)])


(* input the given message from the network *)
let input chant =
  (* Printf.printf "Waiting for input on %s\n" (print_term chant); flush stdout; *)
  let c = Event.new_channel () in
  Event.sync (Event.send chan_in (chant, c));
  let t = Event.sync (Event.receive c) in
  (* Printf.printf "Input: %s on %s\n" (print_term t) (print_term chant); flush stdout; *)
  t

(* output the given message to the network *)
let output (chant,t) =
  Printf.printf "Output: %s on %s\n" (print_term t) (print_term chant); flush stdout;
  Event.sync (Event.send chan_out (chant, t))

(* log the given term *)
let log t = Printf.printf "Log: %s\n" (print_term t); flush stdout

(** We want to model this with a multiset of naturals in Tamarin. *)

type agent = int

type agent_mset = agent list

(** Protocol description *)

(* This is the function in the adversary interface. *)
let rec start_group (init, others, gid) =
  fork (fun () -> initiator (init, others, gid));
  start_group_responders (init, [], others, gid)

and start_group_responders (init, started, not_started, gid) =
  match not_started with
    b::bs -> fork (fun () -> responder (b, init, started, bs, gid));
             start_group_responders (init, started @ [b], bs, gid)
  | [] -> ()

and initiator (me, others, gid) =
  (match others with
     b::bs -> let r = fresh_name () in
              (* receive blinded randomness from b *)
              let br = input (blinded_random(gid,b)) in
              let key = br^r in
              (* send blinded key for b *)
              output (blinded_key(gid,b), g ^ r);
              initiator_loop (me, [b], bs, gid, key)
   | _     -> undefined ())

and initiator_loop (me, handled, not_handled, gid, key) =
  match not_handled with
    b::bs -> (* receive blinded randomness from b *)
             let br = input (blinded_random(gid,b)) in
             let newkey = br^te(key) in
             (* send blinded key for b *)
             output (blinded_key(gid,b), g ^ te(key));
             initiator_loop (me, handled @ [b], bs, gid, newkey)
  | []    -> log (pair(agent me, pair(gid, pair(agent_list (me :: handled), key))))

and responder (me, init, below, above, gid) =
  let r = fresh_name () in
  output (blinded_random(gid,me), g ^ r);
  let bk = input (blinded_key(gid,me)) in
  responder_loop (me, init, below @ [me], above, gid, bk ^ r)

and responder_loop (me, init, below, above, gid, key) =
  match above with
    (b::bs) -> (* receive blinded randomness from b *)
               let br = input (blinded_random(gid,b)) in
               responder_loop (me, init, below @ [b], bs, gid, (br ^ te(key)))
  | []      -> log (pair(agent me, pair(gid, pair(agent_list ( [init] @ below), key))))


(** Testing *)

(* execute two sessions of the protocol in parallel *)
let test () =
  fork (fun () -> start_group (1, [2;3;4], Public ("gid1", 0)));
  fork (fun () -> start_group (1, [2], Public ("gid2", 0)));
  net_handler ([],[])


(*
(** Protocol description *)

(* This is the function in the adversary interface. *)
let rec start_group (init, others, bcast_tag) =
  fork (fun () -> initiator (init,others, bcast_tag));
  start_group_loop (init, init::others, others, bcast_tag)

and start_group_loop (init, all, others, bcast_tag) =
  match others with
    b::bs -> fork (fun () -> responder (b, all, bs, bcast_tag));
             start_group_loop (init, all, bs, bcast_tag)
  | [] -> ()

and initiator (me, others, bcast_tag) =
  let r = fresh_name () in
  initiator_loop (me, me::others, others, bcast_tag, r)

and initiator_loop (me, all, remainder, bcast_tag, key) =
  match remainder with
    (b::bs) -> (* receive blinded randomness from b *)
               let msg = input (blinded_random(bcast_tag,b)) in
               (* send blinded key for b *)
               output (blinded_key(bcast_tag,b), g ^ key);
               initiator_loop (me, all, bs, bcast_tag, msg ^ key)
  | []      -> log (pair(agent me, pair(bcast_tag, pair(agent_list all, key))))

and responder (me, all, above, bcast_tag) =
  let r = fresh_name () in
  output (blinded_random(bcast_tag,me), g ^ r);
  let msg = input (blinded_key(bcast_tag,me)) in
  responder_loop (me, all, above, bcast_tag, msg ^ r)

and responder_loop (me, all, above, bcast_tag, key) =
  match above with
    (b::bs) -> (* receive blinded randomness from b *)
               let msg = input (blinded_random(bcast_tag,b)) in
               responder_loop (me, all, bs, bcast_tag, msg ^ h(key))
  | []      -> log (pair(agent me, pair(bcast_tag, pair(agent_list all, key))))

*)
