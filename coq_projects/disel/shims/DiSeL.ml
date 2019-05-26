open Shim
open Debug

type 'a prog = 'a

let mkProg = fun x -> x

type 'a action = 'a

let mkAction = Obj.magic ()

let ret_prog this w x = x

let act_prog this w act =
  act

let bnd_prog this w p1 p2 =
  p2 p1

let sup_prog _ _ _ =
  failwith "sup_prog"

let inject_prog _ _ _ _ _ x =
  x

let with_inv_prog _ _ _ x =
  x


(*
[Eta expansion for ffix]:

The recursive call must be eta expanded in order to work in a call-by-value semantics.
Otherwise, it would just spin out computing the argument to a value without ever
calling `f`.
*)
let ffix _ _ _ (f : 'a -> 'b) =
  let rec go f = f (fun x -> go f x)
  in go f

let rec coq_while this w cond body init =
  if cond init
  then coq_while this w cond body (body init)
  else init

let find_option f l =
  try
    Some (List.find f l)
  with Not_found -> None

let max_errors = 3
let errors = ref 0

let rec get_msg = function
  | [] -> None
  | fd :: fds ->
     try
       Some (recv_msg fd)
     with e ->
       (* Printf.printf "Got exception: %s\n" (Printexc.to_string e);
       Printexc.print_backtrace stdout; *)
       errors := !errors + 1;
       if !errors < max_errors
       then get_msg fds
       else begin
           (* Printf.printf "Too many errors; aborting.\n%!"; *)
           raise e
         end

let tryrecv_action_wrapper (ctx,hk) this p =
  let () = check_for_new_connections () in
  let fds = get_all_read_fds () in
  let (ready_fds, _, _) = Unix.select fds [] [] 0.0 in
  begin
    match get_msg ready_fds with
    | None -> (* nothing available *) None
    | Some (l, src, tag, msg) ->
       begin
         match Unionmap.UMDef.find Ordtype.nat_ordType (Obj.magic l) ctx with
         | None ->
            begin
              Printf.printf "World is %a\n%!" print_world (Unionmap.UMDef.from (Obj.magic ()) ctx);
              failwith
                (Printf.sprintf "Could not find protocol %a in the world!" sprint_nat l)
            end
         | Some protocol ->
            begin
              match find_option (fun rt -> rt.Protocols.Transitions.t_rcv = tag)
                                protocol.Protocols.Protocols.rcv_trans with
              | None ->
                 failwith
                   (Printf.sprintf
                      "Could not find a receive transition with tag %a in the protocol!"
                      sprint_nat tag)
              | Some rt ->
                 let dstatelet = get_protocol_state (Obj.magic l) in
                 let tm = { State.tag = tag; tms_cont = msg } in
                 if rt.Protocols.Transitions.msg_wf dstatelet (Obj.magic ()) this src tm
                 then
                   let st' = rt.Protocols.Transitions.receive_step this src msg dstatelet (Obj.magic ()) (Obj.magic ()) in
                   update_my_state (Obj.magic l) this st';
                   Some ((src, tag), msg) (* respect Coq tuple associativity *)
                 else
                   failwith (Printf.sprintf "Received a msg that did not pass the wf test!")
            end
       end
  end


let send_action_wrapper (ctx,hk) p this (l : Ordtype.Ordered.sort) t m dst =
  Printf.printf "World is %a\n%!" print_world (Unionmap.UMDef.from (Obj.magic ()) ctx);
  send_msg (Obj.magic l) dst (t.Protocols.Transitions.t_snd) m;
  let dstatelet = get_protocol_state l in
  let ost' = t.Protocols.Transitions.send_step this dst dstatelet m (Obj.magic ()) in
  begin
    match ost' with
    | None -> failwith "send_action_wrapper: send_step failed!"
    | Some st' -> update_my_state l this st'
  end;
  m

let skip_action_wrapper (ctx, hk) this l p f =
  f (get_current_state ()) (Obj.magic ())
