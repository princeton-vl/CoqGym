open Unix
open Util
open Debug

let read_fds : (Unix.file_descr, Datatypes.nat) Hashtbl.t = Hashtbl.create 17
let write_fds : (Datatypes.nat, Unix.file_descr) Hashtbl.t = Hashtbl.create 17

type cfg = { nodes : (Datatypes.nat * (string * int)) list
           ; me : Datatypes.nat
           ; mutable st : State.StateGetters.state
           }

let the_cfg : cfg option ref = ref None
let listen_fd : file_descr = socket PF_INET SOCK_STREAM 0

let get_addr_port cfg name =
  try List.assoc name cfg.nodes
  with Not_found -> failwith (Printf.sprintf "Unknown name: %d" (int_of_nat name))

let get_name_for_read_fd fd =
  Hashtbl.find read_fds fd

let send_chunk (fd : file_descr) (buf : bytes) : unit =
  let len = Bytes.length buf in
  (* Printf.printf "sending chunk of length %d" len; print_newline (); *)
  let n = Unix.send fd (Util.raw_bytes_of_int len) 0 4 [] in
  if n < 4 then
    failwith "send_chunk: message header failed to send all at once.";
  let n = Unix.send fd buf 0 len [] in
  if n < len then
    failwith (Printf.sprintf "send_chunk: message of length %d failed to send all at once." len)

let recv_or_close fd buf offs len flags =
  let n = recv fd buf offs len flags in
  if n = 0 then
    failwith "recv_or_close: other side closed connection.";
  n


let receive_chunk (fd : file_descr) : bytes =
  let buf4 = Bytes.make 4 '\x00' in
  let n = recv_or_close fd buf4 0 4 [] in
  if n < 4 then
    failwith "receive_chunk: message header did not arrive all at once.";
  let len = Util.int_of_raw_bytes buf4 in
  let buf = Bytes.make len '\x00' in
  let n = recv_or_close fd buf 0 len [] in
  (* Printf.printf "received chunk of length %d" len; print_newline (); *)
  if n < len then
    failwith
        (Printf.sprintf "receive_chunk: message of length %d did not arrive all at once." len);
  buf

let get_cfg err_msg =
  match !the_cfg with
  | None -> failwith (err_msg ^ " called before the_cfg was set")
  | Some cfg -> cfg

let get_write_fd name =
  try Hashtbl.find write_fds name
  with Not_found ->
    let write_fd = socket PF_INET SOCK_STREAM 0 in
    let cfg = get_cfg "get_write_fd" in
    let (ip, port) = get_addr_port cfg name in
    let entry = gethostbyname ip in
    let node_addr = ADDR_INET (Array.get entry.h_addr_list 0, port) in
    let chunk = Bytes.of_string (string_of_nat cfg.me) in
    connect write_fd node_addr;
    send_chunk write_fd chunk;
    Hashtbl.add write_fds name write_fd;
    write_fd

let setup cfg =
  Printexc.record_backtrace true;
  the_cfg := Some cfg;
  Printf.printf "initial state is: %a\n%!" print_state (Obj.magic cfg.st);
  let (_, port) = get_addr_port cfg cfg.me in
  (* Printf.printf "listening on port %d" port; print_newline (); *)
  setsockopt listen_fd SO_REUSEADDR true;
  bind listen_fd (ADDR_INET (inet_addr_any, port));
  listen listen_fd 8


let new_conn () =
  print_endline "new connection!";
  let (node_fd, node_addr) = accept listen_fd in
  let chunk = receive_chunk node_fd in
  let node = Bytes.to_string chunk in
  let name = nat_of_string node in
  Hashtbl.add read_fds node_fd name;
  (* ignore (get_write_fd name); *)
  Printf.printf "done processing new connection from node %s" node;
  print_newline ()

let check_for_new_connections () =
  let fds = [listen_fd] in
  let (ready_fds, _, _) = select fds [] [] 0.0 in
  List.iter (fun _ -> new_conn ()) ready_fds

let get_all_read_fds () =
  Hashtbl.fold (fun fd _ acc -> fd :: acc) read_fds []

let serialize_msg l tag msg =
  Marshal.to_string (int_of_nat l, int_of_nat tag, List.map int_of_nat msg) []

let deserialize_msg s =
  let (l, tag, msg) = Marshal.from_string s 0 in
  (nat_of_int l, nat_of_int tag, List.map nat_of_int msg)

let recv_msg fd =
  let chunk = receive_chunk fd in
  let (l, tag, msg) = deserialize_msg (Bytes.to_string chunk) in
  let src = get_name_for_read_fd fd in
  Printf.printf "got msg in protocol %a with tag = %a, contents = %a from %s" print_nat l print_nat tag (print_list print_nat) msg (string_of_nat src);
  print_newline ();
  (l, src, tag, msg)

let send_msg l dst tag msg =
  Printf.printf "sending msg in protocol %a with tag = %a, contents = %a to %s" print_nat l print_nat tag (print_list print_nat) msg (string_of_nat dst);
  print_newline ();
  let fd = get_write_fd dst in
  let s = serialize_msg l tag msg in
  let chunk = Bytes.of_string s in
  send_chunk fd chunk

let get_current_state () =
  let cfg = get_cfg "get_current_sate" in
  (*Printf.printf "current state is: %a\n%!" print_state (Obj.magic cfg.st); *)
  cfg.st

let set_current_state x =
  let cfg = get_cfg "set_current_state" in
  (* Printf.printf "setting state to: %a\n%!" print_state (Obj.magic cfg.st); *)
  cfg.st <- x

let get_protocol_state l =
  let st = get_current_state () in
  State.StateGetters.getStatelet st l

let set_protocol_state l x' =
  let st = get_current_state () in
  set_current_state (Unionmap.UMDef.upd Ordtype.nat_ordType l x' st)

let update_my_state l this x' =
  (* Printf.printf "setting state to %a" (print_heap print_ordered_sort_which_is_nat (super_hacky_print_system_heap (Obj.magic this))) x';
  print_newline(); *)
  let dstatelet = get_protocol_state l in
  let dstatelet' =
    { State.dstate = Unionmap.UMDef.upd Ordtype.nat_ordType (Obj.magic this) x'
                                        dstatelet.State.dstate;
      State.dsoup = dstatelet.State.dsoup } in
  set_protocol_state l dstatelet'

