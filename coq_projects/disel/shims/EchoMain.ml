open Datatypes
open Echo

open Util
open Shim

type mode = Client | Server

let mode : mode option ref = ref None
let server_name : Datatypes.nat option ref = ref None
let me : Datatypes.nat option ref = ref None
let nodes : (Datatypes.nat * (string * int)) list ref = ref []

let usage msg =
  print_endline msg;
  Printf.printf "%s usage:\n" Sys.argv.(0);
  Printf.printf "    %s [OPTIONS] <CLUSTER>\n" (Array.get Sys.argv 0);
  print_endline "where:";
  print_endline "    CLUSTER   is a list of triples of ID IP_ADDR PORT,";
  print_endline "              giving all the nodes in the system";
  print_newline ();
  print_endline "Options are as follows:";
  print_endline "    -me <NAME>      the identity of this node (required)";
  print_endline "    -mode <MODE>    whether this node is a client or server (required)";
  print_endline "    -server <NAME>  the identity of the server (required if mode=client)";
  exit 1


let rec parse_args = function
  | [] -> ()
  | "-mode" :: "client" :: args ->
      begin
        mode := Some Client;
        parse_args args
      end
  | "-mode" :: "server" :: args ->
      begin
        mode := Some Server;
        parse_args args
      end
  | "-me" :: name :: args ->
     begin
       me := Some (nat_of_string name);
       parse_args args
     end
  | "-server" :: name :: args ->
     begin
       server_name := Some (nat_of_string name);
       parse_args args
     end
  | name :: ip :: port :: args -> begin
      nodes := (nat_of_string name, (ip, int_of_string port)) :: !nodes;
      parse_args args
    end
  | arg :: args ->
     usage ("Unknown argument " ^ arg)

let main () =
  print_endline "hello from main!";
  parse_args (List.tl (Array.to_list Sys.argv));
  match !mode, !me with
  | Some mode, Some me -> begin
     Shim.setup { nodes = !nodes; me = me };
     match mode with
     | Client -> ignore (echo_client (Obj.magic O) [] O O [])
     | Server -> echo_server (Obj.magic O) [] O
    end
  | _, _ -> usage "-mode and -me must be given"

let _ = main ()
