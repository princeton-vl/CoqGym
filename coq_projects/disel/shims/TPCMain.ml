open Datatypes

open Util
open Shim

type mode = Coordinator | Participant

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
  print_endline "    -me <NAME>           the identity of this node (required)";
  print_endline "    -mode <MODE>         whether this node is the coordinator or participant (required)";
  print_endline "    -coordinator <NAME>  the identity of the coordinator (required if mode=client)";
  exit 1


let rec parse_args = function
  | [] -> ()
  | "-mode" :: "participant" :: args ->
      begin
        mode := Some Participant;
        parse_args args
      end
  | "-mode" :: "coordinator" :: args ->
      begin
        mode := Some Coordinator;
        parse_args args
      end
  | "-me" :: name :: args ->
     begin
       me := Some (nat_of_string name);
       parse_args args
     end
  | "-coordinator" :: name :: args ->
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
  parse_args (List.tl (Array.to_list Sys.argv));
  match !mode, !me with
  | Some mode, Some me -> begin
     Shim.setup { nodes = !nodes; me = me; st = SimpleTPCApp.init_state };
     match mode with
     | Participant ->
        begin match int_of_nat me with
          | 1 -> SimpleTPCApp.p_runner1 ()
          | 2 -> SimpleTPCApp.p_runner2 ()
          | 3 -> SimpleTPCApp.p_runner3 ()
          | n -> usage ("unknown participant name " ^ string_of_int n)
        end
     | Coordinator ->
        try
          SimpleTPCApp.c_runner ()
        with _ -> print_endline "A participant closed its connection. Coordinator exiting."
    end
  | _, _ -> usage "-mode and -me must be given"

let _ = main ()
