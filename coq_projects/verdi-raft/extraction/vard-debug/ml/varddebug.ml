open List
open Printf
open Str

let num_nodes_default = 3
let debugger_addr_default = "localhost"
let debugger_port_default = 4343

let num_nodes = ref num_nodes_default
let debugger_addr = ref debugger_addr_default
let debugger_port = ref debugger_port_default

let parse inp =
  let opts =
    [ ("-n", Arg.Set_int num_nodes, "{num} number of nodes in cluster")
    ; ("-debugger-addr", Arg.Set_string debugger_addr, "{addr} debugger addr")
    ; ("-debugger-port", Arg.Set_int debugger_port, "{port} debugger port")
    ] in
  Arg.parse_argv ?current:(Some (ref 0)) inp
    opts
    (fun x -> raise (Arg.Bad (sprintf "%s does not take position arguments" inp.(0))))
    "Try -help for help or one of the following."

let rec range start upto =
  if start = upto then
    []
  else
    start :: (range (start + 1) upto)
      
let _ =
  let _ =
    try
      parse Sys.argv
    with
    | Arg.Help msg ->
      printf "%s: %s" Sys.argv.(0) msg;
      exit 2
    | Arg.Bad msg ->
      eprintf "%s" msg;
      exit 2
  in
  let module NumNodes =
      struct
	let v = !num_nodes
      end
  in
  let module Params =
    (val (module VarDDebugArrangement.DebugParams(NumNodes) : VarDDebugArrangement.VarDDebugParams))
  in
  let module Arrangement = VarDDebugArrangement.VarDDebugArrangement(Params) in
  let module VarD = DebugShim.Shim(Arrangement) in
  let open VarD in
  let start_node name =
    Thread.create main {me = name ; debugger_addr = (!debugger_addr, !debugger_port)}
  in
  let threads = List.map start_node (range 0 !num_nodes) in
  List.iter (fun t -> Thread.join t) threads
