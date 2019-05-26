open Hh_term

(* info about what the ATP used in the proof *)
type atp_info = {
  deps : string list; (* dependencies: lemmas, theorems *)
  defs : string list; (* definitions (non-propositional) *)
  typings : string list;
  inversions : string list;
  injections : string list;
  discrims : (string * string) list;
  types : string list; (* (co)inductive types *)
}

val prn_atp_info : atp_info -> string

val extract_eprover_data : string (* file name *) -> atp_info
val extract_vampire_data : string (* file name *) -> atp_info
val extract_z3_data : string (* file name *) -> atp_info
val extract_cvc4_data : string (* file name *) -> atp_info

val write_atp_file : string (* file name *) -> hhdef list (* filtered deps *) ->
  hhdef list (* hyps *) -> hhdef list (* all deps *) -> hhdef (* goal *) -> unit

val minimize : atp_info ->
  hhdef list (* hyps *) -> hhdef list (* all deps *) -> hhdef (* goal *) ->
  atp_info

val predict : hhdef list (* filtered deps *) -> hhdef list (* hyps *) ->
  hhdef list (* all deps *) -> hhdef (* goal *) ->
  atp_info
