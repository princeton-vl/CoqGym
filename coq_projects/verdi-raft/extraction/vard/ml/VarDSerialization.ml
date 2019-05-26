open Str
open Printf
open VarDRaft
open VarD
open Util

let serializeOutput out =
  let (c, os) =
    match Obj.magic out with
    | NotLeader (client_id, request_id) ->
       (string_of_char_list (Obj.magic client_id), sprintf "NotLeader %s" (string_of_int request_id))
    | ClientResponse (client_id, request_id, o) ->
       let Response (k, value, old) = Obj.magic o in
       (string_of_char_list (Obj.magic client_id),
        match value, old with
        | Some v, Some o ->
           sprintf "Response %s %s %s %s"
             (string_of_int request_id)
             (string_of_char_list k)
             (string_of_char_list v)
             (string_of_char_list o)
        | Some v, None ->
           sprintf "Response %s %s %s -"
             (string_of_int request_id)
             (string_of_char_list k)
             (string_of_char_list v)
        | None, Some o ->
           sprintf "Response %s %s - %s"
             (string_of_int request_id)
             (string_of_char_list k)
             (string_of_char_list o)
        | None, None ->
           sprintf "Response %s %s - -"
             (string_of_int request_id)
             (string_of_char_list k))
  in (c, Bytes.of_string os)

let deserializeInp i =
  let inp = String.trim (Bytes.to_string i) in
  let r = regexp "\\([0-9]+\\) \\([A-Z]+\\) +\\([/A-Za-z0-9]+\\|-\\) +\\([/A-Za-z0-9]+\\|-\\) +\\([/A-Za-z0-9]+\\|-\\)[^/A-Za-z0-9]*" in
  if string_match r inp 0 then
    (match (matched_group 1 inp, matched_group 2 inp,
            matched_group 3 inp, matched_group 4 inp,
            matched_group 5 inp) with
     | (i, "GET", k, _, _) -> Some (int_of_string i, Get (char_list_of_string k))
     | (i, "DEL", k, _, _) -> Some (int_of_string i, Del (char_list_of_string k))
     | (i, "PUT", k, v, _) -> Some (int_of_string i, Put ((char_list_of_string k), (char_list_of_string v)))
     | (i, "CAD", k, o, _) -> Some (int_of_string i, CAD (char_list_of_string k, char_list_of_string o))
     | (i, "CAS", k, "-", v) -> Some (int_of_string i, CAS ((char_list_of_string k), None, (char_list_of_string v)))
     | (i, "CAS", k, o, v) -> Some (int_of_string i, CAS ((char_list_of_string k), Some (char_list_of_string o), (char_list_of_string v)))
     | _ -> None)
  else
    (print_endline "No match" ; None)

let deserializeInput inp client_id =
  match deserializeInp inp with
  | Some (request_id, input) ->
    Some (ClientRequest (Obj.magic (char_list_of_string client_id), request_id, Obj.magic input))
  | None -> None

let deserializeMsg (b : bytes) : VarDRaft.msg = Marshal.from_bytes b 0

let serializeMsg (msg : VarDRaft.msg) : bytes = Marshal.to_bytes msg []

let deserializeClientId b =
  let s = Bytes.to_string b in
  (*let r = regexp "^[0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]-[0-9a-f][0-9a-f][0-9a-f][0-9a-f]-4[0-9a-f][0-9a-f][0-9a-f]-[89ab][0-9a-f][0-9a-f][0-9a-f]-[0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]$" in*)
  let r = regexp "^[0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]4[0-9a-f][0-9a-f][0-9a-f][89ab][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]$" in
  if string_match r s 0 then
    Some s
  else
    None
