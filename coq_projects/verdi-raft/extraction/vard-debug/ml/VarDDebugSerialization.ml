open Str
open Printf
open VarDRaftDebug
open VarD
open Util

let serializeOutput out =
  let (cid, outStr) = 
    match (Obj.magic out) with
    | NotLeader (client_id, request_id) ->
       (client_id, sprintf "NotLeader %s" (string_of_int request_id))
    | ClientResponse (client_id, request_id, o) ->
       let Response (k, value, old) = (Obj.magic o) in
       (client_id,
        match (value, old) with
        | Some v, Some o -> sprintf "Response %s %s %s %s"
                                    (string_of_int request_id)
                                    (string_of_char_list k)
                                    (string_of_char_list v)
                                    (string_of_char_list o)
        | Some v, None -> sprintf "Response %s %s %s -"
                                  (string_of_int request_id)
                                  (string_of_char_list k)
                                  (string_of_char_list v)
        | None, Some o -> sprintf "Response %s %s - %s"
                                  (string_of_int request_id)
                                  (string_of_char_list k)
                                  (string_of_char_list o)
        | None, None -> sprintf "Response %s %s - -"
                                (string_of_int request_id)
                                (string_of_char_list k))
  in (cid, Bytes.of_string outStr)

let deserializeInp i =
  let inp = String.trim (Bytes.to_string i) in
  let r = regexp "\\([0-9]+\\) \\([0-9]+\\) \\([A-Z]+\\) +\\([/A-za-z0-9]+\\|-\\) +\\([/A-za-z0-9]+\\|-\\) +\\([/A-za-z0-9]+\\|-\\)[^/A-za-z0-9]*" in
  if string_match r inp 0 then
    (match (matched_group 1 inp, matched_group 2 inp,
            matched_group 3 inp, matched_group 4 inp,
            matched_group 5 inp, matched_group 6 inp) with
     | (c, r, "GET", k, _, _) -> Some (int_of_string c, int_of_string r, Get (char_list_of_string k))
     | (c, r, "DEL", k, _, _) -> Some (int_of_string c, int_of_string r, Del (char_list_of_string k))
     | (c, r, "PUT", k, v, _) -> Some (int_of_string c, int_of_string r, Put ((char_list_of_string k), (char_list_of_string v)))
     | (c, r, "CAD", k, o, _) -> Some (int_of_string c, int_of_string r, CAD (char_list_of_string k, char_list_of_string o))
     | (c, r, "CAS", k, "-", v) -> Some (int_of_string c, int_of_string r, CAS ((char_list_of_string k), None, (char_list_of_string v)))
     | (c, r, "CAS", k, o, v) -> Some (int_of_string c, int_of_string r, CAS ((char_list_of_string k), Some (char_list_of_string o), (char_list_of_string v)))
     | _ -> None)
  else
    (print_endline "No match" ; None)

let deserializeMsg (b : bytes) : VarDRaftDebug.msg = Marshal.from_bytes b 0

let serializeMsg (msg : VarDRaftDebug.msg) : bytes = Marshal.to_bytes msg []
