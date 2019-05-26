open Str
open Printf
open VarDRaftDebug
open VarD
open Util
open Yojson.Basic

module type IntValue = sig
  val v : int
end

module type VarDDebugParams = sig
  val debug : bool
  val heartbeat_timeout : float
  val election_timeout : float
  val num_nodes : int
end

module DebugParams =
  functor (I : IntValue) ->
struct
  let debug = true
  let heartbeat_timeout = 2.0
  let election_timeout = 10.0
  let num_nodes = I.v
end

module VarDDebugArrangement (P : VarDDebugParams) = struct
  type name = VarDRaftDebug.name
  type state = raft_data0
  type input = VarDRaftDebug.raft_input
  type output = VarDRaftDebug.raft_output
  type msg = VarDRaftDebug.msg
  type res = (VarDRaftDebug.raft_output list * raft_data0) * ((VarDRaftDebug.name * VarDRaftDebug.msg) list)
  type client_id = string
  let system_name = "VarD"
  let init = Obj.magic ((vard_raft_multi_params P.num_nodes).init_handlers)
  let reboot = Obj.magic (vard_raft_failure_params P.num_nodes)
  let handle_input (n : name) (inp : input) (st : state) = Obj.magic ((vard_raft_multi_params P.num_nodes).input_handlers (Obj.magic n) (Obj.magic inp) (Obj.magic st))
  let handle_msg (n : name) (src: name) (m : msg) (st : state)  = Obj.magic ((vard_raft_multi_params P.num_nodes).net_handlers (Obj.magic n) (Obj.magic src) (Obj.magic m) (Obj.magic st))
  let handle_timeout (me : name) (st : state) =
    (Obj.magic (vard_raft_multi_params P.num_nodes).input_handlers (Obj.magic me) (Obj.magic Timeout) (Obj.magic st))
  let set_timeout _ s =
    match s.type0 with
    | Leader -> P.heartbeat_timeout
    | _ -> P.election_timeout +. (Random.float 0.1)
  let deserialize_msg = VarDDebugSerialization.deserializeMsg
  let serialize_msg = VarDDebugSerialization.serializeMsg
  let deserialize_input = fun x ->
    match VarDDebugSerialization.deserializeInp x with
    | None -> None
    | Some (client_id, request_id, input) ->
       Some (ClientRequest (Obj.magic (char_list_of_string "1"), request_id, Obj.magic input))
  let commands =
    ["1 1 PUT foo bar -"]
  let debug = P.debug
  let debug_recv s (other, m) =
    (match m with
     | AppendEntries (t, leaderId, prevLogIndex, prevLogTerm, entries, commitIndex) ->
        printf "[Term %d] Received %d entries from %d (currently have %d entries)\n"
               s.currentTerm (List.length entries) other (List.length s.log)
     | AppendEntriesReply (_, entries, success) ->
        printf "[Term %d] Received AppendEntriesReply %d entries %B, commitIndex %d\n"
               s.currentTerm (List.length entries) success s.commitIndex
     | RequestVoteReply (t, votingFor) ->
        printf "[Term %d] Received RequestVoteReply(%d, %B) from %d, have %d votes\n"
               s.currentTerm t votingFor other (List.length s.votesReceived)
     | _ -> ()); flush_all ()
  let debug_send s (other, m) =
    (match m with
     | AppendEntries (t, leaderId, prevLogIndex, prevLogTerm, entries, commitIndex) ->
        printf "[Term %d] Sending %d entries to %d (currently have %d entries), commitIndex=%d\n"
               s.currentTerm (List.length entries) other (List.length s.log) commitIndex
     | RequestVote _ ->
        printf "[Term %d] Sending RequestVote to %d, have %d votes\n"
               s.currentTerm other (List.length s.votesReceived)
     | _ -> ()); flush_all ()
  let debug_timeout (s : state) = ()
  let debug_input s inp = ()
  let string_of_name = string_of_int
  let name_of_string = int_of_string
  let type_of_msg (m : msg) =
    match m with
    | AppendEntries _ -> "AppendEntries"
    | AppendEntriesReply _ -> "AppendEntriesReply"
    | RequestVote _ -> "RequestVote"
    | RequestVoteReply _ -> "RequestVoteReply"
  let json_of_input i =
    match i with
    | Put(k, v) ->
       `String (Printf.sprintf "PUT %s %s" (string_of_char_list k) (string_of_char_list v))
    | _ -> `String ""
  let json_of_entry e =
    `Assoc [("term", `Int e.eTerm); ("index", `Int e.eIndex); ("input", json_of_input (Obj.magic e.eInput))]
  let json_of_log es =
    `List (List.map json_of_entry es)
  let json_of_msg (m : msg) =
    match m with
    | AppendEntries (t, leaderId, prevLogIndex, prevLogTerm, entries, commitIndex) ->
       `Assoc [("term", `Int t)
             ; ("leaderId", `Int leaderId)
             ; ("prevLogIndex", `Int prevLogIndex)
             ; ("prevLogTerm", `Int prevLogTerm)
             ; ("entries", json_of_log entries)
             ; ("commitIndex", `Int commitIndex)]
    | AppendEntriesReply (t, entries, ok) ->
       `Assoc [("term", `Int t)
             ; ("entries", json_of_log entries)
             ; ("ok", `Bool ok)]
    | RequestVote (t, l, li, lt) ->
       `Assoc [("term", `Int t)
             ; ("leaderId", `Int l)
             ; ("maxLogIndex", `Int li)
             ; ("maxLogTerm", `Int lt)]
    | RequestVoteReply (t, ok) ->
       `Assoc [("term", `Int t)
             ; ("ok", `Bool ok)]
  (* `Assoc (List.map (fun (x, y) -> (string_of_char_list x, `String (string_of_char_list y))) b)*)
  let json_of_state (s : state) = `Assoc [("term", `Int s.currentTerm)
                                        ; ("votedFor", match s.votedFor with
                                                       | None -> `Null
                                                       | Some(x) -> `Int x)
                                        ; ("type", `String (match s.type0 with
                                                            | Leader -> "Leader"
                                                            | Candidate -> "Candidate"
                                                            | Follower -> "Follower"))
                                        ; ("log", json_of_log s.log)
                                        ; ("commitIndex", `Int s.commitIndex)]
end
