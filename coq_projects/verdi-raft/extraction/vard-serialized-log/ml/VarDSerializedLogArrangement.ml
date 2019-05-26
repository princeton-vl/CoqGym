open Str
open Printf
open VarDRaftSerializedLog
open VarD
open Util

module type IntValue = sig
  val v : int
end
  
module type VarDParams = sig
  val debug : bool
  val heartbeat_timeout : float
  val election_timeout : float
  val num_nodes : int
  val snapshot_interval : int
end

module DebugParams =
  functor (I : IntValue) ->
struct
  let debug = true
  let heartbeat_timeout = 2.0
  let election_timeout = 10.0
  let num_nodes = I.v
  let snapshot_interval = 100
end

module BenchParams =
  functor (I : IntValue) ->
struct
  let debug = false
  let heartbeat_timeout = 0.05
  let election_timeout = 0.5
  let num_nodes = I.v
  let snapshot_interval = 1000
end

module VarDArrangement (P : VarDParams) = struct
  type name = VarDRaftSerializedLog.name0
  type file_name = VarDRaftSerializedLog.log_files
  type state = VarDRaftSerializedLog.log_state
  type input = VarDRaftSerializedLog.raft_input
  type output = VarDRaftSerializedLog.raft_output
  type msg = Serializer_primitives.wire
  type client_id = string
  type res = ((file_name DiskOpShim.disk_op list * output list) * state) * ((name * msg) list)
  type disk = log_files -> in_channel option
  let system_name = "VarDSerializedLog"
  let reboot = Obj.magic (transformed_failure_params0 P.num_nodes P.snapshot_interval)
  let handle_input (n : name) (inp : input) (st : state) = Obj.magic ((transformed_multi_params0 P.num_nodes P.snapshot_interval).do_input_handlers (Obj.magic n) (Obj.magic inp) (Obj.magic st))
  let handle_msg (n : name) (src: name) (m : msg) (st : state)  = Obj.magic ((transformed_multi_params0 P.num_nodes P.snapshot_interval).do_net_handlers (Obj.magic n) (Obj.magic src) (Obj.magic m) (Obj.magic st))
  let handle_timeout (me : name) (st : state) =
    (Obj.magic (transformed_multi_params0 P.num_nodes P.snapshot_interval).do_input_handlers (Obj.magic me) (Obj.magic Timeout) (Obj.magic st))
  let set_timeout _ s =
    match (Obj.magic s.log_data).type0 with
    | Leader -> P.heartbeat_timeout
    | _ -> P.election_timeout +. (Random.float 0.1)
  let deserialize_msg = fun a -> a
  let serialize_msg = fun a -> a
  let deserialize_input = VarDSerializedLogSerialization.deserializeInput
  let serialize_output = VarDSerializedLogSerialization.serializeOutput
  let debug = P.debug
  let debug_recv (s : state) (other, m) =
    (match Serializer_primitives.deserialize_top (msg_Serializer P.num_nodes).deserialize m with
     | Some (AppendEntries (t, leaderId, prevLogIndex, prevLogTerm, entries, commitIndex)) ->
        printf "[Term %d] Received %d entries from %d (currently have %d entries)\n"
          (Obj.magic s.log_data).currentTerm (List.length entries) other (List.length (Obj.magic s.log_data).log)
     | Some (AppendEntriesReply (_, entries, success)) ->
      printf "[Term %d] Received AppendEntriesReply %d entries %B, commitIndex %d\n"
        (Obj.magic s.log_data).currentTerm (List.length entries) success (Obj.magic s.log_data).commitIndex
     | Some (RequestVoteReply (t, votingFor)) ->
        printf "[Term %d] Received RequestVoteReply(%d, %B) from %d, have %d votes\n"
        (Obj.magic s.log_data).currentTerm t votingFor other (List.length (Obj.magic s.log_data).votesReceived)
     | Some _ -> ()
     | None -> printf "[Term %d] Received UNDESERIALIZABLE message from %d\n" (Obj.magic s.log_data).currentTerm other);
    flush_all ()
  let debug_send s (other, m) =
    (match Serializer_primitives.deserialize_top (msg_Serializer P.num_nodes).deserialize m with
    | Some (AppendEntries (t, leaderId, prevLogIndex, prevLogTerm, entries, commitIndex)) ->
       printf "[Term %d] Sending %d entries to %d (currently have %d entries), commitIndex=%d\n"
         (Obj.magic s.log_data).currentTerm (List.length entries) other (List.length (Obj.magic s.log_data).log) commitIndex
    | Some (RequestVote _) ->
       printf "[Term %d] Sending RequestVote to %d, have %d votes\n"
         (Obj.magic s.log_data).currentTerm other (List.length (Obj.magic s.log_data).votesReceived)
    | Some _ -> ()
    | None -> printf "[Term %d] Sending UNDESERIALIZABLE message to %d\n" (Obj.magic s.log_data).currentTerm other);
    flush_all ()
  let debug_timeout (s : state) = ()
  let debug_input s inp = ()
  let deserialize_client_id = VarDSerializedLogSerialization.deserializeClientId
  let string_of_client_id s = s
  let string_of_file_name = fun f -> match f with
                                     | Count -> "count"
                                     | Snapshot -> "snapshot"
                                     | Log -> "log"
  let files = [Count; Snapshot; Log]
end
