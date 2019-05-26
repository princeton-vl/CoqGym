open Str
open Printf
open VarDRaft
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
end

module DebugParams =
  functor (I : IntValue) ->
struct
  let debug = true
  let heartbeat_timeout = 2.0
  let election_timeout = 10.0
  let num_nodes = I.v
end

module BenchParams =
  functor (I : IntValue) ->
struct
  let debug = false
  let heartbeat_timeout = 0.05
  let election_timeout = 0.5
  let num_nodes = I.v
end

module VarDArrangement (P : VarDParams) = struct
  type name = VarDRaft.name
  type state = raft_data0
  type input = VarDRaft.raft_input
  type output = VarDRaft.raft_output
  type msg = VarDRaft.msg
  type res = (VarDRaft.raft_output list * raft_data0) * ((VarDRaft.name * VarDRaft.msg) list)
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
  let deserialize_msg = VarDSerialization.deserializeMsg
  let serialize_msg = VarDSerialization.serializeMsg
  let deserialize_input = VarDSerialization.deserializeInput
  let serialize_output = VarDSerialization.serializeOutput
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
  let deserialize_client_id = VarDSerialization.deserializeClientId
  let string_of_client_id s = s
end
