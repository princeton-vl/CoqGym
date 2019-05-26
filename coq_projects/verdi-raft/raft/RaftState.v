(* Remember to re-run
     python2 script/extract_record_notation.py raft/RaftState.v.rec raft_data > raft/RaftState.v
   after editing this file!
   Running `make raft/RaftState.v` should take care of this for you. *)
Section RaftState.
  Variable term : Type.
  Variable name : Type.
  Variable entry : Type.
  Variable logIndex : Type.
  Variable serverType : Type.
  Variable stateMachineData : Type.
  Variable clientId : Type.
  Variable output : Type.

  Record raft_data :=
    mkRaft_data {
        (* persistent *)
        currentTerm : term;
        votedFor : option name;
        leaderId : option name;
        log : list entry;
        (* volatile *)
        commitIndex : logIndex;
        lastApplied : logIndex;
        stateMachine : stateMachineData;
        (* leader state *)
        nextIndex : list (name * logIndex);
        matchIndex : list (name * logIndex);
        shouldSend : bool;
        (* candidate state *)
        votesReceived : list name;
        (* whoami *)
        type : serverType;
        (* client request state *)
        clientCache : list (clientId * (nat * output));
        (* ghost variables *)
        electoralVictories : list (term * list name * list entry)
      }.


Definition set_raft_data_currentTerm a v := mkRaft_data v (votedFor a) (leaderId a) (log a) (commitIndex a) (lastApplied a) (stateMachine a) (nextIndex a) (matchIndex a) (shouldSend a) (votesReceived a) (type a) (clientCache a) (electoralVictories a).

Definition set_raft_data_votedFor a v := mkRaft_data (currentTerm a) v (leaderId a) (log a) (commitIndex a) (lastApplied a) (stateMachine a) (nextIndex a) (matchIndex a) (shouldSend a) (votesReceived a) (type a) (clientCache a) (electoralVictories a).

Definition set_raft_data_leaderId a v := mkRaft_data (currentTerm a) (votedFor a) v (log a) (commitIndex a) (lastApplied a) (stateMachine a) (nextIndex a) (matchIndex a) (shouldSend a) (votesReceived a) (type a) (clientCache a) (electoralVictories a).

Definition set_raft_data_log a v := mkRaft_data (currentTerm a) (votedFor a) (leaderId a) v (commitIndex a) (lastApplied a) (stateMachine a) (nextIndex a) (matchIndex a) (shouldSend a) (votesReceived a) (type a) (clientCache a) (electoralVictories a).

Definition set_raft_data_commitIndex a v := mkRaft_data (currentTerm a) (votedFor a) (leaderId a) (log a) v (lastApplied a) (stateMachine a) (nextIndex a) (matchIndex a) (shouldSend a) (votesReceived a) (type a) (clientCache a) (electoralVictories a).

Definition set_raft_data_lastApplied a v := mkRaft_data (currentTerm a) (votedFor a) (leaderId a) (log a) (commitIndex a) v (stateMachine a) (nextIndex a) (matchIndex a) (shouldSend a) (votesReceived a) (type a) (clientCache a) (electoralVictories a).

Definition set_raft_data_stateMachine a v := mkRaft_data (currentTerm a) (votedFor a) (leaderId a) (log a) (commitIndex a) (lastApplied a) v (nextIndex a) (matchIndex a) (shouldSend a) (votesReceived a) (type a) (clientCache a) (electoralVictories a).

Definition set_raft_data_nextIndex a v := mkRaft_data (currentTerm a) (votedFor a) (leaderId a) (log a) (commitIndex a) (lastApplied a) (stateMachine a) v (matchIndex a) (shouldSend a) (votesReceived a) (type a) (clientCache a) (electoralVictories a).

Definition set_raft_data_matchIndex a v := mkRaft_data (currentTerm a) (votedFor a) (leaderId a) (log a) (commitIndex a) (lastApplied a) (stateMachine a) (nextIndex a) v (shouldSend a) (votesReceived a) (type a) (clientCache a) (electoralVictories a).

Definition set_raft_data_shouldSend a v := mkRaft_data (currentTerm a) (votedFor a) (leaderId a) (log a) (commitIndex a) (lastApplied a) (stateMachine a) (nextIndex a) (matchIndex a) v (votesReceived a) (type a) (clientCache a) (electoralVictories a).

Definition set_raft_data_votesReceived a v := mkRaft_data (currentTerm a) (votedFor a) (leaderId a) (log a) (commitIndex a) (lastApplied a) (stateMachine a) (nextIndex a) (matchIndex a) (shouldSend a) v (type a) (clientCache a) (electoralVictories a).

Definition set_raft_data_type a v := mkRaft_data (currentTerm a) (votedFor a) (leaderId a) (log a) (commitIndex a) (lastApplied a) (stateMachine a) (nextIndex a) (matchIndex a) (shouldSend a) (votesReceived a) v (clientCache a) (electoralVictories a).

Definition set_raft_data_clientCache a v := mkRaft_data (currentTerm a) (votedFor a) (leaderId a) (log a) (commitIndex a) (lastApplied a) (stateMachine a) (nextIndex a) (matchIndex a) (shouldSend a) (votesReceived a) (type a) v (electoralVictories a).

Definition set_raft_data_electoralVictories a v := mkRaft_data (currentTerm a) (votedFor a) (leaderId a) (log a) (commitIndex a) (lastApplied a) (stateMachine a) (nextIndex a) (matchIndex a) (shouldSend a) (votesReceived a) (type a) (clientCache a) v.

End RaftState.



Notation "{[ a 'with' 'currentTerm' := v ]}" := (set_raft_data_currentTerm  _ _ _ _ _ _ _ _ a v).

Notation "{[ a 'with' 'votedFor' := v ]}" := (set_raft_data_votedFor  _ _ _ _ _ _ _ _ a v).

Notation "{[ a 'with' 'leaderId' := v ]}" := (set_raft_data_leaderId  _ _ _ _ _ _ _ _ a v).

Notation "{[ a 'with' 'log' := v ]}" := (set_raft_data_log  _ _ _ _ _ _ _ _ a v).

Notation "{[ a 'with' 'commitIndex' := v ]}" := (set_raft_data_commitIndex  _ _ _ _ _ _ _ _ a v).

Notation "{[ a 'with' 'lastApplied' := v ]}" := (set_raft_data_lastApplied  _ _ _ _ _ _ _ _ a v).

Notation "{[ a 'with' 'stateMachine' := v ]}" := (set_raft_data_stateMachine  _ _ _ _ _ _ _ _ a v).

Notation "{[ a 'with' 'nextIndex' := v ]}" := (set_raft_data_nextIndex  _ _ _ _ _ _ _ _ a v).

Notation "{[ a 'with' 'matchIndex' := v ]}" := (set_raft_data_matchIndex  _ _ _ _ _ _ _ _ a v).

Notation "{[ a 'with' 'shouldSend' := v ]}" := (set_raft_data_shouldSend  _ _ _ _ _ _ _ _ a v).

Notation "{[ a 'with' 'votesReceived' := v ]}" := (set_raft_data_votesReceived  _ _ _ _ _ _ _ _ a v).

Notation "{[ a 'with' 'type' := v ]}" := (set_raft_data_type  _ _ _ _ _ _ _ _ a v).

Notation "{[ a 'with' 'clientCache' := v ]}" := (set_raft_data_clientCache  _ _ _ _ _ _ _ _ a v).

Notation "{[ a 'with' 'electoralVictories' := v ]}" := (set_raft_data_electoralVictories  _ _ _ _ _ _ _ _ a v).


Arguments set_raft_data_currentTerm  _ _ _ _ _ _ _ _ _ _/.

Arguments set_raft_data_votedFor  _ _ _ _ _ _ _ _ _ _/.

Arguments set_raft_data_leaderId  _ _ _ _ _ _ _ _ _ _/.

Arguments set_raft_data_log  _ _ _ _ _ _ _ _ _ _/.

Arguments set_raft_data_commitIndex  _ _ _ _ _ _ _ _ _ _/.

Arguments set_raft_data_lastApplied  _ _ _ _ _ _ _ _ _ _/.

Arguments set_raft_data_stateMachine  _ _ _ _ _ _ _ _ _ _/.

Arguments set_raft_data_nextIndex  _ _ _ _ _ _ _ _ _ _/.

Arguments set_raft_data_matchIndex  _ _ _ _ _ _ _ _ _ _/.

Arguments set_raft_data_shouldSend  _ _ _ _ _ _ _ _ _ _/.

Arguments set_raft_data_votesReceived  _ _ _ _ _ _ _ _ _ _/.

Arguments set_raft_data_type  _ _ _ _ _ _ _ _ _ _/.

Arguments set_raft_data_clientCache  _ _ _ _ _ _ _ _ _ _/.

Arguments set_raft_data_electoralVictories  _ _ _ _ _ _ _ _ _ _/.
