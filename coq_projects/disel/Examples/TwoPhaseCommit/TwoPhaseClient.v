From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import State DepMaps Protocols Worlds NetworkSem Rely HoareTriples InferenceRules.
From DiSeL
Require Import While TwoPhaseProtocol TwoPhaseInductiveInv TwoPhaseCoordinator TwoPhaseParticipant.

Section TwoPhaseClient.

(*

This file is a stub that sketches the design of a more interesting
client, where an external node (a member of the "others" crows from
the TPC protocol) communicates with the TPC swarm, retrieving some
information.

For the sake of a cheap-and-cheerful implementation, I suggest not to
add extract permission-based accounting mechanism to the state and
transitions, but rather repurpose a dedicated unconstrained
communication channel already present in the TPC protocol (currently
represented via eval_req and eval_resp tags).

Specifically, we can add the following easy-to support transitions
into the TPC:

- Participant nodes can broadcast the _last_ transaction from the log
  (successfully committed or failed, with a clearly indicated number
  in the common log) by sending the corresponding messages to the
  others. This is the only thing they can do.

- The coordinator is capable of doing the same.

["Proper" client]

- A potential client can then receive a message from the coordinator,
  stating that a specific transaction has been committed or aborted,
  can start two loops waiting for the corresponding (i.e., withrespect
  to the _same_ round) messages coming from the participants. Remember
  that we don't cat about liveness, so these loops migh potentially
  never terminate (which is okay).

- Upon the termination of those two loops, the client should end up
  with two messages from two different participants, and be able to
  formally prove (out of the inductive invariant, to be formally
  defined) that the outcomes and the contents of those two messages
  (since they correpond to the same round as the previously received
  message from the coordinator) are equal to each other and are the
  same as the coordinator's outcome.

- This client should, therefore, demonstrate the causality and the
  coherence between the events in the TPC. Indeed, the coordinator
  gets its log commited last in the round, meaning that the
  participants should already have their logs updated for the same
  round. This is what the inductive invariant should convey.

- In fact, we can first establish the "ground" II about the coherence
  of logs in the system, and then, using another combinator on top of
  it, ensure the required property about the supplementary messages,
  used to poll the results.


[Future Work]

- Ideally, we should have a client that is also pro-active, i.e., be
  able to propose the values to commit and then observe the
  outcomes. However, this will require to either

  a. Supplying a mechanism of permissions, or

  b. Ensuring a stronger invariant about messages in the system.

  Both things are implementable, but intrusive for the protocol, hence
  I suggest to postpone it until we build a reacher set of protocol
  combinators, e.g., to extend the state and add new transitions.

*)

End TwoPhaseClient.
