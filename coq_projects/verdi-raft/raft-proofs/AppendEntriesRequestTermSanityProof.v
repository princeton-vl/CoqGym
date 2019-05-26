Require Import Verdi.GhostSimulations.

Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.

Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.AppendEntriesRequestTermSanityInterface.

Section AppendEntriesRequestTermSanity.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {si : sorted_interface}.

  Theorem lift_sorted :
    forall net,
      refined_raft_intermediate_reachable net ->
      logs_sorted (deghost net).
  Proof using si rri. 
    intros.
    eapply lift_prop; eauto using logs_sorted_invariant.
  Qed.

  Lemma ghost_packet :
    forall (net : network (params := raft_refined_multi_params)) p,
      In p (nwPackets net) ->
      In (deghost_packet p) (nwPackets (deghost net)).
  Proof using. 
    unfold deghost.
    simpl. intuition.
    apply in_map_iff.
    eexists; eauto.
  Qed.

  Lemma logs_sorted_aerts :
    forall net,
      logs_sorted (deghost net) ->
      append_entries_request_term_sanity net.
  Proof using. 
    unfold logs_sorted, append_entries_request_term_sanity. intuition.
    unfold packets_ge_prevTerm in *. find_apply_lem_hyp ghost_packet.
    eauto.
  Qed.

  Instance aertsi : append_entries_request_term_sanity_interface.
  Proof.
    split. intros. find_apply_lem_hyp lift_sorted.
    eauto using logs_sorted_aerts.
  Qed.
End AppendEntriesRequestTermSanity.
