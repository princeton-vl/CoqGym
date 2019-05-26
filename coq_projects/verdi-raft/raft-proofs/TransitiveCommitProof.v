Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.

Require Import VerdiRaft.LeaderCompletenessInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.

Require Import VerdiRaft.TransitiveCommitInterface.

Section TransitiveCommit.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  
  Context {rlmli : refined_log_matching_lemmas_interface}.

  Theorem transitive_commit_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      transitive_commit net.
  Proof using rlmli. 
    unfold transitive_commit, committed. intros.
    break_exists_name h'; exists h'.
    break_exists_name e''; exists e''.
    intuition; eauto.
    eapply (entries_match_invariant net h h'); eauto.
  Qed.

  Instance tci : transitive_commit_interface.
  Proof.
    split.
    exact transitive_commit_invariant.
  Qed.
End TransitiveCommit.
