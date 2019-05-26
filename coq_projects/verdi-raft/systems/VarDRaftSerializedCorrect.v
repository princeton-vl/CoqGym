Require Import Verdi.Verdi.
Require Import Verdi.VarD.
Require Import Verdi.PartialMapSimulations.
Require Import Cheerios.Cheerios.
Require Import VerdiRaft.Raft.

Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.Linearizability.
Require Import VerdiRaft.RaftLinearizableProofs.

Require Import VerdiRaft.EndToEndLinearizability.
Require Import Verdi.SerializedMsgParamsCorrect.

Require Import VerdiRaft.VarDRaftSerialized.

Section VarDSerializedCorrect.
  Variable n : nat.

  Instance raft_params : RaftParams VarD.vard_base_params :=
    raft_params n.

  Instance base_params : BaseParams :=
    transformed_base_params n.

  Instance multi_params : MultiParams _ :=
    transformed_multi_params n.

  Instance failure_params : FailureParams _ :=
    transformed_failure_params n.

  Lemma correct_input_correct_filterMap_trace_non_empty_out :
    forall tr,
      input_correct tr ->
      input_correct (filterMap trace_non_empty_out tr).
  Proof using.
    induction tr; simpl; intro H_inp; auto.
    destruct a, s; simpl.
    - assert (H_inp': input_correct tr).
        intros client id i0 i1 h h' H_in H_in'.
        eapply H_inp; right; eauto.
      concludes.
      intros client id i0 i1 h h' H_in H_in'.
      simpl in *.
      break_or_hyp; break_or_hyp.
      * find_injection; find_injection; auto.
      * find_injection.
        eapply H_inp.
        + right.
          find_apply_lem_hyp In_filterMap.
          break_exists_name e.
          break_and.
          destruct e, s; simpl in *; [ find_injection; eauto | destruct l; congruence ].
        + left; eauto.
      * find_injection.
        eapply H_inp.
        + left; eauto.
        + right.
          find_apply_lem_hyp In_filterMap.
          break_exists_name e.
          break_and.
          destruct e, s; simpl in *; [ find_injection; eauto | destruct l; congruence ].
       * eapply IHtr; eauto.
     - destruct l.
       * apply IHtr.
         intros client id i0 i1 h h' H_in H_in'.
         eapply H_inp; right; eauto.
       * assert (H_inp': input_correct tr).
           intros client id i0 i1 h h' H_in H_in'.
           eapply H_inp; right; eauto.
         concludes.
         intros client id i0 i1 h h' H_in H_in'.
         simpl in *.
         break_or_hyp; [ find_inversion | idtac ].
         break_or_hyp; [ find_inversion | idtac ].
         eapply IHtr; eauto.
  Qed.

  Lemma correct_filterMap_trace_non_empty_out_input_correct :
    forall tr,
      input_correct (filterMap trace_non_empty_out tr) ->
      input_correct tr.
  Proof using.
    induction tr; simpl; auto.
    destruct a, s; simpl; intro H_inp.
    - assert (H_inp': input_correct (filterMap trace_non_empty_out tr)).
        intros client id i0 i1 h h' H_in H_in'.
        eapply H_inp; right; eauto.
      concludes.
      intros client id i0 i1 h h' H_in H_in'.
      simpl in *.
      break_or_hyp; break_or_hyp.
      * find_injection; find_injection; auto.
      * find_injection.
        eapply H_inp; [ idtac | left; eauto ].
        right.
        eapply filterMap_In; eauto.
        simpl; eauto.
      * find_injection.
        eapply H_inp; [ left; eauto | idtac ].
        right.
        eapply filterMap_In; eauto.
        simpl; eauto.
      * eapply IHtr; eauto.
    - destruct l.
      * intros client id i0 i1 h h' H_in H_in'.
        simpl in *.
        break_or_hyp; [ find_inversion | idtac ].
        break_or_hyp; [ find_inversion | idtac ].
        eapply IHtr; eauto.
      * assert (H_inp': input_correct (filterMap trace_non_empty_out tr)).
          intros client id i0 i1 h h' H_in H_in'.
          eapply H_inp; right; eauto.
        concludes.
        intros client id i0 i1 h h' H_in H_in'.
        simpl in *.
        break_or_hyp; [ find_inversion | idtac ].
        break_or_hyp; [ find_inversion | idtac ].
        eapply IHtr; eauto.
  Qed.

  Lemma input_correct_filterMap_trace_non_empty_out :
    forall tr tr',
      input_correct tr ->
      filterMap trace_non_empty_out tr = filterMap trace_non_empty_out tr' ->
      input_correct tr'.
  Proof using.
    intros tr tr' H_in H_eq.
    apply correct_filterMap_trace_non_empty_out_input_correct.
    rewrite <- H_eq.
    apply correct_input_correct_filterMap_trace_non_empty_out; auto.
  Qed.

  Lemma get_input_tr_filterMap_trace_non_empty_out :
    forall tr,
      get_input tr = get_input (filterMap trace_non_empty_out tr).
  Proof using.
    induction tr; simpl; auto.
    destruct a, s; simpl.
    - rewrite IHtr; auto.
    - destruct l; auto.
  Qed.

  Lemma get_output_tr_filterMap_trace_non_empty_out :
    forall tr,
      get_output tr = get_output (filterMap trace_non_empty_out tr).
  Proof using.
    induction tr; simpl; auto.
    destruct a, s; simpl.
    - rewrite IHtr; auto.
    - destruct l; auto.
      rewrite IHtr; auto.
  Qed.

  Lemma exported_filterMap_trace_non_empty_out : 
    forall tr tr' l tr1,
      exported (get_input tr') (get_output tr') l tr1 ->
      filterMap trace_non_empty_out tr = filterMap trace_non_empty_out tr' ->
      exported (get_input tr) (get_output tr) l tr1.
  Proof using.
    intros tr tr' l tr1 H_exp H_eq.
    rewrite get_input_tr_filterMap_trace_non_empty_out in H_exp.
    rewrite get_output_tr_filterMap_trace_non_empty_out in H_exp.
    rewrite <- H_eq in H_exp.
    rewrite <- get_input_tr_filterMap_trace_non_empty_out in H_exp.
    rewrite <- get_output_tr_filterMap_trace_non_empty_out in H_exp.
    auto.
  Qed.

  Lemma import_exported_filterMap_trace_non_empty_out : 
    forall tr,
      import tr = import (filterMap trace_non_empty_out tr).
  Proof using.
    induction tr; simpl; auto.
    destruct a, s; simpl.
    - rewrite IHtr; auto.
    - rewrite IHtr.
      destruct l; auto.
  Qed.

  Lemma equivalent_filterMap_trace_non_empty_out :
    forall tr tr' l,
      equivalent key (import tr') l ->
      filterMap trace_non_empty_out tr = filterMap trace_non_empty_out tr' ->
      equivalent key (import tr) l.
  Proof using.
    intros tr tr' l H_equ H_eq.
    rewrite import_exported_filterMap_trace_non_empty_out.
    rewrite H_eq.
    rewrite <- import_exported_filterMap_trace_non_empty_out.
    auto.
  Qed.

  Theorem vard_raft_serialized_linearizable :
    forall failed net tr,
      input_correct tr ->
      step_failure_star step_failure_init (failed, net) tr ->
      exists l tr1 st,
        equivalent _ (import tr) l /\
        exported (get_input tr) (get_output tr) l tr1 /\
        step_1_star init st tr1.
  Proof using.
    intros failed net tr H_inp H_step.
    apply step_failure_deserialized_simulation_star in H_step.
    break_exists_name tr'.
    break_and.
    find_apply_lem_hyp raft_linearizable.
    - break_exists_name l.
      break_exists_name tr1.
      break_exists_name st.
      break_and.
      exists l, tr1, st.
      split.
      * eapply equivalent_filterMap_trace_non_empty_out; eauto.
      * split; auto. eapply exported_filterMap_trace_non_empty_out; eauto.
    - eapply input_correct_filterMap_trace_non_empty_out; eauto.
  Qed.
End VarDSerializedCorrect.
