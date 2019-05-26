Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Ensembles.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.StreamFunctions.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.HoareLogic.ProgramState.

Definition trace (state: Type): Type := stream (state * MetaState state).

Identity Coercion trace_stream: trace >-> stream.

Definition singleton_trace {state: Type} s ms: trace state :=
  fin_stream ((s, ms) :: nil).

Lemma singleton_trace_n_stream {state: Type}: forall (s: state) ms,
  is_n_stream 1 (singleton_trace s ms).
Proof.
  intros.
  apply fin_stream_n_stream; auto.
Qed.

Definition sequential_trace {state: Type} (tr: trace state) : Prop :=
  forall k s ms s' ms',
    tr k = Some (s, ms) ->
    tr (S k) = Some (s' , ms') ->
    ms = Terminating s'.

Definition sound_trace {state: Type} (R: state -> MetaState state -> Prop) (tr: trace state) : Prop :=
  forall k s ms,
    tr k = Some (s, ms) ->
    R s ms.

Lemma sound_trace_and {state: Type}: forall R1 R2 (tr: trace state),
  sound_trace (fun s ms => R1 s ms /\ R2 s ms) tr <->
  sound_trace R1 tr /\ sound_trace R2 tr.
Proof.
  intros.
  split; intros.
  + split; hnf; intros k H0 m ms;
    specialize (H k H0 m ms); destruct H; auto.
  + destruct H.
    hnf; intros k H1 m ms;
    specialize (H k H1 m ms);
    specialize (H0 k H1 m ms); auto.
Qed.

Lemma trace_app_sequential1 {state: Type}: forall (tr1 tr2: trace state),
  sequential_trace (stream_app tr1 tr2) ->
  sequential_trace tr1.
Proof.
  intros.
  hnf; intros.
  specialize (H k s ms s' ms').
  erewrite stream_app_spec1' in H by eauto.
  erewrite stream_app_spec1' in H by eauto.
  apply H; auto.
Qed.

Lemma trace_app_sequential2 {state: Type}: forall (tr1 tr2: trace state),
  is_fin_stream tr1 ->
  sequential_trace (stream_app tr1 tr2) ->
  sequential_trace tr2.
Proof.
  intros.
  hnf; intros.
  rewrite is_fin_stream_spec in H.
  destruct H as [n ?].
  specialize (H0 (k + n) s ms s' ms').
  change (S (k + n)) with (S k + n) in H0.
  erewrite stream_app_spec2 in H0 by eauto.
  erewrite stream_app_spec2 in H0 by eauto.
  apply H0; auto.
Qed.

Lemma trace_app_sound1 {state: Type}: forall R (tr1 tr2: trace state),
  sound_trace R (stream_app tr1 tr2) ->
  sound_trace R tr1.
Proof.
  intros.
  hnf; intros.
  specialize (H k s ms).
  erewrite stream_app_spec1' in H by eauto.
  apply H; auto.
Qed.

Lemma trace_app_sound2 {state: Type}: forall R (tr1 tr2: trace state),
  is_fin_stream tr1 ->
  sound_trace R (stream_app tr1 tr2) ->
  sound_trace R tr2.
Proof.
  intros.
  hnf; intros.
  rewrite is_fin_stream_spec in H.
  destruct H as [n ?].
  specialize (H0 (k + n) s ms).
  erewrite stream_app_spec2 in H0 by eauto.
  apply H0; auto.
Qed.

Inductive begin_end_state {state: Type}: state -> trace state -> MetaState state -> Prop :=
| begin_end_empty: forall s, begin_end_state s empty_stream (Terminating s)
| begin_end_fin: forall s ms s' ms' tr n,
    is_n_stream (S n) tr ->
    tr 0 = Some (s, ms) ->
    tr n = Some (s', ms') ->
    begin_end_state s tr ms'
| begin_end_inf: forall s ms tr,
    is_inf_stream tr ->
    tr 0 = Some (s, ms) ->
    begin_end_state s tr NonTerminating.

Definition begin_state {state: Type} (tr: trace state) (s: state): Prop :=
  exists ms, begin_end_state s tr ms.

Definition end_state {state: Type} (tr: trace state) (ms: MetaState state): Prop :=
  exists s, begin_end_state s tr ms.

Definition ctrace2trace
           {cmd: Type}
           {state: Type}: trace (cmd * state) -> trace state := 
  stream_map (fun p => match p with ((c, s), mcs) => (s, lift_function snd mcs) end).

Lemma begin_end_state_ctrace: forall {cmd state: Type} (ctr: trace (cmd * state)) cs mcs,
  begin_end_state cs ctr mcs ->
  begin_end_state (snd cs) (ctrace2trace ctr) (lift_function snd mcs).
Proof.
  intros.
  destruct H.
  + destruct s; simpl.
    unfold ctrace2trace; rewrite stream_map_empty_stream.
    apply begin_end_empty; auto.
  + eapply begin_end_fin.
    - apply stream_map_n_stream; eassumption.
    - unfold ctrace2trace; rewrite stream_map_spec.
      rewrite H0. destruct s; reflexivity.
    - unfold ctrace2trace; rewrite stream_map_spec.
      rewrite H1. instantiate (1 := snd s'); destruct s'; reflexivity.
  + eapply begin_end_inf.
    - apply stream_map_inf_stream; eassumption.
    - unfold ctrace2trace; rewrite stream_map_spec.
      rewrite H0. destruct s; reflexivity.
Qed.

Lemma begin_end_state_singleton_trace: forall {state: Type} (s: state) ms,
  begin_end_state s (singleton_trace s ms) ms.
Proof.
  intros.
  apply (begin_end_fin s ms s ms _ 0).
  + apply singleton_trace_n_stream.
  + reflexivity.
  + reflexivity.
Qed.

Lemma begin_end_state_singleton_trace_rev: forall {state: Type} (s s': state) ms ms',
  begin_end_state s' (singleton_trace s ms) ms' ->
  s = s' /\ ms = ms'.
Proof.
  intros.
  inversion H; subst.
  + exfalso.
    match goal with
    | HH: ?A = ?B |- _ => remember A as A0; remember B as B0;
                          assert (A0 0 = B0 0) by (rewrite HH; auto); subst
    end.
    simpl in H0; inversion H0.
  + pose proof singleton_trace_n_stream s ms.
    pose proof is_n_stream_pf _ _ _ H0 H3.
    inversion H4; subst; clear H4.
    inversion H1; inversion H2; subst; auto.
  + pose proof singleton_trace_n_stream s ms.
    pose proof n_stream_inf_stream_conflict _ _ H2 H0.
    tauto.
Qed.

Definition traces (state: Type): Type := Ensemble (trace state).

Definition traces_app {state: Type} (d1 d2: traces state): traces state :=
  fun tr =>
    (exists tr1 tr2, d1 tr1 /\ d2 tr2 /\ tr = stream_app tr1 tr2) \/
  (exists tr1, d1 tr1 /\ (end_state tr1 NonTerminating \/ end_state tr1 Error) /\ tr = tr1).

Fixpoint traces_power {state: Type} (d: traces state) (n: nat): traces state :=
  match n with
  | 0 => is_empty_stream
  | S n => traces_app (traces_power d n) d
  end.

Definition traces_pstar {state: Type} (d: traces state): traces state :=
  fun tr => exists n, traces_power d n tr.

Definition traces_pomega {state: Type} (d: traces state): traces state :=
  fun tr => exists f, tr = stream_capp f /\ forall n, d (f n).

Lemma traces_app_mono {state: Type}: forall (d1 d2 d3 d4: traces state),
  Included _ d1 d3 ->
  Included _ d2 d4 ->
  Included _ (traces_app d1 d2) (traces_app d3 d4).
Proof.
  intros.
  unfold Included, Ensembles.In in *; intros tr ?.
  destruct H1.
  + destruct H1 as [tr1 [tr2 [? [? ?]]]].
    left; exists tr1, tr2; auto.
  + destruct H1 as [tr1 [? [? ?]]].
    right; exists tr1; auto.
Qed.

Lemma traces_power_mono {state: Type}: forall (d1 d2: traces state) (n: nat),
  Included _ d1 d2 ->
  Included _ (traces_power d1 n) (traces_power d2 n).
Proof.
  intros.
  induction n.
  + hnf; intros; auto.
  + simpl.
    apply traces_app_mono; auto.
Qed.

Lemma traces_pstar_mono {state: Type}: forall (d1 d2: traces state),
  Included _ d1 d2 ->
  Included _ (traces_pstar d1) (traces_pstar d2).
Proof.
  intros.
  unfold Included, Ensembles.In; intros tr ?.
  destruct H0 as [n ?].
  exists n.
  revert tr H0.
  apply traces_power_mono; auto.
Qed.

Lemma traces_pomega_mono {state: Type}: forall (d1 d2: traces state),
  Included _ d1 d2 ->
  Included _ (traces_pomega d1) (traces_pomega d2).
Proof.
  intros.
  unfold Included, Ensembles.In; intros tr ?.
  destruct H0 as [f [? ?]].
  exists f; split; auto.
  intros; apply H, H1.
Qed.

Module Type FORWARD_TRACE.

Declare Module F: FORWARD.

Parameter forward_trace: forall {state: Type} {state_R: Relation state}, traces state.

Parameter forward_trace_with_test: forall {state: Type} {state_R: Relation state} (P: state -> Prop), traces state.

Axiom singleton_trace_forward: forall {state: Type} {state_R: Relation state} s ms,
  F.forward (Terminating s) ms ->
  forward_trace (singleton_trace s ms).

Axiom singleton_trace_forward_test: forall {state: Type} {state_R: Relation state} (P: _ -> Prop) s ms,
  F.forward (Terminating s) ms ->
  P s ->
  forward_trace_with_test P (singleton_trace s ms).

End FORWARD_TRACE.

Module ForwardTrace (F: FORWARD) <: FORWARD_TRACE with Module F := F.

Module F := F.
Export F.

Definition forward_trace {state: Type} {state_R: Relation state}: traces state :=
  fun tr => is_fin_stream tr /\ forall n s ms, tr n = Some (s, ms) -> forward (Terminating s) ms.

Definition forward_trace_with_test {state: Type} {state_R: Relation state} (P: state -> Prop) : traces state :=
  fun tr => forward_trace tr /\ exists s, begin_state tr s /\ P s.

Lemma singleton_trace_forward {state: Type} {state_R: Relation state}: forall s ms,
  F.forward (Terminating s) ms ->
  forward_trace (singleton_trace s ms).
Proof.
  intros.
  split; [apply fin_stream_fin |].
  intros.
  simpl in H0.
  destruct n.
  + simpl in H0.
    inversion H0; subst; auto.
  + destruct n; inversion H0.
Qed.

Lemma singleton_trace_forward_test {state: Type} {state_R: Relation state}: forall (P: _ -> Prop) s ms,
  F.forward (Terminating s) ms ->
  P s ->
  forward_trace_with_test P (singleton_trace s ms).
Proof.
  intros.
  split; [apply singleton_trace_forward; auto |].
  exists s; split; auto.
  exists ms.
  apply begin_end_state_singleton_trace.
Qed.

End ForwardTrace.

Module Partial := ForwardTrace (ProgramState.Partial).
Module Total := ForwardTrace (ProgramState.Total).

Lemma Total2Partial_forward_trace
      {state: Type}
      {state_R: Relation state}:
  Included _ Total.forward_trace Partial.forward_trace.
Proof.
  unfold Included, Ensembles.In; intros tr ?.
  destruct H as [? ?].
  split; auto.
  intros.
  apply Total2Partial_forward, (H0 n); auto.
Qed.

Lemma Total2Partial_forward_trace_with_test
      {state: Type}
      {state_R: Relation state}
      (P: state -> Prop):
  Included _
   (Total.forward_trace_with_test P)
   (Partial.forward_trace_with_test P).
Proof.
  unfold Included, Ensembles.In; intros tr ?.
  destruct H as [? ?].
  split; auto.
  apply Total2Partial_forward_trace; auto.
Qed.
