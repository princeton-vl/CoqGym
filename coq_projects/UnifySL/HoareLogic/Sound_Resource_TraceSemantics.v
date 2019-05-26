Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAExamples.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.
Require Import Logic.HoareLogic.TraceSemantics.
Require Import Logic.HoareLogic.HoareTriple_BigStepSemantics.
Require Import Logic.HoareLogic.GuardedHoareTriple_TraceSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.

Lemma start_by_Aacq_or_Arel {Ac: Action} {Res: Resource} {Acr: Action_resource Ac Res} {nAcr: NormalAction_resource Ac Res}: forall r tr, start_by_Aacq r tr -> start_by_Arel r tr -> False.
Proof.
  intros.
  induction tr.
  + inversion H0.
  + destruct (classic (is_resource_action r a)) as [[? | ?] | ?]; subst.
    - inversion H0; subst; solve_resource_action.
    - inversion H; subst; solve_resource_action.
    - inversion H; subst; solve_resource_action.
      inversion H0; subst; solve_resource_action.
      auto.
Qed.

Lemma start_by_Aacq_trace_acc_spec {state: Type} {Ac: Action} {Res: Resource} {J: Join state} {state_R: Relation state} {Acr: Action_resource Ac Res} {nAcr: NormalAction_resource Ac Res} {ac_sem: ActionInterpret (resources * state) Ac} {AIr: ActionInterpret_resource state Ac Res ac_sem}: forall (Inv: resource * (state -> Prop) -> Prop) (tr: trace) A1 A2 s1 s2,
  (forall r, start_by_Aacq r tr) ->
  @trace_access _ _ (ThreadLocal_ActionInterpret_resource _ Inv) tr (A1, s1) (Terminating (A2, s2)) ->
  A1 = A2.
Proof.
  intros.
  assert (join A2 (fun r => start_by_Arel r tr) A1).
  Focus 2. {
    extensionality r; apply prop_ext.
    specialize (H r); specialize (H1 r).
    pose proof start_by_Aacq_or_Arel r tr.
    destruct H1; tauto.
  } Unfocus.
  assert (forall r, start_by_Aacq r tr \/ start_by_Arel r tr).
  Focus 1. {
    intros r.
    specialize (H r).
    auto.
  } Unfocus.
  clear H.
  revert s1 A1 H0; induction tr; intros.
  + inversion H0; subst; clear H0.
    clear - nAcr.
    intros r.
    pose proof start_by_Aacq_or_Arel r nil.
    pose proof start_by_Aacq_nil r.
    split; tauto.
  + inversion H0; subst; clear H0.
    destruct s' as [A1' s1'].
    specialize (fun HH => IHtr HH s1' A1' H6); clear H6.
    simpl in H3.
    assert (HH: forall r : resource, start_by_Aacq r tr \/ start_by_Arel r tr).
    Focus 1. {
      clear - nAcr H1.
      intros r; specialize (H1 r).
      destruct (classic (is_resource_action r a)) as [[? | ?] | ?]; subst;
      destruct H1 as [HH | HH]; inversion HH; auto.
    } Unfocus.
    specialize (IHtr HH); clear HH.
    intros r; specialize (IHtr r); specialize (H1 r).
    destruct (classic (is_resources_action a)) as [[?r [? | ?]] | ?]; subst.
    - inversion H3; subst; clear H3; solve_resource_action.
      clear I f H7 H8 H9.
      specialize (H6 r).
      pose proof start_by_Aacq_or_Arel r (Aacquire_res r0 :: tr).
      pose proof start_by_Aacq_or_Arel r tr.
      destruct H1 as [H1 | H1]; inversion H1; subst; solve_resource_action;
      destruct IHtr, H6; split; try tauto.
    - inversion H3; subst; clear H3; solve_resource_action.
      clear I H7 H8.
      specialize (H6 r).
      pose proof start_by_Aacq_or_Arel r (Arelease_res r0 :: tr).
      pose proof start_by_Aacq_or_Arel r tr.
      destruct H1 as [H1 | H1]; inversion H1; subst; solve_resource_action;
      destruct IHtr, H6; split; try tauto.
    - rewrite <- thread_local_state_enable_non_resource_action in H3 by auto.
      apply state_enable_non_resource_action1 in H3; auto.
      subst A1.
      assert (~ is_resource_action r a) by (intro HH; apply H; exists r; auto).
      pose proof start_by_Aacq_or_Arel r (a :: tr).
      pose proof start_by_Aacq_or_Arel r tr.
      destruct H1 as [H1 | H1]; inversion H1; subst; solve_resource_action;
      destruct IHtr; split; try tauto.
Qed.

Section soundness.

Existing Instance unit_kMD.

Context {P: ProgrammingLanguage}
        {MD: Model}
        {J: Join model}
        {SA: SeparationAlgebra model}
        {R: Relation model}
        {po_R: PreOrder Krelation}
        {DCSA: DownwardsClosedSeparationAlgebra model}
        {UCSA: UpwardsClosedSeparationAlgebra model}
        {Res: Resource}
        {Ac: Action}
        {Acr: Action_resource Ac Res}
        {nAcr: NormalAction_resource Ac Res}
        {TS: TraceSemantics P (resources * model) Ac}
        {AIr: ActionInterpret_resource model Ac Res ac_sem}
        {SAAIr: @SAActionInterpret_resource (resources * model) Ac ac_sem (@prod_Join _ _ (Pred_Join resource) J) (fun a => ~ is_resources_action a)}
        {KAIr: @KActionInterpret_resource (resources * model) Ac ac_sem (RelProd (discPred_R resource) R)}.

Instance KSAAIr: @KSAActionInterpret_resource (resources * model) Ac ac_sem (@prod_Join _ _ (Pred_Join resource) J) (RelProd (discPred_R resource) R) (fun a => ~ is_resources_action a) :=
  ordered_and_frame_AIr _ _ _.

Context {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {fsSM: FlatSemantics.SeparatingSemantics L MD tt SM}.

Class LegalInvariants (Inv: resource * (model -> Prop) -> Prop): Prop := {
  at_most_one_invariant: forall r I1 I2, Inv (r, I1) -> Inv (r, I2) -> I1 = I2;
  invariant_mono: forall r I,  Inv (r, I) -> forall s1 s2, I s1 -> s1 <= s2 -> I s2;
  invariant_precise: forall r I, Inv (r, I) -> forall s,
    (exists s', (fun s' => exists f, I f /\ join s' f s) s') ->
    (exists s', greatest (fun s' => exists f, I f /\ join s' f s) s')
}.
(*
Definition ThreadLocal_KSA_AIr: forall (Inv: resource * (model -> Prop) -> Prop) {INV: LegalInvariants Inv}, @KSAActionInterpret_resource (resources * model) Ac (ThreadLocal_ActionInterpret_resource ac_sem Inv) (@prod_Join _ _ (Pred_Join resource) J) (RelProd (discPred_R resource) R).
  Check @lift_join.
 *)

Lemma ThreadLocal_ordered_frame_property (Inv: resource * (model -> Prop) -> Prop) {INV: LegalInvariants Inv}: forall (a: action) (m1 f n1' n1: resources * model) (n2: MetaState (resources * model)) fst_m2
    (ASSU: res_enable a (fst m1) fst_m2 (fst f) (*forall r, a = Arelease_res r -> ~ fst f r*)),
    @join _ (prod_Join _ _) m1 f n1' ->
    (RelProd (discPred_R _) R) n1' n1 ->
    thread_local_state_enable Inv a n1 n2  ->
    exists m2 n2', @lift_join _ (prod_Join _ _) m2 (Terminating f) n2' /\ @Partial.forward _ (RelProd (discPred_R _) R) n2' n2 /\ match m2 with Terminating m2 => fst m2 = fst_m2 | _ => True end /\ thread_local_state_enable Inv a m1 m2.
Proof.
  intros.
  destruct (classic (is_resources_action a)) as [[?r [? | ?]] | ?].
  + subst a.
    inversion H1; subst; solve_resource_action.
    rename m into n1, n into n2.
    destruct n1' as [A1' n1'], f as [Af f], m1 as [B1 m1].
    hnf in H; simpl in H; destruct H.
    hnf in H0; simpl in H0. destruct H0. hnf in H0, H7; simpl in H0, H7.
    pose proof join_Korder_down _ _ _ _ _ H6 H7 ltac:(reflexivity) as [n2' [? ?]].
    pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H2) H8 as [m2 [? ?]].
    assert (A1 = A1').
    Focus 1. {
      extensionality r0; apply prop_ext.
      apply iff_sym, H0.
    } Unfocus.
    subst A1'.
    pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H) H3 as [B2 [? ?]].
    exists (Terminating (B2, m2)), (Terminating (A2, n2')).
    split; [| split; [| split]].
    - constructor.
      split; apply join_comm; auto.
    - constructor; split; auto; simpl.
      hnf; intro; simpl; hnf; tauto.
    - apply res_enable_acq_inv in ASSU.
      simpl in ASSU; destruct ASSU as [? _].
      simpl; clear - H14 H12.
      extensionality r0; apply prop_ext.
      specialize (H12 r0); specialize (H14 r0); destruct H12, H14; tauto.
    - simpl.
      eapply thread_local_state_enable_acq; eauto.
  + subst a.
    destruct n1 as [A1 n1], n1' as [A1' n1'], f as [Af f], m1 as [B1 m1].
    hnf in H; simpl in H; destruct H.
    hnf in H0; unfold RelCompFun in H0; simpl in H0; destruct H0.
    assert (A1' = A1).
    Focus 1. {
      extensionality r0; apply prop_ext.
      apply H0.
    } Unfocus.
    subst A1'; clear H0.
    destruct (classic (forall I, Inv (r, I) -> exists m2, (fun m2 => exists f, I f /\ join m2 f m1) m2)).
    - inversion H1; subst; solve_resource_action.
      Focus 2. {
        exfalso.
        specialize (H0 _ H8).
        destruct H0 as [m2 [f0 [? ?]]].
        pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H4) H2 as [n2' [? ?]].
        pose proof join_Korder_up _ _ _ _ H6 H3 as [_f0 [n2 [? [? ?]]]].
        apply (H10 n2); clear H10.
        exists _f0; split; [eapply (invariant_mono _ _ H8); eauto | apply join_comm; auto].
      } Unfocus.
      specialize (H0 _ H8).
      apply (invariant_precise _ _ H8) in H0.
      destruct H0 as [m2 ?].
      destruct (proj1 H0) as [f0 [? ?]].
      pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H5) H2 as [n2' [? ?]].
      pose proof join_Korder_up _ _ _ _ H9 H3 as [_f0 [_n2 [? [? ?]]]].
      assert ((fun n : model => exists f : model, I f /\ join n f n1) _n2).
      Focus 1. { exists _f0; split; [eapply (invariant_mono _ _ H8); eauto | apply join_comm; auto]. } Unfocus.
      apply (proj2 H10) in H14.
      apply res_enable_rel_inv in ASSU; simpl in ASSU.
      rename fst_m2 into B2.
      exists (Terminating (B2, m2)), (Terminating (A2, n2')).
      split; [| split; [| split]].
      * constructor.
        split; auto.
        simpl.
        clear - ASSU H H7.
        intros r0; specialize (ASSU r0); specialize (H r0); specialize (H7 r0).
        destruct ASSU, H, H7; split; tauto.
      * constructor.
        split; [hnf; intros ?; hnf; tauto | change (n2' <= n); etransitivity; eauto].
      * auto.
      * simpl.
        eapply thread_local_state_enable_rel_succ; eauto.
    - exists Error, n2.
      split; [| split; [| split]].
      * constructor.
      * destruct n2; constructor.
        destruct p as [A2 n2].
        split; [hnf; intros ?; hnf; tauto | change (n2 <= n2); reflexivity].
      * auto.
      * apply Classical_Pred_Type.not_all_ex_not in H0; destruct H0 as [I ?].
        apply imply_to_and in H0; destruct H0.
        apply res_enable_rel_inv in ASSU; simpl in ASSU.
        eapply thread_local_state_enable_rel_fail; eauto.
  + rewrite <- (thread_local_state_enable_non_resource_action Inv) in H1 by auto.
    change ((fun a => ~ is_resources_action a) a) in H2.
    pose proof ordered_frame_property _ _ _ _ _ _ H2 H H0 H1 as [m2 [n2' [? [? ?]]]].
    exists m2, n2'.
    split; [| split; [| split]]; auto.
    - apply res_enable_not_res_inv in ASSU; auto.
      destruct m1 as [A1 m1], m2 as [| | [A2 m2]]; auto.
      simpl in H5.
      apply state_enable_non_resource_action1 in H5; auto.
      subst; auto.
    - simpl.
      rewrite <- (thread_local_state_enable_non_resource_action Inv) by auto.
      auto.
Qed.

Lemma hoare_parallel_partial_sound
      {CPP: ConcurrentProgrammingLanguage_Sparallel P}
      {AcP: Action_Parallel Ac}
      {nAcPr: NormalAction_Parallel_resource Ac Res}
      {c2tP: Command2Traces_Sparallel_resource P model Ac Res c2t}
      {AIPr: ActionInterpret_Parallel_resource model Ac Res ac_sem}:
  forall Inv c1 P1 Q1 c2 P2 Q2 (INV: LegalInvariants Inv),
  guarded_triple_partial_valid Inv P1 c1 Q1 ->
  guarded_triple_partial_valid Inv P2 c2 Q2 ->
  guarded_triple_partial_valid Inv (P1 * P2) (Sparallel c1 c2) (Q1 * Q2).
Proof.
  intros.
  rename H into LEFT_ASSU, H0 into RIGHT_ASSU.
  hnf in LEFT_ASSU, RIGHT_ASSU |- *; intros.
  unfold access, ThreadLocal_BSS in LEFT_ASSU, RIGHT_ASSU, H0; simpl in LEFT_ASSU, RIGHT_ASSU, H0.
  inversion H0; subst; clear H0.
  rewrite Sparallel_denote in H1.
  set (Tr1 := cmd_denote c1) in LEFT_ASSU, H1.
  set (Tr2 := cmd_denote c2) in RIGHT_ASSU, H1.
  clearbody Tr1 Tr2; clear c1 c2.
  inversion H1; subst; clear H1.
  set (A1 := fun _: resource => False) in LEFT_ASSU at 1, H4 at 1.
  set (A2 := fun _: resource => False) in RIGHT_ASSU at 1, H4 at 1.
  set (A := fun _: resource => False) in H2 at 1.
  rewrite sat_sepcon in H.
  destruct H as [s1 [s2 [? [? ?]]]].
  set (s0 := s_pre) in H.
  assert (STATE_JOIN: @join _ (prod_Join resources model) (A1, s1) (A2, s2) (A, s0)).
  Focus 1. {
    split; auto.
    hnf; intros r0.
    simpl; subst A1 A2 A; split; tauto.
  } Unfocus.
  assert (STATE_LE: @Krelation _ (RelProd (discPred_R resource) R) (A, s0) (A, s_pre)).
  Focus 1. {
    split; hnf; simpl.
    + intros; hnf; tauto.
    + change (s_pre <= s_pre).
      reflexivity.
  } Unfocus.
  clearbody A1 A2 A s0. clear H.
  specialize (fun ms_post HH => LEFT_ASSU s1 ms_post H1 (traces_access_intro tr1 _ _ _ H0 HH)).
  specialize (fun ms_post HH => RIGHT_ASSU s2 ms_post H5 (traces_access_intro tr2 _ _ _ H3 HH)).
  clear P1 P2 H1 H5 Tr1 Tr2 H0 H3.
  rename H2 into TRACE_ACC.
  revert s0 s1 s2 s_pre A LEFT_ASSU RIGHT_ASSU STATE_JOIN STATE_LE TRACE_ACC; induction H4; intros.
  + inversion TRACE_ACC; subst.
    destruct ms_post; subst; inversion H.
    subst m A.
    assert (A2 = fun _ => False).
    Focus 1. {
      extensionality r; apply prop_ext.
      destruct STATE_JOIN as [? _].
      hnf in H0. specialize (H0 r).
      simpl in H0; destruct H0.
      tauto.
    } Unfocus.
    assert (A1 = fun _ => False).
    Focus 1. {
      extensionality r; apply prop_ext.
      destruct STATE_JOIN as [? _].
      hnf in H1. specialize (H1 r).
      simpl in H1; destruct H1.
      tauto.
    } Unfocus.
    subst A1 A2.
    specialize (LEFT_ASSU (Terminating s1) (trace_access_nil _)); simpl in LEFT_ASSU.
    specialize (RIGHT_ASSU (Terminating s2) (trace_access_nil _)); simpl in RIGHT_ASSU.
    eapply sat_mono; [exact (proj2 STATE_LE) |].
    rewrite sat_sepcon.
    exists s1, s2.
    split; [| split]; auto.
    exact (proj2 STATE_JOIN).
  + exfalso.
    destruct (res_actions_no_race _ _ H).
    apply (state_enable_race_actions_spec a1 a2 A1 A2 s1 s2 s0); auto.
    - intro.
      rewrite (thread_local_state_enable_non_resource_action Inv) in H2 by auto.
      specialize (LEFT_ASSU Error (@trace_access_Error _ _ (ThreadLocal_ActionInterpret_resource _ Inv) _ _ _ H2)).
      inversion LEFT_ASSU.
    - intro.
      rewrite (thread_local_state_enable_non_resource_action Inv) in H2 by auto.
      specialize (RIGHT_ASSU Error (@trace_access_Error _ _ (ThreadLocal_ActionInterpret_resource _ Inv) _ _ _ H2)).
      inversion RIGHT_ASSU.
    - exact (proj2 STATE_JOIN).
  + change (res_enable a1 (fst (A1, s1)) A1' (fst (A2, s2))) in H.
    inversion TRACE_ACC; subst.
    - (* NonTerminating *)
      destruct ms_post; inversion H5; clear H5; auto.
    - (* Error *)
      pose proof ThreadLocal_ordered_frame_property Inv _ _ _ _ _ Error A1' H STATE_JOIN STATE_LE H3 as [Error' [Error'' [? [? [_ ?]]]]].
      inversion H1; subst; clear H1.
      inversion H0; subst; clear H0.
      simpl lift_function in H2.
      exfalso.
      apply (LEFT_ASSU Error).
      apply trace_access_Error; auto.
    - (* Terminating *)
      pose proof ThreadLocal_ordered_frame_property Inv _ _ _ _ _ (Terminating s') A1' H STATE_JOIN STATE_LE H2 as [m2 [n2' [? [? [? ?]]]]].
      destruct n2' as [| | n2']; inversion H1; subst.
      destruct m2 as [| | m2]; inversion H0; subst.
      * exfalso.
        apply (LEFT_ASSU Error).
        apply trace_access_Error; auto.
      * destruct s' as [A' s'], m2 as [A1' s1'], n2' as [A0' s0'].
        assert (A0' = A').
        Focus 1. {
          clear - H9. destruct H9 as [? _]; hnf in H; simpl in H.
          extensionality r0; apply prop_ext; apply H.
        } Unfocus.
        subst A0'.
        apply (IHtrace_interleave s0' s1' s2 s' A'); auto.
        intros.
        apply LEFT_ASSU.
        eapply trace_access_Terminating; eauto.
  + change (res_enable a2 (fst (A2, s2)) A2' (fst (A1, s1))) in H.
    inversion TRACE_ACC; subst.
    - (* NonTerminating *)
      destruct ms_post; inversion H5; clear H5; auto.
    - (* Error *)
      pose proof ThreadLocal_ordered_frame_property Inv _ _ _ _ _ Error A2' H (@join_comm _ _ (prod_SA _ _) _ _ _ STATE_JOIN) STATE_LE H3 as [Error' [Error'' [? [? [_ ?]]]]].
      inversion H1; subst; clear H1.
      inversion H0; subst; clear H0.
      simpl lift_function in H2.
      exfalso.
      apply (RIGHT_ASSU Error).
      apply trace_access_Error; auto.
    - (* Terminating *)
      pose proof ThreadLocal_ordered_frame_property Inv _ _ _ _ _ (Terminating s') A2' H (@join_comm _ _ (prod_SA _ _) _ _ _ STATE_JOIN) STATE_LE H2 as [m2 [n2' [? [? [? ?]]]]].
      destruct n2' as [| | n2']; inversion H1; subst.
      destruct m2 as [| | m2]; inversion H0; subst.
      * exfalso.
        apply (RIGHT_ASSU Error).
        apply trace_access_Error; auto.
      * destruct s' as [A' s'], m2 as [A2' s2'], n2' as [A0' s0'].
        assert (A0' = A').
        Focus 1. {
          clear - H9. destruct H9 as [? _]; hnf in H; simpl in H.
          extensionality r0; apply prop_ext; apply H.
        } Unfocus.
        subst A0'.
        apply (IHtrace_interleave s0' s1 s2' s' A'); auto.
        intros.
        apply RIGHT_ASSU.
        eapply trace_access_Terminating; eauto.
        apply (@join_comm _ _ (prod_SA _ _)); auto.
Qed.

Lemma SRA_triple_spec
      {c2tSRA: StructuralResourceAccess P Ac Res c2t}:
  forall (Inv: (resource * (model -> Prop)) -> Prop) (Pre: expr) (c: cmd) (Post: expr),
     guarded_triple_partial_valid Inv Pre c Post <->
     (forall s_pre A_post ms_post, KRIPKE: s_pre |= Pre -> @traces_access _ _ (ThreadLocal_ActionInterpret_resource _ Inv) (cmd_denote c) (fun _ => False, s_pre) (lift_function (pair A_post) ms_post) -> match ms_post with | Error => False | NonTerminating => True | Terminating s_post => KRIPKE: s_post |= Post end).
Proof.
  intros.
  split.
  + intros.
    hnf in H.
    inversion H1; subst.
    replace (lift_function (pair A_post) ms_post) with (lift_function (pair (fun _:resource => False)) ms_post) in H3.
    Focus 2. {
      destruct ms_post as [| | ms_post]; auto.
      simpl lift_function in H3.
      eapply start_by_Aacq_trace_acc_spec in H3; [subst; auto |].
      intros; eapply resource_sequential; eauto.
    } Unfocus.
    apply (H s_pre ms_post); auto.
    apply (traces_access_intro tr); auto.
  + intros.
    hnf; intros.
    apply (H s_pre (fun _ => False) ms_post); auto.
Qed.

Lemma hoare_resource_block_partial_sound
      {CPP: ConcurrentProgrammingLanguage_Sresource P Res}
      {c2tR: Command2Traces_Sresource P Ac Res c2t}
      {c2tSRA: StructuralResourceAccess P Ac Res c2t}:
  forall Inv0 Inv1 r P1 P2 c I dI (INV: LegalInvariants Inv1),
  @join _ (Pred_Join _) Inv0 (eq (r, dI)) Inv1 ->
  (dI = fun m => KRIPKE: m |= I) ->
  resource_no_occur r (cmd_denote c) ->
  guarded_triple_partial_valid Inv0 (P1 * I) c (P2 * I) ->
  guarded_triple_partial_valid Inv1 P1 (Sresource r c) P2.
Proof.
  intros.
  subst dI.
  rewrite SRA_triple_spec in H2 |- *.
  rename H into INV_CONS, H1 into NO_OCCUR.
  rename H2 into ASSU; intros.
  unfold access, ThreadLocal_BSS in ASSU, H0; simpl in ASSU, H0.
  inversion H0; subst; clear H0.
  rewrite Sresource_denote in H1.
  set (Tr := cmd_denote c) in ASSU, H1, NO_OCCUR.
  clearbody Tr; clear c.
  inversion H1; subst; clear H1.
  inversion H3; subst; clear H3.
  unfold singleton_traces, singleton_trace in H0, H4.
  subst tr1 tr3; rename tr0 into tr.
  specialize (fun s A_post ms_post _H HH => ASSU s A_post ms_post _H (traces_access_intro tr _ _ _ H1 HH)).
  specialize (NO_OCCUR _ H1).
  clear Tr H1.
  unfold trace_app in H2; simpl app in H2; inversion H2; subst; clear H2.
  Focus 1. { exfalso; inversion H4; subst; solve_resource_action. } Unfocus.
  Focus 1. { exfalso; inversion H4; subst; solve_resource_action. } Unfocus.
  inversion H3; subst; clear H3; solve_resource_action.
  assert (I0 = fun m => KRIPKE: m |= I).
  Focus 1. {
    clear - INV_CONS INV H7.
    apply (at_most_one_invariant r); auto.
    specialize (INV_CONS (r, fun m => m |= I)).
    destruct INV_CONS; simpl in *.
    tauto.
  } Unfocus.
  subst I0.
  assert (KRIPKE: n |= P1 * I).
  Focus 1. {
    rewrite sat_sepcon.
    exists s_pre, f; auto.
  } Unfocus.
  clear f s_pre H8 H9 H.
  rename n into s.
  specialize (fun A_post ms_post => ASSU s A_post ms_post H0); clear H0 P1.

  set (A1 := fun _ => False) in H5, ASSU at 1.
  clearbody A1.
  rename H5 into JOIN_RES, H6 into TRACE_ACC, H7 into Inv_r.

  revert A1 A2 s JOIN_RES TRACE_ACC ASSU; induction tr; intros.
  + simpl in TRACE_ACC.
    specialize (ASSU A1 (Terminating s) (trace_access_nil _)).
    change (KRIPKE: s |= P2 * I) in ASSU.
    rewrite sat_sepcon in ASSU.
    destruct ASSU as [s' [f [? [? ?]]]].
    assert ((fun n : model => exists f : model, KRIPKE: f |= I /\ join n f s) s') by (exists f; auto).
    inversion TRACE_ACC; subst.
    - inversion H6; subst; solve_resource_action.
    - inversion H6; subst; solve_resource_action.
      pose proof at_most_one_invariant _ _ _ H9 Inv_r; subst I0; clear H9.
      exfalso; apply (H10 s').
      exists f; auto.
    - inversion H5; subst; solve_resource_action.
      pose proof at_most_one_invariant _ _ _ H10 Inv_r; subst I0; clear H10.
      apply (proj2 H11) in H2.
      eapply sat_mono in H0; [| exact H2].
      inversion H8; subst.
      destruct ms_post; inversion H3; subst.
      auto.
  + simpl in TRACE_ACC.
    assert (forall ms, thread_local_state_enable Inv1 a (A2, s) ms ->
                       match ms with
                       | Error => thread_local_state_enable Inv0 a (A1, s) Error
                       | NonTerminating => thread_local_state_enable Inv0 a (A1, s) NonTerminating
                       | Terminating (A2', s') => exists A1', join A1' (eq r) A2' /\ thread_local_state_enable Inv0 a (A1, s) (Terminating (A1', s'))
                       end).
    Focus 1. {
      clear - INV_CONS INV NO_OCCUR JOIN_RES AIr.
      intros.
      assert (~ is_resource_action r a).
      Focus 1. {
        intros [? | ?].
        + subst; apply (proj1 NO_OCCUR).
          left; auto.
        + subst; apply (proj2 NO_OCCUR).
          left; auto.
      } Unfocus.
      clear NO_OCCUR; rename H0 into NO_OCCUR.
      inversion H; subst; solve_resource_action.
      + assert (Inv0 (r0, I0)).
        Focus 1. {
          specialize (INV_CONS (r0, I0)).
          assert ((r, fun m : model => KRIPKE: m |= I) <> (r0, I0)) by congruence.
          destruct INV_CONS; tauto.
        } Unfocus.
        rename A3 into A2'.
        pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ JOIN_RES) H2 as [A1' [? ?]].
        apply join_comm in H4.
        exists A1'; split; auto.
        eapply (thread_local_state_enable_acq _ _ _ _ _ _ _ _ H1 H0 H5 H7).
      + assert (Inv0 (r0, I0)).
        Focus 1. {
          specialize (INV_CONS (r0, I0)).
          assert ((r, fun m : model => KRIPKE: m |= I) <> (r0, I0)) by congruence.
          destruct INV_CONS; tauto.
        } Unfocus.
        rename A3 into A2'.
        set (A1' := fun rr => A2' rr /\ r <> rr).
        assert (join A1' (eq r) A2').
        Focus 1. {
          subst A1'; intros rr; specialize (H2 rr); specialize (JOIN_RES rr).
          assert (r0 = rr -> r = rr -> False) by (intros; congruence).
          destruct H2, JOIN_RES; split; tauto.
        } Unfocus.
        assert (join A1' (eq r0) A1).
        Focus 1. {
          subst A1'; intros rr; specialize (H2 rr); specialize (JOIN_RES rr).
          assert (r0 = rr -> r = rr -> False) by (intros; congruence).
          destruct H2, JOIN_RES; split; tauto.
        } Unfocus.
        exists A1'; split; auto.
        eapply (thread_local_state_enable_rel_succ _ _ _ _ _ _ _ H3 H0 H6).
      + assert (Inv0 (r0, I0)).
        Focus 1. {
          specialize (INV_CONS (r0, I0)).
          assert ((r, fun m : model => KRIPKE: m |= I) <> (r0, I0)) by congruence.
          destruct INV_CONS; tauto.
        } Unfocus.
        rename A3 into A2'.
        set (A1' := fun rr => A2' rr /\ r <> rr).
        assert (join A1' (eq r) A2').
        Focus 1. {
          subst A1'; intros rr; specialize (H2 rr); specialize (JOIN_RES rr).
          assert (r0 = rr -> r = rr -> False) by (intros; congruence).
          destruct H2, JOIN_RES; split; tauto.
        } Unfocus.
        assert (join A1' (eq r0) A1).
        Focus 1. {
          subst A1'; intros rr; specialize (H2 rr); specialize (JOIN_RES rr).
          assert (r0 = rr -> r = rr -> False) by (intros; congruence).
          destruct H2, JOIN_RES; split; tauto.
        } Unfocus.
        eapply (thread_local_state_enable_rel_fail _ _ _ _ _ _ H3 H0 H6).
      + destruct ms as [| | [A2' s']].
        - eapply thread_local_state_enable_non_resource; auto.
          change Error with (lift_function (pair A1) (@Error model)).
          change Error with (lift_function (pair A2) (@Error model)) in H1.
          apply (state_enable_non_resource_action2 _ _ _ _ _ H0 H1).
        - eapply thread_local_state_enable_non_resource; auto.
          change NonTerminating with (lift_function (pair A1) (@NonTerminating model)).
          change NonTerminating with (lift_function (pair A2) (@NonTerminating model)) in H1.
          apply (state_enable_non_resource_action2 _ _ _ _ _ H0 H1).
        - pose proof state_enable_non_resource_action1 _ _ _ _ _ H0 H1; subst A2'.
          exists A1.
          split; auto.
          eapply thread_local_state_enable_non_resource; auto.
          change (Terminating (A2, s')) with (lift_function (pair A2) (Terminating s')) in H1.
          apply (state_enable_non_resource_action2 _ _ _ _ _ H0 H1).
    } Unfocus.
    inversion TRACE_ACC; subst.
    - destruct ms_post; inversion H4; auto.
    - simpl in H3.
      apply H in H3.
      specialize (ASSU A1 Error (@trace_access_Error _ _ (ThreadLocal_ActionInterpret_resource _ Inv0) _ _ _ H3)).
      inversion ASSU.
    - simpl in H2.
      apply H in H2.
      destruct s' as [A2' s'].
      destruct H2 as [A1' [? ?]].
      assert (~ In (Aacquire_res r) tr /\ ~ In (Arelease_res r) tr)
        by (simpl in NO_OCCUR; tauto).
      apply (IHtr H2 A1' A2' s'); auto; clear H2 ms_post IHtr TRACE_ACC H5 A_post.
      intros.
      apply (ASSU A_post ms_post).
      eapply trace_access_Terminating; eauto.
Qed.

End soundness.

