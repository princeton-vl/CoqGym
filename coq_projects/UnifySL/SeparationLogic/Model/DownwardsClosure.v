Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Section DownwardsClosure.

Context {worlds : Type}
        {R: Relation worlds}
        {po_R: PreOrder Krelation}
        {J: Join worlds}
        {SA: SeparationAlgebra worlds}
        {uSA: UpwardsClosedSeparationAlgebra worlds}.

  (** *Downwards CLosure*)

Definition DownwardsClosure_J: Join worlds.
Proof. exact (fun m1 m2 m: worlds => exists n1 n2, m1 <= n1 /\ m2 <= n2 /\ join n1 n2 m).
Defined.

Definition DownwardsClosure_SA:
  @SeparationAlgebra worlds (DownwardsClosure_J).
Proof.
  constructor.
  + (* join_comm *)
    intros.
    destruct H as [n1 [n2 [? [? ?]]]].
    exists n2, n1.
    split; [| split]; auto.
    apply join_comm; auto.
  + (* join_assoc *)
    intros.
    destruct H as [mx'' [my'' [? [? ?]]]].
    destruct H0 as [mxy' [mz' [? [? ?]]]].
    destruct (join_Korder_up _ _ _ _ H2 H0) as [mx' [my' [? [? ?]]]].
    destruct (join_assoc _ _ _ _ _ H5 H4) as [myz' [? ?]].
    exists myz'.
    split.
    - exists my', mz'; split; [| split]; auto.
      etransitivity; eauto.
    - exists mx', myz'; split; [| split]; auto.
      * etransitivity; eauto.
      * reflexivity.
Defined.

Lemma DownwardsClosure_increasing: forall m, @increasing' _ _ J m <-> @increasing _ _ (DownwardsClosure_J) m.
Proof.
  intros.
  unfold increasing', increasing; split; intros.
  + destruct H0 as [m0 [n0 [? [? ?]]]].
    etransitivity; [eassumption |].
    eapply H; [| eassumption].
    auto.
  + apply H.
    exists n, n0.
    split; [| split]; auto; reflexivity.
Qed.

Definition DownwardsClosure_DownwardsClosed:
  @DownwardsClosedSeparationAlgebra worlds _ (DownwardsClosure_J).
Proof.
  intros until n2; intros.
  exists m.
  split; [| reflexivity].
  destruct H as [m1' [m2' [? [? ?]]]].
  exists m1', m2'.
  split; [| split]; auto; etransitivity; eauto.
Qed.

Definition DownwardsClosure_UpwardsClosed : @UpwardsClosedSeparationAlgebra worlds _ (DownwardsClosure_J).
Proof.
  intros until m2; intros.
  simpl in *.
  destruct H as [n1 [n2 [? [? ?]]]].
  destruct (join_Korder_up _ _ _ _ H2 H0) as [n1' [n2' [? [? ?]]]].
  exists n1, n2; split; [| split]; auto.
  exists n1', n2'; split; [| split]; auto.
Qed.

Definition DownwardsClosure_USA {USA': UnitalSeparationAlgebra' worlds}: @UnitalSeparationAlgebra worlds _ (DownwardsClosure_J).
Proof.
  constructor.
  intros.
  destruct (incr'_exists n) as [u [? ?]].
  destruct H as [n' [H1 H2]].
  exists u; split; auto.
  + exists n'; split; auto.
    exists u, n'; split; [| split]; auto; reflexivity.
  + rewrite <- DownwardsClosure_increasing; auto.
Defined.

Definition DownwardsClosure_incrSA {incrSA: IncreasingSeparationAlgebra worlds}: @IncreasingSeparationAlgebra worlds _ (DownwardsClosure_J).
Proof.
  constructor.
  simpl.
  intros.
  hnf; intros.
  destruct H as [n1 [n2 [? [? ?]]]].
  etransitivity; [eauto |].
  eapply all_increasing; eauto.
Qed.

End DownwardsClosure.
