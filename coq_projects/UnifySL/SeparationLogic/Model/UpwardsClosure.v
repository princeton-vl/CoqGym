Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Section UpwardsClosure.

Context {worlds: Type}
        {R: Relation worlds}
        {po_R: PreOrder Krelation}
        {J: Join worlds}
        {SA: SeparationAlgebra worlds}
        {dSA: DownwardsClosedSeparationAlgebra worlds}.

(** *Upwards CLosure*)
Definition UpwardsClosure_J: Join worlds.
Proof. intros m1 m2 m; exact (exists n, n <= m /\ join m1 m2 n).
Defined.

Definition UpwardsClosure_SA:
  @SeparationAlgebra worlds (UpwardsClosure_J).
Proof.
  constructor.
  + intros.
    destruct H as [n [? ?]].
    exists n.
    split; auto.
    apply join_comm; auto.
  + intros.
    rename mx into mx', my into my', mz into mz'.
    destruct H as [mxy' [? ?]].
    destruct H0 as [mxyz' [? ?]].
    destruct (join_Korder_down _ _ _ _ mz' H2 H) as [mxyz'' [? ?]]; [reflexivity |].
    destruct (join_assoc _ _ _ _ _ H1 H3) as [myz' [? ?]].
    exists myz'.
    split.
    - exists myz'; split; auto.
      reflexivity.
    - exists mxyz''; split; auto.
      etransitivity; eauto.
Defined.

Lemma UpwardsClosure_increasing:
  forall m, @increasing _ _ J m <-> @increasing _ _ (UpwardsClosure_J) m.
Proof.
  intros.
  unfold increasing; split; intros.
  + destruct H0 as [n0 [? ?]].
    etransitivity; eauto.
  + apply H.
    exists n'.
    split; auto.
    reflexivity.
Qed.

Definition UpwardsClosure_UpwardsClosed:
  @UpwardsClosedSeparationAlgebra worlds _ (UpwardsClosure_J).
Proof.
  intros until m2; intros.
  exists m1, m2.
  split; [| split]; [| reflexivity | reflexivity].
  destruct H as [n' [? ?]].
  exists n'.
  split; auto; etransitivity; eauto.
Defined.

Definition UpwardsClosure_DownwardsClosed:
  @DownwardsClosedSeparationAlgebra worlds _ (UpwardsClosure_J).
Proof.
  intros until n2; intros.
  simpl in *.
  destruct H as [n [? ?]].
  destruct (join_Korder_down _ _ _ _ _ H2 H0 H1) as [n' [? ?]].
  exists n; split; auto.
  exists n'; split; auto.
Defined.

Definition UpwardsClosure_USA {USA: UnitalSeparationAlgebra worlds}:
  @UnitalSeparationAlgebra worlds _ (UpwardsClosure_J).
Proof.
  constructor.
  - intros.
    simpl.
    destruct (incr_exists n) as [u [? ?]].
    destruct H as [n' [H1 H2]].
    exists u; split; auto.
    + exists n'; split; auto.
      exists n; split; auto; reflexivity.
    + rewrite <- UpwardsClosure_increasing; auto.
Defined.

Definition UpwardsClosure_incrSA {incrSA: IncreasingSeparationAlgebra worlds}:
  @IncreasingSeparationAlgebra worlds _ (UpwardsClosure_J).
Proof.
  constructor.
  simpl.
  intros.
  hnf; intros.
  destruct H as [m [? ?]].
  etransitivity; eauto.
  eapply all_increasing; eauto.
Qed.

End UpwardsClosure.
