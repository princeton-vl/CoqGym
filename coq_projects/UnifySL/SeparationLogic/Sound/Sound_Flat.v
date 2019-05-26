Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Sound_Flat.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {MD: Model}
        {kMD: KripkeModel MD}
        (M: Kmodel)
        {R: Relation (Kworlds M)}
        {po_R: PreOrder Krelation}
        {J: Join (Kworlds M)}
        {SA: SeparationAlgebra (Kworlds M)}
        {dSA: DownwardsClosedSeparationAlgebra (Kworlds M)}
        {SM: Semantics L MD}
        {kiSM: KripkeIntuitionisticSemantics L MD M SM}
        {kminSM: KripkeMinimunSemantics L MD M SM}
        {kpSM: KripkePropositionalSemantics L MD M SM}
        {fsSM: FlatSemantics.SeparatingSemantics L MD M SM}.

Lemma sound_sepcon_comm:
  forall x y: expr,
    forall m,
      KRIPKE: M, m |= x * y --> y * x.
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_sepcon in H0 |- *; intros.
  destruct H0 as [m1 [m2 [? [? ?]]]].
  exists m2, m1.
  split; [| split]; auto.
  apply join_comm; auto.
Qed.

Lemma sound_sepcon_assoc:
  forall x y z: expr,
    forall m,
      KRIPKE: M, m |= x * (y * z) <--> (x * y) * z.
Proof.
  intros.
  unfold iffp.
  rewrite sat_andp.
  split; intros.
  + rewrite sat_impp; intros.
    rewrite sat_sepcon in H0.
    destruct H0 as [mx [myz [? [? ?]]]].
    rewrite sat_sepcon in H2.
    destruct H2 as [my [mz [? [? ?]]]].
    apply join_comm in H0.
    apply join_comm in H2.
    destruct (join_assoc mz my mx myz n H2 H0) as [mxy [? ?]].
    apply join_comm in H5.
    apply join_comm in H6.
    rewrite sat_sepcon.
    exists mxy, mz.
    split; [| split]; auto.
    rewrite sat_sepcon.
    exists mx, my.
    split; [| split]; auto.
  + rewrite sat_impp; intros.
    rewrite sat_sepcon in H0.
    destruct H0 as [mxy [mz [? [? ?]]]].
    rewrite sat_sepcon in H1.
    destruct H1 as [mx [my [? [? ?]]]].
    destruct (join_assoc mx my mz mxy n H1 H0) as [myz [? ?]].
    rewrite sat_sepcon.
    exists mx, myz.
    split; [| split]; auto.
    rewrite sat_sepcon.
    exists my, mz.
    split; [| split]; auto.
Qed.

Lemma sound_wand_sepcon_adjoint:
  forall x y z: expr,
    (forall m, KRIPKE: M, m |= x * y --> z) <-> (forall m, KRIPKE: M, m |= x --> (y -* z)).
Proof.
  intros.
  split; intro.
  + assert (ASSU: forall m1 m2 m, join m1 m2 m -> KRIPKE: M, m1 |= x -> KRIPKE: M, m2 |= y -> KRIPKE: M, m |= z).
    Focus 1. {
      intros.
      specialize (H m).
      rewrite sat_impp in H.
      apply (H m); [reflexivity |].
      rewrite sat_sepcon.
      exists m1, m2; auto.
    } Unfocus.
    clear H.
    intros.
    rewrite sat_impp; intros.
    rewrite sat_wand; intros.
    apply (ASSU n m1 m2); auto.
  + assert (ASSU: forall m1 m2 m, join m m1 m2 -> KRIPKE: M, m |= x -> KRIPKE: M, m1 |= y -> KRIPKE: M, m2 |= z).
    Focus 1. {
      intros.
      specialize (H m).
      rewrite sat_impp in H.
      revert m1 m2 H0 H2.
      rewrite <- sat_wand.
      apply (H m); [reflexivity | auto].
    } Unfocus.
    intros.
    rewrite sat_impp; intros.
    rewrite sat_sepcon in H1.
    destruct H1 as [m1 [m2 [? [? ?]]]].
    apply (ASSU m2 n m1); auto.
Qed.

Lemma sound_sepcon_mono:
  forall x1 x2 y1 y2: expr,
   (forall m, KRIPKE: M, m |= x1 --> x2) ->
   (forall m, KRIPKE: M, m |= y1 --> y2) ->
   (forall m, KRIPKE: M, m |= x1 * y1 --> x2 * y2).
Proof.
  intros.
  assert (ASSUx: forall m, KRIPKE: M, m |= x1 -> KRIPKE: M, m |= x2).
  Focus 1. {
    intros.
    specialize (H m0).
    rewrite sat_impp in H.
    apply (H m0); [reflexivity | auto].
  } Unfocus.
  assert (ASSUy: forall m, KRIPKE: M, m |= y1 -> KRIPKE: M, m |= y2).
  Focus 1. {
    intros.
    specialize (H0 m0).
    rewrite sat_impp in H0.
    apply (H0 m0); [reflexivity | auto].
  } Unfocus.
  rewrite sat_impp; intros.
  rewrite sat_sepcon in H2 |- *.
  destruct H2 as [m1 [m2 [? [? ?]]]].
  exists m1, m2; auto.
Qed.

Lemma sound_sepcon_elim1 {incrSA: IncreasingSeparationAlgebra (Kworlds M)}:
  forall x y: expr,
    forall m, KRIPKE: M, m |= x * y --> x.
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_sepcon in H0.
  destruct H0 as [m1 [m2 [? [? ?]]]].
  apply join_comm in H0.
  apply all_increasing in H0.
  eapply sat_mono; eauto.
Qed.

Context {s'L: SeparationEmpLanguage L}
        {feSM: EmpSemantics L MD M SM}.

Lemma sound_sepcon_emp {USA: UnitalSeparationAlgebra (Kworlds M)}:
  forall x: expr,
    forall m, KRIPKE: M, m |= x * emp <--> x.
Proof.
  intros.
  unfold iffp.
  rewrite sat_andp.
  split.
  + rewrite sat_impp; intros.
    rewrite sat_sepcon in H0.
    destruct H0 as [n' [u [? [? ?]]]].
    rewrite sat_emp in H2.
    apply join_comm in H0.
    unfold increasing in H2.
    specialize (H2 _ _ H0).
    eapply sat_mono; eauto.
  + rewrite sat_impp; intros.
    rewrite sat_sepcon.
    destruct (incr_exists n) as [u [? ?]].
    destruct H1 as [n' [H1 H1']].
    exists n', u.
    split; [| split]; auto.
    - apply join_comm; auto.
    - eapply sat_mono; eauto.
    - rewrite sat_emp; auto.
Qed.

Lemma sound_emp_sepcon_elim1 {ISSSA: IncreasingSplitSmallerSeparationAlgebra (Kworlds M)}:
  forall x y: expr,
    forall m, KRIPKE: M, m |= x * y && emp --> x.
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_andp, sat_sepcon, sat_emp in H0.
  clear m H.
  destruct H0 as [[n1 [n2 [? [? ?]]]] ?].
  eapply incr_split_smaller in H2; [| exact H].
  eapply sat_mono; eauto.
Qed.

Lemma sound_emp_dup {IJSSA: IncreasingJoinSelfSeparationAlgebra (Kworlds M)}:
  forall x y: expr,
    forall m, KRIPKE: M, m |= x && emp --> x * x.
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_andp, sat_emp in H0.
  rewrite sat_sepcon.
  clear m H.
  destruct H0.
  pose proof incr_join_self n H0.
  exists n, n; auto.
Qed.

End Sound_Flat.
