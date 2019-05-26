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
Require Import Logic.SeparationLogic.Semantics.UpwardsSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Sound_Upwards.

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
        {usSM: UpwardsSemantics.SeparatingSemantics L MD M SM}.

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
    apply (ASSU m0 m1 m2); auto.
    eapply sat_mono; eauto.
  + assert (ASSU: forall m0 m1 m2 m, m <= m0 -> join m0 m1 m2 -> KRIPKE: M, m |= x -> KRIPKE: M, m1 |= y -> KRIPKE: M, m2 |= z).
    Focus 1. {
      intros.
      specialize (H m).
      rewrite sat_impp in H.
      revert m0 m1 m2 H0 H1 H3.
      rewrite <- sat_wand.
      apply (H m); [reflexivity | auto].
    } Unfocus.
    intros.
    rewrite sat_impp; intros.
    rewrite sat_sepcon in H1.
    destruct H1 as [m1 [m2 [? [? ?]]]].
    apply (ASSU m1 m2 n m1); auto.
    reflexivity.
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
        {ueSM: UpwardsSemantics.EmpSemantics L MD M SM}.

Lemma sound_sepcon_emp {USA': UnitalSeparationAlgebra' (Kworlds M)}:
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
    specialize (H2 _ ltac:(reflexivity) _ _ H0).
    eapply sat_mono; eauto.
  + rewrite sat_impp; intros.
    rewrite sat_sepcon.
    destruct (incr'_exists n) as [u [? ?]].
    destruct H1 as [n' [H1 H1']].
    exists n', u.
    split; [| split]; auto.
    - apply join_comm; auto.
    - eapply sat_mono; eauto.
    - rewrite sat_emp; eauto. 
Qed.

End Sound_Upwards.

(*****************************************)
(* For SL extension                      *)
(*****************************************)

(*
Definition unique_cancel {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {J: Join worlds} (P: worlds -> Prop): Prop :=
  forall n,
    (exists n1 n2, P n1 /\ join n1 n2 n) ->
    (exists n1 n2, P n1 /\ join n1 n2 n /\
       forall n1' n2', (P n1' /\ join n1' n2' n) -> n2 <= n2').

Lemma sound_precise_sepcon {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {J: Join (Kworlds M)} {nSA: SeparationAlgebra (Kworlds M)} {dSA: UpwardsClosedSeparationAlgebra (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {usSM: UpwardsSemantics.SeparatingSemantics L MD M SM}:
  forall x y,
    unique_cancel (fun m => KRIPKE: M, m |= x) ->
    unique_cancel (fun m => KRIPKE: M, m |= y) ->
    unique_cancel (fun m => KRIPKE: M, m |= x * y).
Proof.
  pose proof Korder_PreOrder as H_PreOrder.
  intros.
  hnf; intros.
  destruct H1 as [nxy [n_res [? ?]]].
  rewrite sat_sepcon in H1.
  destruct H1 as [nx [ny [? [? ?]]]].
  destruct (join_assoc _ _ _ _ _ H1 H2) as [nyr [? ?]].
  destruct (H n (ex_intro _ nx (ex_intro _ nyr (conj H3 H6))))
    as [nx' [nyr' [? [? ?]]]].
  pose proof H9 _ _ (conj H3 H6).
  destruct (join_Korder_up _ _ _ _ H5 H10) as [ny' [n_res' [? [? ?]]]].
  eapply sat_mono in H4; [| exact H12].
  destruct (H0 nyr' (ex_intro _ ny' (ex_intro _ n_res' (conj H4 H11))))
    as [ny'' [n_res'' [? [? ?]]]].

  clear nx ny nxy n_res nyr H1 H2 H3 ny' n_res' H5 H6 H10 H11 H12 H13 H4.
  rename nx' into nx, nyr' into nyr, ny'' into ny, n_res'' into nr.
  destruct (join_assoc _ _ _ _ _ (join_comm _ _ _ H15) (join_comm _ _ _ H8))
    as [nxy [? ?]].
  apply join_comm in H1.
  apply join_comm in H2.

  exists nxy, nr.
  split; [rewrite sat_sepcon; eauto | split; [auto |]].

  clear H7 H8 H14 H15 H1 H2.
  intros nxy' nr' [? ?].
  rewrite sat_sepcon in H1.
  destruct H1 as [nx' [ny' [? [? ?]]]].
  destruct (join_assoc _ _ _ _ _ H1 H2) as [nyr' [? ?]].
  specialize (H9 _ _ (conj H3 H6)).
  destruct (join_Korder_up _ _ _ _ H5 H9) as [ny'' [nr'' [? [? ?]]]].
  eapply sat_mono in H4; [| exact H8].
  specialize (H16 _ _ (conj H4 H7)).
  etransitivity; eassumption.
Qed.
*)
(*
(* This is over generalization, i.e. the soundness of pure_fact_andp needs extra restriction on models. *)

Definition join_inv {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {J: Join worlds} (P: worlds -> Prop): Prop :=
  (forall n1 n2 n, join n1 n2 n -> P n ->
     exists n1' n2', join n1' n2' n /\ n1' <= n1 /\ n2' <= n2 /\ P n1') /\
  (forall n1 n2 n, join n1 n2 n -> P n1 -> P n).

Lemma sound_andp_sepcon {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {J: Join (Kworlds M)} {nSA: SeparationAlgebra (Kworlds M)} {dSA: UpwardsClosedSeparationAlgebra (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {usSM: UpwardsSemantics.SeparatingSemantics L MD M SM}:
  forall x y z,
    join_inv (fun m => KRIPKE: M, m |= x) ->
    forall m,
      KRIPKE: M, m |= (x && (y * z)) <--> ((x && y) * z).
Proof.
  intros.
  unfold iffp.
  rewrite sat_andp, !sat_impp; split; intros ? _ ?; clear m.
  + rewrite sat_andp in H0; destruct H0.
    rewrite sat_sepcon in H1; destruct H1 as [ny [nz [? [? ?]]]].
    destruct H as [? _].
    specialize (H _ _ _ H1 H0).
    destruct H as [ny' [nz' [? [? [? ?]]]]].
    rewrite sat_sepcon; exists ny', nz'.
    split; [| split]; auto.
    - rewrite sat_andp; split; auto.
      eapply sat_mono; eauto.
    - eapply sat_mono; eauto.
  + rewrite sat_sepcon in H0; destruct H0 as [ny [nz [? [? ?]]]].
    rewrite sat_andp in H1; destruct H1.
    rewrite sat_andp; split.
    - destruct H as [_ ?].
      apply (H _ _ _ H0 H1).
    - rewrite sat_sepcon; exists ny, nz.
      auto.
Qed.

*)
