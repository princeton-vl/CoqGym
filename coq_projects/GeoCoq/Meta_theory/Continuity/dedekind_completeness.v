Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Meta_theory.Continuity.completeness.
Require Import GeoCoq.Meta_theory.Continuity.grad.
Require Import GeoCoq.Tarski_dev.Ch08_orthogonality.

(** This file contains the proof that Dedekind completeness implies Hilbert's line completeness. *)

Section Line_extension.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma line_extension_symmetry : forall {Tm : Tarski_neutral_dimensionless}
  (f : @Tpoint Tn -> @Tpoint Tm) P Q, line_extension f P Q -> line_extension f Q P.
Proof.
  intros Tm f P Q [HPQ [fInj [fBet fCong]]].
  repeat split; auto; intro; intros; [apply fInj|apply fBet|apply fCong]; Col.
Qed.

Lemma line_extension_stability : forall {Tm: Tarski_neutral_dimensionless}
  (f : @Tpoint Tn -> @Tpoint Tm) P Q R,
  Col P Q R -> P <> R -> line_extension f P Q -> line_extension f P R.
Proof.
  intros Tm f P Q R HCol HPR [HPQ [fInj [fBet fCong]]].
  repeat split; auto; intro; intros;
    [apply fInj|apply fBet|apply fCong]; trivial; apply col_transitivity_1 with R; Col.
Qed.

Lemma line_extension_reverse_bet : forall {Tm: Tarski_neutral_dimensionless}
  {Tm2: Tarski_neutral_dimensionless_with_decidable_point_equality Tm}
  (f : @Tpoint Tn -> @Tpoint Tm) P Q, line_extension f P Q ->
  forall A B C, Col P Q A -> Col P Q B -> Col P Q C -> Bet (f A) (f B) (f C) -> Bet A B C.
Proof.
  intros Tm Tm2 f P Q [HPQ [fInj [fBet fCong]]] A B C HA HB HC HBet.
  destruct (eq_dec_points (f A) (f B)) as [Heq|Hdiff].
    apply fInj in Heq; subst; Between.
  assert (A <> B) by (intro; subst; auto).
  destruct (segment_construction A B B C) as [D [HD1 HD2]].
  assert (C = D); [|subst; auto].
  assert (Col P Q D) by (apply (colx A B); Col).
  apply fInj; trivial.
  apply between_cong_3 with (f A) (f B); Cong.
Qed.

Lemma pres_bet_line__col : forall {Tm: Tarski_neutral_dimensionless}
  f (P Q : @Tpoint Tn), P <> Q -> pres_bet_line f P Q ->
  forall A B C, Col P Q A -> Col P Q B -> Col P Q C -> Col (f A) (f B) (f C).
Proof.
  intros Tm f P Q HPQ fBet A B C HA HB HC.
  destruct (col3 P Q A B C) as [HBet|[HBet|HBet]]; trivial; apply fBet in HBet; Col.
Qed.

End Line_extension.

Section Completeness.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** If there exists n such that (f A) X = n times (f A) (f B),
    then X belongs to the image of the line extension f *)

Lemma extension_grad : forall {Tm: Tarski_neutral_dimensionless}
  {Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm}
  P Q (f : @Tpoint Tn -> @Tpoint Tm),
  line_extension f P Q ->
  forall A B X, Col P Q A -> Col P Q B -> Grad (f A) (f B) X ->
  exists C, Col P Q C /\ Grad A B C /\ f C = X.
Proof.
  intros Tm Tm2 P Q f [HPQ [fInj [fBet fCong]]] A B X HA HB HGrad.
  destruct (eq_dec_points A B).
  { subst B.
    apply grad112__eq in HGrad; subst X.
    exists A; repeat split; [assumption|constructor].
  }
  remember (f A) as A0.
  remember (f B) as B0.
  induction HGrad.
    exists B; repeat split; auto; constructor.
  rename C into X, C' into X'.
  destruct IHHGrad as [C [HC1 [HC2 HC3]]]; trivial.
  assert (A0 <> X).
  { intro; subst X.
    assert (A = C) by (apply fInj; auto; congruence).
    subst.
    apply grad121__eq in HGrad.
    apply fInj in HGrad; auto.
  }
  destruct (segment_construction A C A B) as [C' [HC'1 HC'2]].
  exists C'.
  assert (Col P Q C').
    apply (colx A C); Col; apply grad_neq__neq13 with B; auto.
  repeat split; trivial.
    apply grad_stab with C; Cong.
  apply (construction_uniqueness A0 X A0 B0); Cong; subst; auto.
Qed.

(** If there exists n such that (f A) X = (f A) (f B) divided by 2^n,
    then X belongs to the image of the line extension f *)

Lemma extension_gradexp : forall {Tm: Tarski_neutral_dimensionless}
  {Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm}
  P Q (f : @Tpoint Tn -> @Tpoint Tm),
  line_extension f P Q ->
  forall A B X, Col P Q A -> Col P Q B -> GradExp (f A) X (f B) ->
  exists C, Col P Q C /\ GradExp A C B /\ f C = X.
Proof.
  intros Tm Tm2 P Q f [HPQ [fInj [fBet fCong]]] A B X HA HB.
  remember (f A) as A'.
  remember (f B) as B'.
  rewrite gradexp__gradexpinv.
  induction 1.
    exists B; repeat split; auto; constructor.
  destruct IHGradExpInv as [C' [HCol []]]; auto.
  destruct (midpoint_existence A C') as [M []].
  assert (Col P Q M).
  { destruct (eq_dec_points A C').
      treat_equalities; assumption.
    apply colx with A C'; Col.
  }
  exists M; repeat split; trivial.
    rewrite gradexp__gradexpinv.
    apply gradexpinv_stab with C'; trivial.
    rewrite <- gradexp__gradexpinv; assumption.
  apply l7_17 with A0 B0; split; trivial; subst; [apply fBet|apply fCong]; assumption.
Qed.

Lemma extension_image_density_aux : forall {Tm: Tarski_neutral_dimensionless}
  {Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm}
  P Q (f : @Tpoint Tn -> @Tpoint Tm),
  @archimedes_axiom Tm ->
  line_extension f P Q ->
  forall A B, A <> B ->
  Lt (f P) (f Q) A B -> Bet (f P) (f Q) A -> Bet (f P) A B ->
  exists X, Col P Q X /\ Bet A (f X) B /\ f X <> A /\ f X <> B.
Proof.
  intros Tm Tm2 P Q f archi fLineExt A B HAB HLt HBet1 HBet2.
  cut (exists C, Grad (f P) (f Q) C /\ Bet A C B /\ C <> A /\ C <> B).
    intros [C [HC1 [HC2 [HC3 HC4]]]].
    destruct (extension_grad P Q f fLineExt P Q C) as [X]; Col.
    exists X; spliter; subst; auto.
  assert (Hdiff : f P <> f Q).
    intro; destruct fLineExt as [HPQ [fInj]]; apply HPQ, fInj; Col.
  destruct (reach__grad_min (f P) (f Q) A) as [D [E [HD1 [HD2 [HE1 [HE2 [HDE1 HDE2]]]]]]]; auto.
  assert (Bet D A E) by (apply (between_exchange3 (f P)); assumption).
  assert (Le A E D E) by Le.
  exists E; repeat split; auto.
  - apply grad_stab with D; assumption.
  - apply l6_13_1.
    { destruct (eq_dec_points A D).
        subst D; apply l6_2 with (f P); Between; apply bet_neq12__neq with (f Q); assumption.
      apply l6_2 with D; Between.
        apply between_symmetry, (between_exchange3 (f P)); assumption.
    }
    apply le_transitivity with D E; trivial.
    apply le_transitivity with (f P) (f Q); Le.
  - intro; subst E.
    apply lt__nle in HLt.
    apply HLt, le_transitivity with D B; Le.
Qed.

Lemma extension_image_density_aux2 : forall {Tm: Tarski_neutral_dimensionless}
  {Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm}
  P Q (f : @Tpoint Tn -> @Tpoint Tm),
  @archimedes_axiom Tm ->
  line_extension f P Q ->
  forall A B, A <> B -> Col (f P) (f Q) A -> Col (f P) (f Q) B ->
  Lt (f P) (f Q) A B -> Bet (f P) A B ->
  exists X, Col P Q X /\ Bet A (f X) B /\ f X <> A /\ f X <> B.
Proof.
  assert (Haux := line_extension_symmetry).
  intros Tm Tm2 P Q f archi fLineExt A B HAB HColA HColB HLt HBet.
  assert (Hf' := fLineExt); destruct Hf' as [HPQ [fInj [fBet fCong]]].
  destruct (eq_dec_points (f P) A).
  { treat_equalities.
    assert (f P <> f Q) by (intro; apply HPQ, fInj; Col).
    destruct (or_bet_out (f Q) (f P) B) as [HBet|[HOut|]]; [..|exfalso; Col].
    - destruct (segment_construction Q P P Q) as [Q' []].
      exists Q'.
      assert (HBet' : Bet (f Q) (f P) (f Q')) by (apply fBet; Col).
      assert (HCong' : Cong (f P) (f Q') (f P) (f Q)) by (apply fCong; Col).
      assert (f P <> f Q').
        intro; assert (P = Q') by (apply fInj; Col); assert_diffs; auto.
      repeat split; Col.
      * apply l6_13_1.
          apply l6_2 with (f Q); Between.
          apply le_transitivity with (f P) (f Q); Le.
      * intro; subst; destruct HLt; Cong.
    - exists Q; repeat split; Col.
        apply l6_13_1; Le.
        intro; subst; destruct HLt; Cong.
  }
  destruct HColA as [|[|]].
  - apply (extension_image_density_aux P Q); trivial.
  - destruct (eq_dec_points (f Q) A).
    { treat_equalities.
      destruct (segment_construction P Q P Q) as [Q' []].
      exists Q'.
      assert (HBet' : Bet (f P) (f Q) (f Q')) by (apply fBet; Col).
      assert (HCong' : Cong (f Q) (f Q') (f P) (f Q)) by (apply fCong; Col).
      assert (f Q <> f Q') by (assert_diffs; auto).
      assert (HLt2 : Lt (f Q) (f Q') (f Q) B) by (apply (cong2_lt__lt (f P) (f Q) (f Q) B); Cong).
      repeat split; Col.
        apply l6_13_1; Le; apply l6_2 with (f P); Between.
        intro; subst; destruct HLt2; Cong.
    }
    exists Q.
    assert (HLt2 : Lt A (f Q) A B) by (apply le1234_lt__lt with (f P) (f Q); Le).
    repeat split; Col.
      apply l6_13_1; Le; apply l6_2 with (f P); Between.
      intro; subst; destruct HLt2; Cong.
  - apply line_extension_symmetry in fLineExt.
    destruct (extension_image_density_aux Q P f archi fLineExt A B) as [X]; Between.
      apply lt_left_comm, HLt.
      apply outer_transitivity_between2 with (f P); Between.
    spliter; exists X; repeat split; Col.
Qed.

(** Given a line extension f to a line l in an Archimedean space, the image of f is dense in l *)

Lemma extension_image_density : forall {Tm: Tarski_neutral_dimensionless}
  {Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm}
  P Q (f : @Tpoint Tn -> @Tpoint Tm),
  @archimedes_axiom Tm ->
  line_extension f P Q ->
  forall A B, Col (f P) (f Q) A -> Col (f P) (f Q) B -> A <> B ->
  exists X, Col P Q X /\ Bet A (f X) B /\ f X <> A /\ f X <> B.
Proof.
  intros Tm Tm2 P Q f archi fLineExt A B HA HB HAB.
  assert (Hf' := fLineExt); destruct Hf' as [HPQ [fInj [fBet fCong]]].
  assert (f P <> f Q).
    intro; apply HPQ, fInj; Col.
  destruct (reach__ex_gradexp_lt (f P) (f Q) A B) as [fQ' [HGrad' HLt]]; auto.
  destruct (extension_gradexp P Q f fLineExt P Q fQ') as [Q' [HCol [HGrad]]]; Col.
  subst fQ'.
  apply gradexp__grad in HGrad; apply gradexp__grad in HGrad'.
  assert (HPQ' : P <> Q').
    intro; subst; apply grad112__eq in HGrad; auto.
  assert (fLineExt' : line_extension f P Q').
    apply line_extension_stability with Q; auto.
  assert (HCols : Col (f P) (f Q') A /\ Col (f P) (f Q') B /\ Col (f P) A B).
    split; [|split]; apply col_transitivity_1 with (f Q); Col.
  destruct HCols as [HA' [HB' Hdij]].
  assert (HColX : forall X, Col P Q' X -> Col P Q X).
    intros; apply col_transitivity_1 with Q'; Col.
  assert (HH : Bet (f P) A B -> exists X, Col P Q X /\ Bet A (f X) B /\ f X <> A /\ f X <> B).
  { intro HBet.
    destruct (extension_image_density_aux2 P Q' f archi fLineExt' A B) as [X]; auto.
    exists X; spliter; repeat split; auto.
  }
  assert (HH' : Bet (f P) B A -> exists X, Col P Q X /\ Bet A (f X) B /\ f X <> A /\ f X <> B).
  { intro HBet.
    destruct (extension_image_density_aux2 P Q' f archi fLineExt' B A) as [X [HX1 [HX2 []]]]; auto.
      apply lt_right_comm, HLt.
    exists X; repeat split; Between.
  }
  destruct Hdij as [|[|]].
    apply HH; trivial.
    apply HH'; Between.
  destruct (eq_dec_points (f P) A).
    subst; apply HH; Between.
  destruct (eq_dec_points (f P) B).
    subst; apply HH'; Between.
  exists P; repeat split; finish.
Qed.

Lemma dedekind__completeness : dedekind_s_axiom -> line_completeness.
Proof.
  intros dedekind Tm Tm2 P Q f archi fLineExt A HA.
  destruct (eq_dec_points (f P) A).
    subst; exists P; split; Col.
  destruct (dedekind (fun X => Col P Q X /\ Bet (f P) (f X) A)
    (fun X => Col P Q X /\ Bet (f P) A (f X))) as [B HB].
  { exists P.
    intros X Y [] [].
    apply (line_extension_reverse_bet f P Q); Col.
    eBetween.
  }
  exists B.
  assert (HR : exists R, Col P Q R /\ Bet (f P) A (f R)).
  { destruct (segment_construction (f P) A (f P) A) as [A' []].
    assert_diffs.
    destruct (extension_image_density P Q f archi fLineExt A A') as [R [HR1 [HR2 []]]]; Col.
      apply col_transitivity_1 with A; Col.
    exists R; split; eBetween.
  }
  destruct HR as [R []].
  assert (HBet : Bet P B R).
    apply HB; split; finish; eBetween.
  assert (Col P Q B).
    apply col_transitivity_1 with R; Col; intro; treat_equalities; auto.
  destruct (eq_dec_points (f B) A); [split; assumption|].
  exfalso.
  assert (Hf := fLineExt).
  destruct Hf as [HPQ [finj [fBet fCong]]].
  destruct (extension_image_density P Q f archi fLineExt A (f B)) as [X [HX1 [HX2 [HX3 Habs]]]]; auto.
    apply (pres_bet_line__col f P Q); Col.
  destruct (l5_3 (f P) A (f B) (f R)); auto; [apply fBet; Col|apply Habs..].
  - apply between_equality with (f P).
      apply between_symmetry, fBet, HB; try split; Col; Between.
      apply between_inner_transitivity with (f B); assumption.
    clear dependent R; eBetween.
  - apply between_equality with (f P).
      clear dependent R; eBetween.
    apply between_exchange3 with (f R).
      apply between_symmetry, fBet; Col; apply HB; split; Col; eBetween.
    apply bet3__bet with A (f B); finish.
Qed.

End Completeness.