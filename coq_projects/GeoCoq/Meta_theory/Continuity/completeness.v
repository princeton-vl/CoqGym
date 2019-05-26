Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Meta_theory.Dimension_axioms.upper_dim_2.
Require Import GeoCoq.Meta_theory.Dimension_axioms.upper_dim_3.
Require Import GeoCoq.Tarski_dev.Ch10_line_reflexivity_2.

(** This development is inspired by Theorem 32 of Hilbert's Foundations of Geometry (10th edition).
    It deduces completeness of a 2 or 3-dimensional space from completeness of lines.
    The original proof is due to Paul Bernays. *)

Section Completeness.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma extension__line_extension : forall {Tm: Tarski_neutral_dimensionless}
  (f : @Tpoint Tn -> @Tpoint Tm) P Q,
  P <> Q -> extension f -> line_extension f P Q.
Proof.
  unfold extension, inj, pres_bet, pres_cong, line_extension, inj_line, pres_bet_line, pres_cong_line.
  intros Tm f P Q HPQ fext; spliter.
  repeat split; auto.
Qed.

Lemma extension_reverse_bet : forall {Tm: Tarski_neutral_dimensionless}
  {Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm}
  (f : @Tpoint Tn -> @Tpoint Tm),
  extension f ->
  forall A B C, Bet (f A) (f B) (f C) -> Bet A B C.
Proof.
  intros Tm Tm2 f [finj [fBet fCong]] A B C HBet.
  destruct (eq_dec_points (f A) (f B)) as [Heq|].
    apply finj in Heq; subst; Between.
  destruct (segment_construction A B B C) as [D [HD1 HD2]].
  assert (C = D); [|subst; auto].
  apply finj.
  apply between_cong_3 with (f A) (f B); Cong.
Qed.

Lemma extension_reverse_col : forall {Tm: Tarski_neutral_dimensionless}
  {Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm}
  (f : @Tpoint Tn -> @Tpoint Tm),
  extension f ->
  forall A B C, Col (f A) (f B) (f C) -> Col A B C.
Proof.
  unfold Col.
  intros Tm Tm2 f fext A B C HCol.
  assert (fBetInv := extension_reverse_bet f fext).
  destruct HCol as [|[|]]; auto.
Qed.


Lemma line_completeness_aux : line_completeness ->
  forall (Tm: Tarski_neutral_dimensionless)
  (Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm)
  (f : @Tpoint Tn -> @Tpoint Tm),
  @archimedes_axiom Tm ->
  extension f ->
  forall A P Q R, ~ Col P Q R -> Coplanar (f P) (f Q) (f R) A ->
    exists B, Coplanar P Q R B /\ f B = A.
Proof.
  intros lc Tm Tm2 f archi fext A P Q R HNCol HCop.
  assert (fext' := fext).
  assert (Haux : forall X Y, X <> Y -> line_extension f X Y).
    intros; apply extension__line_extension; assumption.
  unfold extension, inj, pres_bet, pres_cong in fext'; spliter.
  destruct (@midpoint_existence Tn TnEQD P Q) as [S HS].
  assert_diffs.
  destruct (col_dec (f R) (f S) A).
  { assert (HB : exists B, Col R S B /\ f B = A).
      assert (R <> S) by (intro; subst; apply HNCol; Col).
      apply lc; auto.
    destruct HB as [B []].
    exists B; split; [exists S; left; split|]; Col.
  }
  destruct (col_dec (f P) (f Q) A).
  { assert (HB : exists B, Col P Q B /\ f B = A) by (apply lc; auto).
    destruct HB as [B []].
    exists B; split; Cop.
  }
  destruct (hilbert_s_version_of_pasch (f P) (f Q) (f R) A (f S)) as [X [HX1 HX2]]; trivial.
    repeat split; Between.
  assert (HY : exists Y, Coplanar P Q R Y /\ f Y = X).
  { destruct HX2 as [[]|[]];
      [assert (HY : exists Y, Col P R Y /\ f Y = X)|assert (HY : exists Y, Col Q R Y /\ f Y = X)];
      try apply lc; Col;
      destruct HY as [Y []]; exists Y; split; Cop.
  }
  destruct HY as [Y []].
  subst X.
  assert (S <> Y).
  { intro; treat_equalities.
    apply HNCol.
    apply (extension_reverse_col f); auto.
    assert (Bet P S Q) by Between.
    assert (Bet (f P) (f S) (f Q)) by auto.
    destruct HX2 as [[HBet []]|[HBet []]];
      [|apply col_permutation_4]; apply (col_transitivity_2 (f S)); Col.
  }
  assert (HB : exists B, Col S Y B /\ f B = A) by (apply lc; Col).
  destruct HB as [B []].
  exists B.
  split; [apply col_cop2__cop with S Y|]; Cop.
Qed.

Lemma line_completeness__completeness_for_planes : line_completeness -> completeness_for_planes.
Proof.
  intros lc Tm Tm2 M f archi fext A.
  assert (HB : exists B, Coplanar PA PB PC B /\ f B = A).
    apply line_completeness_aux; trivial; [exact lower_dim|apply all_coplanar].
  destruct HB as [B []].
  exists B; assumption.
Qed.

Lemma completeness_aux : forall {Tm: Tarski_neutral_dimensionless}
  P Q R (f : @Tpoint Tn -> @Tpoint Tm) A,
  (exists B, Coplanar P Q R B /\ f B = A) -> exists B, f B = A.
Proof.
  intros Tm P Q R f A [B []].
  exists B; assumption.
Qed.

Lemma line_completeness__completeness_for_3d_spaces :
  (exists P Q R S, ~ Coplanar P Q R S) ->
  line_completeness -> completeness_for_3d_spaces.
Proof.
  intros [P [Q [R [S HNCop]]]] lc Tm Tm2 M f archi fext A.
  assert (~ Col P Q R) . apply ncop__ncol with S, HNCop.
  destruct (col_dec (f P) (f Q) A).
    apply (completeness_aux P Q R), line_completeness_aux; Cop.
  assert (pi : plane_intersection_axiom).
  { cut upper_dim_3_axiom.
      apply upper_dim_3_equivalent_axioms; simpl; tauto.
    unfold upper_dim_3_axiom; exact upper_dim_3.
  }
  destruct (pi (f P) (f Q) A (f P) (f R) (f S) (f P)) as [X [HX1 [HX2 HX3]]]; Cop.
  assert (HY : exists Y, Coplanar P R S Y /\ f Y = X).
    apply line_completeness_aux; trivial; apply ncop__ncol with Q; Cop.
  destruct HY as [Y []]; subst.
  apply completeness_aux with P Q Y, line_completeness_aux; Cop.
  intro.
  apply HNCop.
  apply coplanar_perm_16, col_cop__cop with Y; Col; Cop.
  intro; subst; apply HX3; reflexivity.
Qed.

End Completeness.

(** In the following sections, we prove that our formalizations of Hilbert's axiom of completeness
    are always true in spaces with dimension respectively greater than 2 and 3. *)

Section Dimension.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma extension_to_plane__plane : forall {Tm: Tarski_neutral_dimensionless}
  {Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm}
  {M : Tarski_2D Tm2}
  (f : @Tpoint Tn -> @Tpoint Tm),
  extension f ->
  @upper_dim_axiom Tn.
Proof.
  intros Tm Tm2 M f fext A B C P Q HPQ H1 H2 H3.
  apply (extension_reverse_col f); trivial.
  unfold extension, inj, pres_cong in fext; spliter.
  unfold Col; apply upper_dim with (f P) (f Q); auto.
Qed.

Lemma nupper_dim__completeness_for_planes : ~ upper_dim_axiom -> completeness_for_planes.
Proof.
  intros lowerdim Tm Tm2 M f archi fext A.
  exfalso; apply lowerdim.
  apply extension_to_plane__plane with f; trivial.
Qed.

Lemma extension_to_3d__upper_dim_3 : forall {Tm: Tarski_neutral_dimensionless}
  {Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm}
  {M : Tarski_3D Tm2}
  (f : @Tpoint Tn -> @Tpoint Tm),
  extension f ->
  @upper_dim_3_axiom Tn.
Proof.
  intros Tm Tm2 M f fext A B C P Q R; intros.
  apply (extension_reverse_col f); trivial.
  unfold extension, inj, pres_cong in fext; spliter.
  unfold Col; apply upper_dim_3 with (f P) (f Q) (f R); auto.
Qed.

Lemma nupper_dim_3__completeness_for_3d_spaces : ~ upper_dim_3_axiom -> completeness_for_3d_spaces.
Proof.
  intros lowerdim Tm Tm2 M f archi fext A.
  exfalso; apply lowerdim.
  apply extension_to_3d__upper_dim_3 with f; trivial.
Qed.

End Dimension.


Section Dimension'.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma ncompleteness_for_planes__upper_dim : ~ completeness_for_planes -> upper_dim_axiom.
Proof.
  intro nc.
  apply upper_dim_stab.
  intro nupper.
  apply nc, (nupper_dim__completeness_for_planes nupper).
Qed.

Lemma ncompleteness_for_3d_spaces__upper_dim_3 : ~ completeness_for_3d_spaces -> upper_dim_3_axiom.
Proof.
  intro nc.
  apply upper_dim_3_stab.
  intro nupper.
  apply nc, (nupper_dim_3__completeness_for_3d_spaces nupper).
Qed.

End Dimension'.