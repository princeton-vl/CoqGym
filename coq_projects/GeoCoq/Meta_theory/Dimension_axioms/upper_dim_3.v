Require Export GeoCoq.Tarski_dev.Ch11_angles.
Require Import GeoCoq.Utils.all_equiv.

Section Upper_dim_3.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** In this file, we prove that all the following properties are equivalent. *)

(** If three points A, B and C are equidistant to three distinct points P, Q and R,
    then A, B and C are collinear. *)

Definition upper_dim_3_axiom := forall A B C P Q R,
  P <> Q -> Q <> R -> P <> R ->
  Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
  Cong A P A R -> Cong B P B R -> Cong C P C R ->
  (Bet A B C \/ Bet B C A \/ Bet C A B).

(** If four points are equidistant to two distinct points, then they are coplanar. *)

Definition median_planes_axiom := forall A B C D P Q, P <> Q ->
  Cong A P A Q -> Cong B P B Q -> Cong C P C Q -> Cong D P D Q ->
  Coplanar A B C D.

(** If two planes meet in some point, then they also meet in another point. *)

Definition plane_intersection_axiom := forall A B C D E F P,
  Coplanar A B C P -> Coplanar D E F P ->
  exists Q, Coplanar A B C Q /\ Coplanar D E F Q /\ P <> Q.

(** If two points do not lie on a plane, then they are either
    on opposite sides or on the same side of the plane. *)

Definition space_separation_axiom := forall A B C P Q,
  ~ Coplanar A B C P -> ~ Coplanar A B C Q -> TSP A B C P Q \/ OSP A B C P Q.

(** The line segments SU1, SU2, SU3 and SU4 can not form an orthonormal family *)

Definition orthonormal_family_axiom := forall S U1' U1 U2 U3 U4,
  ~ (S <> U1' /\ Bet U1 S U1' /\
     Cong S U1 S U1' /\ Cong S U2 S U1' /\ Cong S U3 S U1' /\ Cong S U4 S U1' /\
     Cong U1 U2 U1' U2 /\ Cong U1 U3 U1' U2 /\ Cong U1 U4 U1' U2 /\
     Cong U2 U3 U1' U2 /\ Cong U2 U4 U1' U2 /\ Cong U3 U4 U1' U2).


Lemma upper_dim_3_stab : ~ ~ upper_dim_3_axiom -> upper_dim_3_axiom.
Proof.
  intros nnupper A B C P Q R; intros.
  destruct (col_dec A B C) as [|HNCol]; auto.
  exfalso.
  apply nnupper.
  intro upper.
  apply HNCol.
  apply upper with P Q R; auto.
Qed.

Lemma median_planes_implies_upper_dim : median_planes_axiom -> upper_dim_3_axiom.
Proof.
  intros mp A B C P Q R HPQ HQR HPR; intros.
  destruct (col_dec A B C); trivial.
  exfalso.
  apply HQR.
  destruct (midpoint_existence P Q) as [X].
  apply symmetric_point_uniqueness with P X; trivial.
  destruct (midpoint_existence P R) as [Y].
  replace X with Y; trivial.
  apply (l8_7 P); apply l8_2.
  - apply l11_60 with A B C; [|exists R; split..|]; trivial.
    apply mp with P Q; Cong.
  - apply l11_60 with A B C; [|exists Q; split..|]; trivial.
    apply mp with P R; Cong.
Qed.

Lemma median_planes_aux :
  (forall A B C P Q M, P <> Q -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q -> Midpoint M P Q ->
                       Coplanar M A B C) ->
  median_planes_axiom.
Proof.
  intros Haux A B C D P Q; intros.
  destruct (col_dec A B C) as [HCop|]; [apply col__coplanar, HCop|].
  destruct (midpoint_existence P Q) as [M].
  destruct (ex_ncol_cop2 A B C M) as [A1 [A2 [HCop1 [HCop2 HNCol1]]]].
  assert (Cong A1 P A1 Q) by (apply (l11_60_aux A B C); assumption).
  assert (Cong A2 P A2 Q) by (apply (l11_60_aux A B C); assumption).
  apply coplanar_pseudo_trans with M A1 A2; eauto.
Qed.

Lemma orthonormal_family_aux : orthonormal_family_axiom <->
  (forall A B X P Q, ~ Col P Q X -> Per A X P -> Per A X Q -> Per B X P -> Per B X Q -> Col A B X).
Proof.
  split.
  - intros up A B X P Q HNCol HAXP HAXQ HBXP HBXQ.
    destruct (col_dec A B X) as [|HNCol1]; [assumption|].
    exfalso.
    destruct (segment_construction P X P X) as [P' []].
    assert_diffs.
    destruct (ex_per_cong P X X Q P' X) as [Q']; Col; spliter.
    assert (HAXQ' : Per Q' X A) by (apply (l11_60 P Q X); Perp; Cop).
    assert (HBXQ' : Per Q' X B) by (apply (l11_60 P Q X); Perp; Cop).
    assert (HNCol' : ~ Col P X Q') by (apply one_side_not_col123 with Q; assumption).
    clear dependent Q.
    rename Q' into Q.
    destruct (segment_construction A X P' X) as [A' []].
    assert (HAXP' : Per P X A') by (assert_diffs; apply per_col with A; Perp; Col).
    assert (HAXQ : Per Q X A') by (assert_diffs; apply per_col with A; Perp; Col).
    assert (HNCol : ~ Col A' B X) by (intro; apply HNCol1; ColR).
    clear dependent A.
    rename A' into A.
    destruct (ex_per_cong A X X B P' X) as [B']; Col; [assert_diffs; auto|].
    spliter.
    assert (HBXP' : Per B' X P) by (apply (l11_60 A B X); Perp; Cop).
    assert (HBXQ : Per B' X Q) by (apply (l11_60 A B X); Perp; Cop).
    clear dependent B.
    rename B' into B.
    assert (HCong : Cong Q P Q P') by (apply per_double_cong with X; [|split]; Cong).
    apply (up X P' P Q A B); repeat split; [Cong..| | | | |];
      (apply cong_transitivity with P Q; [|Cong]);
      apply l10_12 with X X; Perp; eCong.
  - intros p4col S U1' U1 U2 U3 U4 H; spliter.
    assert (HMid : Midpoint S U1 U1') by (split; Cong).
    assert (HPer21 : Per U2 S U1) by (exists U1'; split; Cong).
    absurd (Col U2 U1 S).
      assert_diffs; apply not_col_permutation_5, per_not_col; auto.
    apply p4col with U3 U4;
      [assert_diffs; apply not_col_permutation_2, per_not_col; auto|..];
      apply (l8_10 U2 S U1); trivial; repeat split; eCong.
Qed.

Lemma upper_dim_implies_orthonormal_family_axiom : upper_dim_3_axiom -> orthonormal_family_axiom.
Proof.
  rewrite orthonormal_family_aux.
  intros up A B X P Q HNCol HAXP HAXQ HBXP HBXQ.
  destruct (segment_construction Q X X P) as [Q' []].
  assert (HNCol' : ~ Col P Q' X) by (intro; apply HNCol; ColR).
  assert (HAXQ' : Per A X Q') by (assert_diffs; apply per_col with Q; Col).
  assert (HBXQ' : Per B X Q') by (assert_diffs; apply per_col with Q; Col).
  clear dependent Q.
  destruct (symmetric_point_construction P X) as [R].
  assert_diffs.
  apply up with P Q' R.
    auto.
    intro; subst; apply HNCol'; Col.
    auto.
    apply l10_12 with X X; Cong.
    apply l10_12 with X X; Cong.
    Cong.
    apply per_double_cong with X; assumption.
    apply per_double_cong with X; assumption.
    Cong.
Qed.

Lemma orthonormal_family_axiom_implies_orth_at2__col :
  orthonormal_family_axiom ->
  (forall A B C P Q X, Orth_at X A B C X P -> Orth_at X A B C X Q -> Col P Q X).
Proof.
  rewrite orthonormal_family_aux.
  intros up A B C P Q X HP HQ.
  apply orth_at_chara in HP.
  apply orth_at_chara in HQ.
  spliter; clean.
  destruct (ex_ncol_cop2 A B C X) as [D [E [HD [HE HNCol]]]].
  apply up with D E; [Col|apply l8_2..]; auto.
Qed.

Lemma orthonormal_family_axiom_implies_not_two_sides_one_side :
  orthonormal_family_axiom ->
  (forall A B C X Y, ~ Coplanar A B C X -> ~ Coplanar A B C Y -> ~ TSP A B C X Y -> OSP A B C X Y).
Proof.
  intros up A B C X Y HX HY HNTS.
  destruct (l11_62_existence_bis A B C X HX) as [P HOrth].
  assert (HOrth1 := HOrth).
  apply orth_at_chara in HOrth1.
  destruct HOrth1 as [HNCol [HPX [HP HOrth1]]].
  destruct (l8_21_3 A B C P Y HP HY) as [X' [T [HOrth' [HT HBet]]]].
  apply (col_cop_orth__orth_at _ _ _ _ _ P) in HOrth'; Col.
  assert (~ Coplanar A B C X') by (apply orth_at__ncop with P, HOrth').
  assert (HTS : TSP A B C Y X').
    repeat split; trivial; exists T; split; assumption.
  exists X'; split; [|assumption].
  repeat split; trivial.
  exists P; split; [assumption|].
  apply not_out_bet.
    apply col_permutation_1, (orthonormal_family_axiom_implies_orth_at2__col up A B C); assumption.
  intro; apply HNTS.
  apply l9_41_2 with X'.
    apply l9_38, HTS.
  apply osp_symmetry, cop_out__osp with P; assumption.
Qed.

Lemma orthonormal_family_axiom_implies_space_separation :
  orthonormal_family_axiom -> space_separation_axiom.
Proof.
  intros up A B C X Y HX HY.
  destruct (tsp_dec A B C X Y).
    left; assumption.
    right; apply (orthonormal_family_axiom_implies_not_two_sides_one_side up); assumption.
Qed.

Lemma space_separation_implies_plane_intersection : space_separation_axiom -> plane_intersection_axiom.
Proof.
  intro sep.
  assert (Haux : forall A B C D E P, Coplanar A B C P -> ~ Col D E P ->
    exists Q, Coplanar A B C Q /\ Coplanar D E P Q /\ P <> Q).
  { intros A B C D E P HP1 HP2.
    destruct (cop_dec A B C D).
      assert_diffs; exists D; repeat split; Cop.
    destruct (cop_dec A B C E).
      assert_diffs; exists E; repeat split; Cop.
    destruct (sep A B C D E); auto.
      apply cop_tsp__ex_cop2; assumption.
      apply cop_osp__ex_cop2; assumption.
  }
  intros A B C D E F P HP1 HP2.
  destruct (ex_ncol_cop2 D E F P) as [D' [E']].
  spliter.
  destruct (Haux A B C D' E' P) as [Q [HQ1 [HQ2 HPQ]]]; Col.
  exists Q.
  repeat split; auto.
  destruct (col_dec D E F) as [HCol|]; [apply col__coplanar, HCol|].
  apply coplanar_pseudo_trans with D' E' P; Col; apply coplanar_pseudo_trans with D E F; Cop.
Qed.

Lemma plane_intersection_implies_space_separation :
  plane_intersection_axiom -> space_separation_axiom.
Proof.
  intros pint A B C X Y HX HY.
  assert (HA : Coplanar A B C A) by Cop.
  destruct (pint A B C A X Y A HA) as [D [HD1 [HD2 HAD]]]; Cop.
  destruct (cop__one_or_two_sides A D X Y).
    Cop.
    intro; apply HX, col_cop2__cop with A D; Col.
    intro; apply HY, col_cop2__cop with A D; Col.
    left; apply cop2_ts__tsp with A D; assumption.
    right; apply cop2_os__osp with A D; assumption.
Qed.

Lemma space_separation_implies_median_planes : space_separation_axiom -> median_planes_axiom.
Proof.
  intro sep.
  apply median_planes_aux.
  intros A B.
  assert (Haux : forall X P Q M, P <> Q ->
          Cong A P A Q -> Cong B P B Q -> Midpoint M P Q -> TSP M A B Q X -> Cong X P X Q -> False).
  { intros X P Q M HPQ HA HB HM [HQ [HX [T [HT HBet]]]].
    assert (HCong : forall C, Coplanar M A B C -> Cong C P C Q).
      intros; apply (l11_60_aux M A B); Cong; apply ncop__ncol with Q, HQ.
    apply triangle_strict_inequality with T; Between.
    intro.
    apply (not_bet_and_out P M Q); split; [Between|].
    assert (~ Coplanar M A B P) by (intro HP; apply HCong in HP; treat_equalities; auto).
    assert_all_diffs_by_contradiction.
    replace M with T.
      apply l6_2 with X; Between.
    apply (col2_cop2__eq M A B P Q); Cop; ColR.
  }
  intros C P Q M HPQ HA HB HC HM.
  destruct (cop_dec M A B C) as [HCop|HNCop]; [apply HCop|].
  assert (~ Col M A B) by (apply ncop__ncol with C, HNCop).
  assert (HQ : ~ Coplanar M A B Q).
    intro Ha; apply (l11_60_aux _ _ _ _ P Q) in Ha; Cong; treat_equalities; auto.
  exfalso.
  destruct (sep M A B Q C HQ HNCop).
    eauto.
  apply l7_2 in HM.
  apply (Haux C Q P M); Cong.
  apply l9_38, l9_41_2 with Q; [|assumption].
  repeat split; trivial.
    intro Ha; apply (l11_60_aux _ _ _ _ P Q) in Ha; Cong; treat_equalities; auto.
  exists M; split; Between; Cop.
Qed.

Theorem upper_dim_3_equivalent_axioms : all_equiv (upper_dim_3_axiom::
                                                   orthonormal_family_axiom::
                                                   space_separation_axiom::
                                                   plane_intersection_axiom::
                                                   median_planes_axiom::
                                                   nil).
Proof.
  assert (H := upper_dim_implies_orthonormal_family_axiom).
  assert (I := orthonormal_family_axiom_implies_space_separation).
  assert (J := space_separation_implies_plane_intersection).
  assert (K := plane_intersection_implies_space_separation).
  assert (L := space_separation_implies_median_planes).
  assert (M := median_planes_implies_upper_dim).
  apply all_equiv__equiv; unfold all_equiv'; simpl; repeat split; tauto.
Qed.

End Upper_dim_3.