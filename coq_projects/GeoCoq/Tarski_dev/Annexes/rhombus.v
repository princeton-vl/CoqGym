(* Roland Coghetto, 29 March 2018, 
                    04 April 2018.
   GNU Lesser General Public License v3.0 
   See LICENSE GeoCoq 2.3.0
     
     MOTIVATION: 
     
      - Existence of a rhombus (absolute geometry).
      - Unicity of rhomus with 3 points determinated (absolute geometry).
      
     TODO:
     
      29 march 2018 - In Euclidean geometry, construction of a rhombus from 3 determined points. DONE
                    - What about rhombus in non-euclidean geometry case ?
      04 april 2018 - MOVE all "Plg"'s lemma in quadrialterals.v 
                       (after modify context Tarski_2D by 
                          Tarski_neutral_dimensionless_with_decidable_point_equality 
                          in quadrilaterals.v) ?
                    - MOVE all "rhombus"'s lemma in quadrilaterals.v
                       (after modify context Tarski_2D by 
                          Tarski_neutral_dimensionless_with_decidable_point_equality 
                          in quadrilaterals.v) ?
                    - DELETE rhombus.v
                    - EXPERIMENTAL: (in quadrilaterals_inter_dec.v)
                        Lemma rmb_cong :
                          forall A B C D,
                          Rhombus A B C D ->
                          Cong A B B C /\ Cong A B C D /\ Cong A B D A.
                        TRY MODIFY CONTEXT ? Tarski_2D_euclidean -> Tarski_2D or Tarski_neutral_dimensionless_with_decidable_point_equality

   CHANGES: 04 april 2018, RC
   1) See JNarboux, comments about pull requests Rhombus.
   2) ADD End Rhombus_Existence_Unicity.
   2) MODIFY CONTEXT: Tarski_2D by Tarski_neutral_dimensionless_with_decidable_point_equality.
   3) ADD Existence Plg, Rhombus.

*)

Require Export GeoCoq.Tarski_dev.Annexes.perp_bisect.

Section Rhombus_Existence_Unicity.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma PlgLeft: forall A B C D, Plg A B C D -> (A <> C \/ B <> D).
Proof.
  intros.
  unfold Plg in H. spliter.
assumption.
Qed.

Lemma PlgEquivDef: forall A B C D, (A <> C \/ B <> D) -> ((exists M,
OnCircle C M A /\ OnCircle D M B /\ Bet C M A /\ Bet D M B) <-> Plg A B C D).
Proof.
  intros.
  split.
  - intros.
    unfold OnCircle in *.
    split. 
    assumption.
    ex_and H0 M.
    exists M.
    split.
    { unfold Midpoint.
      split;Between. 
      Cong. 
    }
    { unfold Midpoint in *.
      split;Between. 
      Cong.
    }
  - intros.
    unfold OnCircle in *.
    ex_and H0 M.
    ex_and H1 M1.
    unfold Midpoint in *.
    exists M1.
    split;Cong.
    split;[Cong|Between].
Qed.

Lemma PlgAABB: forall A B, A <> B -> Plg A A B B.
Proof.
  intros.
  unfold Plg.
  split;auto.
  midpoint M A B.
  exists M.
  split;auto.
Qed.

Lemma PlgEx: exists A B C D, Plg A B C D.
Proof.
  destruct two_distinct_points as [A [B H]].
  exists A, A, B, B.
  apply PlgAABB.
  assumption.
Qed.

Lemma RhombusEx: exists A B C D, Rhombus A B C D.
Proof.
  destruct lower_dim_ex as [A [B [C HNC]]].
  assert (H1 : ~ Col A B C) by auto.
  clear HNC.
  assert_diffs.
  assert (HAB := perp_bisect_existence A B);
  destruct HAB as [C1 [C2 HAB]]; try (assert_diffs; assumption).
  assert(Cong A C1 B C1).
  apply perp_bisect_cong_2 with C2.
  apply perp_bisect_sym_1.
  assumption.
  unfold Perp_bisect in HAB.
  spliter.
  unfold ReflectL in *.
  spliter.
  destruct H0 as [M H0];
  spliter.
  assert(H10 := H).
  unfold Midpoint in H10.
  spliter.
  assert (exists x, Bet C1 M x /\ Cong M x C1 M) by (apply segment_construction).
  ex_and H8 x.
  exists A.
  exists C1.
  exists B.
  exists x.
  assert(Plg A C1 B x).
  unfold Plg.
  split.
  tauto.
  exists M.
  split.
  apply l7_2;assumption.
  unfold Midpoint.
  split.
  assumption.
  Cong.
  unfold Rhombus.
  split.
  assumption.
  Cong.
Qed.

Lemma RhombusUnicity: forall A B C D E, Rhombus A B C D -> Rhombus A B C E -> D = E.
Proof.
  intros.
  unfold Rhombus in *.
  spliter.
  unfold Plg in *.
  spliter.
  ex_and H4 M.
  ex_and H3 N.
  assert (M = N). 
  apply l7_17 with A C;assumption.
  subst.
  apply symmetric_point_uniqueness with B N;assumption.
Qed.

Lemma ColCongMid: forall A B C, A <> C -> Col A B C -> Cong A B B C -> Midpoint B A C.
Proof.
  intros.
  assert(Col A B C). Col.
  assert(Cong B A B C). Cong.
  assert(A = C \/ Midpoint B A C).
  apply l7_20; tauto. 
  tauto.
Qed.

Lemma PlgExABC1: forall A B C, A <> C -> Col A B C -> Cong A B B C -> exists D, Plg A B C D.
Proof.
  intros.
  unfold Col in H0.
  assert(Midpoint B A C).
  apply ColCongMid;
  trivial.
  exists B.
  unfold Plg in *.
  split.
  tauto.
  exists B.
  split.
  trivial.
  Midpoint.
Qed.

Lemma PlgExABC2: forall A B C, ~Col A B C -> Cong A B B C -> exists D, Plg A B C D.
Proof.
  intros A B C HC H.
  unfold Plg in *.
  assert(Is_on_perp_bisect B A C). exact H.
  destruct (midpoint_existence A B) as [X H1].
  destruct (l10_2_existence A C B) as [D H3].
  unfold Reflect in H3.
  unfold ReflectL in H3.
  induction (eq_dec_points A C).
  case H3.
    - intros. tauto.
    - intros.
      unfold Midpoint in H4.
      destruct (midpoint_existence A C) as [Y H5].
      destruct (symmetric_point_construction B Y) as [E H6].
      exists E.
      assert(B <> E).
      induction (eq_dec_points B E).
      subst E.
      assert(Y = B).
      apply l7_3. exact H6.
      subst Y.
      assert(Col A B C). Col. tauto. tauto. 
      split. tauto.
      exists Y.
      tauto.
    - intros.
      destruct H3.
      destruct H3;destruct H4;destruct H4.
      destruct H4.
      unfold Midpoint in H4.
      destruct (midpoint_existence A C) as [Y H7].
      destruct (symmetric_point_construction B Y) as [E H8].
      exists E.
      assert(B <> E).
      induction (eq_dec_points B E).
      subst E.
      assert(Y = B).
      apply l7_3. exact H8.
      subst Y.
      assert(Col A B C). Col. tauto. tauto. 
      split. tauto.
      exists Y.
      tauto.
      exists D.
      split.
      tauto.
      exists A.
      tauto.
Qed.

Lemma RhombusExABC1: forall A B C, A <> C -> Col A B C -> Cong A B B C -> exists D, Rhombus A B C D.
Proof.
  intros.
  assert(Midpoint B A C).
  apply ColCongMid; tauto.
  exists B.
  unfold Rhombus in *.
  split.
  unfold Plg in *.
  split.
  tauto.
  exists B.
  split. 
  assumption. 
  Midpoint. 
  assumption.
Qed.

Lemma RhombusExABC2: forall A B C, ~Col A B C -> Cong A B B C -> exists D, Rhombus A B C D.
Proof.
  intros.
  assert(exists D, Plg A B C D).
  apply PlgExABC2;trivial.
  destruct H1 as [D H2].
  exists D.
  unfold Rhombus in *.
  tauto.
Qed.

End Rhombus_Existence_Unicity.


