Require Import GeoCoq.Tactics.Coinc.tactics_axioms.
Require Import GeoCoq.Tarski_dev.Annexes.inscribed_angle.

Section Tarski_is_a_Coinc_theory_for_concyclic.

Context `{TE:Tarski_euclidean}.

Definition not_col : arity Tpoint 3 := fun A B C : Tpoint => ~ Col A B C.

Lemma not_col_perm_1 : forall A X, app_1_n not_col A X -> app_n_1 not_col X A.
Proof. unfold not_col; simpl; Col. Qed.

Lemma not_col_perm_2 : forall A B (X : cartesianPower Tpoint 1),
  app_2_n not_col A B X -> app_2_n not_col B A X.
Proof. unfold not_col, app_2_n; simpl; Col. Qed.

Lemma concyclic_aux : forall A B C D, Concyclic A B C D -> exists O P,
  OnCircle A O P /\ OnCircle B O P /\ OnCircle C O P /\ OnCircle D O P /\ Coplanar A B C O.
Proof.
  intros A B C D [HCop [O1 [P1]]]; spliter.
  destruct (col_dec A B C).
    exists O1, P1; repeat split; Cop.
  destruct (l11_62_existence A B C O1) as [O []].
  exists O, A.
  assert (HCong := onc2__cong O1 P1).
  repeat split; [Circle|apply cong2_per2__cong with O1 O1; Cop; Cong..|assumption].
Qed.

Definition Concyclic_gen A B C D :=
  Concyclic A B C D \/ (Col A B C /\ Col A B D /\ Col A C D /\ Col B C D).

Definition concy : arity Tpoint 4 := Concyclic_gen.

Lemma concyclic_gen_2341 : forall A B C D,
  Concyclic_gen A B C D -> Concyclic_gen B C D A.
Proof.
unfold Concyclic_gen; simpl; intros A B C D H.
elim H; clear H; intro H;
[left; destruct H as [HCop [O [P]]]; split; Cop; exists O, P|right]; spliter; repeat split; Col.
Qed.

Lemma concy_perm_1 : forall (A : Tpoint) (X : cartesianPower Tpoint 3),
app_1_n concy A X -> app_n_1 concy X A.
Proof. unfold concy; simpl. intros; apply concyclic_gen_2341; auto. Qed.

Lemma concyclic_gen_2134 : forall A B C D,
  Concyclic_gen A B C D -> Concyclic_gen B A C D.
Proof.
unfold Concyclic_gen; simpl; intros A B C D H.
elim H; clear H; intro H;
[left; destruct H as [HCop [O [P]]]; split; Cop; exists O, P|right]; spliter; repeat split; Col.
Qed.

Lemma concy_perm_2 : forall (A B : Tpoint) (X : cartesianPower Tpoint 2),
app_2_n concy A B X -> app_2_n concy B A X.
Proof.
unfold app_2_n, concy; simpl; intros; apply concyclic_gen_2134; auto.
Qed.

Lemma concyclic_gen_1123 : forall A B C, Concyclic_gen A A B C.
Proof.
unfold Concyclic_gen; simpl; intros A B C.
elim (col_dec A B C); intro; [right; repeat split; Col|].
left.
split; Cop.
destruct (triangle_circumscription A B C H) as [O]; spliter.
exists O, A; unfold OnCircle; repeat split; Cong.
Qed.

Lemma concy_bd : forall (A : Tpoint) (X  : cartesianPower Tpoint 2),
app_2_n concy A A X.
Proof. unfold app_2_n, concy; simpl; intros; apply concyclic_gen_1123. Qed.

Lemma concy_trans_1 : forall P Q R A B,
  ~Col P Q R ->
  Concyclic_gen P Q R A -> Concyclic_gen P Q R B ->
  Concyclic_gen Q R A B.
Proof.
unfold Concyclic_gen; intros P Q R A B HNC H1 H2.
elim H1; clear H1; intro H1; [|spliter; exfalso; apply HNC; Col].
elim H2; clear H2; intro H2; [|spliter; exfalso; apply HNC; Col].
destruct (concyclic_aux P Q R A H1) as [O [M]].
destruct (concyclic_aux P Q R B H2) as [O' [M']].
spliter.
assert (O = O').
  apply (cong4_cop2__eq P Q R); trivial;
  [apply cong_transitivity with O M..|
   apply cong_transitivity with O' M'|apply cong_transitivity with O' M']; Cong.
subst O'.
assert (OnCircle B O M).
  apply cong_transitivity with O M'; [|apply cong_transitivity with O P]; Cong.
clear dependent M'.
destruct H1 as [HCop1 _].
destruct H2 as [HCop2 _].
left.
split.
  apply coplanar_trans_1 with P; Col; Cop.
exists O, M; repeat split; assumption.
Qed.

Lemma concyclic_gen_pseudo_trans : forall A B C D P Q R,
  ~ Col P Q R ->
  Concyclic_gen P Q R A ->
  Concyclic_gen P Q R B ->
  Concyclic_gen P Q R C ->
  Concyclic_gen P Q R D ->
  Concyclic_gen A B C D.
Proof.
intros A B C D P Q R HNC HConcy1 HConcy2 HConcy3 HConcy4.
elim (col_dec R A B); intro HRAB.

  {
  elim (col_dec R C D); intro HRCD.

    {
    elim (col_dec Q A B); intro HQAB.

      {
      elim (eq_dec_points A B); intro HAB; try (subst A; apply concyclic_gen_1123).
      assert (HPAB : ~ Col P A B) by (intro; apply HNC; ColR).
      elim (col_dec P Q A); intro HPQA.

        {
        assert (HQRB : ~ Col P Q B) by (intro; assert_diffs; apply HPAB; ColR).
        assert (HNC' : ~ Col R P Q) by Col.
        assert (H : forall A B C D, Concyclic_gen A B C D ->
                                    Concyclic_gen C A B D).
          {
          intros; apply concyclic_gen_2341; apply concyclic_gen_2134.
          do 2 apply concyclic_gen_2341; auto.
          }
        apply H in HConcy1; apply H in HConcy2.
        apply H in HConcy3; apply H in HConcy4.
        assert (HConcy5 := concy_trans_1 R P Q B A HNC' HConcy2 HConcy1).
        assert (HConcy6 := concy_trans_1 R P Q B C HNC' HConcy2 HConcy3).
        assert (HConcy7 := concy_trans_1 R P Q B D HNC' HConcy2 HConcy4).
        assert (HQPB : ~ Col Q P B) by Col.
        apply concyclic_gen_2134 in HConcy5.
        apply concyclic_gen_2134 in HConcy6.
        apply concyclic_gen_2134 in HConcy7.
        assert (HConcy8 := concy_trans_1 Q P B A C HQPB HConcy5 HConcy6).
        assert (HConcy9 := concy_trans_1 Q P B A D HQPB HConcy5 HConcy7).
        assert (HRBA : ~ Col P B A) by Col.
        assert (HConcy := concy_trans_1 P B A C D HRBA HConcy8 HConcy9).
        apply concyclic_gen_2134; auto.
        }

        {
        assert (HNC' : ~ Col R P Q) by Col.
        assert (H : forall A B C D, Concyclic_gen A B C D ->
                                    Concyclic_gen C A B D).
          {
          intros; apply concyclic_gen_2341; apply concyclic_gen_2134.
          do 2 apply concyclic_gen_2341; auto.
          }
        apply H in HConcy1; apply H in HConcy2.
        apply H in HConcy3; apply H in HConcy4.
        assert (HConcy5 := concy_trans_1 R P Q A B HNC' HConcy1 HConcy2).
        assert (HConcy6 := concy_trans_1 R P Q A C HNC' HConcy1 HConcy3).
        assert (HConcy7 := concy_trans_1 R P Q A D HNC' HConcy1 HConcy4).
        assert (HQPA : ~ Col Q P A) by Col.
        apply concyclic_gen_2134 in HConcy5.
        apply concyclic_gen_2134 in HConcy6.
        apply concyclic_gen_2134 in HConcy7.
        assert (HConcy8 := concy_trans_1 Q P A B C HQPA HConcy5 HConcy6).
        assert (HConcy9 := concy_trans_1 Q P A B D HQPA HConcy5 HConcy7).
        assert (HConcy := concy_trans_1 P A B C D HPAB HConcy8 HConcy9).
        auto.
        }
      }

      {
      elim (col_dec P Q A); intro HPQA.

        {
        assert (HPQB : ~ Col P Q B) by (intro; assert_diffs; apply HQAB; ColR).
        assert (HNC' : ~ Col R P Q) by Col.
        assert (H : forall A B C D, Concyclic_gen A B C D ->
                                    Concyclic_gen C A B D).
          {
          intros; apply concyclic_gen_2341; apply concyclic_gen_2134.
          do 2 apply concyclic_gen_2341; auto.
          }
        apply H in HConcy1; apply H in HConcy2.
        apply H in HConcy3; apply H in HConcy4.
        assert (HConcy5 := concy_trans_1 R P Q B A HNC' HConcy2 HConcy1).
        assert (HConcy6 := concy_trans_1 R P Q B C HNC' HConcy2 HConcy3).
        assert (HConcy7 := concy_trans_1 R P Q B D HNC' HConcy2 HConcy4).
        assert (HConcy8 := concy_trans_1 P Q B A C HPQB HConcy5 HConcy6).
        assert (HConcy9 := concy_trans_1 P Q B A D HPQB HConcy5 HConcy7).
        assert (HQBA : ~ Col Q B A) by Col.
        assert (HConcy := concy_trans_1 Q B A C D HQBA HConcy8 HConcy9).
        apply concyclic_gen_2134; auto.
        }

        {
        assert (HNC' : ~ Col R P Q) by Col.
        assert (H : forall A B C D, Concyclic_gen A B C D ->
                                    Concyclic_gen C A B D).
          {
          intros; apply concyclic_gen_2341; apply concyclic_gen_2134.
          do 2 apply concyclic_gen_2341; auto.
          }
        apply H in HConcy1; apply H in HConcy2.
        apply H in HConcy3; apply H in HConcy4.
        assert (HConcy5 := concy_trans_1 R P Q A B HNC' HConcy1 HConcy2).
        assert (HConcy6 := concy_trans_1 R P Q A C HNC' HConcy1 HConcy3).
        assert (HConcy7 := concy_trans_1 R P Q A D HNC' HConcy1 HConcy4).
        assert (HConcy8 := concy_trans_1 P Q A B C HPQA HConcy5 HConcy6).
        assert (HConcy9 := concy_trans_1 P Q A B D HPQA HConcy5 HConcy7).
        assert (HConcy := concy_trans_1 Q A B C D HQAB HConcy8 HConcy9).
        auto.
        }
      }
    }

    {
    elim (col_dec Q R C); intro HQRC.

      {
      assert (HQRD : ~ Col Q R D) by (intro; assert_diffs; apply HRCD; ColR).
      assert (HConcy5 := concy_trans_1 P Q R D A HNC HConcy4 HConcy1).
      assert (HConcy6 := concy_trans_1 P Q R D B HNC HConcy4 HConcy2).
      assert (HConcy7 := concy_trans_1 P Q R D C HNC HConcy4 HConcy3).
      assert (HConcy8 := concy_trans_1 Q R D C A HQRD HConcy7 HConcy5).
      assert (HConcy9 := concy_trans_1 Q R D C B HQRD HConcy7 HConcy6).
      assert (HRDC : ~ Col R D C) by Col.
      assert (HConcy := concy_trans_1 R D C A B HRDC HConcy8 HConcy9).
      do 2 apply concyclic_gen_2341; apply concyclic_gen_2134; auto.
      }

      {
      assert (HConcy5 := concy_trans_1 P Q R C A HNC HConcy3 HConcy1).
      assert (HConcy6 := concy_trans_1 P Q R C B HNC HConcy3 HConcy2).
      assert (HConcy7 := concy_trans_1 P Q R C D HNC HConcy3 HConcy4).
      assert (HConcy8 := concy_trans_1 Q R C D A HQRC HConcy7 HConcy5).
      assert (HConcy9 := concy_trans_1 Q R C D B HQRC HConcy7 HConcy6).
      assert (HConcy := concy_trans_1 R C D A B HRCD HConcy8 HConcy9).
      do 2 apply concyclic_gen_2341; auto.
      }
    }
  }

  {
  elim (col_dec Q R A); intro HQRA.

    {
    assert (HQRB : ~ Col Q R B) by (intro; assert_diffs; apply HRAB; ColR).
    assert (HConcy5 := concy_trans_1 P Q R B A HNC HConcy2 HConcy1).
    assert (HConcy6 := concy_trans_1 P Q R B C HNC HConcy2 HConcy3).
    assert (HConcy7 := concy_trans_1 P Q R B D HNC HConcy2 HConcy4).
    assert (HConcy8 := concy_trans_1 Q R B A C HQRB HConcy5 HConcy6).
    assert (HConcy9 := concy_trans_1 Q R B A D HQRB HConcy5 HConcy7).
    assert (HRBA : ~ Col R B A) by Col.
    assert (HConcy := concy_trans_1 R B A C D HRBA HConcy8 HConcy9).
    apply concyclic_gen_2134; auto.
    }

    {
    assert (HConcy5 := concy_trans_1 P Q R A B HNC HConcy1 HConcy2).
    assert (HConcy6 := concy_trans_1 P Q R A C HNC HConcy1 HConcy3).
    assert (HConcy7 := concy_trans_1 P Q R A D HNC HConcy1 HConcy4).
    assert (HConcy8 := concy_trans_1 Q R A B C HQRA HConcy5 HConcy6).
    assert (HConcy9 := concy_trans_1 Q R A B D HQRA HConcy5 HConcy7).
    assert (HConcy := concy_trans_1 R A B C D HRAB HConcy8 HConcy9).
    auto.
    }
  }
Qed.

Lemma concy_3 :
  forall (CONCY : cartesianPower Tpoint 4) (NOT_COL : cartesianPower Tpoint 3),
  pred_conj concy CONCY NOT_COL -> app not_col NOT_COL -> app concy CONCY.
Proof.
unfold pred_conj, app_2_n, concy; simpl.
intros CONCY NOT_COL HConcy HNot_Col.
destruct HConcy as [HConcy1 [HConcy2 [HConcy3 HConcy4]]].
apply concyclic_gen_pseudo_trans with (fst NOT_COL) (fst (snd NOT_COL)) (snd (snd NOT_COL)); try apply concyclic_gen_2341; auto.
Qed.

Global Instance Tarski_is_a_Coinc_theory_for_concy : (Coinc_theory (Build_Arity Tpoint 1) (Build_Coinc_predicates (Build_Arity Tpoint 1) not_col concy)).
Proof.
exact (Build_Coinc_theory (Build_Arity Tpoint 1) (Build_Coinc_predicates (Build_Arity Tpoint 1) not_col concy) not_col_perm_1 not_col_perm_2 concy_perm_1 concy_perm_2 concy_bd concy_3).
Qed.

End Tarski_is_a_Coinc_theory_for_concyclic.
