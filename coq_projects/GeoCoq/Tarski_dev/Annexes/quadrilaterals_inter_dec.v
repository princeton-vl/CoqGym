Require Export GeoCoq.Tarski_dev.Ch12_parallel_inter_dec.
Require Export GeoCoq.Tarski_dev.Annexes.Tagged_predicates.

Ltac image_6 A B P' H P:=
 let T:= fresh in assert (T:= l10_6_existence A B P' H);
 ex_and T P.

Ltac image A B P P':=
 let T:= fresh in assert (T:= l10_2_existence A B P);
 ex_and T P'.

Ltac perp A B C X :=
 match goal with
   | H:(~Col A B C) |- _ =>
    let T:= fresh in assert (T:= l8_18_existence A B C H);
    ex_and T X
 end.

Ltac parallel A B C D P :=
 match goal with
   | H:(A <> B) |- _ =>
    let T := fresh in assert(T:= parallel_existence A B P H);
    ex_and T C
 end.

Ltac par_strict :=
repeat
 match goal with
      | H: Par_strict ?A ?B ?C ?D |- _ =>
       let T := fresh in not_exist_hyp (Par_strict B A D C); assert (T := par_strict_comm A B C D H)  
      | H: Par_strict ?A ?B ?C ?D |- _ =>
       let T := fresh in not_exist_hyp (Par_strict C D A B); assert (T := par_strict_symmetry A B C D H)  
      | H: Par_strict ?A ?B ?C ?D |- _ =>
       let T := fresh in not_exist_hyp (Par_strict B A C D); assert (T := par_strict_left_comm A B C D H)   
      | H: Par_strict ?A ?B ?C ?D |- _ =>
       let T := fresh in not_exist_hyp (Par_strict A B D C); assert (T := par_strict_right_comm A B C D H) 
 end.

Ltac clean_trivial_hyps :=
  repeat
  match goal with
   | H:(Cong ?X1 ?X1 ?X2 ?X2) |- _ => clear H
   | H:(Cong ?X1 ?X2 ?X2 ?X1) |- _ => clear H
   | H:(Cong ?X1 ?X2 ?X1 ?X2) |- _ => clear H
   | H:(Bet ?X1 ?X1 ?X2) |- _ => clear H
   | H:(Bet ?X2 ?X1 ?X1) |- _ => clear H
   | H:(Col ?X1 ?X1 ?X2) |- _ => clear H
   | H:(Col ?X2 ?X1 ?X1) |- _ => clear H
   | H:(Col ?X1 ?X2 ?X1) |- _ => clear H
   | H:(Par ?X1 ?X2 ?X1 ?X2) |- _ => clear H
   | H:(Par ?X1 ?X2 ?X2 ?X1) |- _ => clear H
   | H:(Per ?X1 ?X2 ?X2)     |- _ => clear H
   | H:(Per ?X1 ?X1 ?X2)     |- _ => clear H
   | H:(Midpoint ?X1 ?X1 ?X1) |- _ => clear H
end.

Ltac show_distinct2 := unfold not;intro;treat_equalities; try (solve [intuition]).

Ltac symmetric A B A' :=
 let T := fresh in assert(T:= symmetric_point_construction A B);
 ex_and T A'.

Tactic Notation "Name" ident(X) "the" "symmetric" "of" ident(A) "wrt" ident(C) :=
 symmetric A C X.

Ltac sfinish := repeat match goal with
 | |- Bet ?A ?B ?C => Between; eBetween
 | |- Col ?A ?B ?C => Col;ColR
 | |- ~ Col ?A ?B ?C => Col
 | |- ~ Col ?A ?B ?C => intro;search_contradiction
 | |- Par ?A ?B ?C ?D => Par
 | |- Par_strict ?A ?B ?C ?D => Par
 | |- Perp ?A ?B ?C ?D => Perp
 | |- Perp_at ?A ?B ?C ?D ?E => Perp
 | |- Per ?A ?B ?C => Perp
 | |- Cong ?A ?B ?C ?D => Cong;eCong
 | |- Midpoint ?A ?B ?C => Midpoint
 | |- ?A<>?B => apply swap_diff;assumption
 | |- ?A<>?B => intro;treat_equalities; solve [search_contradiction]
 | |- ?G1 /\ ?G2 => split
 | |- _ => try assumption
end.

Ltac clean_reap_hyps :=
  clean_duplicated_hyps;
  repeat
  match goal with
   | H:(Parallelogram ?A ?B ?C ?D), H2 : Parallelogram ?B ?C ?D ?A |- _ => clear H2
   | H:(Parallelogram ?A ?B ?C ?D), H2 : Parallelogram ?C ?D ?A ?B |- _ => clear H2
   | H:(Parallelogram ?A ?B ?C ?D), H2 : Parallelogram ?D ?A ?B ?C |- _ => clear H2
   | H:(Parallelogram ?A ?B ?C ?D), H2 : Parallelogram ?D ?C ?B ?A |- _ => clear H2
   | H:(Parallelogram ?A ?B ?C ?D), H2 : Parallelogram ?C ?B ?A ?D |- _ => clear H2
   | H:(Parallelogram ?A ?B ?C ?D), H2 : Parallelogram ?B ?A ?D ?C |- _ => clear H2
   | H:(Parallelogram ?A ?B ?C ?D), H2 : Parallelogram ?A ?D ?C ?B |- _ => clear H2
   | H:(Par ?A ?B ?C ?D), H2 : Par ?A ?B ?D ?C |- _ => clear H2
   | H:(Par ?A ?B ?C ?D), H2 : Par ?C ?D ?A ?B |- _ => clear H2
   | H:(Par ?A ?B ?C ?D), H2 : Par ?C ?D ?B ?A |- _ => clear H2
   | H:(Par ?A ?B ?C ?D), H2 : Par ?D ?C ?B ?A |- _ => clear H2
   | H:(Par ?A ?B ?C ?D), H2 : Par ?D ?C ?A ?B |- _ => clear H2
   | H:(Par ?A ?B ?C ?D), H2 : Par ?B ?A ?C ?D |- _ => clear H2
   | H:(Par ?A ?B ?C ?D), H2 : Par ?B ?A ?D ?C |- _ => clear H2
   | H:(Par_strict ?A ?B ?C ?D), H2 : Par_strict ?A ?B ?D ?C |- _ => clear H2
   | H:(Par_strict ?A ?B ?C ?D), H2 : Par_strict ?C ?D ?A ?B |- _ => clear H2
   | H:(Par_strict ?A ?B ?C ?D), H2 : Par_strict ?C ?D ?B ?A |- _ => clear H2
   | H:(Par_strict ?A ?B ?C ?D), H2 : Par_strict ?D ?C ?B ?A |- _ => clear H2
   | H:(Par_strict ?A ?B ?C ?D), H2 : Par_strict ?D ?C ?A ?B |- _ => clear H2
   | H:(Par_strict ?A ?B ?C ?D), H2 : Par_strict ?B ?A ?C ?D |- _ => clear H2
   | H:(Par_strict ?A ?B ?C ?D), H2 : Par_strict ?B ?A ?D ?C |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?A ?B ?D ?C |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?C ?D ?A ?B |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?C ?D ?B ?A |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?D ?C ?B ?A |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?D ?C ?A ?B |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?B ?A ?C ?D |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?B ?A ?D ?C |- _ => clear H2
   | H:(Perp_at ?X ?A ?B ?C ?D), H2 : Perp_at ?X ?A ?B ?D ?C |- _ => clear H2
   | H:(Perp_at ?X ?A ?B ?C ?D), H2 : Perp_at ?X ?C ?D ?A ?B |- _ => clear H2
   | H:(Perp_at ?X ?A ?B ?C ?D), H2 : Perp_at ?X ?C ?D ?B ?A |- _ => clear H2
   | H:(Perp_at ?X ?A ?B ?C ?D), H2 : Perp_at ?X ?D ?C ?B ?A |- _ => clear H2
   | H:(Perp_at ?X ?A ?B ?C ?D), H2 : Perp_at ?X ?D ?C ?A ?B |- _ => clear H2
   | H:(Perp_at ?X ?A ?B ?C ?D), H2 : Perp_at ?X ?B ?A ?C ?D |- _ => clear H2
   | H:(Perp_at ?X ?A ?B ?C ?D), H2 : Perp_at ?X ?B ?A ?D ?C |- _ => clear H2
   | H:(Per ?A ?B ?C), H2 : Per ?C ?B ?A |- _ => clear H2
   | H:(Midpoint ?A ?B ?C), H2 : Midpoint ?A ?C ?B |- _ => clear H2
   | H:(~Col ?A ?B ?C), H2 : (~Col ?B ?A ?C) |- _ => clear H2
   | H:(~Col ?A ?B ?C), H2 : (~Col ?B ?C ?A) |- _ => clear H2
   | H:(~Col ?A ?B ?C), H2 : (~Col ?C ?B ?A) |- _ => clear H2
   | H:(~Col ?A ?B ?C), H2 : (~Col ?C ?A ?B) |- _ => clear H2
   | H:(~Col ?A ?B ?C), H2 : (~Col ?A ?C ?B) |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?A ?C ?B |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?B ?A ?C |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?B ?C ?A |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?C ?B ?A |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?C ?A ?B |- _ => clear H2
   | H:(Bet ?A ?B ?C), H2 : Bet ?C ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?A ?B ?D ?C |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?C ?D ?A ?B |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?C ?D ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?D ?C ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?D ?C ?A ?B |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?B ?A ?C ?D |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?B ?A ?D ?C |- _ => clear H2
   | H:(?A<>?B), H2 : (?B<>?A) |- _ => clear H2
end.

Ltac tag_hyps :=
  repeat
  match goal with
    | H : ?A <> ?B |- _ => apply Diff_Diff_tagged in H
    | H : Cong ?A ?B ?C ?D |- _ => apply Cong_Cong_tagged in H
    | H : Bet ?A ?B ?C |- _ => apply Bet_Bet_tagged in H
    | H : Col ?A ?B ?C |- _ => apply Col_Col_tagged in H
    | H : ~ Col ?A ?B ?C |- _ => apply NCol_NCol_tagged in H
    | H : Midpoint ?A ?B ?C |- _ => apply Mid_Mid_tagged in H
    | H : Per ?A ?B ?C |- _ => apply Per_Per_tagged in H
    | H : Perp_at ?X ?A ?B ?C ?D |- _ => apply Perp_in_Perp_in_tagged in H
    | H : Perp ?A ?B ?C ?D |- _ => apply Perp_Perp_tagged in H
    | H : Par_strict ?A ?B ?C ?D |- _ => apply Par_strict_Par_strict_tagged in H
    | H : Par ?A ?B ?C ?D |- _ => apply Par_Par_tagged in H
    | H : Parallelogram ?A ?B ?C ?D |- _ => apply Plg_Plg_tagged in H
  end.

Ltac permutation_intro_in_goal :=
 match goal with
 | |- Par ?A ?B ?C ?D => apply Par_cases
 | |- Par_strict ?A ?B ?C ?D => apply Par_strict_cases
 | |- Perp ?A ?B ?C ?D => apply Perp_cases
 | |- Perp_at ?X ?A ?B ?C ?D => apply Perp_in_cases
 | |- Per ?A ?B ?C => apply Per_cases
 | |- Midpoint ?A ?B ?C => apply Mid_cases
 | |- ~ Col ?A ?B ?C => apply NCol_cases
 | |- Col ?A ?B ?C => apply Col_cases
 | |- Bet ?A ?B ?C => apply Bet_cases
 | |- Cong ?A ?B ?C ?D => apply Cong_cases
 end.

Ltac perm_apply t :=
 permutation_intro_in_goal;
 try_or ltac:(apply t;solve [finish]).

Ltac assert_ncols :=
repeat
  match goal with
      | H:OS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B X;assert (~ Col A B X) by (apply(one_side_not_col123 A B X Y);finish)

      | H:OS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B Y;assert (~ Col A B Y) by (apply(one_side_not_col124 A B X Y);finish)

      | H:TS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B X;assert (~ Col A B X) by (apply(two_sides_not_col A B X Y);finish)

      | H:TS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B Y;assert (~ Col A B Y) by (apply(two_sides_not_col A B Y X);finish)

      | H:~ Coplanar ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp_perm4 A B C D;
      assert (h := ncop__ncols A B C D H);decompose [and] h;clear h;clean_reap_hyps

      | H:Par_strict ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp_perm4 A B C D;
      assert (h := par_strict_not_cols A B C D H);decompose [and] h;clear h;clean_reap_hyps

      | H:Parallelogram_strict ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp_perm4 A B C D;
      assert (h := plgs_not_col A B C D H);decompose [and] h;clear h;clean_reap_hyps
  end.

Section Quadrilateral_inter_dec_1.

Context `{TE:Tarski_euclidean}.

Lemma par_cong_mid_ts :
 forall A B A' B',
  Par_strict A B A' B' ->
  Cong A B A' B' ->
  TS A A' B B' ->
  exists M,  Midpoint M A A' /\ Midpoint M B B'.
Proof.
intros.

assert(HH:= H1).
unfold TS in HH.
assert(~ Col B A A').
spliter; assumption.
spliter.
ex_and H5 M.
exists M.

assert(HH:= H).
unfold Par_strict in HH.
spliter.

assert(HH:=(midpoint_existence A A')).
ex_and HH X.

prolong B X B'' B X.
assert(Midpoint X B B'').
unfold Midpoint.
split.
assumption.
Cong.

assert(Par_strict B A B'' A').
apply (midpoint_par_strict B A B'' A' X); auto.

assert(Col B'' B' A' /\ Col A' B' A').
apply(parallel_uniqueness B A B' A' B'' A' A').
apply par_comm.
unfold Par.
left.
assumption.
Col.
unfold Par.
left.
assumption.
Col.
spliter.

assert(Cong A B A' B'').
eapply l7_13.
apply l7_2.
apply H11.
apply l7_2.
assumption.
assert(Cong A' B' A' B'').
eapply cong_transitivity.
apply cong_symmetry.
apply H0.
assumption.

assert(B' = B'' \/ Midpoint A' B' B'').
eapply l7_20.
Col.
Cong.
induction H20.

subst B''.

assert(X = M).
eapply (l6_21 A A' B B'); Col.

intro.
subst B'.
apply H10.
exists B.
split; Col.
subst X.
split; auto.

assert(TS A A' B B'').
unfold TS.
repeat split; auto.
intro.
apply H4.
apply col_permutation_1.
eapply (col_transitivity_1 _ B'').
intro.
subst B''.
apply l7_2 in H20.
apply is_midpoint_id in H20.
contradiction.
Col.
Col.
exists X.
split.

unfold Midpoint in H11.
spliter.
apply bet_col in H11.
Col.
assumption.

assert(OS A A' B' B'').
eapply l9_8_1.
apply l9_2.
apply H1.
apply l9_2.
assumption.

assert(TS A A' B' B'').
unfold TS.
repeat split.
intro.
apply H4.
Col.
intro.
apply H4.

apply col_permutation_1.
eapply (col_transitivity_1 _ B'').
intro.
subst B''.
apply l7_2 in H20.
apply is_midpoint_id in H20.
contradiction.
Col.
Col.

exists A'.
split.
Col.
unfold Midpoint in H20.
spliter.
assumption.
apply l9_9 in H23.
contradiction.
Qed.

Lemma par_cong_mid_os :
  forall A B A' B',
   Par_strict A B A' B' ->
   Cong A B A' B' ->
   OS A A' B B' ->
   exists M, Midpoint M A B' /\ Midpoint M B A'.
Proof.
intros.
assert(HH:= H).
unfold Par_strict in HH.
spliter.

assert(HH:=(midpoint_existence A' B)).
ex_and HH X.
exists X.

prolong A X B'' A X.
assert(Midpoint X A B'').
unfold Midpoint.
split.
assumption.
Cong.

assert(~Col A B A').
intro.
apply H5.
exists A'.
split; Col.

assert(Par_strict  A B B'' A').
apply (midpoint_par_strict A B  B'' A' X).
auto.
assumption.
assumption.
apply l7_2.
assumption.

assert(Col B'' B' A' /\ Col A' B' A').
apply (parallel_uniqueness B A B' A' B'' A' A').

apply par_comm.
unfold Par.
left.
assumption.
Col.
apply par_left_comm.
unfold Par.
left.
assumption.
Col.
spliter.

assert(Cong A B  B'' A').
eapply l7_13.
apply l7_2.
apply H9.
assumption.
assert(Cong A' B' A' B'').
eapply cong_transitivity.
apply cong_symmetry.
apply H0.
Cong.
assert(B' = B'' \/ Midpoint A' B' B'').
eapply l7_20.
Col.
Cong.

induction H16.
subst B''.
split.
assumption.
apply l7_2.
assumption.

assert(OS A A' X B'').

eapply (out_one_side_1 _ _ X B'').

intro.
apply H10.
apply col_permutation_1.
eapply (col_transitivity_1 _ X).
intro.
subst X.
apply is_midpoint_id in H6.
subst A'.
apply H5.
exists B.
split; Col.
Col.
unfold Midpoint in H6.
spliter.
apply bet_col in H6.
Col.
Col.
unfold Out.
repeat split.
intro.
subst X.
apply cong_identity in H8.
subst B''.
unfold Par_strict in H11.
spliter.
apply H18.
exists A.
split; Col.
intro.
subst B''.
unfold Par_strict in H11.
spliter.
apply H19.
exists A.
split; Col.
unfold Midpoint in H8.
spliter.
left.
assumption.

assert(TS A A' B' B'').
unfold TS.
repeat split.
intro.
apply H5.
exists A.
split; Col.

unfold OS in H17.
ex_and H17 T.
unfold TS in H18.
spliter.
assumption.
exists A'.
split.
Col.
unfold Midpoint in H16.
spliter.
assumption.

assert(TS A A' X B').
eapply l9_8_2.
apply l9_2.
apply H18.
apply one_side_symmetry.
assumption.

assert(OS A A' X B).

eapply (out_one_side_1).
intro.
apply H10.
apply col_permutation_1.
eapply (col_transitivity_1 _ X).
intro.
subst X.
apply is_midpoint_id in H6.
subst A'.
apply H5.
exists B.
split; Col.
Col.
unfold Midpoint in H6.
spliter.
apply bet_col in H6.
Col.
apply col_trivial_2;Col.
unfold Out.
repeat split.
intro.
subst X.
unfold TS in H19.
spliter.
apply H19.
Col.
intro.
subst A'.
unfold Par_strict in H11.
spliter.
apply H22.
exists B.
split; Col.
unfold Midpoint in H6.
spliter.
left.
assumption.

assert(OS A A' X B').
eapply one_side_transitivity.
apply H20.
assumption.
apply l9_9 in H19.
contradiction.
Qed.

Lemma par_strict_cong_mid :
 forall A B A' B',
  Par_strict A B A' B' ->
  Cong A B A' B' ->
  exists M,  Midpoint M A A' /\ Midpoint M B B' \/
             Midpoint M A B' /\ Midpoint M B A'.
Proof.
intros A B A' B' HParS HCong.
assert (HP:=parallel_uniqueness).
destruct (midpoint_existence A A') as [M1 HM1].
destruct (symmetric_point_construction B M1) as [B'' HB''].
assert (HCol1 : Col B'' A' B').
  {
  assert (Col A' A' B' /\ Col B'' A' B'); try (spliter; Col).
  assert (HPar := par_strict_par A B A' B' HParS);
  apply HP with A B A'; Col; unfold Par_strict in HParS; spliter;
  apply l12_17 with M1; Col.
  }
assert (HCong1 : Cong A' B' A' B'')
  by (assert (H := l7_13 M1 A' B'' A B HM1 HB''); eCong).
destruct (midpoint_existence A B') as [M2 HM2].
destruct (symmetric_point_construction B M2) as [A'' HA''].
assert (HCol2 : Col A'' A' B').
  {
  assert (Col B' A' B' /\ Col A'' A' B'); try (spliter; Col).
  assert (HPar := par_strict_par A B A' B' HParS);
  apply HP with A B B'; Col; unfold Par_strict in HParS; spliter;
  apply l12_17 with M2; Col.
  }
assert (HCong2 : Cong A' B' B' A'')
  by (assert (H := l7_13 M2 B' A'' A B HM2 HA''); eCong).
elim (l7_20 A' B' B''); Col; intro HElim1; treat_equalities.

  {
  exists M1; left; Col.
  }


  {
  elim (l7_20 B' A' A''); Cong; Col; intro HElim2; treat_equalities.

    {
    exists M2; right; Col.
    }

    {
    exfalso; destruct (outer_pasch B' A A' B'' M1) as [I [HAIB' HA''IM1]];
    unfold Midpoint in*; spliter; Between.
    assert (HM1I : M1 <> I).
      {
      intro; treat_equalities.
      show_distinct A M1; apply HParS; exists A; split; Col; assert_cols; ColR.
      }
    assert (HB''M1 : B'' <> M1).
      {
      intro; treat_equalities; apply HParS; exists B; assert_cols; Col.
      }
    elim (l5_2 B'' M1 I B); Between; intro HBM1I.

      {
      assert (HFalse : TS A B' B A'').
        {
        split; try (intro; apply HParS; exists B'; Col).
        show_distinct B' A''; try (apply HParS; exists A; Col).
        show_distinct A' B'; try (apply HParS; exists A; Col).
        split; try (intro; apply HParS; exists A; split; Col; assert_cols; ColR).
        exists M2; assert_cols; Col.
        }
      apply l9_9 in HFalse; apply HFalse; clear HFalse.
      exists A'; split.

        {
        apply l9_2; apply l9_8_2 with B''.

          {
          show_distinct A' B'; try (apply HParS; exists A; Col).
          show_distinct B' B''; try (apply HParS; exists A; Col).
          split; try (intro; apply HParS; exists A; split; Col; assert_cols; ColR).
          split; try (intro; apply HParS; exists B'; split; Col).
          exists I; assert_cols; split; Col; eBetween.
          }

          {
          apply l9_19 with B'; Col; try (intro; treat_equalities; apply HParS; exists A; Col).
          show_distinct A' B'; try (apply HParS; exists A; Col).
          show_distinct B' B''; try (apply HParS; exists A; Col).
          split; try (intro; apply HParS; exists A; split; Col; assert_cols; ColR).
          split; Col.
          }
        }

        {
        show_distinct B' A''; try (apply HParS; exists A; Col).
        show_distinct A' B'; try (apply HParS; exists A; Col).
        split; try (intro; apply HParS; exists A; split; Col; assert_cols; ColR).
        split; try (intro; apply HParS; exists A; Col).
        exists B'; split; Col; Between.
        }
      }

      {
      assert (HFalse : OS A A' B B').
        {
        exists B''; split.

          {
          split; try (intro; apply HParS; exists A'; Col).
          show_distinct A' B'; try (apply HParS; exists A; Col).
          show_distinct A' B''; try (apply HParS; exists A; Col).
          split; try (intro; apply HParS; exists A; split; Col; assert_cols; ColR).
          exists M1; assert_cols; Col.
          }

          {
          split; try (intro; apply HParS; exists A; Col).
          show_distinct A' B'; try (apply HParS; exists A; Col).
          show_distinct A' B''; try (apply HParS; exists A; Col).
          split; try (intro; apply HParS; exists A; split; Col; assert_cols; ColR).
          exists A'; Col.
          }
        }
      apply l9_9_bis in HFalse; apply HFalse; clear HFalse; apply l9_31.

        {
        apply l12_6; Col.
        }

        {
        apply one_side_transitivity with B''.

          {
          apply l9_19 with B'; Col; try (intro; treat_equalities; apply HParS; exists A; Col).
          split; try (intro; apply HParS; exists A; Col).
          split; try (intro; treat_equalities; apply HParS; exists A; Col).
          split; try (intro; treat_equalities; apply HParS; exists A; Col); Between.
          }

          {
          assert_cols; apply l9_19 with I; Col; try ColR;
          try (intro; treat_equalities; apply HParS; exists A; Col).
          show_distinct A' B'; try (apply HParS; exists A; Col).
          show_distinct B' B''; try (apply HParS; exists A; Col).
          split; try (intro; apply HParS; exists A; split; Col; assert_cols; ColR).
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; apply HParS; assert_cols; exists B'; Col).
          eBetween.
          }
        }
      }
    }
  }
Qed.

Lemma par_strict_cong_mid1 :
 forall A B A' B',
  Par_strict A B A' B' ->
  Cong A B A' B' ->
  (TS A A' B B'  /\ exists M,  Midpoint M A A' /\ Midpoint M B B') \/ 
  (OS A A' B B' /\ exists M, Midpoint M A B' /\ Midpoint M B A').
Proof.
intros.
assert(HH:= H).
unfold Par_strict in HH.
spliter.
destruct (cop__one_or_two_sides A A' B B').
Cop.
intro.
apply H4.
exists A'.
split; Col.
intro.
apply H4.
exists A.
split; Col.
left.
split.
assumption.
assert(HH:=par_cong_mid_ts A B A' B' H H0 H5).
ex_and HH M.
exists M.
split; assumption.
right.
split.
assumption.
assert(HH:=par_cong_mid_os A B A' B' H H0 H5).
ex_and HH M.
exists M.
split; assumption.
Qed.

Lemma par_cong_mid :
 forall A B A' B',
  Par A B A' B' ->
  Cong A B A' B' ->
  exists M,  Midpoint M A A' /\ Midpoint M B B' \/
             Midpoint M A B' /\ Midpoint M B A'.
Proof.
intros.
induction H.
apply par_strict_cong_mid; try assumption.
apply col_cong_mid.
unfold Par.
right.
assumption.
intro.
unfold Par_strict in H1.
spliter.
apply H4.
exists A.
split; Col.
assumption.
Qed.

Lemma ts_cong_par_cong_par :
 forall A B A' B',
 TS A A' B B' ->
 Cong A B A' B' ->
 Par A B A' B' ->
 Cong A B' A' B /\ Par A B' A' B.
Proof.
intros A B A' B' HTS HCong HPar.
assert(HAB : A <> B) by (intro; treat_equalities; unfold TS in *; spliter; Col).
destruct (par_cong_mid A B A' B') as [M HM]; Col.
elim HM; clear HM; intro HM; destruct HM as [HMid1 HMid2].

  {
  assert(HAB' : A <> B') by (intro; treat_equalities; unfold TS in HTS; spliter; Col).
  split; try apply l7_13 with M; try apply l12_17 with M; Midpoint.
  }

  {
  assert(HAA' : A <> A') by (intro; treat_equalities; unfold TS in HTS; spliter; Col).
  assert (HFalse := HTS); apply l9_9 in HFalse; exfalso; apply HFalse; clear HFalse.
  unfold TS in HTS; spliter; apply l12_6; apply par_not_col_strict with B; Col.
  assert (Par  A A' B' B); Par; apply l12_17 with M; Midpoint.
  }
Qed.

Lemma plgs_cong :
 forall A B C D,
 Parallelogram_strict A B C D ->
 Cong A B C D /\ Cong A D B C.
Proof.
intros A B C D HPara.
destruct HPara as [HTS [HCong HPar]]; split; Col.
destruct (ts_cong_par_cong_par A B C D) as [HCong' HPar']; Cong.
Qed.

Lemma plg_cong :
 forall A B C D,
  Parallelogram A B C D ->
 Cong A B C D /\ Cong A D B C.
Proof.
intros.
induction H.
apply plgs_cong.
assumption.
apply plgf_cong.
assumption.
Qed.

Lemma rmb_cong :
 forall A B C D,
  Rhombus A B C D ->
  Cong A B B C /\ Cong A B C D /\ Cong A B D A.
Proof.
intros.
unfold Rhombus in H.
spliter.
assert(HH:= plg_to_parallelogram A B C D H).
assert(HH1:= plg_cong A B C D HH).
spliter.
repeat split; trivial.
apply cong_transitivity with B C; Cong.
Qed.

Lemma rmb_per:
 forall A B C D M,
  Midpoint M A C ->
  Rhombus A B C D ->
  Per A M D.
Proof.
intros.
assert(HH:=H0).
unfold Rhombus in HH.
spliter.
assert(HH:=H1).
unfold Plg in HH.
spliter.
ex_and H4 M'.
assert(M = M').
eapply l7_17.
apply H.
assumption.
subst M'.
unfold Per.
exists B.
split.
apply l7_2.
assumption.
apply rmb_cong in H0.
spliter.
Cong.
Qed.

Lemma per_rmb :
 forall A B C D M,
  Plg A B C D ->
  Midpoint M A C ->
  Per A M B ->
  Rhombus A B C D.
Proof.
intros.
unfold Per in H1.
ex_and H1 D'.
assert(HH:=H).
unfold Plg in HH.
spliter.
ex_and H4 M'.
assert(M = M').
eapply l7_17.
apply H0.
apply H4.
subst M'.
assert(D = D').
eapply symmetric_point_uniqueness.
apply H5.
assumption.
subst D'.
unfold Rhombus.
split.
assumption.
assert(Cong A D B C).
apply plg_to_parallelogram in H.
assert(HH:=plg_cong A B C D H).
spliter.
assumption.
eapply cong_transitivity.
apply H2.
assumption.
Qed.

Lemma perp_rmb :
 forall A B C D,
  Plg A B C D ->
  Perp A C B D ->
  Rhombus A B C D.
Proof.
intros.
assert(HH:=midpoint_existence A C).
ex_and HH M.
apply (per_rmb A B C D M).
assumption.
assumption.
apply perp_in_per.
unfold Plg in H.
spliter.
ex_and H2 M'.
assert(M = M').
eapply l7_17.
apply H1.
assumption.
subst M'.
assert(Perp A M B M).
eapply perp_col.
intro.
subst M.
apply is_midpoint_id in H1.
subst C.
apply perp_not_eq_1 in H0.
tauto.
apply perp_sym.
eapply perp_col.
intro.
subst M.
apply is_midpoint_id in H3.
subst D.
apply perp_not_eq_2 in H0.
tauto.
apply perp_sym.
apply H0.
unfold Midpoint in H3.
spliter.
apply bet_col in H3.
Col.
unfold Midpoint in H2.
spliter.
apply bet_col in H2.
Col.
apply perp_left_comm in H4.
apply perp_perp_in in H4.
apply perp_in_comm.
assumption.
Qed.

Lemma plg_conga1 : forall A B C D, A <> B -> A <> C -> Plg A B C D -> CongA B A C D C A.
Proof.
intros.
apply cong3_conga; auto.
assert(HH := plg_to_parallelogram A B C D H1).
apply plg_cong in HH.
spliter.
repeat split; Cong.
Qed.

Lemma os_cong_par_cong_par :
 forall A B A' B',
  OS A A' B B' ->
  Cong A B A' B' ->
  Par A B A' B' ->
 Cong A A' B B' /\ Par A A' B B'.
Proof.
intros.

induction H1.

assert(A <> B /\ A <> A').
unfold OS in H.
ex_and H C.
unfold TS in H.
spliter.
split.
intro.
subst B.
apply H.
Col.
intro.
subst A'.
Col.
spliter.

assert(HH:= (par_strict_cong_mid1 A B A' B' H1 H0 )).
induction HH.
spliter.
apply l9_9 in H4.
contradiction.
spliter.
ex_and H5 M.
assert(HH:= mid_par_cong A B B' A' M H2 H3).
assert(Cong A B B' A' /\ Cong A A' B' B /\ Par A B B' A' /\ Par A A' B' B).
apply HH.
assumption.
assumption.
spliter.
split.
Cong.
Par.
spliter.
unfold OS in H.
ex_and H C.
unfold TS in H5.
spliter.
apply False_ind.
apply H5.
Col.
Qed.

Lemma plgs_permut :
 forall A B C D,
  Parallelogram_strict A B C D ->
  Parallelogram_strict B C D A.
Proof.
intros A B C D HPara.
destruct HPara as [HTS [HCong HPar]].
destruct (ts_cong_par_cong_par A B C D) as [HCong' HPar']; Col.
destruct (par_cong_mid A B C D) as [M HM]; Col.
elim HM; clear HM; intro HM; destruct HM as [HMid1 HMid2].

  {
  assert (HAM : A <> M) by (intro; treat_equalities; unfold TS in HTS; spliter; Col).
  assert (HCM : C <> M) by (intro; treat_equalities; unfold TS in HTS; spliter; Col).
  assert (HBD : B <> D) by (assert (H:=not_two_sides_id B A C); intro; treat_equalities; Col).
  destruct HTS as [HAC [HABC HTS]]; assert_cols.
  repeat try (split; Cong; Par; try (intro; apply HABC; ColR)).
  unfold Midpoint in *; spliter; exists M; split; Col; Between.
  }

  {
  assert(HAB : A <> B) by (intro; treat_equalities; unfold TS in HTS; spliter; Col).
  assert(HAC : A <> C) by (intro; treat_equalities; unfold TS in HTS; spliter; Col).
  assert (HFalse := HTS); apply l9_9 in HFalse; exfalso; apply HFalse; clear HFalse.
  unfold TS in HTS; spliter; apply l12_6; apply par_not_col_strict with B; Col.
  assert (Par A C D B); Par; apply l12_17 with M; Midpoint.
  }
Qed.

Lemma plg_permut :
 forall A B C D,
  Parallelogram A B C D ->
  Parallelogram B C D A.
Proof.
intros A B C D HPara.
elim HPara; clear HPara; intro HPara.

  {
  left; apply plgs_permut; Col.
  }

  {right; apply plgf_permut; Col.
  }
Qed.

Lemma plgs_mid :
 forall A B C D,
  Parallelogram_strict A B C D ->
  exists M, Midpoint M A C /\ Midpoint M B D.
Proof.
intros A B C D HPara.
destruct HPara as [HTS [HCong HPar]].
destruct (par_cong_mid A B C D) as [M HM]; Col.
elim HM; clear HM; intro HM; destruct HM as [HMid1 HMid2]; try (exists M; Col).
assert(HAB : A <> B) by (intro; treat_equalities; unfold TS in HTS; spliter; Col).
assert(HAC : A <> C) by (intro; treat_equalities; unfold TS in HTS; spliter; Col).
assert (HFalse := HTS); apply l9_9 in HFalse; exfalso; apply HFalse; clear HFalse.
unfold TS in HTS; spliter; apply l12_6; apply par_not_col_strict with B; Col.
assert (Par A C D B); Par; apply l12_17 with M; Midpoint.
Qed.

Lemma plg_mid :
 forall A B C D,
  Parallelogram A B C D ->
  exists M, Midpoint M A C /\ Midpoint M B D.
Proof.
intros A B C D HPara.
elim HPara; clear HPara; intro HPara.

  {
  apply plgs_mid; Col.
  }

  {
  apply plgf_mid; Col.
  }

Qed.

Lemma plg_mid_2 :
 forall A B C D I,
  Parallelogram A B C D ->
  Midpoint I A C ->
  Midpoint I B D.
Proof.
intros.
elim (plg_mid A B C D).
intros I' HI'.
spliter.
treat_equalities.
assumption.
assumption.
Qed.


Lemma plgs_not_comm :
  forall A B C D,
   Parallelogram_strict A B C D ->
 ~ Parallelogram_strict A B D C /\ ~ Parallelogram_strict B A C D.
Proof.
intros.
unfold Parallelogram_strict in *.
split.
intro.
spliter.
assert(HH:=
ts_cong_par_cong_par A B C D H H4 H3).
spliter.

assert(Par_strict A D C B).
induction H6.
assumption.
spliter.

unfold Par_strict.
repeat split; Cop.
intro.
unfold TS in *.
spliter.
apply H.
Col.
apply l12_6 in H7.
apply l9_9 in H0.
apply one_side_symmetry in H7.
contradiction.

intro.
spliter.
assert(HH:=ts_cong_par_cong_par A B C D H H4 H3).
spliter.
apply par_symmetry in H6.

assert(Par_strict C B A D).
induction H6.
assumption.
spliter.
unfold Par_strict.
repeat split; Cop.
intro.
unfold TS in *.
spliter.
apply H13.
Col.
apply l12_6 in H7.
apply l9_9 in H0.
apply invert_one_side in H7.
contradiction.
Qed.

Lemma plg_not_comm :
 forall A B C D,
 A <> B ->
 Parallelogram A B C D ->
 ~ Parallelogram A B D C /\ ~ Parallelogram B A C D.
Proof.
intros.
unfold Parallelogram.
induction H0.
split.
intro.
induction H1.
apply plgs_not_comm in H0.
spliter.
contradiction.
unfold Parallelogram_strict in H0.
spliter.
unfold Parallelogram_flat in H1.
spliter.
apply par_symmetry in H2.
induction H2.
unfold Par_strict in H2.
spliter.
apply H10.
exists D; Col.
spliter.
unfold TS in H0.
spliter.
apply H0.
Col.
intro.
assert(~ Parallelogram_strict A B D C /\ ~ Parallelogram_strict B A C D).
apply plgs_not_comm.
assumption.
spliter.
induction H1.
contradiction.
unfold Parallelogram_strict in H0.
unfold Parallelogram_flat in H1.
spliter.
unfold TS in H0.
spliter.
contradiction.
assert(~ Parallelogram_flat A B D C /\ ~ Parallelogram_flat B A C D).
apply plgf_not_comm.
assumption.
assumption.
spliter.
split.
intro.
induction H3.
unfold Parallelogram_strict in H3.
unfold Parallelogram_flat in H0.
spliter.
unfold TS in H3.
spliter.
apply H3.
Col.
apply plgf_not_comm in H0.
spliter.
contradiction.
assumption.
intro.
induction H3.
unfold Parallelogram_strict in H3.
unfold Parallelogram_flat in H0.
spliter.
unfold TS in H3.
spliter.
contradiction.
contradiction.
Qed.

Lemma parallelogram_to_plg : forall A B C D, Parallelogram A B C D -> Plg A B C D.
Proof.
intros A B C D HPara.
destruct (plg_mid A B C D) as [M HM]; Col.
split; try (exists M; Col).
elim HPara; clear HPara; intro HPara; try (apply plgs_diff in HPara; spliter; Col);
unfold Parallelogram_flat in HPara; spliter; Col.
Qed.

Lemma parallelogram_equiv_plg : forall A B C D, Parallelogram A B C D <-> Plg A B C D.
Proof.
intros.
split.
apply parallelogram_to_plg.
apply plg_to_parallelogram.
Qed.

Lemma plg_conga : forall A B C D, A <> B /\ A <> C /\ B <> C -> Parallelogram A B C D -> CongA A B C C D A /\ CongA B C D D A B.
Proof.
intros.
assert(Cong A B C D /\ Cong A D B C).
apply plg_cong.
assumption.
spliter.
assert(HH:= plg_mid A B C D H0).
ex_and HH M.
split.
apply cong3_conga; auto.
repeat split; Cong.
apply cong3_conga; auto.
intro.
subst D.
apply H.
eapply symmetric_point_uniqueness;
apply l7_2.
apply H5.
assumption.
repeat split; Cong.
Qed.

Lemma half_plgs :
 forall A B C D P Q M,
  Parallelogram_strict A B C D ->
  Midpoint P A B ->
  Midpoint Q C D ->
  Midpoint M A C ->
  Par P Q A D /\ Midpoint M P Q /\ Cong A D P Q.
Proof.
intros.
assert(HH:=H).
apply plgs_mid in HH.
ex_and HH M'.
assert(M=M').
eapply l7_17.
apply H2.
assumption.
subst M'.
clear H3.

prolong P M Q' P M.
assert(Midpoint M P Q').
split.
assumption.
Cong.
assert(Midpoint Q' C D).
eapply symmetry_preserves_midpoint.
apply H2.
apply H6.
apply H4.
apply H0.
assert(Q=Q').
eapply l7_17.
apply H1.
assumption.
subst Q'.
assert(HH:=H).
unfold Parallelogram_strict in HH.
spliter.

assert(Cong A P D Q).
eapply cong_cong_half_1.
apply H0.
apply l7_2.
apply H1.
Cong.

assert(Par A P Q D).
eapply par_col_par_2.
intro.
subst P.
apply is_midpoint_id in H0.
subst B.
induction H9.
unfold Par_strict in H0.
spliter.
tauto.
spliter.
tauto.
unfold Midpoint in H0.
spliter.
apply bet_col in H0.
apply col_permutation_5.
apply H0.
apply par_symmetry.
apply par_left_comm.
eapply par_col_par_2.
intro.
subst Q.
apply cong_identity in H11.
subst P.
apply is_midpoint_id in H0.
subst B.
induction H9.
unfold Par_strict in H0.
spliter.
tauto.
spliter.
tauto.
unfold Midpoint in H1.
spliter.
apply bet_col in H1.
apply col_permutation_2.
apply H1.
apply par_left_comm.
Par.


assert(Cong A D P Q /\ Par A D P Q).
apply(os_cong_par_cong_par A P D Q).

unfold TS in H8.
assert(~ Col B A C).
spliter.
assumption.
spliter.

assert(OS A D P B).
eapply out_one_side_1.
intro.
assert(Col P B D).
eapply (col_transitivity_1 _ A).
intro.
subst P.
apply is_midpoint_id in H0.
subst B.
apply cong_symmetry in H10.
apply cong_identity in H10.
subst D.
apply H14.
Col.
unfold Midpoint in H0.
spliter.
apply bet_col in H0.
Col.
Col.

assert(HH:=H).
apply plgs_permut in HH.
unfold Parallelogram_strict in HH.
spliter.
unfold TS in H18.
assert(~ Col C B D).
spliter.
assumption.
spliter.
apply H22.
apply col_permutation_1.
eapply (col_transitivity_1 _ P).
intro.
subst P.
apply H22.
unfold Midpoint in H0.
spliter.
apply bet_col in H0.
Col.
Col.
Col.
Col.
unfold Midpoint in H0.
spliter.

repeat split.
intro.
subst P.
apply cong_symmetry in H11.
apply cong_identity in H11;

unfold TS in H8.
subst Q.
apply l7_2 in H1.
apply is_midpoint_id in H1.
subst D.
apply H14.
Col.
intro.
subst B.
apply cong_symmetry in H10.
apply cong_identity in H10;
unfold Par_strict in H12.
subst D.
apply H13.
Col.
left.
assumption.

assert(OS A D Q C).
eapply out_one_side_1.
intro.
apply H14.
eapply (col_transitivity_1 _ Q).
intro.
subst Q.
apply l7_2 in H1.
apply is_midpoint_id in H1.
subst D.
apply H14.
Col.
Col.
unfold Midpoint in H1.
spliter.
apply bet_col in H1.
Col.
apply col_trivial_2;Col.

repeat split.
intro.
subst Q.
apply cong_identity in H11.
subst P.
unfold OS in H16.
ex_and H16 K.
unfold TS in H11.
spliter.
apply H11.
Col.
intro.
subst D.
apply cong_identity in H10.
subst B.
apply H14.
Col.

unfold Midpoint in H1.
spliter.
left.
Between.

assert(OS A D B C).

apply ts_cong_par_cong_par in H9.
spliter.

induction H18.
apply l12_6.
unfold Par_strict in *.
spliter.
repeat split; Cop.
intro.
apply H21.
ex_and H22 X.
exists X.
split; Col.
spliter.
apply False_ind.
apply H13.
Col.
repeat split; auto.
Cong.
eapply one_side_transitivity.
apply H16.
eapply one_side_transitivity.
apply H18.
apply one_side_symmetry.
assumption.
assumption.
Par.
spliter.
apply par_symmetry in H14.
split; auto.
Qed.

Lemma plgs_two_sides :
 forall A B C D,
 Parallelogram_strict A B C D ->
 TS A C B D /\ TS B D A C.
Proof.
intros.
assert(HH:= plgs_mid A B C D H).
ex_and HH M.
unfold Parallelogram_strict in H.
spliter.
split.
assumption.

unfold TS.
assert(~Col B A C).
unfold TS in H.
spliter.
Col.
assert(B <> D).
intro.
assert(HH:=one_side_reflexivity A C B H4).
apply l9_9 in H.
subst D.
contradiction.
unfold TS in H.
assert(~ Col B A C).
spliter.
assumption.
spliter.
repeat split.
intro.
assert(Col M A B).
unfold Midpoint in H1.
spliter.
apply bet_col in H1.
ColR.

apply H4.
apply col_permutation_2.
eapply (col_transitivity_1 _ M).
intro.
subst M.
apply is_midpoint_id in H0.
subst C.
Col.
unfold Midpoint in H0.
spliter.
apply bet_col.
assumption.
Col.
intro.
assert(Col M B C).
unfold Midpoint in H1.
spliter.
apply bet_col in H1.
ColR.
apply H6.
apply col_permutation_1.
eapply (col_transitivity_1 _ M).
intro.
subst M.
apply l7_2 in H0.
apply is_midpoint_id in H0.
subst C.
Col.
Col.
unfold Midpoint in H0.
spliter.
apply bet_col in H0.
Col.
exists M.
unfold Midpoint in *.
spliter.
apply bet_col in H1.
split; Col.
Qed.

Lemma plgs_par_strict :
 forall A B C D,
  Parallelogram_strict A B C D ->
  Par_strict A B C D /\ Par_strict A D B C.
Proof.
intros A B C D HPara.
destruct (plgs_mid A B C D) as [M [HMid1 HMid2]]; Col.
destruct HPara as [HTS [HCong HPar]].
assert(HAB : A <> B) by (intro; treat_equalities; unfold TS in HTS; spliter; Col).
assert(HAC : A <> D) by (intro; treat_equalities; unfold TS in HTS; spliter; Col).
unfold TS in HTS; spliter; split; try apply par_not_col_strict with C; Col.
assert (Par A D C B); Par; apply l12_17 with M; Midpoint.
Qed.

Lemma plgs_half_plgs_aux :
 forall A B C D P Q,
  Parallelogram_strict A B C D ->
  Midpoint P A B ->
  Midpoint Q C D ->
  Parallelogram_strict A P Q D.
Proof.
intros.
assert(HH:= H).
apply plgs_mid in HH.
ex_and HH M.
assert(HH:=half_plgs A B C D P Q M H H0 H1 H2).
spliter.

assert(HH:=H).
apply plgs_par_strict in HH.
spliter.

assert(HH:=par_cong_mid P Q A D H4 (cong_symmetry A D P Q H6)).
ex_and HH N.
induction H9.
spliter.
apply False_ind.
unfold Par_strict in H7.
spliter.
apply H13.
exists N.

assert(A <> P).
intro.
subst P.
apply l7_3 in H9.
subst N.
apply is_midpoint_id in H0.
subst B.
tauto.

assert(D <> Q).
intro.
subst Q.
apply l7_3 in H10.
subst N.
apply l7_2 in H1.
apply is_midpoint_id in H1.
subst D.
tauto.

unfold Midpoint in *.
spliter.
split.
apply bet_col in H0.
apply bet_col in H9.
ColR.
apply bet_col in H1.
apply bet_col in H10.
ColR.

spliter.

assert(A <> P).
intro.
subst P.
apply is_midpoint_id in H0.
subst B.
unfold Par_strict in H7.
spliter.
tauto.

assert(D <> Q).
intro.
subst Q.
apply l7_2 in H1.
apply is_midpoint_id in H1.
subst D.
unfold Par_strict in H7.
spliter.
tauto.

eapply mid_plgs.
intro.
unfold Par_strict in H7.
spliter.
apply H16.
exists Q.
split.
unfold Midpoint in H0.
spliter.
apply bet_col in H0.
ColR.
unfold Midpoint in H1.
spliter.
apply bet_col in H1.
Col.
apply l7_2.
apply H10.
assumption.
Qed.

Lemma plgs_comm2 :
 forall A B C D,
  Parallelogram_strict A B C D ->
  Parallelogram_strict B A D C.
Proof.
intros.
assert(HH:= H).
apply plgs_two_sides in HH.
spliter.
unfold Parallelogram_strict in *.
split.
assumption.
spliter.
split.
apply par_comm.
assumption.
Cong.
Qed.

Lemma plgf_comm2 :
 forall A B C D,
  Parallelogram_flat A B C D ->
  Parallelogram_flat B A D C.
Proof.
intros.
unfold Parallelogram_flat in *.
spliter.
repeat split; Col.
Cong.
Cong.
induction H3.
right; assumption.
left; assumption.
Qed.

Lemma plg_comm2 :
 forall A B C D,
  Parallelogram A B C D ->
  Parallelogram B A D C.
Proof.
intros.
induction H.
left.
apply plgs_comm2.
assumption.
right.
apply plgf_comm2.
assumption.
Qed.

Lemma par_preserves_conga_os :
 forall A B C D P , Par A B C D -> Bet A D P -> D <> P -> OS A D B C -> CongA B A P C D P.
Proof.
intros.
assert(HH:= H2).
unfold OS in HH.
ex_and HH T.
unfold TS in *.
spliter.

prolong C D C' C D.

assert(C' <> D).
intro.
subst C'.
apply cong_symmetry in H10.
apply cong_identity in H10.
subst D.
apply H4.
Col.

assert(CongA B A D C' D A).
eapply l12_21_a.
apply (l9_8_2 _ _ C).
unfold TS.
repeat split; auto.
intro.
apply H4.
apply bet_col in H9.
ColR.

exists D.
split.
Col.
assumption.
apply one_side_symmetry.
assumption.

apply par_symmetry.
eapply (par_col_par_2 _ C).
auto.

apply bet_col in H9.
Col.
apply par_symmetry.
Par.

assert(A <> B).
intro.
subst B.
apply H3.
Col.

assert(CongA B A D B A P).
assert(A <> D).
intro.
subst D.
Col.
eapply (out_conga B A D B A D).
apply conga_refl.
auto.
auto.
apply out_trivial.
auto.
apply out_trivial.
auto.
apply out_trivial.
auto.
unfold Out.
repeat split; auto.
intro.
subst P.
apply between_identity in H0.
contradiction.
apply conga_right_comm.

assert(CongA C D P C' D A).
eapply l11_14; auto.
intro.
subst D.
apply H4.
Col.
Between.
intro.
subst D.
Col.
eapply conga_trans.
apply conga_sym.
apply H14.
eapply conga_trans.
apply H12.
apply conga_sym.
apply conga_left_comm.
assumption.
Qed.

Lemma cong3_par2_par :
 forall A B C A' B' C', A <> C -> Cong_3 B A C B' A' C' -> Par B A B' A' -> Par B C B' C' ->
 Par A C A' C' \/ ~ Par_strict B B' A A' \/ ~Par_strict B B' C C'.
Proof.
intros.

assert(HH0:=par_distinct B A B' A' H1).
assert(HH1:=par_distinct B C B' C' H2).
spliter.

assert(HH:=midpoint_existence B B').
ex_and HH M.

prolong A M A'' A M.
prolong C M C'' C M.

assert(Midpoint M A A'').
split; Cong.
assert(Midpoint M C C'').
split; Cong.

assert(Par B A B' A'').
apply (l12_17 _ _ _ _ M); assumption.

assert(Par B C B' C'').
apply (l12_17 _ _ _ _ M); assumption.

assert(Par  A C A'' C'').
apply (l12_17 _ _ _ _ M);assumption.

assert(Par B' A' B' A'').
eapply par_trans.
apply par_symmetry.
apply H1.
assumption.

assert(Par B' C' B' C'').
eapply par_trans.
apply par_symmetry.
apply H2.
assumption.


assert(Col B' A' A'').
unfold Par in H17.
induction H17.
apply False_ind.
apply H17.
exists B'.
split; Col.
spliter.
Col.

assert(Col B' C' C'').
unfold Par in H18.
induction H18.
apply False_ind.
apply H18.
exists B'.
split; Col.
spliter.
Col.

assert(Cong B A B' A'').
eapply l7_13.
apply l7_2.
apply H7.
apply l7_2.
assumption.

assert(Cong B C B' C'').
eapply l7_13.
apply l7_2.
apply H7.
apply l7_2.
assumption.

unfold Cong_3 in H0.
spliter.

assert(A' = A'' \/ Midpoint B' A' A'').
eapply l7_20.
Col.
apply cong_transitivity with B A; Cong.

assert(C' = C'' \/ Midpoint B' C' C'').
eapply l7_20.
Col.
apply cong_transitivity with B C; Cong.

induction H25.

induction H26.
subst A''.
subst C''.
left.
assumption.

right; left.
intro.
apply H27.
exists M.
unfold Midpoint in *.
spliter.
split.
apply bet_col in H7.
Col.
subst.
apply bet_col in H8.
Col.

induction H26.

subst C''.
clean_duplicated_hyps.
clean_trivial_hyps.

right; right.
intro.
apply H15.
exists M.
split.
unfold Midpoint in H7.
spliter.
apply bet_col in  H7.
Col.
unfold Midpoint in H13.
spliter.
apply bet_col in  H13.
Col.

assert(Par A' C' A'' C'').

apply(l12_17 A' C' A'' C'' B').

intro.
subst C'.
assert(A'' = C'').
eapply l7_9.
apply l7_2.
apply H25.
apply l7_2.
assumption.
subst C''.
apply H.
eapply l7_9.
apply H12.
assumption.
apply H25.
apply H26.
left.
eapply par_trans.
apply H16.
Par.
Qed.



Lemma square_perp_rectangle : forall A B C D,
 Rectangle A B C D ->
 Perp A C B D ->
 Square A B C D.
Proof.
intros.
assert (Rhombus A B C D).
apply perp_rmb.
apply H. assumption.
apply Rhombus_Rectangle_Square;auto.
Qed.

Lemma plgs_half_plgs :
 forall A B C D P Q,
  Parallelogram_strict A B C D ->
  Midpoint P A B -> Midpoint Q C D ->
  Parallelogram_strict A P Q D /\ Parallelogram_strict B P Q C.
Proof.
intros.
split.
eapply plgs_half_plgs_aux.
apply H.
assumption.
assumption.
apply plgs_comm2 in H.
eapply plgs_half_plgs_aux.
apply H.
Midpoint.
Midpoint.
Qed.

Lemma parallel_2_plg :
  forall A B C D,
  ~ Col A B C ->
  Par A B C D ->
  Par A D B C ->
  Parallelogram_strict A B C D.
Proof.
intros.
assert (Cong A B C D /\ Cong B C D A /\
        TS B D A C /\ TS A C B D)
  by (apply l12_19;Par).
unfold Parallelogram_strict; intuition.
Qed.

Lemma par_2_plg :
  forall A B C D,
  ~ Col A B C ->
  Par A B C D ->
  Par A D B C ->
  Parallelogram A B C D.
Proof.
intros.
assert (H2 := parallel_2_plg A B C D H H0 H1).
apply Parallelogram_strict_Parallelogram; assumption.
Qed.

Lemma plg_cong_1 : forall A B C D, Parallelogram A B C D -> Cong A B C D.
Proof.
intros.
apply plg_cong in H.
spliter.
assumption.
Qed.

Lemma plg_cong_2 : forall A B C D, Parallelogram A B C D -> Cong A D B C.
Proof.
intros.
apply plg_cong in H.
spliter.
assumption.
Qed.

Lemma plgs_cong_1 : forall A B C D, Parallelogram_strict A B C D -> Cong A B C D.
Proof.
intros.
apply plgs_cong in H.
spliter.
assumption.
Qed.

Lemma plgs_cong_2 : forall A B C D, Parallelogram_strict A B C D -> Cong A D B C.
Proof.
intros.
apply plgs_cong in H.
spliter.
assumption.
Qed.

Lemma Plg_perm :
  forall A B C D,
  Parallelogram A B C D ->
  Parallelogram A B C D /\ Parallelogram B C D A /\ Parallelogram C D A B /\Parallelogram D A B C /\ 
  Parallelogram A D C B /\ Parallelogram D C B A /\ Parallelogram C B A D /\ Parallelogram B A D C.
Proof.
intros.
split; try assumption.
split; try (apply plg_permut; assumption).
split; try (do 2 apply plg_permut; assumption).
split; try (do 3 apply plg_permut; assumption).
split; try (apply plg_comm2; do 3 apply plg_permut; assumption).
split; try (apply plg_comm2; do 2 apply plg_permut; assumption).
split; try (apply plg_comm2; apply plg_permut; assumption).
apply plg_comm2; assumption.
Qed.

Lemma plg_not_comm_1 :
  forall A B C D : Tpoint,
  A <> B ->
  Parallelogram A B C D -> ~ Parallelogram A B D C.
Proof.
intros.
assert (HNC := plg_not_comm A B C D H H0); spliter; assumption.
Qed.

Lemma plg_not_comm_2 :
  forall A B C D : Tpoint,
  A <> B ->
  Parallelogram A B C D -> ~ Parallelogram B A C D.
Proof.
intros.
assert (HNC := plg_not_comm A B C D H H0); spliter; assumption.
Qed.

End Quadrilateral_inter_dec_1.

Ltac assert_cols :=
repeat
 match goal with
      | H:Bet ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;assert (Col X1 X2 X3) by (apply bet_col;apply H)

      | H:Midpoint ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;let N := fresh in assert (N := midpoint_col X2 X1 X3 H)

      | H:Out ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;let N := fresh in assert (N := out_col X1 X2 X3 H)

      | H:Par ?X1 ?X2 ?X1 ?X3 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;let N := fresh in assert (N := par_id X1 X2 X3 H)
      | H:Par ?X1 ?X2 ?X3 ?X1 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;let N := fresh in
     assert (N := par_id X1 X2 X3 (par_right_comm X1 X2 X3 X1 H))
      | H:Par ?X2 ?X1 ?X1 ?X3 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;let N := fresh in
     assert (N := par_id X1 X2 X3 (par_left_comm X2 X1 X1 X3 H))
      | H:Par ?X2 ?X1 ?X3 ?X1 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;let N := fresh in
     assert (N := par_id X1 X2 X3 (par_comm X2 X1 X3 X1 H))
 end.

Ltac permutation_intro_in_hyps_aux :=
 repeat
 match goal with
 | H : Plg_tagged ?A ?B ?C ?D |- _ => apply Plg_tagged_Plg in H; apply Plg_perm in H; spliter
 | H : Par_tagged ?A ?B ?C ?D |- _ => apply Par_tagged_Par in H; apply Par_perm in H; spliter
 | H : Par_strict_tagged ?A ?B ?C ?D |- _ => apply Par_strict_tagged_Par_strict in H; apply Par_strict_perm in H; spliter
 | H : Perp_tagged ?A ?B ?C ?D |- _ => apply Perp_tagged_Perp in H; apply Perp_perm in H; spliter
 | H : Perp_in_tagged ?X ?A ?B ?C ?D |- _ => apply Perp_in_tagged_Perp_in in H; apply Perp_in_perm in H; spliter
 | H : Per_tagged ?A ?B ?C |- _ => apply Per_tagged_Per in H; apply Per_perm in H; spliter
 | H : Mid_tagged ?A ?B ?C |- _ => apply Mid_tagged_Mid in H; apply Mid_perm in H; spliter
 | H : NCol_tagged ?A ?B ?C |- _ => apply NCol_tagged_NCol in H; apply NCol_perm in H; spliter
 | H : Col_tagged ?A ?B ?C |- _ => apply Col_tagged_Col in H; apply Col_perm in H; spliter
 | H : Bet_tagged ?A ?B ?C |- _ => apply Bet_tagged_Bet in H; apply Bet_perm in H; spliter
 | H : Cong_tagged ?A ?B ?C ?D |- _ => apply Cong_tagged_Cong in H; apply Cong_perm in H; spliter
 | H : Diff_tagged ?A ?B |- _ => apply Diff_tagged_Diff in H; apply Diff_perm in H; spliter
 end.

Ltac permutation_intro_in_hyps := clean_reap_hyps; clean_trivial_hyps; tag_hyps; permutation_intro_in_hyps_aux.

Ltac assert_cols_aux :=
repeat
 match goal with
      | H:Bet ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp (Col X1 X2 X3);assert (Col X1 X2 X3) by (apply bet_col;apply H) 

      | H:Midpoint ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp (Col X1 X2 X3);let N := fresh in assert (N := midpoint_col X2 X1 X3 H)

      | H:Out ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp (Col X1 X2 X3);let N := fresh in assert (N := out_col X1 X2 X3 H)

      | H:Par ?X1 ?X2 ?X1 ?X3 |- _ =>
     not_exist_hyp (Col X1 X2 X3);let N := fresh in assert (N := par_id X1 X2 X3 H)
      | H:Par ?X1 ?X2 ?X1 ?X3 |- _ =>
     not_exist_hyp (Col X1 X2 X3);let N := fresh in assert (N := par_id_1 X1 X2 X3 H)
      | H:Par ?X1 ?X2 ?X1 ?X3 |- _ =>
     not_exist_hyp (Col X1 X2 X3);let N := fresh in assert (N := par_id_2 X1 X2 X3 H)
      | H:Par ?X1 ?X2 ?X1 ?X3 |- _ =>
     not_exist_hyp (Col X1 X2 X3);let N := fresh in assert (N := par_id_3 X1 X2 X3 H)
      | H:Par ?X1 ?X2 ?X1 ?X3 |- _ =>
     not_exist_hyp (Col X1 X2 X3);let N := fresh in assert (N := par_id_4 X1 X2 X3 H)
      | H:Par ?X1 ?X2 ?X1 ?X3 |- _ =>
     not_exist_hyp (Col X1 X2 X3);let N := fresh in assert (N := par_id_5 X1 X2 X3 H)

      | H:Par ?X1 ?X2 ?X3 ?X4, H2:Col ?X1 ?X2 ?X5, H3:Col ?X3 ?X4 ?X5 |- _ =>
     not_exist_hyp (Col X1 X2 X3);let N := fresh in assert (N := not_strict_par1 X1 X2 X3 X4 X5 H H2 H3)
 end.

Ltac assert_cols_perm := permutation_intro_in_hyps; assert_cols_aux; clean_reap_hyps.

Ltac not_exist_hyp_perm_cong A B C D := not_exist_hyp (Cong A B C D); not_exist_hyp (Cong A B D C);
                                        not_exist_hyp (Cong B A C D); not_exist_hyp (Cong B A D C);
                                        not_exist_hyp (Cong C D A B); not_exist_hyp (Cong C D B A);
                                        not_exist_hyp (Cong D C A B); not_exist_hyp (Cong D C B A).

Ltac assert_congs_1 :=
repeat
 match goal with
      | H:Midpoint ?X1 ?X2 ?X3 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_cong X1 X2 X1 X3;
      assert (h := midpoint_cong X2 X1 X3 H)

      | H1:Midpoint ?M1 ?A1 ?B1, H2:Midpoint ?M2 ?A2 ?B2, H3:Cong ?A1 ?B1 ?A2 ?B2 |- _ => 
      let h := fresh in
      not_exist_hyp_perm_cong A1 M1 A2 M2;
      assert (h := cong_cong_half_1 A1 M1 B1 A2 M2 B2 H1 H2 H3)

      | H:Parallelogram ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_cong X1 X2 X3 X4;
      assert (h := plg_cong_1 X1 X2 X3 X4 H)

      | H:Parallelogram_strict ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_cong X1 X2 X3 X4;
      assert (h := plgs_cong_1 X1 X2 X3 X4 H)
  end.

Ltac assert_congs_2 :=
repeat
 match goal with
      | H1:Midpoint ?M1 ?A1 ?B1, H2:Midpoint ?M2 ?A2 ?B2, H3:Cong ?A1 ?B1 ?A2 ?B2 |- _ => 
      let h := fresh in
      not_exist_hyp_perm_cong A1 M1 A2 M2;
      assert (h := cong_cong_half_2 A1 M1 B1 A2 M2 B2 H1 H2 H3)

      | H:Parallelogram ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_cong X1 X4 X2 X3;
      assert (h := plg_cong_2 X1 X2 X3 X4 H);clean_reap_hyps

      | H:Parallelogram_strict ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_cong X1 X4 X2 X3;
      assert (h := plgs_cong_2 X1 X2 X3 X4 H);clean_reap_hyps
  end.

Ltac assert_congs_perm := permutation_intro_in_hyps; assert_congs_1; assert_congs_2; clean_reap_hyps.

Ltac not_exist_hyp_perm_para A B C D := not_exist_hyp (Parallelogram A B C D); not_exist_hyp (Parallelogram B C D A);
                                        not_exist_hyp (Parallelogram C D A B); not_exist_hyp (Parallelogram D A B C);
                                        not_exist_hyp (Parallelogram A D C B); not_exist_hyp (Parallelogram D C B A);
                                        not_exist_hyp (Parallelogram C B A D); not_exist_hyp (Parallelogram B A D C).

Ltac not_exist_hyp_perm_para_s A B C D := not_exist_hyp (Parallelogram_strict A B C D);
                                          not_exist_hyp (Parallelogram_strict B C D A);
                                          not_exist_hyp (Parallelogram_strict C D A B);
                                          not_exist_hyp (Parallelogram_strict D A B C);
                                          not_exist_hyp (Parallelogram_strict A D C B);
                                          not_exist_hyp (Parallelogram_strict D C B A);
                                          not_exist_hyp (Parallelogram_strict C B A D);
                                          not_exist_hyp (Parallelogram_strict B A D C).

Ltac assert_paras_aux :=
repeat
 match goal with
      | H:Parallelogram_strict ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_para X1 X2 X3 X4;
      assert (h := Parallelogram_strict_Parallelogram X1 X2 X3 X4 H)

      | H:Plg ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_para X1 X2 X3 X4;
      assert (h := plg_to_parallelogram X1 X2 X3 X4 H)

      | H:(~ Col ?X1 ?X2 ?X3), H2:Par ?X1 ?X2 ?X3 ?X4, H3:Par ?X1 ?X4 ?X2 ?X3 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_para_s X1 X2 X3 X4;
      assert (h := parallel_2_plg X1 X2 X3 X4 H H2 H3)
  end.

Ltac assert_paras_perm := permutation_intro_in_hyps; assert_paras_aux; clean_reap_hyps.

Ltac not_exist_hyp_perm_npara A B C D := not_exist_hyp (~Parallelogram A B C D); not_exist_hyp (~Parallelogram B C D A);
                                         not_exist_hyp (~Parallelogram C D A B); not_exist_hyp (~Parallelogram D A B C);
                                         not_exist_hyp (~Parallelogram A D C B); not_exist_hyp (~Parallelogram D C B A);
                                         not_exist_hyp (~Parallelogram C B A D); not_exist_hyp (~Parallelogram B A D C).

Ltac assert_nparas_1 :=
 repeat
 match goal with
      | H:(?X1<>?X2), H2:Parallelogram ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_npara X1 X2 X4 X3;
      assert (h := plg_not_comm_1 X1 X2 X3 X4 H H2)
  end.

Ltac assert_nparas_2 :=
 repeat
 match goal with
      | H:(?X1<>?X2), H2:Parallelogram ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_npara X2 X1 X3 X4;
      assert (h := plg_not_comm_2 X1 X2 X3 X4 H H2)
  end.

Ltac assert_nparas_perm := permutation_intro_in_hyps; assert_nparas_1; assert_nparas_2; clean_reap_hyps.

Ltac diag_plg_intersection M A B C D H :=
 let T := fresh in assert(T:= plg_mid A B C D H);
 ex_and T M.

Tactic Notation "Name" ident(M) "the" "intersection" "of" "the" "diagonals" "(" ident(A) ident(C) ")" "and" "(" ident(B) ident(D) ")" "of" "the" "parallelogram" ident(H) :=
 diag_plg_intersection M A B C D H.

Ltac assert_diffs :=
repeat
 match goal with
      | H:(~Col ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp3 X1 X2 X1 X3 X2 X3;
      assert (h := not_col_distincts X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps 

      | H:(~Bet ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp2 X1 X2 X2 X3;
      assert (h := not_bet_distincts X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq12__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq21__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq23__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?C <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq32__neq A B C H H2);clean_reap_hyps

      | H:Cong ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= cong_diff A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= cong_diff_2 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?C <> ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= cong_diff_3 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?D <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= cong_diff_4 A B C D H2 H);clean_reap_hyps

      | H:Le ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= le_diff A B C D H2 H);clean_reap_hyps
      | H:Le ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= le_diff A B C D (swap_diff B A H2) H);clean_reap_hyps
      | H:Lt ?A ?B ?C ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= lt_diff A B C D H);clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= midpoint_distinct_1 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= midpoint_distinct_1 I A B (swap_diff B A H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?I<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= midpoint_distinct_2 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?A<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= midpoint_distinct_2 I A B (swap_diff A I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?I<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= midpoint_distinct_3 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?B<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= midpoint_distinct_3 I A B (swap_diff B I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Per ?A ?B ?C, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct A B C H (swap_diff B A H2)); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?C |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct_1 A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?C<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct_1 A B C H (swap_diff C B H2)); clean_reap_hyps

      | H:Perp ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= perp_distinct A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Perp_at ?X ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= perp_in_distinct X A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:TS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ts_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:OS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp5 A B A C A D B C B D;
      assert (h := os_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:~ Coplanar ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ncop_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps

      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= conga_diff1 A B C A' B' C' H);clean_reap_hyps
      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B C);
        assert (T:= conga_diff2 A B C A' B' C' H);clean_reap_hyps
      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A' B');
        assert (T:= conga_diff45 A B C A' B' C' H);clean_reap_hyps
      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B' C');
        assert (T:= conga_diff56 A B C A' B' C' H);clean_reap_hyps

      | H:(InAngle ?P ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp3 A B C B P B;
      assert (h := inangle_distincts A B C P H);decompose [and] h;clear h;clean_reap_hyps
      | H:LeA ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := lea_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:LtA ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := lta_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Acute ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := acute_distincts A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Obtuse ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := obtuse_distincts A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:SuppA ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := suppa_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps

      | H:(Orth_at ?X ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_at_distincts A B C U V X H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Orth ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_distincts A B C U V H);decompose [and] h;clear h;clean_reap_hyps

      | H:Inter ?A ?B ?C ?D ?X |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= inter_distincts A B C D X H);decompose [and] T;clear T;clean_reap_hyps

      | H:Par_strict ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp6 A B A C A D B C B D C D);
       assert (T:= par_strict_distinct A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Par ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= par_distincts A B C D H);decompose [and] T;clear T;clean_reap_hyps
      | H:Perp ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= perp_distinct A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Perp_at ?X ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= perp_in_distinct X A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:SumA ?A ?B ?C ?D ?E ?F ?G ?I ?J |- _ =>
      let h := fresh in
      not_exist_hyp6 A B B C D E E F G I I J;
      assert (h := suma_distincts A B C D E F G I J H);decompose [and] h;clear h;clean_reap_hyps

      | H:TriSumA ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp5 A B B C A C D E E F;
      assert (h := trisuma_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps

      | H:SAMS ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := sams_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps

      | H:Parallelogram_strict ?A ?B ?C ?D |- _ =>
      let T := fresh in
      not_exist_hyp6 A B B C C D D A A C B D;
       assert (T:= plgs_diff A B C D H);decompose [and] T;clear T;clean_reap_hyps
 end.

Hint Resolve parallelogram_strict_not_col
             parallelogram_strict_not_col_2
             parallelogram_strict_not_col_3
             parallelogram_strict_not_col_4 : col.

Hint Resolve plg_cong_1 plg_cong_2 plgs_cong_1 plgs_cong_2 : cong.

Section Quadrilateral_inter_dec_2.

Context `{TE:Tarski_euclidean}.

Lemma parallelogram_strict_midpoint : forall A B C D I,
  Parallelogram_strict A B C D ->
  Col I A C ->
  Col I B D ->
  Midpoint I A C /\ Midpoint I B D.
Proof.
intros.
assert (T:=Parallelogram_strict_Parallelogram A B C D H).
assert (HpF := plg_mid A B C D T).
elim HpF; intros I' HI;spliter;clear HpF.
assert (H01 : Col A C I).
 Col.
assert (H02 : Col D B I).
 Col.
assert (H03 : ~Col A D C).
 apply parallelogram_strict_not_col_3 in H.
 Col.
unfold Parallelogram_strict in H.
decompose [and] H.
(* trouver unicité intersection *)
assert (H8 := two_sides_not_col A C B D H4).
assert (MDB:D<>B).
 assert (Col A I' C).
  assert (H9 := midpoint_bet A I' C H2).
  assert (H10 := bet_col A I' C H9).
  assumption.
 assert (H11 : ~ Col A C D).
  Col.
 assert (H12 := l7_2 I' B D H3).
 assert (H13 : Col A C I').
  Col.
 apply (midpoint_distinct A C I' D B H11 H13 H12).
assert (H11 : Col D B I').
 assert (H14 := midpoint_bet B I' D H3).
 assert (H15 := bet_col B I' D H14).
 Col.
assert (H12 : Col A C I').
 assert (H14 := midpoint_bet A I' C H2).
 assert (H15 := bet_col A I' C H14).
 Col.
apply not_col_permutation_5 in H03.
assert (H13 := l6_21 A C D B I I' H03 MDB H01 H12 H02 H11).
split.
 rewrite H13;assumption.
 subst;assumption.
Qed.

Lemma rmb_perp :
 forall A B C D,
  A <> C -> B <> D ->
  Rhombus A B C D ->
  Perp A C B D.
Proof.
intros.
assert(HH:= H1).
unfold Rhombus in HH.
spliter.
apply plg_to_parallelogram in H2.
apply plg_mid in H2.
ex_and H2 M.
assert(HH:= H1).
eapply (rmb_per _ _ _ _ M) in HH.
apply per_perp_in in HH.

apply perp_in_perp_bis in HH.
induction HH.
apply perp_not_eq_1 in H5.
tauto.
unfold Midpoint in *.
spliter.
eapply perp_col.
assumption.
apply perp_sym.
apply perp_left_comm.
eapply perp_col.
auto.
apply perp_left_comm.
apply perp_sym.
apply H5.
apply bet_col in H4.
Col.
apply bet_col in H2.
Col.
intro.
subst M.
apply is_midpoint_id in H2.
contradiction.
intro.
subst M.
apply l7_2 in H4.
apply is_midpoint_id in H4.
subst D.
tauto.
assumption.
Qed.

Lemma rect_permut : forall A B C D, Rectangle A B C D -> Rectangle B C D A.
Proof.
intros.
unfold Rectangle in *.
spliter.
split.
apply plg_to_parallelogram in H.
apply plg_permut in H.
apply parallelogram_to_plg in H.
assumption.
Cong.
Qed.

Lemma rect_comm2 : forall A B C D, Rectangle A B C D -> Rectangle B A D C.
Proof.
intros.
unfold Rectangle in *.
spliter.
apply plg_to_parallelogram in H.

apply plg_comm2 in H.
split.
apply parallelogram_to_plg.
assumption.
Cong.
Qed.

Lemma rect_per1 : forall A B C D, Rectangle A B C D -> Per B A D.
Proof.
intros.
unfold Rectangle in H.
spliter.

assert(HH:= midpoint_existence A B).
ex_and HH P.
assert(HH:= midpoint_existence C D).
ex_and HH Q.
assert(HH:=H).
unfold Plg in HH.
spliter.
ex_and H4 M.
apply plg_to_parallelogram in H.
induction H.

assert(HH:=half_plgs A B C D P Q M H H1 H2 H4).
spliter.
assert(Per A P Q).
eapply (per_col _  _ M).
intro.
subst M.
apply is_midpoint_id in H7.
subst Q.
apply cong_identity in H8.
subst D.
assert(B = C).
eapply symmetric_point_uniqueness.
apply l7_2.
apply H5.
Midpoint.
subst C.
unfold Parallelogram_strict in H.
spliter.
unfold TS in H.
spliter.
apply H9.
Col.
apply l8_2.
unfold Per.
exists B.
split.
assumption.
eapply (cong_cong_half_1 _ M _ _ M) in H0.
Cong.
assumption.
assumption.
unfold Midpoint in H7.
spliter.
apply bet_col.
assumption.

assert(A <> B).
intro.
subst B.
apply l7_3 in H1.
subst P.
unfold Parallelogram_strict in H.
spliter.
unfold TS in H.
spliter.
apply H.
Col.

assert(A <> P).
intro.
subst P.
apply is_midpoint_id in H1.
contradiction.

apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.

apply perp_sym.
apply perp_left_comm.
eapply cop_par_perp__perp.
apply H6.
apply per_perp_in in H9.
apply perp_in_perp_bis in H9.
induction H9.
apply perp_not_eq_1 in H9.
tauto.
apply perp_sym.
eapply perp_col.
assumption.
apply H9.
unfold Midpoint in H1.
spliter.
apply bet_col.
assumption.
assumption.

induction H6.
unfold Par_strict in H6.
spliter.
assumption.
spliter.
assumption.
Cop.
unfold Parallelogram_flat in H.
spliter.

assert(A = B /\ C = D \/ A = D /\ C = B).
apply(midpoint_cong_uniqueness A C B D M).
Col.
split; assumption.
assumption.
induction H10.
spliter.
subst B.
apply l8_2.
apply l8_5.
spliter.
subst D.
apply l8_5.
Qed.

Lemma rect_per2 : forall A B C D, Rectangle A B C D -> Per A B C.
Proof.
intros.
apply rect_comm2 in H.
eapply rect_per1.
apply H.
Qed.

Lemma rect_per3 : forall A B C D, Rectangle A B C D -> Per B C D.
Proof.
intros.
apply rect_permut in H.
apply rect_comm2 in H.
eapply rect_per1.
apply H.
Qed.

Lemma rect_per4 : forall A B C D, Rectangle A B C D -> Per A D C.
Proof.
intros.
apply rect_comm2 in H.
eapply rect_per2.
apply rect_permut.
apply H.
Qed.

Lemma plg_per_rect1 : forall A B C D, Plg A B C D -> Per D A B -> Rectangle A B C D.
Proof.
intros.

assert(HH:= midpoint_existence A B).
ex_and HH P.
assert(HH:= midpoint_existence C D).
ex_and HH Q.
assert(HH:=H).
unfold Plg in HH.
spliter.
ex_and H4 M.
apply plg_to_parallelogram in H.
induction H.

assert(HH:=half_plgs A B C D P Q M H H1 H2 H4).
spliter.

assert(A <> D /\ P <> Q).
induction H6.
unfold Par_strict in H6.
spliter.
unfold Par in H6.
split; assumption.
spliter.
split; assumption.
spliter.

assert(A <> B).
intro.
subst B.
unfold Parallelogram_strict in H.
spliter.
unfold TS in H.
spliter.
apply H.
Col.
assert(A <> P).
intro.
subst P.
apply is_midpoint_id in H1.
contradiction.

assert(Perp P Q A B).
apply (cop_par_perp__perp A D P Q A B).
Par.
apply per_perp_in in H0.
apply perp_in_comm in H0.
apply perp_in_perp_bis in H0.
induction H0.
apply perp_right_comm.
assumption.
apply perp_not_eq_1 in H0.
tauto.
auto.
assumption.
assert_cols.
Cop.

assert(Perp P M A B).
eapply perp_col.
intro.
subst M.
apply is_midpoint_id in H7.
contradiction.
apply H13.
unfold Midpoint in H7.
spliter.
apply bet_col in H7.
Col.

assert(Perp A P P M).
eapply perp_col.
assumption.
apply perp_sym.
apply H14.
unfold Midpoint in H1.
spliter.
apply bet_col in H1.
Col.

assert(Per A P M).
apply perp_comm in H15.
apply perp_perp_in in H15.
apply perp_in_comm in H15.
apply perp_in_per in H15.
assumption.

unfold Rectangle.
split.
apply parallelogram_to_plg .
left.
assumption.

apply l8_2 in H16.
unfold Per in H16.
ex_and H16 B'.
assert(B = B').
eapply symmetric_point_uniqueness.
apply H1.
assumption.
subst B'.

unfold Midpoint in H4.
spliter.
unfold Midpoint in H5.
spliter.
eapply l2_11.
apply H4.
apply H5.
Cong.
apply cong_transitivity with A M; Cong.
apply cong_transitivity with B M; Cong.

unfold Rectangle.
split.
apply parallelogram_to_plg.
right.
assumption.

unfold Parallelogram_flat in H.
spliter.

assert(D = A \/ B = A).
apply (l8_9 D A B).
assumption.
Col.
induction H10.
subst D.
apply cong_symmetry in H8.
apply cong_identity in H8.
subst C.
Cong.
subst B.
apply cong_symmetry in H7.
apply cong_identity in H7.
subst D.
Cong.
Qed.

Lemma plg_per_rect2 : forall A B C D, Plg A B C D -> Per C B A -> Rectangle A B C D.
Proof.
intros.
apply rect_comm2.
apply plg_per_rect1.
apply parallelogram_to_plg.
apply plg_to_parallelogram in H.
apply plg_comm2.
assumption.
assumption.
Qed.

Lemma plg_per_rect3 : forall A B C D, Plg A B C D -> Per A D C -> Rectangle A B C D.
Proof.
intros.
apply rect_permut.
apply plg_per_rect1.
apply parallelogram_to_plg.
apply plg_to_parallelogram in H.
apply plg_permut.
apply plg_sym.
assumption.
apply l8_2.
assumption.
Qed.

Lemma plg_per_rect4 : forall A B C D, Plg A B C D -> Per B C D -> Rectangle A B C D.
Proof.
intros.
apply rect_comm2.
apply plg_per_rect3.
apply parallelogram_to_plg.
apply plg_to_parallelogram in H.
apply plg_comm2.
assumption.
assumption.
Qed.

Lemma plg_per_rect : forall A B C D, Plg A B C D -> (Per D A B \/ Per C B A \/ Per A D C \/ Per B C D) -> Rectangle A B C D.
Proof.
intros.
induction H0.
apply plg_per_rect1; assumption.
induction H0.
apply plg_per_rect2; assumption.
induction H0.
apply plg_per_rect3; assumption.
apply plg_per_rect4; assumption.
Qed.

Lemma rect_per : forall A B C D, Rectangle A B C D -> Per B A D /\ Per A B C /\ Per B C D /\ Per A D C.
Proof.
intros.
repeat split.
apply (rect_per1 A B C D); assumption.
apply (rect_per2 A B C D); assumption.
apply (rect_per3 A B C D); assumption.
apply (rect_per4 A B C D); assumption.
Qed.

Lemma plgf_rect_id : forall A B C D, Parallelogram_flat A B C D -> Rectangle A B C D -> A = D /\ B = C \/ A = B /\ D = C.
Proof.
intros.
unfold Parallelogram_flat in H.
spliter.
assert(Per B A D /\ Per A B C /\ Per B C D /\ Per A D C).

apply rect_per.
assumption.
spliter.

assert(HH:=l8_9 A B C H6 H).
induction HH.
right.
subst B.
apply cong_symmetry in H2.
apply cong_identity in H2.
subst D.
split; reflexivity.
left.
subst B.
apply cong_identity in H3.
subst D.
split; reflexivity.
Qed.

Lemma cop_perp3__perp :
 forall A B C D,
  Coplanar A B C D ->
  Perp A B B C ->
  Perp B C C D ->
  Perp C D D A ->
  Perp D A A B.
Proof.
intros.
assert (Par A B C D)
 by (apply (l12_9 A B C D B C); Perp; Cop).
assert (Perp A B D A)
 by (apply (cop_par_perp__perp C D A B D A); Perp; Par; Cop).
auto using perp_sym, perp_left_comm.
Qed.

Lemma cop_perp3__rect :
 forall A B C D,
  Coplanar A B C D ->
  Perp A B B C ->
  Perp B C C D ->
  Perp C D D A ->
  Rectangle A B C D.
Proof.
intros.
assert (~ Col A B C)
 by (assert_diffs; apply per_not_col; Perp).
assert (Par A B C D)
 by (apply (l12_9 A B C D B C); Perp; Cop).
assert (Perp D A A B)
 by (eapply cop_perp3__perp;eauto).
assert (Par A D B C)
 by (apply (l12_9 A D B C A B); Perp; Cop).
assert (Parallelogram_strict A B C D)
 by (apply (parallel_2_plg); auto).
apply plg_per_rect1.
apply parallelogram_to_plg.
apply Parallelogram_strict_Parallelogram.
assumption.
Perp.
Qed.

Lemma conga_to_par_os : forall A B C D P , Bet A D P -> OS A D B C -> CongA B A P C D P
                                           -> Par A B C D.
Proof.
intros A B C D P HBet HOS HCongA.
assert_diffs.
apply par_right_comm, l12_22_b with P; trivial.
  apply l6_6, bet_out; Between.
apply invert_one_side, col_one_side with D; Col.
Qed.

Lemma plg_par : forall A B C D, A <> B -> B <> C -> Parallelogram A B C D -> Par A B C D /\ Par A D B C.
Proof.
intros.
assert(HH:= H1).
apply plg_mid in HH.
ex_and HH M.

assert(HH:=l12_17 A B C D M H H2 H3).
apply l7_2 in H2.
assert(HH1:=l12_17 B C D A M H0 H3 H2).
split.
assumption.
apply par_symmetry.
Par.
Qed.

Lemma plg_par_1 : forall A B C D, A <> B -> B <> C -> Parallelogram A B C D -> Par A B C D.
Proof with finish.
intros.
assert (HPar := plg_par A B C D H H0 H1); spliter...
Qed.

Lemma plg_par_2 : forall A B C D, A <> B -> B <> C -> Parallelogram A B C D -> Par A D B C.
Proof with finish.
intros.
assert (HPar := plg_par A B C D H H0 H1); spliter...
Qed.

Lemma plgs_pars_1: forall A B C D : Tpoint, Parallelogram_strict A B C D -> Par_strict A B C D.
Proof with finish.
intros.
assert (HPar := plgs_par_strict A B C D H); spliter...
Qed.

Lemma plgs_pars_2: forall A B C D : Tpoint, Parallelogram_strict A B C D -> Par_strict A D B C.
Proof with finish.
intros.
assert (HPar := plgs_par_strict A B C D H); spliter...
Qed.

End Quadrilateral_inter_dec_2.

Ltac not_exist_hyp_perm_par A B C D := not_exist_hyp (Par A B C D); not_exist_hyp (Par A B D C);
                                       not_exist_hyp (Par B A C D); not_exist_hyp (Par B A D C);
                                       not_exist_hyp (Par C D A B); not_exist_hyp (Par C D B A);
                                       not_exist_hyp (Par D C A B); not_exist_hyp (Par D C B A).

Ltac not_exist_hyp_perm_pars A B C D := not_exist_hyp (Par_strict A B C D); not_exist_hyp (Par_strict A B D C);
                                        not_exist_hyp (Par_strict B A C D); not_exist_hyp (Par_strict B A D C);
                                        not_exist_hyp (Par_strict C D A B); not_exist_hyp (Par_strict C D B A);
                                        not_exist_hyp (Par_strict D C A B); not_exist_hyp (Par_strict D C B A).

Ltac assert_pars_1 :=
 repeat
 match goal with
      | H:Par_strict ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_par X1 X2 X3 X4;
      assert (h := par_strict_par X1 X2 X3 X4 H)

      | H:Par ?X1 ?X2 ?X3 ?X4, H2:Col ?X1 ?X2 ?X5, H3:(~Col ?X3 ?X4 ?X5) |- _ =>
      let h := fresh in
      not_exist_hyp_perm_pars X1 X2 X3 X4;
      assert (h := par_not_col_strict X1 X2 X3 X4 X5 H H2 H3)

      | H: ?X1 <> ?X2, H2:?X2 <> ?X3, H3:Parallelogram ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_par X1 X2 X3 X4;
      assert (h := plg_par_1 X1 X2 X3 X4 H H2 H3)

      | H:Parallelogram_strict ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_pars X1 X2 X3 X4;
      assert (h := plgs_pars_1 X1 X2 X3 X4 H)
  end.

Ltac assert_pars_2 :=
 repeat
 match goal with
      | H: ?X1 <> ?X2, H2:?X2 <> ?X3, H3:Parallelogram ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_par X1 X4 X2 X3;
      assert (h := plg_par_2 X1 X2 X3 X4 H H2 H3)

      | H:Parallelogram_strict ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_pars X1 X4 X2 X3;
      assert (h := plgs_pars_2 X1 X2 X3 X4 H)
  end.

Ltac assert_pars_perm := permutation_intro_in_hyps; assert_pars_1; assert_pars_2; clean_reap_hyps.

Hint Resolve plg_par_1 plg_par_2 plgs_pars_1 plgs_pars_2 : par.

Section Quadrilateral_inter_dec_3.

Context `{TE:Tarski_euclidean}.

Lemma par_cong_cong : forall A B C D, Par A B C D -> Cong A B C D -> Cong A C B D \/ Cong A D B C.
Proof.
intros.

induction(eq_dec_points A B).
subst B.
apply cong_symmetry in H0.
apply cong_identity in H0.
subst D.
left.
Cong.

induction(eq_dec_points A D).
subst D.

assert(B = C \/ Midpoint A B C).
eapply l7_20.
unfold Par in H.
induction H.
apply False_ind.
unfold Par_strict in H.
spliter.
apply H4.
exists A.
split; Col.
spliter.
Col.
Cong.
induction H2.
subst C.
left.
Cong.
unfold Midpoint in H2.
spliter.
left.
Cong.

assert(HH:=par_cong_mid A B C D H H0).
ex_and HH M.
induction H3.
spliter.
right.

assert(HH:=mid_par_cong A B C D M H1 H2 H3 H4).
spliter.
Cong.

induction(eq_dec_points A C).
subst C.
assert(B = D \/ Midpoint A B D).
eapply l7_20.
unfold Par in H.
induction H.
apply False_ind.
unfold Par_strict in H.
spliter.
apply H7.
exists A.
split; Col.
spliter.
Col.
Cong.
induction H4.
subst D.
right.
Cong.
unfold Midpoint in H4.
spliter.
right.
Cong.

left.
spliter.
assert(HH:=mid_par_cong A B D C M H1 H4 H3 H5).
spliter.
Cong.
Qed.

Lemma col_cong_cong : forall A B C D, Col A B C -> Col A B D -> Cong A B C D -> Cong A C B D \/ Cong A D B C.
Proof.
intros.

induction(eq_dec_points A B).
subst B.
apply cong_symmetry in H1.
apply cong_identity in H1.
subst D.
left.
Cong.

induction(eq_dec_points C D).
subst D.
apply cong_identity in H1.
subst B.
right.
Cong.

apply par_cong_cong.
right.
repeat split; Col; ColR.
assumption.
Qed.

Lemma par_cong_cop :
  forall A B C D, Par A B C D -> Cong A B C D -> Coplanar A B C D.
Proof.
intros.
destruct (par_cong_mid A B C D) as [M HM]; trivial.
exists M; right.
destruct HM as [[]|[]]; [left|right]; split; Col.
Qed.

Lemma par_cong_plg :
  forall A B C D, Par A B C D -> Cong A B C D -> Plg A B C D \/ Plg A B D C.
Proof.
intros A B C D HPar HCong.
destruct (par_cong_mid A B C D) as [M HM]; trivial.
elim HM; clear HM; intro HM; destruct HM as [HMid1 HMid2].

  {
  left; split; try (exists M; Col).
  elim (eq_dec_points A C); intro HAC; treat_equalities; Col; right;
  intro; treat_equalities; apply par_distincts in HPar; spliter; Col.
  }

  {
  right; split; try (exists M; Col).
  elim (eq_dec_points A D); intro HAD; treat_equalities; Col; right;
  intro; treat_equalities; apply par_distincts in HPar; spliter; Col.
  }
Qed.

Lemma par_cong_plg_2 :
  forall A B C D,
  Par A B C D ->
  Cong A B C D ->
  Parallelogram A B C D \/ Parallelogram A B D C.
Proof.
intros.
assert (HElim : Plg A B C D \/ Plg A B D C)
  by (apply par_cong_plg; assumption).
elim HElim; intro.

  left; apply plg_to_parallelogram; assumption.

  right; apply plg_to_parallelogram; assumption.
Qed.

Lemma par_cong3_rect : forall A B C D, A <> C \/ B <> D -> Par A B C D -> Cong A B C D -> Cong A D B C -> Cong A C B D -> Rectangle A B C D \/ Rectangle A B D C.
Proof.
intros.
unfold Par in H0.
induction H0.

assert(HH:=par_strict_cong_mid1 A B C D H0 H1).

induction HH.
spliter.
left.
unfold Rectangle.
split; auto.
unfold Plg.
split; auto.
spliter.
ex_and H5 M.

right.
unfold Rectangle.
split; auto.
unfold Plg.
split; auto.

left.
intro.
subst D.
unfold Par_strict in H0.
spliter.
apply H9.
exists A.
split; Col.
exists M.
split; auto.

spliter.
left.
unfold Rectangle.
split; auto.

apply parallelogram_to_plg.
unfold Parallelogram.
right.
unfold Parallelogram_flat.

induction(eq_dec_points C D).
subst D.
apply cong_identity in H1.
subst B.
repeat split; Col; Cong.
repeat split; Col; Cong; ColR.
Qed.

Lemma pars_par_pars : forall A B C D, Par_strict A B C D -> Par A D B C -> Par_strict A D B C.
Proof.
intros.
induction H0.
assumption.
spliter.
repeat split; Cop.
intro.
ex_and H4 X.
unfold Par_strict in H.
spliter.
apply H8.
exists C.
split; Col.
Qed.

Lemma pars_par_plg : forall A B C D, Par_strict A B C D -> Par A D B C -> Plg A B C D.
Proof.
intros.
assert(Par_strict A D B C).
apply pars_par_pars; auto.

assert(Par A B C D).
left.
assumption.

assert(A <> B /\ C <> D /\ A <> D /\ B <> C).
apply par_distinct in H0.
apply par_distinct in H2.
spliter.
auto.
spliter.

assert(A <> C).
intro.
subst C.
unfold Par_strict in H.
spliter.
apply H9.
exists A.
split; Col.

assert(B <> D).
intro.
subst D.
unfold Par_strict in H.
spliter.
apply H10.
exists B.
split; Col.

unfold Plg.
split.

left.
assumption.

assert(HH:=midpoint_existence A C).
ex_and HH M.
exists M.
split.
assumption.
prolong B M D' B M.
assert(Midpoint M B D').
unfold Midpoint.
split; auto.
Cong.
assert(Plg A B C D').
unfold Plg.
repeat split.
induction H.
left.

assumption.

exists M.
split; auto.

assert(Parallelogram A B C D').
apply plg_to_parallelogram.
assumption.
assert(HH:=plg_par A B C D' H3 H6 H14).
spliter.

assert(~Col C A B).
intro.
unfold Par_strict in H.
spliter.
apply H20.
exists C.
split; Col.

assert(Col C C D /\ Col D' C D).

apply (parallel_uniqueness A B C D C D' C H2).
Col.
assumption.
Col.
spliter.

assert(A <> D').
intro.
subst D'.
unfold Par_strict in H1.
spliter.
apply H22.
exists C.
split; Col.

assert(HH:=mid_par_cong A B C D' M H3 H20 H9 H12).
spliter.

assert(Col A A D /\ Col D' A D).
apply (parallel_uniqueness B C A D A D' A).

Par.
Col.
apply par_left_comm.
Par.
Col.
spliter.

assert(D = D').

eapply (l6_21 A D C D D D'); Col.
intro.
unfold Par_strict in H.
spliter.
apply H30.
exists A.
split; Col.
subst D'.
assumption.
Qed.

Lemma not_par_pars_not_cong : forall O A B A' B', Out O A B -> Out O A' B' -> Par_strict A A' B B' -> ~Cong A A' B B'.
Proof.
intros.
intro.

assert(A <> B).
intro.
subst B.
unfold Par_strict in H1.
spliter.
apply H5.
exists A.
split; Col.

assert(A' <> B').
intro.
subst B'.
unfold Par_strict in H1.
spliter.
apply H6.
exists A'.
split; Col.

assert(O <> A).
unfold Out in H.
spliter.
auto.

assert(O <> A').
unfold Out in H0.
spliter.
auto.

assert(~Col O A A').
intro.
apply out_col in H.
apply out_col in H0.
assert(Col O B A').
ColR.
unfold Par_strict in H1.
spliter.
apply H11.
exists O.
split.
assumption.
ColR.

assert(OS A B A' B').

apply(out_one_side_1 _ _  _ _ O).
intro.
apply H7.
apply out_col in H.
apply out_col in H0.
ColR.
apply out_col in H.
Col.
assumption.

assert(Par A A' B B').
left.
assumption.

assert(HH:=os_cong_par_cong_par A A' B B' H8 H2 H9).
spliter.
unfold Par in H11.
induction H11.
unfold Par_strict in H11.
spliter.
apply H14.
exists O.
split.
apply out_col in H.
assumption.
apply out_col in H0.
assumption.
spliter.
apply H7.
apply out_col in H.
apply out_col in H0.
ColR.
Qed.

Lemma plg_uniqueness : forall A B C D D', Parallelogram A B C D -> Parallelogram A B C D' -> D = D'.
Proof.
intros.
apply plg_mid in H.
apply plg_mid in H0.
ex_and H M.
ex_and H0 M'.
assert(M = M').
eapply l7_17.
apply H.
assumption.
subst M'.
eapply symmetric_point_uniqueness.
apply H1.
assumption.
Qed.

Lemma plgs_trans_trivial : forall A B C D B', Parallelogram_strict A B C D -> Parallelogram_strict C D A B' 
                                             -> Parallelogram A B B' A.
Proof.
intros.
apply plgs_permut in H.
apply plgs_permut in H.
assert (B = B').
eapply plg_uniqueness.
left.
apply H.
left.
assumption.
subst B'.
apply plg_trivial.
apply plgs_diff in H.
spliter.
assumption.
Qed.

Lemma par_strict_trans : forall A B C D E F, Par_strict A B C D -> Par_strict C D E F -> Par A B E F.
Proof.
intros.
eapply par_trans.
left.
apply H.
left.
assumption.
Qed.

Lemma plgs_pseudo_trans : forall A B C D E F, Parallelogram_strict A B C D -> Parallelogram_strict C D E F -> Parallelogram A B F E.
Proof.
intros.

induction(eq_dec_points A E).
subst E.
eapply (plgs_trans_trivial A B C D); assumption.

apply plgs_diff in H.
apply plgs_diff in H0.
spliter.

clean_duplicated_hyps.

prolong D C D' D C.

assert(C <> D').
intro.
subst D'.
apply cong_symmetry in H14.
apply cong_identity in H14.
subst D.
tauto.

assert(HH1:=plgs_par_strict A B C D H).
assert(HH2:=plgs_par_strict C D E F H0).
spliter.

apply par_strict_symmetry in H18.

assert(HH1:= l12_6 C D A B H18).
assert(HH2:= l12_6 C D E F H16).


assert(CongA A D D' B C D').
apply par_preserves_conga_os.
left.
Par.
assumption.
assumption.
apply invert_one_side.
assumption.

assert(CongA E D D' F C D').
apply par_preserves_conga_os.
left.
Par.
assumption.
assumption.
apply invert_one_side.
assumption.

assert(~ Col A C D).
apply (par_strict_not_col_2 B).
Par.

assert(~ Col E C D).
apply (par_strict_not_col_2 F).
Par.

induction (cop_dec C D A E).

assert(HH:=cop__one_or_two_sides C D A E H24 H22 H23).

assert(CongA A D E B C F).

induction HH.

assert(TS C D A F).
apply l9_2.
eapply l9_8_2.
apply l9_2.
apply H25.
assumption.

assert(TS C D B F).
eapply l9_8_2.
apply H26.
assumption.

apply(l11_22a A D E D' B C F D').
split.
eapply col_two_sides.
apply bet_col.
apply H2.
intro.
subst D'.
apply between_identity in H2.
subst D.
tauto.
apply invert_two_sides.
assumption.
split.
eapply (col_two_sides _ D).
apply bet_col in H2.
Col.
assumption.
assumption.
split.
assumption.
apply conga_comm.
assumption.

apply(l11_22b A D E D' B C F D').
split.
eapply col_one_side.
apply bet_col.
apply H2.
intro.
subst D'.
apply between_identity in H2.
subst D.
tauto.
apply invert_one_side.
assumption.
split.
eapply (col_one_side _ D).
apply bet_col in H2.
Col.
assumption.
eapply one_side_transitivity.
apply one_side_symmetry.
apply HH1.
apply one_side_symmetry.
eapply one_side_transitivity.
apply one_side_symmetry.
apply HH2.
apply one_side_symmetry.
assumption.
split.
assumption.
apply conga_comm.
assumption.

assert(HP0:=plgs_cong A B C D H).
assert(HP1:=plgs_cong C D E F H0).
spliter.
apply cong_symmetry in H27.

assert(HP:=cong2_conga_cong A D E B C F H25 H29 H27).
(**************)

assert(Par A B E F).
eapply par_trans.
apply par_symmetry.
left.
apply H18.
left.
assumption.

induction(col_dec A E F).
induction H30.
apply False_ind.
apply H30.
exists A.
split; Col.
spliter.

right.
unfold Parallelogram_flat.
repeat split; Cong.
ColR.
ColR.
apply cong_transitivity with C D; Cong.

induction(eq_dec_points A F).
right.
subst F.
intro.
subst E.

apply cong_symmetry in H27.

assert(HQ:=par_strict_cong_mid C A D B H17 H27).
ex_and HQ M.
induction H35.
unfold Midpoint in *.
spliter.

apply H16.
exists M.
split; Col.
unfold Midpoint in *.
spliter.
apply H19.
exists M.
split.
ColR.
ColR.
left.
assumption.

assert(Par A E B F \/ ~ Par_strict D C A B \/ ~ Par_strict D C E F).

eapply(cong3_par2_par ); auto.
repeat split; Cong.
apply par_comm.
left.
assumption.
apply par_symmetry.
left.
assumption.

induction H32.
apply plg_to_parallelogram.
apply pars_par_plg.

assert(Par A B F E).
eapply par_trans.
apply par_symmetry.
left.
apply H18.
apply par_right_comm.
left.
assumption.
induction H33.
assumption.
spliter.
apply False_ind.
apply H31.
Col.
assumption.
induction H32.
apply False_ind.
apply H32.
apply par_strict_left_comm.
assumption.
apply False_ind.
apply H32.
apply par_strict_left_comm.
assumption.

destruct (par_cong_plg_2 A B E F); auto.
apply par_trans with C D; Par.
apply cong_transitivity with C D; apply plgs_cong_1; assumption.
exfalso.

assert (OS A E B F).
apply (cop3_osp__os A D E); Cop.
assert (~ Col D A B) by (apply (par_strict_not_col_2 C), H18).
apply osp_transitivity with C.
  apply cop2_os__osp with A D; [|Cop..|Side].
  intro; apply H24, coplanar_perm_12, coplanar_trans_1 with B; Col; Cop.
apply cop2_os__osp with D E; [|Cop..|Side].
intro; apply H24, coplanar_perm_12, coplanar_trans_1 with C; Col; Cop.

apply (l9_9 A E B F); [|assumption].
repeat split.
  apply one_side_not_col123 in H26; Col.
  apply one_side_not_col124 in H26; Col.
apply plg_mid in H25.
destruct H25 as [M []].
exists M; split; [Col|Between].
Qed.



Lemma plgf_plgs_trans : forall A B C D E F, A <> B -> Parallelogram_flat A B C D -> Parallelogram_strict C D E F -> Parallelogram_strict A B F E.
Proof.
intros.

induction(eq_dec_points A D).
subst D.
induction H0.
spliter.
apply cong_symmetry in H4.
apply cong_identity in H4.
spliter.
subst C.
apply plgs_comm2.
assumption.

induction(eq_dec_points B C).
subst C.
induction H0.
spliter.
apply cong_identity in H5.
spliter.
subst D.
apply plgs_comm2.
assumption.

assert(HH:=plgs_par_strict C D E F H1).
spliter.

assert(HH:=plgs_cong C D E F H1).
spliter.

assert(HH2:= l12_6 C D E F H4).

assert(HOS := HH2).
induction HH2.
spliter.

unfold TS in H9.
assert(~ Col F C D).
spliter.
assumption.
spliter.
unfold TS in H8.
assert(~ Col E C D).
spliter.
assumption.
spliter.

assert(D <> E).
intro.
subst E.
apply H13.
Col.
assert(HH0:=H0).

induction HH0.
spliter.

prolong D C D' D C.

assert(D <> D').
intro.
subst D'.
apply between_identity in H22.
subst D.
Col.

assert(C <> D').
intro.
subst D'.
apply cong_symmetry in H23.
apply cong_identity in H23.
contradiction.


assert(CongA E D D' F C D').

apply(par_preserves_conga_os D E F C D').
apply par_symmetry.
apply par_left_comm.
left.
assumption.
assumption.
intro.
subst D'.
apply cong_symmetry in H23.
apply cong_identity in H23.
subst D.
tauto.
apply invert_one_side.
assumption.

induction(eq_dec_points A C).
subst C.
assert(B=D \/ Midpoint A B D).
eapply l7_20.
Col.
Cong.
(*induction H21.
tauto.*)
induction H27.
induction H21.
tauto.
contradiction.

unfold Parallelogram_strict.
spliter.
split.

apply l9_2.

eapply (l9_8_2  _ _ D).
unfold TS.
repeat split.
intro.
apply H10.
Col.
intro.
apply H10.
ColR.

exists A.
split.
Col.
apply midpoint_bet.
apply l7_2.
assumption.
eapply l12_6.
assumption.
split.
eapply (par_col_par_2 _ D).
auto.
unfold Midpoint in H27.
spliter.
apply bet_col in H27.
Col.
apply par_right_comm.
left.
assumption.
apply cong_transitivity with A D; Cong.

induction(eq_dec_points B D).
subst D.

assert(A=C \/ Midpoint B A C).
eapply l7_20.
Col.
Cong.

induction H28.
tauto.

apply plgs_comm2.
unfold Parallelogram_strict.
split.
apply l9_2.

eapply (l9_8_2 _ _ C).
unfold TS.
repeat split.
auto.
intro.
apply H13.
Col.
intro.
apply H13.
ColR.
exists B.
split.
Col.
apply midpoint_bet.
apply l7_2.
assumption.
eapply l12_6.
apply par_strict_symmetry.
assumption.
split.
eapply (par_col_par_2 _ C).
auto.
unfold Midpoint in H28.
spliter.
apply bet_col in H28.
Col.
apply par_left_comm.
left.
assumption.
apply cong_transitivity with C B; Cong.

assert(HH:=plgf_bet A B D C H0).

assert(CongA A D E B C F).

induction HH.
spliter.
eapply out_conga.
apply conga_comm.
apply H26.
repeat split.
auto.
auto.
eapply (l5_1 _ C).
intro.
subst D.
Col.
Between.
Between.
apply out_trivial.
intro.
subst E.
apply H13.
Col.
repeat split.
auto.
auto.

assert(Bet D C B).
eapply outer_transitivity_between.
apply H29.
assumption.
auto.

eapply (l5_2 D);
auto.
intro.
subst D.
Col.

apply out_trivial.
intro.
subst F.
apply H10.
Col.

induction H29.

spliter.

eapply (out_conga D' D E D' C F).
apply conga_comm.
apply H26.
unfold Out.
repeat split;auto.
right.
eBetween.
apply out_trivial.
intro.
subst E.
apply H13.
Col.
repeat split; auto.
right.

eapply (bet3_cong3_bet A B C D D');
auto;
Cong.
apply out_trivial.
intro.
subst F.
apply H10.
Col.

induction H29.
spliter.

eapply l11_13.

apply conga_comm.
apply H26.

assert_diffs.
eBetween.
auto.
eBetween.
auto.

spliter.

eapply l11_13.

apply conga_comm.

apply H26.
assert_diffs.
eBetween.
auto.
assert_diffs.
eBetween.
auto.


assert(Cong A E B F).

eapply(cong2_conga_cong A D E B C F H29);Cong.
assert(Cong_3 E A D F B C).
repeat split; Cong.

assert(Par A B E F).
eapply (par_trans A B C D E F).
right.
repeat split; auto.
intro.
subst.
Col.
ColR.
ColR.
left.
assumption.

assert(CongA E A D F B C).
apply cong3_conga.
intro.
subst E.
apply H13.
ColR.
auto.
assumption.

assert(OS A B E F).
eapply l12_6.
induction H32.
assumption.
spliter.
assert(Col A B E).
ColR.
apply False_ind.
apply H13.
eapply (col3 A B); Col.

assert(Par A E F B).

induction HH.

prolong A B A' A B.

apply (conga_to_par_os _ _ _ _ A');
auto.
apply conga_comm.
eapply l11_13.
apply conga_comm.
apply H33.
eBetween.
intro.
subst A'.
apply between_identity in H36.
contradiction.
eBetween.
intro.
subst A'.
apply cong_symmetry in H37.
apply cong_identity in H37.
contradiction.

induction H35.
spliter.

prolong A B A' A B.
apply (conga_to_par_os _ _ _ _ A');
auto.
apply conga_comm.
eapply l11_13.
apply conga_comm.
apply H33.
eBetween.
intro.
subst A'.
apply between_identity in H37.
contradiction.
eBetween.
intro.
subst A'.
apply cong_symmetry in H38.
apply cong_identity in H38.
contradiction.


induction H35.
spliter.
prolong A B A' A B.

apply (conga_to_par_os _ _ _ _ A');
auto.
apply conga_comm.

eapply out_conga.
apply conga_comm.
apply H33.
repeat split; auto.
intro.
subst A'.
apply between_identity in H37.
contradiction.
left.
eBetween.
apply out_trivial.
intro.
subst E.
apply H13.
ColR.
repeat split; auto.
intro.
subst A'.
apply cong_symmetry in H38.
apply cong_identity in H38.
contradiction.
left.
eapply (bet3_cong3_bet D _ _ A);
auto;
Cong.
intro.
subst D.
Col.
apply out_trivial.
intro.
subst F.
apply H10.
ColR.

spliter.
prolong A B A' A C.

apply (conga_to_par_os _ _ _ _ A');
auto.
apply conga_comm.

eapply out_conga.
apply conga_comm.
apply H33.
repeat split; auto.
intro.
subst A'.
apply between_identity in H37.
contradiction.
left.

assert(Bet B C A').

eapply (bet_cong_bet A); auto.
eBetween.
Cong.
eBetween.
apply out_trivial.
intro.
subst E.
apply H13.
ColR.
repeat split.
auto.
intro.
subst A'.
apply cong_symmetry in H38.
apply cong_identity in H38.
contradiction.
left.

eapply (bet_cong_bet A); auto.
eBetween.
Cong.
apply out_trivial.
intro.
subst F.
apply H10.
ColR.

assert(Plg A B F E).
apply pars_par_plg.
induction H32.
apply par_strict_right_comm.
assumption.
spliter.
apply False_ind.
assert(Col A B E).
ColR.
apply H13.
eapply (col3 A B); Col.
Par.
apply plg_to_parallelogram in H36.
induction H36.
assumption.
unfold Parallelogram_flat in H36.
spliter.

assert(Col A B E).
ColR.
apply False_ind.
apply H13.
eapply (col3 A B); Col.
Qed.

Lemma plgf_plgf_plgf: forall A B C D E F, A <> B -> Parallelogram_flat A B C D -> Parallelogram_flat C D E F
                                          -> Parallelogram_flat A B F E.
Proof.
intros.
assert(C <> D).
unfold Parallelogram_flat in H0.
spliter.
intro.
subst D.
apply cong_identity in H3.
contradiction.
assert(E <> F).
unfold Parallelogram_flat in H1.
spliter.
intro.
subst F.
apply cong_identity in H4.
contradiction.

assert(HH:=plgs_existence C D H2).
ex_and HH D'.
ex_and H4 C'.

assert(Parallelogram_strict A B C' D').
eapply (plgf_plgs_trans A B C D); auto.
assert(Parallelogram_strict E F C' D').
eapply (plgf_plgs_trans E F C D); auto.

apply plgf_sym.
assumption.
assert(Parallelogram A B F E).
eapply plgs_pseudo_trans.
apply H4.
apply plgs_sym.
assumption.
induction H7.
induction H7.
unfold TS in H7.
spliter.
unfold Parallelogram_flat in *.
spliter.
apply False_ind.
apply H10.

assert(Col C D A).
ColR.
assert(Col C D B).
ColR.
apply (col3 C D); Col.
assumption.
Qed.

Lemma plg_pseudo_trans : forall A B C D E F, Parallelogram A B C D -> Parallelogram C D E F -> Parallelogram A B F E \/ (A = B /\ C = D /\ E = F /\ A = E).
Proof.
intros.
induction(eq_dec_points A B).
subst B.
induction H.
unfold Parallelogram_strict in H.
spliter.
unfold TS in H.
spliter.
apply False_ind.
apply H.
Col.
assert(C = D).
assert(HH:=plgf_trivial_neq A C D H).
spliter.
assumption.
subst D.
induction H0.
unfold Parallelogram_strict in H0.
spliter.
unfold TS in H0.
spliter.
apply False_ind.
apply H0.
Col.
assert(E=F).
assert(HH:=plgf_trivial_neq C E F H0).
spliter.
assumption.
subst F.
induction (eq_dec_points A E).
right.
repeat split; auto.
left.
apply plg_trivial1.
assumption.


assert(C <> D).
intro.
subst D.
induction H.
unfold Parallelogram_strict in H.
spliter.
unfold TS in H.
spliter.
apply H4.
Col.
apply plgf_sym in H.
apply plgf_trivial_neq in H.
spliter.
contradiction.

assert(E <> F).
intro.
subst F.
induction H0.
unfold Parallelogram_strict in H0.
spliter.
unfold TS in H0.
spliter.
apply H5.
Col.
apply plgf_sym in H0.
apply plgf_trivial_neq in H0.
spliter.
contradiction.

left.
induction H; induction H0.
eapply plgs_pseudo_trans.
apply H.
assumption.
left.
apply plgs_sym.
apply (plgf_plgs_trans F E D C);auto.
apply plgf_comm2.
apply plgf_sym.
assumption.
apply plgs_comm2.
apply plgs_sym.
assumption.
left.
apply (plgf_plgs_trans A B C D E F); auto.
right.
apply  (plgf_plgf_plgf A B C D E F); auto.
Qed.

Lemma Square_Rhombus : forall A B C D,
 Square A B C D -> Rhombus A B C D.
Proof.
intros.
unfold Rhombus.
split.
apply Square_Parallelogram in H.
apply parallelogram_to_plg in H.
assumption.
unfold Square in H.
tauto.
Qed.

Lemma plgs_in_angle : forall A B C D, Parallelogram_strict A B C D -> InAngle D A B C.
Proof.
intros.
assert(Plg A B C D).
apply parallelogram_to_plg.
left.
assumption.

unfold Parallelogram_strict in H.
unfold Plg in H0.
spliter.
ex_and H1 M.

assert(A <> B /\ C <> B).
unfold TS in H.
spliter.

split;
intro;
subst B;
apply H;
Col.
spliter.

assert(HH:=H).
unfold TS in HH.
spliter.
ex_and H9 T.

unfold InAngle.
repeat split; auto.
intro.
subst D.
apply l7_3 in H4.
subst M.
apply midpoint_bet in H1.
apply H7.
apply bet_col in H1.
Col.

exists M.
split.
apply midpoint_bet.
auto.
right.

unfold Out.
repeat split.
intro.
subst M.
unfold Midpoint in H4.
spliter.
apply cong_symmetry in H11.
apply cong_identity in H11.
subst D.
apply between_identity in H10.
subst T.
contradiction.
intro.
subst D.
apply between_identity in H10.
subst T.
contradiction.
left.
apply midpoint_bet.
auto.
Qed.

Lemma par_par_cong_cong_parallelogram :
 forall A B C D,
 B<>D ->
 Cong A B C D ->
 Cong B C D A ->
 Par B C A D ->
 Par A B C D ->
 Parallelogram A B C D.
Proof.
intros.
assert (Parallelogram A B C D \/ Parallelogram A B D C)
 by (apply par_cong_plg_2;finish).
assert (Parallelogram B C A D \/ Parallelogram B C D A)
 by (apply par_cong_plg_2;finish).
induction H4.
assumption.
induction H5.
apply Plg_perm in H4.
apply Plg_perm in H5.
assert_diffs.
spliter.
apply plg_not_comm in H8.
intuition.
auto.
apply Plg_perm in H5.
spliter.
assumption.
Qed.

Lemma degenerated_rect_eq : forall A B C, Rectangle A B B C -> A = C.
Proof.
intros A B C HRect.
apply Rectangle_Parallelogram in HRect; apply plg_mid in HRect.
destruct HRect as [M [HMid1 HMid2]]; treat_equalities; auto.
Qed.

Lemma rect_2_rect : forall A B C1 C2 D1 D2,
  A <> B ->
  Rectangle A B C1 D1 ->
  Rectangle A B C2 D2 ->
  Rectangle C1 D1 D2 C2.
Proof.
intros A B C1 C2 D1 D2 HDiff HRect1 HRect2.
elim (eq_dec_points C1 C2); intro HC1C2; treat_equalities.

  {
  apply Rectangle_Parallelogram in HRect1; apply plg_mid in HRect1.
  apply Rectangle_Parallelogram in HRect2; apply plg_mid in HRect2.
  destruct HRect1 as [M [HMid1 HMid2]]; destruct HRect2 as [M' [HMid3 HMid4]].
  treat_equalities; split; Cong; apply parallelogram_to_plg.
  apply plg_trivial; intro; treat_equalities; auto.
  }

  {
  elim (eq_dec_points B C1); intro HBC1; elim (eq_dec_points B C2); intro HBC2;
  treat_equalities; [intuition|apply degenerated_rect_eq in HRect1; treat_equalities|
                     apply degenerated_rect_eq in HRect2; treat_equalities|];
  apply rect_comm2; auto; apply rect_comm2; do 2 (apply rect_permut); auto.
  assert (HPara1 := HRect1); apply Rectangle_Parallelogram in HPara1.
  assert (HPara2 := HRect2); apply Rectangle_Parallelogram in HPara2.

  assert (HNC1 : ~ Col A B C1) by (apply rect_per2 in HRect1; apply per_not_col; auto).
  assert (HNC2 : ~ Col A B C2) by (apply rect_per2 in HRect2; apply per_not_col; auto).
  apply plg_per_rect2.

    {
    elim HPara1; clear HPara1; intro HPara1;
    [|unfold Parallelogram_flat in HPara1; spliter; intuition].
    elim HPara2; clear HPara2; intro HPara2;
    [|unfold Parallelogram_flat in HPara2; spliter; intuition].
    apply parallelogram_to_plg; apply plgs_pseudo_trans with B A;
    apply plgs_comm2; auto; do 2 (apply plgs_permut); auto.
    }

  elim (cop_dec A B C1 C2); intro HCop.

    {
    apply perp_per_1; auto; apply perp_sym; apply cop_par_perp__perp with A B; Cop;
    apply plg_par_1 in HPara2; Par; clear HPara1; clear HPara2.
    apply rect_per2 in HRect1; apply rect_per2 in HRect2.
    assert (HCol : Col C1 C2 B) by (apply cop_per2__col with A; Perp; Cop).
    apply perp_col0 with B C1; Col; apply per_perp in HRect1; Perp.
    }

    {
    apply rect_per in HRect1; apply rect_per in HRect2; spliter.
    destruct (eq_dec_points C2 D2); [subst; Perp|].
    assert (HOrth : Orth_at C2 B C1 C2 C2 D2);
      [|destruct HOrth as [_ [_ [_ [_ HOrth]]]]; apply HOrth; Col; Cop].
    apply l11_61_bis with B A; Perp; Cop.
    apply l11_60_bis; Perp; Cop.
    apply ncop__ncol with A; Cop.
    }
  }
Qed.

Lemma ncol123_plg__plgs : forall A B C D,
  ~ Col A B C -> Parallelogram A B C D -> Parallelogram_strict A B C D.
Proof.
intros A B C D HNC H; induction H; auto.
exfalso; apply HNC; unfold Parallelogram_flat in *; spliter; Col.
Qed.

Lemma ncol124_plg__plgs : forall A B C D,
  ~ Col A B D -> Parallelogram A B C D -> Parallelogram_strict A B C D.
Proof.
intros A B C D HNC H; induction H; auto.
exfalso; apply HNC; unfold Parallelogram_flat in *; spliter; Col.
Qed.

Lemma ncol134_plg__plgs : forall A B C D,
  ~ Col A C D -> Parallelogram A B C D -> Parallelogram_strict A B C D.
Proof.
intros A B C D HNC H; induction H; auto.
exfalso; apply HNC; unfold Parallelogram_flat in *; spliter; assert_diffs; ColR.
Qed.

Lemma ncol234_plg__plgs : forall A B C D,
  ~ Col B C D -> Parallelogram A B C D -> Parallelogram_strict A B C D.
Proof.
intros A B C D HNC H; induction H; auto.
exfalso; apply HNC; unfold Parallelogram_flat in *; spliter; assert_diffs; ColR.
Qed.

Lemma ncol123_plg__pars1234 : forall A B C D,
  ~ Col A B C -> Parallelogram A B C D -> Par_strict A B C D.
Proof.
intros; apply plgs_pars_1; apply ncol123_plg__plgs; auto.
Qed.

Lemma ncol124_plg__pars1234 : forall A B C D,
  ~ Col A B D -> Parallelogram A B C D -> Par_strict A B C D.
Proof.
intros; apply plgs_pars_1; apply ncol124_plg__plgs; auto.
Qed.

Lemma ncol134_plg__pars1234 : forall A B C D,
  ~ Col A C D -> Parallelogram A B C D -> Par_strict A B C D.
Proof.
intros; apply plgs_pars_1; apply ncol134_plg__plgs; auto.
Qed.

Lemma ncol234_plg__pars1234 : forall A B C D,
  ~ Col B C D -> Parallelogram A B C D -> Par_strict A B C D.
Proof.
intros; apply plgs_pars_1; apply ncol234_plg__plgs; auto.
Qed.

Lemma ncol123_plg__pars1423 : forall A B C D,
  ~ Col A B C -> Parallelogram A B C D -> Par_strict A D B C.
Proof.
intros; apply plgs_pars_2; apply ncol123_plg__plgs; auto.
Qed.

Lemma ncol124_plg__pars1423 : forall A B C D,
  ~ Col A B D -> Parallelogram A B C D -> Par_strict A D B C.
Proof.
intros; apply plgs_pars_2; apply ncol124_plg__plgs; auto.
Qed.

Lemma ncol134_plg__pars1423 : forall A B C D,
  ~ Col A C D -> Parallelogram A B C D -> Par_strict A D B C.
Proof.
intros; apply plgs_pars_2; apply ncol134_plg__plgs; auto.
Qed.

Lemma ncol234_plg__pars1423 : forall A B C D,
  ~ Col B C D -> Parallelogram A B C D -> Par_strict A D B C.
Proof.
intros; apply plgs_pars_2; apply ncol234_plg__plgs; auto.
Qed.

Lemma sac_plg : forall A B C D, Saccheri A B C D -> Parallelogram A B C D.
Proof.
intros A B C D H.
assert (T:=sac__par_strict1234 A B C D H).
assert (U:=sac__par1423 A B C D H).
assert (V:=sac__par1234 A B C D H).
apply par_2_plg;eauto using par_strict_not_col_1.
Qed.

Lemma sac_rectangle : forall A B C D, Saccheri A B C D -> Rectangle A B C D.
Proof.
intros A B C D H.
assert (Parallelogram A B C D) by (apply sac_plg;auto).
apply parallelogram_to_plg in H0.
apply plg_per_rect1.
assumption.
unfold Saccheri in H.
spliter;finish.
Qed.

Lemma exists_square : forall A B, A<>B -> exists C D,  Square A B C D.
Proof.
intros.
destruct (exists_cong_per A B A B) as [C [HC1 HC2]].
assert_diffs.
destruct (per__ex_saccheri B C A) as [D HSac]; Perp.
exists C.
exists D.
assert (Rectangle B C D A) by (apply sac_rectangle;auto).
unfold Square;split.
auto using rect_permut.
Cong.
Qed.

End Quadrilateral_inter_dec_3.

Section Quadrilateral_inter_dec_2D.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Lemma perp3__perp :
 forall A B C D,
  Perp A B B C ->
  Perp B C C D ->
  Perp C D D A ->
  Perp D A A B.
Proof.
intros A B C D.
apply cop_perp3__perp, all_coplanar.
Qed.

Lemma perp3__rect :
 forall A B C D,
  Perp A B B C ->
  Perp B C C D ->
  Perp C D D A ->
  Rectangle A B C D.
Proof.
intros A B C D.
apply cop_perp3__rect, all_coplanar.
Qed.

End Quadrilateral_inter_dec_2D.