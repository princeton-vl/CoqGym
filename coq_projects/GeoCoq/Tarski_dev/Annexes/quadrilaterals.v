(* Gabriel Braun November 2012 *)

Require Export GeoCoq.Tarski_dev.Ch12_parallel.

Section Quadrilateral.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma cong_identity_inv :
 forall A B C, A <> B -> ~ Cong A B C C.
Proof.
intros.
intro.
apply H.
eapply cong_identity.
apply H0.
Qed.

Lemma midpoint_midpoint_col : forall A B A' B' M,
 A <> B ->
 Midpoint M A A' -> Midpoint M B B' ->
 Col A B B' ->
 A' <> B' /\ Col A A' B' /\ Col B A' B'.
Proof.
intros.
assert(A' <> B').
intro.
apply H.
assert(Cong A' B' A B).
eapply l7_13.
apply H0.
assumption.
apply cong_symmetry in H4.
subst B'.
apply cong_identity in H4.
assumption.

assert(HH0:= H0).
assert(HH1:= H1).
unfold Midpoint in HH0.
unfold Midpoint in HH1.
spliter.

assert(Col M A A').
apply bet_col in H6.
Col.
assert(Col M B B').
apply bet_col in H4.
Col.

induction(eq_dec_points B B').
subst B'.
apply l7_3 in H1.
subst M.
Col5.

assert(Col A A' B').

assert(Col B M A).
eapply col_transitivity_1.
apply H10.
Col.
Col.

assert(Col A M B').

eapply col_transitivity_1.
apply H.
Col.
Col.

induction(eq_dec_points A M).
subst M.
apply cong_symmetry in H7.
apply cong_identity in H7.
subst A'.
Col.

eapply col_transitivity_1.
apply H13.
Col.
Col.
repeat split;
Col.

induction(eq_dec_points A B').
subst B'.
assert(A'=B).
eapply l7_9.
2: apply H1.
apply l7_2.
assumption.
subst A'.
Col.
ColR.
Qed.

Lemma midpoint_par_strict :
 forall A B A' B' M,
 A <> B ->
 ~ Col A B B' ->
 Midpoint M A A' ->
 Midpoint M B B' ->
 Par_strict A B A' B'.
Proof.
intros.
assert(Par A B A' B').
eapply (l12_17 A B A' B' M); assumption.
induction H3.
assumption.
spliter.
apply False_ind.

assert(HH:=midpoint_midpoint_col B' A' B A M).
assert(B <> A /\ Col B' B A /\ Col A' B A).
apply HH.
auto.
apply l7_2.
assumption.
apply l7_2.
assumption.
Col.
spliter.
apply H0.
Col.
Qed.

Lemma bet3_cong3_bet : forall A B C D D', A <> B -> A <> C -> A <> D -> Bet D A C -> Bet A C B -> Bet D C D' -> Cong A B C D -> Cong A D B C -> Cong D C C D'
                              -> Bet C B D'.
Proof.
intros.
assert(Bet D C B).
eBetween.
assert(B <> C).
intro.
subst C.
apply cong_identity in H6.
contradiction.

assert(D' <> C).
intro.
subst D'.
apply cong_identity in H7.
subst D.
apply cong_identity in H5.
contradiction.

assert(D <> C).
intro.
subst D.
apply cong_identity in H5.
contradiction.

assert (Out C B D').
repeat split; auto.
eapply (l5_2 D); auto.

assert(Out D B D').
repeat split; auto.

intro.
subst D.
apply between_identity in H8.
contradiction.
intro.
subst D'.
apply between_identity  in H4.
contradiction.

eapply (l5_1 _ C); auto.

assert(Le D A D C).
unfold Le.
exists A.
split; Cong.

assert(Le D B D D').
eapply (bet2_le2__le1346 _ A _ _ C).
eBetween.
assumption.
assumption.
apply cong__le; eCong.

assert(Bet D B D').

apply l6_13_1; auto.
eapply (between_exchange3 D); auto.
Qed.

Lemma bet_double_bet :
 forall A B C B' C',
 Midpoint B' A B ->
 Midpoint C' A C ->
 Bet A B' C' ->
 Bet A B C.
Proof.
intros.
unfold Midpoint in *.
spliter.
assert(Le A B' A C').
unfold Le.
exists B'.
split.
assumption.
apply cong_reflexivity.
assert (Le B' B C' C).
eapply l5_6.
apply H4.
auto.
auto.
assert(Le A B A C).
eapply bet2_le2__le1346.
apply H.
apply H0.
assumption.
assumption.

induction (eq_dec_points A B').
subst B'.
apply cong_symmetry in H3.
apply cong_identity in H3.
subst B.
apply between_trivial2.

assert( A <> C').
intro.
subst C'.
apply le_zero in H4.
contradiction.

assert(A <> B).
intro.
subst B.
apply between_identity in H.
contradiction.
assert(A <> C).
intro.
subst C.
apply between_identity in H0.
contradiction.

assert(Out A B C).

assert(Bet A B C' \/ Bet A C' B).
eapply l5_1.
apply H7.
assumption.
assumption.
induction H11.

eapply l6_7.
apply bet_out.
auto.
apply H11.
apply bet_out.
auto.
assumption.

assert(Bet A B C \/ Bet A C B).
eapply l5_1.
2: apply H11.
assumption.
assumption.
induction H12.
apply bet_out.
auto.
assumption.
apply l6_6.
apply bet_out.
auto.
assumption.
eapply l6_13_1.
assumption.
assumption.
Qed.


Lemma bet_half_bet :
 forall A B C B' C',
 Bet A B C  ->
 Midpoint B' A B ->
 Midpoint C' A C ->
 Bet A B' C'.
Proof.
intros.
assert(HH0:= H0).
assert(HH1:= H1).
unfold Midpoint in H0.
unfold Midpoint in H1.
spliter.

induction(eq_dec_points A B).
subst B.
apply between_identity in H0.
subst B'.
apply between_trivial2.
assert(A <> C).
intro.
subst C.
apply between_identity in H1.
subst C'.
apply between_identity in H.
contradiction.
assert(A <> B').
intro.
subst B'.
apply cong_symmetry in H3.
apply cong_identity in H3.
contradiction.
assert(A <> C').
intro.
subst C'.
apply cong_symmetry in H2.
apply cong_identity in H2.
contradiction.

assert(Col A B' C').
apply bet_col in H0.
apply bet_col in H1.
apply bet_col in H.
ColR.
induction H8.
assumption.
induction H8.
apply between_symmetry in H8.

assert(Bet A C B).
eapply bet_double_bet.
apply HH1.
apply HH0.
assumption.

assert(B = C).
eapply between_equality.
apply between_symmetry.
apply H9.
Between.
subst C.
assert(B' = C').
eapply l7_17.
apply HH0.
assumption.
subst C'.
apply between_trivial.

(***********************************)

assert(Bet A B' C).
eapply between_exchange4.
apply H0.
assumption.

assert(Out A B' C').
unfold Out.
repeat split; auto.
eapply l5_3.
apply H9.
assumption.
eapply l6_4_1 in H10.
spliter.
apply between_symmetry in H8.
contradiction.
Qed.

Lemma midpoint_preserves_bet :
 forall A B C B' C',
  Midpoint B' A B ->
  Midpoint C' A C ->
 (Bet A B C <-> Bet A B' C').
Proof.
intros.
split.
intro.
eapply bet_half_bet.
apply H1.
assumption.
assumption.
intro.
eapply bet_double_bet.
apply H.
apply H0.
assumption.
Qed.

Lemma symmetry_preseves_bet1 :
 forall A B M A' B',
  Midpoint M A A' ->
  Midpoint M B B' ->
  Bet M A B ->
  Bet M A' B'.
Proof.
intros.
eapply l7_15.
2: apply H.
2: apply H0.
2: apply H1.
apply l7_3_2.
Qed.

Lemma symmetry_preseves_bet2 :
 forall A B M A' B',
  Midpoint M A A' ->
  Midpoint M B B' ->
  Bet M A' B' ->
  Bet M A B.
Proof.
intros.
eapply l7_15.
apply l7_3_2.
apply l7_2.
apply H.
apply l7_2.
apply H0.
assumption.
Qed.

Lemma symmetry_preserves_bet :
 forall A B M A' B',
  Midpoint M A A' ->
  Midpoint M B B' ->
 (Bet M A' B' <-> Bet M A B).
Proof.
intros.
split.
apply symmetry_preseves_bet2;
assumption.
intro.
eapply (symmetry_preseves_bet1 A B);
assumption.
Qed.

Lemma bet_cong_bet :
 forall A B C D,
  A <> B ->
  Bet A B C ->
  Bet A B D ->
  Cong A C B D ->
  Bet B C D.
Proof.
intros.

assert(Bet B C D \/ Bet B D C).
eapply (l5_2 A); auto.
induction H3.
assumption.

assert(D = C /\ A = B).
eapply (bet_cong_eq A B D C); auto.
eBetween.
Cong.
spliter.
contradiction.
Qed.

Lemma col_cong_mid :
 forall A B A' B',
  Par A B A' B' ->
  ~ Par_strict A B A' B' ->
  Cong A B A' B' ->
  exists M,  Midpoint M A A' /\ Midpoint M B B' \/
             Midpoint M A B' /\ Midpoint M B A'.
Proof.
intros.
unfold Par in H.
induction H.
contradiction.
spliter.

induction (eq_dec_points A A').
subst A'.
assert(B = B' \/ Midpoint A B B').
eapply l7_20; auto.
induction H5.
subst B'.
assert( HH:= midpoint_existence A B).
ex_and HH M.
exists M.
right.
split.
assumption.
apply l7_2.
assumption.
exists A.
left.
split.
apply l7_3_2.
assumption.

induction (eq_dec_points B B').
subst B'.
assert(A = A' \/ Midpoint B A A').
eapply l7_20.
Col.
Cong.
induction H6.
subst A'.
assert( HH:= midpoint_existence A B).
ex_and HH M.
exists M.
right.
split.
assumption.
apply l7_2.
assumption.
exists B.
left.
split.
assumption.
apply l7_3_2.

induction (eq_dec_points A B').
subst B'.
assert(B = A' \/ Midpoint A B A').
eapply l7_20.
Col.
Cong.
induction H7.
subst A'.
assert( HH:= midpoint_existence A B).
ex_and HH M.
exists M.
left.
split.
assumption.
apply l7_2.
assumption.
exists A.
right.
split.
apply l7_3_2.
assumption.

induction (eq_dec_points A' B).
subst A'.
assert(A = B' \/ Midpoint B A B').
eapply l7_20.
Col.
Cong.
induction H8.
subst B'.
assert( HH:= midpoint_existence A B).
ex_and HH M.
exists M.
left.
split.
assumption.
apply l7_2.
assumption.
exists B.
right.
split.
assumption.
apply l7_3_2.

assert(Col A B A').
ColR.
assert(Col A B B').
ColR.

induction H10.
induction H4.

assert( HH:= midpoint_existence A' B).
ex_and HH M.
exists M.
right.
assert(HH:= H11).
unfold Midpoint in HH.
spliter.
split.

assert(Bet B M B').

eapply between_exchange4.
2: apply H4.
Between.

assert(Bet A M B').
eapply between_exchange2.
apply H10.
assumption.
assert(Cong A M B' M).
eapply (l2_11 A  B _  _ A').
eapply between_inner_transitivity.
apply H10.
assumption.
eapply between_inner_transitivity.
apply between_symmetry.
apply H4.

assumption.
Cong.
Cong.

unfold Midpoint.
split.
assumption.
Cong.
apply l7_2.
assumption.

induction H4.

assert( HH:= midpoint_existence B B').
ex_and HH M.
exists M.
left.

assert(HH:= H11).
unfold Midpoint in HH.
spliter.

split.

assert(Bet A' M B).
eapply between_exchange2.
apply H4.
Between.
assert(Bet M B A).
eapply between_exchange3.

apply between_symmetry.
apply H12.
Between.

assert(Bet A' M A).
eapply outer_transitivity_between.
apply H14.
assumption.
intro.
subst M.
apply is_midpoint_id in H11.
contradiction.
assert(Cong A M A' M).
eapply l2_11.
apply between_symmetry.
apply H15.
eapply between_inner_transitivity.
apply H4.
Between.
assumption.
Cong.
unfold Midpoint.
split.
Between.
Cong.
assumption.

assert(Bet B A' A).
eapply (bet_cong_bet B').
auto.
Between.
Between.
Cong.

assert( HH:= midpoint_existence A' B).
ex_and HH M.
exists M.
right.
assert(HH:=H12).
unfold Midpoint in HH.
spliter.

split.
assert(Bet B M A).
eapply between_exchange4.
apply between_symmetry.
apply H13.
assumption.

assert(Bet B' B M).
eapply between_inner_transitivity.
apply between_symmetry.
apply H10.
assumption.

assert(Bet M A' A).
eapply between_exchange3.
2:apply H11.
Between.
assert(Bet B' M A').
eapply outer_transitivity_between2.
apply H16.
Between.
intro.
subst M.
apply l7_2 in H12.
apply is_midpoint_id in H12.
auto.
assert(Bet B' M A).
eapply outer_transitivity_between.
apply H18.
assumption.
intro.
subst A'.
apply is_midpoint_id in H12.
subst M.
tauto.

assert(Cong A M B' M).
eapply l4_3.
apply between_symmetry.
apply H15.
apply H18.
Cong.
Cong.
unfold Midpoint.
split.
Between.
Cong.
Midpoint.

induction H10.
induction H3.


assert(B' = B /\ A = A').
eapply bet_cong_eq.
assumption.
Between.
Cong.
spliter.
contradiction.
induction H3.

assert(Bet B' B A').
eapply bet_cong_bet.
apply H7.
Between.
Between.
Cong.

assert( HH:= midpoint_existence B B').
ex_and HH M.
exists M.

assert(HH:=H12).
unfold Midpoint in HH.
spliter.
left.

split.

assert(Bet A' M B').
eapply between_exchange2.
apply between_symmetry.
apply H11.
assumption.

assert(Bet M B' A).
eapply between_exchange3.
apply H13.
assumption.
assert(Bet A' M A).
eapply outer_transitivity_between.
apply H15.
assumption.
intro.
subst M.
apply l7_2 in H12.
apply is_midpoint_id in H12.
subst B'.
tauto.

assert(Bet A M B).
eapply outer_transitivity_between2.
apply between_symmetry.
apply H16.
Between.
intro.
subst M.
apply l7_2 in H12.
apply is_midpoint_id in H12.
subst B'.
tauto.

assert(Cong A' M A M).
eapply l4_3.
apply H15.
apply H18.
Cong.
Cong.
unfold Midpoint.
split.
Between.
Cong.
assumption.

assert( HH:= midpoint_existence A B').
ex_and HH M.
exists M.
assert(HH:=H11).
unfold Midpoint in HH.
spliter.
right.
split.
assumption.

assert(Bet A' A M).
eapply between_inner_transitivity.
apply between_symmetry.
apply H3.
assumption.

assert(Bet A M B).
eapply between_exchange4.
apply H11.
Between.

assert(Bet A' M B).
eapply outer_transitivity_between2.
apply H14.
assumption.
intro.
subst M.
apply is_midpoint_id in H11.
contradiction.

assert(Cong B M A' M).
eapply l4_3.
apply between_symmetry.
apply H15.
eapply between_exchange2.
apply between_symmetry.
apply H3.
assumption.
Cong.
Cong.
unfold Midpoint.
split.
Between.
Cong.

induction H9.

assert(Bet B' B A').
eapply outer_transitivity_between2.
apply H10.
assumption.
assumption.

assert(B = A' /\ B' = A).
eapply bet_cong_eq.
assumption.
assumption.
Cong.
spliter.
subst A'.
tauto.

induction H9.

assert( HH:= midpoint_existence A A').
ex_and HH M.
exists M.
assert(HH:=H11).
unfold Midpoint in HH.
spliter.
left.
split.
assumption.

assert(Bet B A' M).
eapply between_inner_transitivity.
apply H9.
Between.

assert(Bet B M A).
eapply outer_transitivity_between2.
apply H14.
Between.
intro.
subst M.
apply l7_2 in H11.
apply is_midpoint_id in H11.
subst A'.
tauto.

assert(Bet B M B').
eapply between_exchange4.
apply H15.
Between.

assert(Cong B M B' M).
eapply l4_3.
apply H15.

assert(Bet B' A A').
eapply between_inner_transitivity.
apply H10.
Between.
eapply between_exchange2.
apply H17.
assumption.
Cong.
Cong.
unfold Midpoint.
split.
assumption.
Cong.

assert(Bet A B' A' \/ Bet A A' B').
eapply (l5_2 B).
auto.
Between.
Between.
induction H11.

assert( HH:= midpoint_existence A B').
ex_and HH M.
exists M.
assert(HH:=H12).
unfold Midpoint in HH.
spliter.
right.
split.
assumption.

assert(Bet B M B').
eapply between_exchange2.
apply between_symmetry.
apply H10.
assumption.
assert(Bet A' B' M).
eapply between_inner_transitivity.
apply between_symmetry.
apply H11.
Between.

assert(Bet A' M B).
eapply outer_transitivity_between2.
apply H16.
Between.
intro.
subst M.
apply l7_2 in H12.
apply is_midpoint_id in H12.
subst B'.
tauto.

assert(Cong M A' M B).
eapply l2_11.
apply between_symmetry.
apply H16.
eapply between_exchange3.
apply between_symmetry.
apply H13.
assumption.
Cong.
Cong.
unfold Midpoint.
split.
Between.
Cong.

assert( HH:= midpoint_existence A A').
ex_and HH M.
exists M.
assert(HH:=H12).
unfold Midpoint in HH.
spliter.
left.
split.
assumption.

assert(Bet B A M).
eapply between_inner_transitivity.
apply between_symmetry.
apply H9.
assumption.
assert(Bet B' M A).
eapply between_exchange2.
apply between_symmetry.
apply H11.
Between.
assert(Bet B' M B).
eapply outer_transitivity_between.
apply H16.
Between.
intro.
subst M.
apply is_midpoint_id in H12.
contradiction.
assert(Cong B' M B M).
eapply l2_11.
eapply between_inner_transitivity.
apply between_symmetry.
apply H11.
Between.
apply H15.
Cong.
Cong.
unfold Midpoint.
split.
Between.
Cong.
Qed.

Lemma mid_par_cong1 :
 forall A B A' B' M,
  A <> B ->
  Midpoint M A A' ->
  Midpoint M B B' ->
  Cong A B A' B' /\ Par A B A' B'.
Proof.
intros.
split.
eapply (l7_13 M);
Midpoint.
apply (l12_17 _ _ _ _ M); auto.
Qed.

Lemma mid_par_cong2 :
 forall A B A' B' M,
  A <> B' ->
  Midpoint M A A' ->
  Midpoint M B B' ->
  Cong A B' A' B /\ Par A B' A' B.
Proof.
intros.
spliter.
split.
apply (l7_13 M); Midpoint.
eapply (l12_17 _ _ _ _ M); Midpoint.
Qed.


Lemma mid_par_cong :
 forall A B A' B' M,
  A <> B -> A <> B' ->
  Midpoint M A A' ->
  Midpoint M B B' ->
  Cong A B A' B' /\ Cong A B' A' B /\ Par A B A' B' /\ Par A B' A' B.
Proof.
intros.
spliter.
assert(Cong A B A' B' /\ Par A B A' B').
eapply (mid_par_cong1 _  _ _ _ M); Midpoint.
assert(Cong A B' A' B /\ Par A B' A' B).
apply (mid_par_cong2 _ _ _ _ M);Midpoint.
spliter.
repeat split;
assumption.
Qed.

Lemma Parallelogram_strict_Parallelogram :
 forall A B C D,
  Parallelogram_strict A B C D -> Parallelogram A B C D.
Proof.
unfold Parallelogram.
tauto.
Qed.

Lemma plgf_permut :
 forall A B C D,
  Parallelogram_flat A B C D ->
  Parallelogram_flat B C D A.
Proof.
intros.
unfold Parallelogram_flat in *.
spliter.
induction(eq_dec_points A B).
subst B.
apply cong_symmetry in H1.
apply cong_identity in H1.
subst D.
repeat split; Col.
apply  cong_trivial_identity.
induction H3;
left; assumption.

assert(C <> D).
intro.
subst D.
apply cong_identity in H1.
contradiction.
repeat split.
ColR.
Col.
Cong.
Cong.
induction H3.
right.
auto.
left; assumption.
Qed.

Lemma plgf_sym :
 forall A B C D,
 Parallelogram_flat A B C D ->
 Parallelogram_flat C D A B.
Proof.
intros.
apply plgf_permut.
apply plgf_permut.
assumption.
Qed.

Lemma plgf_irreflexive :
 forall A B,
 ~ Parallelogram_flat A B A B.
Proof.
intros.
unfold Parallelogram_flat.
intro.
spliter.
induction H3; tauto.
Qed.

Lemma plgs_irreflexive :
 forall A B,
  ~ Parallelogram_strict A B A B.
Proof.
intros.
intro.
unfold Parallelogram_strict in H.
spliter.
unfold TS in H.
spliter.
apply H2.
Col.
Qed.

Lemma plg_irreflexive :
 forall A B,
 ~ Parallelogram A B A B.
Proof.
intros.
intro.
induction H.
apply plgs_irreflexive in H.
assumption.
apply plgf_irreflexive in H.
assumption.
Qed.

Lemma plgf_mid :
 forall A B C D,
  Parallelogram_flat A B C D ->
  exists M, Midpoint M A C /\ Midpoint M B D.
Proof.
intros.
unfold Parallelogram_flat in H.
spliter.

induction(eq_dec_points A B).
subst B.
apply cong_symmetry in H1.
apply cong_identity in H1.
subst D.
assert(HH:=midpoint_existence A C).
ex_and HH M.
exists M.
split; assumption.
assert(C <> D).
intro.
subst D.
apply cong_identity in H1.
contradiction.

assert(Par A B C D).
apply par_symmetry.
unfold Par.
right.
repeat split; Col.

assert(~Par_strict A B C D).
intro.
unfold Par_strict in H7.
spliter.
apply H10.
exists C.
split; Col.

assert(HH:= col_cong_mid A B C D H6 H7 H1).
ex_and HH M.
induction H8.
exists M.
assumption.
spliter.
induction(eq_dec_points B C).
subst C.
apply cong_identity in H2.
subst D.
apply l7_3 in H8.
apply l7_3 in H9.
subst M.
contradiction.
assert(A <> D).
intro.
subst D.
apply cong_symmetry in H2.
apply cong_identity in H2.
subst C.
tauto.

apply False_ind.
assert(Col A B M).
unfold Midpoint in *.
spliter.
eapply (col_transitivity_1 _ D).
assumption.
Col.
apply bet_col in H8.
Col.

assert(B <> M).
intro.
subst M.
apply is_midpoint_id in H9.
contradiction.

assert(A <> M).
intro.
subst M.
apply is_midpoint_id in H8.
contradiction.

induction H12.

assert(HH:=symmetry_preserves_bet B A M C D H9 H8).
destruct HH.
assert(Bet M C D).
apply H16.
Between.
clear H15 H16.

assert(B = A /\ D = C).
unfold Midpoint in *.
spliter.
apply bet_cong_eq.

eBetween.
eBetween.
Cong.
spliter.
subst B.
tauto.

induction H12.

assert(Bet M A C \/ Bet M C A).
unfold Midpoint in *.
spliter.
eapply (l5_2 B); assumption.
induction H15.

assert(Bet M D B <-> Bet M A C).
apply(symmetry_preserves_bet A C M D B).
assumption.
Midpoint.
destruct H16.
assert(Bet M D B).
apply H17.
assumption.
clear H17 H16.

assert(A = C /\ B = D).
unfold Midpoint in *.
spliter.
apply bet_cong_eq.
eBetween.
eBetween.
Cong.
spliter.
subst C.
induction H3.
tauto.
subst D.
tauto.

assert(Bet M B D <-> Bet M C A).
apply(symmetry_preserves_bet); Midpoint.
destruct H16.
assert(Bet M B D).
apply H17.
assumption.
clear H16 H17.

assert(C = A /\ D = B).
unfold Midpoint in *.
spliter.
apply bet_cong_eq.
eBetween.
eBetween.
Cong.
spliter.
subst C.
induction H3.
tauto.
subst D.
tauto.

assert(HH:=symmetry_preserves_bet  A B M D C H8 H9).
destruct HH.
assert(Bet M D C).
apply H16.
Between.
clear H15 H16.

assert(A = B /\ C = D).
unfold Midpoint in *.
spliter.
apply bet_cong_eq.

eBetween.
eBetween.
Cong.
spliter.
subst B.
tauto.
Qed.

Lemma mid_plgs :
 forall A B C D M,
  ~ Col A B C ->
  Midpoint M A C -> Midpoint M B D ->
  Parallelogram_strict A B C D.
Proof.
intros.
unfold Parallelogram_strict.
assert(A <>C).
intro.
apply H.
subst C.
Col.

assert(B <> D).
intro.
subst D.
apply l7_3 in H1.
subst M.
unfold Midpoint in H0.
spliter.
apply bet_col in H0.
contradiction.

assert(M <> D).
intro.
subst M.
apply l7_2 in H1.
apply is_midpoint_id in H1.
subst D.
tauto.

assert( M <> A).
intro.
subst M.
apply is_midpoint_id in H0.
contradiction.
repeat split.

intro.
apply H.
Col.
intro.
unfold Midpoint in *.
spliter.
apply bet_col in H0.
apply bet_col in H1.
apply H.
assert(Col M A D).
ColR.
assert(Col M A B).
ColR.
ColR.
exists M.
unfold Midpoint in *.
spliter.
split.
apply bet_col in H0.
Col.
apply H1.
apply (l12_17 _ _ _ _ M).
intro.
subst B.
apply H.
Col.
assumption.
assumption.
eapply (l7_13 M); Midpoint.
Qed.

Lemma mid_plgf_aux :
 forall A B C D M,
  A <> C ->
  Col A B C ->
  Midpoint M A C -> Midpoint M B D ->
  Parallelogram_flat A B C D.
Proof.
intros.
unfold Parallelogram_flat.
induction(eq_dec_points B D).
subst D.
apply l7_3 in H2.
subst M.
unfold Midpoint in H1.
spliter.
repeat split; Col.
Cong.
Cong.

assert(Col A B M).
unfold Midpoint in *.
spliter.
apply bet_col in H1.
apply bet_col in H2.
ColR.
assert(M <> B).
intro.
subst M.
apply is_midpoint_id in H2.
contradiction.

assert(M <> A).
intro.
subst M.
apply is_midpoint_id in H1.
contradiction.

induction H4.

assert(HH:=symmetry_preserves_bet B A M D C H2 H1).
destruct HH.
assert(Bet M D C).
apply H8.
Between.
clear H8 H7.

repeat split.
Col.
unfold Midpoint in *.
spliter.
apply bet_col in H2.
apply bet_col in H1.
apply bet_col in H4.
ColR.

eapply l4_3.
apply H4.
apply between_symmetry.
apply H9.
unfold Midpoint in H1.
spliter.
Cong.
unfold Midpoint in H2.
spliter.
Cong.

unfold Midpoint in *.
spliter.
eapply (l2_11 _ M _ _ M _).
eBetween.
eBetween.
Cong.
Cong.
left.
assumption.

induction H4.

assert(Bet M A D \/ Bet M D A).
eapply (l5_2 B).
auto.
assumption.
unfold Midpoint in H2.
spliter.
assumption.
induction H7.

assert(Bet M C B <-> Bet M A D).

apply (symmetry_preserves_bet A D M C B).
assumption.
Midpoint.
destruct H8.
assert(Bet M C B).
apply H9.
assumption.
clear H9 H8.

unfold Midpoint in *.
spliter.
repeat split.
assumption.
apply bet_col in H4.
apply bet_col in H1.
apply bet_col in H2.
ColR.
eapply (l2_11 _ M _ _ M _).
Between.
eBetween.
Cong.
Cong.
apply cong_commutativity.
eapply (l4_3).
apply between_symmetry.
apply H7.
apply between_symmetry.
apply H10.
Cong.
Cong.
left.
assumption.

assert(Bet M B C <-> Bet M D A).

apply (symmetry_preserves_bet D A M B C).
Midpoint.
Midpoint.
destruct H8.
assert(Bet M B C).
apply H9.
assumption.
clear H8 H9.
unfold Midpoint in *.
spliter.
repeat split.
assumption.
apply bet_col in H4.
apply bet_col in H1.
apply bet_col in H2.
ColR.

eapply (l2_11 _ M _ _ M _).
Between.
eBetween.
Cong.
Cong.

eapply l4_3.
apply between_symmetry.
apply H7.
apply between_symmetry.
apply H10.
Cong.
Cong.
left.
assumption.

assert(Bet M C D <-> Bet M A B).
apply (symmetry_preserves_bet A B M C D H1 H2).

destruct H7.
assert(Bet M C D).
apply H8.
assumption.
clear H8 H7.

repeat split.
Col.
unfold Midpoint in *.
spliter.
apply bet_col in H2.
apply bet_col in H1.
apply bet_col in H4.
ColR.
apply cong_commutativity.
eapply l4_3.
apply between_symmetry.
apply H4.
apply between_symmetry.
apply H9.
unfold Midpoint in H2.
spliter.
Cong.
unfold Midpoint in H1.
spliter.
Cong.

unfold Midpoint in *.
spliter.
eapply (l2_11 _ M _ _ M _).
eBetween.
eBetween.
Cong.
Cong.
left.
assumption.
Qed.


Lemma mid_plgf :
 forall A B C D M,
  (A <> C \/ B <> D ) ->
  Col A B C ->
  Midpoint M A C -> Midpoint M B D ->
  Parallelogram_flat A B C D.
Proof.
intros.
induction H.
eapply (mid_plgf_aux A B C D M); assumption.
apply plgf_sym.
induction(eq_dec_points A C).
subst C.
spliter.
apply l7_3 in H1.
subst M.
unfold Midpoint in H2.
spliter.
unfold Parallelogram_flat.
repeat split.
Col.
apply bet_col in H1.
Col.
Cong.
Cong.
right.
auto.
spliter.
eapply (mid_plgf_aux C D A B M).
auto.
unfold Midpoint in *.
spliter.
apply bet_col in H1.
apply bet_col in H2.

assert( M <> C).
intro.
subst M.
apply cong_identity in H5.
contradiction.

assert( M <> B).
intro.
subst M.
apply cong_symmetry in H4.
apply cong_identity in H4.
contradiction.
ColR.
Midpoint.
Midpoint.
Qed.

Lemma mid_plg :
 forall A B C D M,
 (A <> C \/ B <> D ) ->
 Midpoint M A C -> Midpoint M B D ->
 Parallelogram A B C D.
Proof.
intros.
unfold Parallelogram.

induction(col_dec A B C).
right.
apply (mid_plgf _ _ _ _ M);
assumption.
left.
apply (mid_plgs _ _ _ _ M);
assumption.
Qed.

Lemma mid_plg_1 :
 forall A B C D M,
 A <> C ->
 Midpoint M A C -> Midpoint M B D ->
 Parallelogram A B C D.
Proof.
intros.
apply mid_plg with M; intuition.
Qed.

Lemma mid_plg_2 :
 forall A B C D M,
 B <> D ->
 Midpoint M A C -> Midpoint M B D ->
 Parallelogram A B C D.
Proof.
intros.
apply mid_plg with M; intuition.
Qed.

Lemma midpoint_cong_uniqueness :
 forall A B C D M,
  Col A B C ->
  Midpoint M A B /\ Midpoint M C D ->
  Cong A B C D ->
  A = C /\ B = D \/ A = D /\ B = C.
Proof.
intros.

induction (eq_dec_points A B).
subst B.
spliter.
apply l7_3 in H0.
subst M.
apply cong_symmetry in H1.
apply cong_identity in H1.
subst D.
apply l7_3 in H2.
left.
split; assumption.

induction(eq_dec_points A C).
left.
split.
assumption.
subst C.
spliter.
eapply symmetric_point_uniqueness.
apply H0.
assumption.
right.
spliter.
assert(HH:=cong_cong_half_1 A M B C M D H0 H4 H1).
assert(A = C \/ Midpoint M A C).
apply l7_20.
unfold Midpoint in *.
spliter.
apply bet_col in H0.
apply bet_col in H4.
ColR.
Cong.
induction H5.
contradiction.
assert(B = C).
eapply symmetric_point_uniqueness.
apply H0.
assumption.
split.
subst C.
eapply symmetric_point_uniqueness.
apply l7_2.
apply H0.
assumption.
assumption.
Qed.



Lemma plgf_not_comm :
 forall A B C D, A <> B ->
  Parallelogram_flat A B C D ->
  ~ Parallelogram_flat A B D C /\ ~ Parallelogram_flat B A C D.
Proof.
intros.

assert(HH0:=plgf_mid  A B C D H0).
split.
intro.
assert(HH1:=plgf_mid  A B D C H1).

unfold Parallelogram_flat in *.
spliter.
ex_and HH0 M.

assert(A = B /\ C = D \/ A = D /\ C = B).
apply(midpoint_cong_uniqueness A C B D M).
Col.
split; assumption.
Cong.
induction H12.
spliter.
contradiction.
spliter.
subst D.
subst C.
induction H5; tauto.

ex_and HH0 M.
unfold Parallelogram_flat in *.
intro.
spliter.
assert(A = B /\ C = D \/ A = D /\ C = B).
apply(midpoint_cong_uniqueness A C B D M).
Col.
split; assumption.
Cong.
induction H12.
spliter.
contradiction.
spliter.
subst D.
subst C.
induction H7; tauto.
Qed.

Lemma plgf_cong :
 forall A B C D,
  Parallelogram_flat A B C D ->
  Cong A B C D /\ Cong A D B C.
Proof.
intros.
unfold Parallelogram_flat in H.
spliter.
split; Cong.
Qed.

Lemma plg_to_parallelogram : forall A B C D, Plg A B C D -> Parallelogram A B C D.
Proof.
intros.
unfold Plg in H.
spliter.
ex_and H0 M.
eapply (mid_plg _ _ _ _ M).
induction H;[left|right]; assumption.
assumption.
assumption.
Qed.

Lemma plgs_one_side :
 forall A B C D,
 Parallelogram_strict A B C D ->
 OS A B C D /\ OS C D A B.
Proof.
intros.
unfold Parallelogram_strict in H.
spliter.
induction H0.
split.
apply l12_6.
assumption.
apply par_strict_symmetry in H0.
apply l12_6.
assumption.
apply False_ind.
spliter.
unfold TS in H.
spliter.
apply H5.
Col.
Qed.

Lemma parallelogram_strict_not_col : forall A B C D,
 Parallelogram_strict A B C D ->
 ~ Col A B C.
Proof.
unfold Parallelogram_strict.
intros.
spliter.
apply two_sides_not_col in H.
Col.
Qed.

Lemma parallelogram_strict_not_col_2 : forall A B C D,
 Parallelogram_strict A B C D ->
 ~ Col B C D.
Proof.
intros.
apply plgs_one_side in H.
destruct H.
apply one_side_not_col124 in H0.
Col.
Qed.

Lemma parallelogram_strict_not_col_3 : forall A B C D,
 Parallelogram_strict A B C D ->
 ~ Col C D A.
Proof.
unfold Parallelogram_strict, TS.
intros.
spliter.
Col.
Qed.

Lemma parallelogram_strict_not_col_4 : forall A B C D,
 Parallelogram_strict A B C D ->
 ~ Col A B D.
Proof.
intros.
apply plgs_one_side in H.
destruct H.
apply one_side_not_col124 in H.
Col.
Qed.

Lemma plgs__pars :
 forall A B C D,
 Parallelogram_strict A B C D ->
 Par_strict A B C D.
Proof.
intros.
assert (HH := H).
unfold Parallelogram_strict in HH; spliter.
destruct H1; auto; spliter.
apply parallelogram_strict_not_col_2 in H.
contradiction.
Qed.

Lemma plgs_sym :
 forall A B C D,
  Parallelogram_strict A B C D ->
  Parallelogram_strict C D A B.
Proof.
unfold Parallelogram_strict.
intros; spliter.
repeat (split; finish).
Qed.

Lemma plg_sym :
 forall A B C D,
  Parallelogram A B C D ->
  Parallelogram C D A B.
Proof.
intros.
induction H.
left.
apply plgs_sym.
assumption.
right.
apply plgf_sym.
assumption.
Qed.

Lemma Rhombus_Plg : forall A B C D, Rhombus A B C D -> Plg A B C D.
Proof.
unfold Rhombus.
tauto.
Qed.

Lemma Rectangle_Plg : forall A B C D,
  Rectangle A B C D ->
  Plg A B C D.
Proof.
unfold Rectangle;tauto.
Qed.

Lemma Rectangle_Parallelogram : forall A B C D,
  Rectangle A B C D ->
  Parallelogram A B C D.
Proof.
unfold Rectangle.
intros.
decompose [and] H.
apply plg_to_parallelogram in H0.
auto.
Qed.

Lemma plg_cong_rectangle :
 forall A B C D,
  Plg A B C D ->
  Cong A C B D ->
  Rectangle A B C D.
Proof.
intros.
unfold Rectangle.
tauto.
Qed.

(*////////////////////////////////////////////////////////////////*)

Lemma plg_trivial : forall A B, A <> B -> Parallelogram A B B A.
Proof.
intros.
right.
unfold Parallelogram_flat.
repeat split; Col; Cong.
Qed.

Lemma plg_trivial1 : forall A B, A <> B -> Parallelogram A A B B.
Proof.
intros.
right.
unfold Parallelogram_flat.
repeat split; Col; Cong.
Qed.

Lemma col_not_plgs : forall A B C D, Col A B C -> ~Parallelogram_strict A B C D.
Proof.
intros.
intro.
unfold Parallelogram_strict in H0.
spliter.
unfold TS in H0.
repeat split.
spliter.
apply H0.
Col.
Qed.

Lemma plg_col_plgf : forall A B C D, Col A B C -> Parallelogram A B C D -> Parallelogram_flat A B C D.
Proof.
intros.
induction H0.
eapply (col_not_plgs A B C D) in H.
contradiction.
assumption.
Qed.





Lemma plg_bet1 : forall A B C D, Parallelogram A B C D -> Bet A C B -> Bet D A C.
Proof.
intros.

apply plg_col_plgf in H.
unfold Parallelogram_flat in H.
spliter.
apply between_symmetry.
apply (col_cong2_bet1 B).
Col.
Between.
Cong.
Cong.
apply bet_col in H0.
Col.
Qed.

Lemma plgf_trivial1 : forall A B, A <> B -> Parallelogram_flat A B B A.
Proof.
intros.
repeat split; Col; Cong.
Qed.

Lemma plgf_trivial2 : forall A B, A <> B -> Parallelogram_flat A A B B.
Proof.
intros.
repeat split; Col; Cong.
Qed.

Lemma plgf_not_point : forall A B, Parallelogram_flat A A B B -> A <> B.
Proof.
intros.
unfold Parallelogram_flat in H.
spliter.
intro.
subst B.
induction H3; tauto.
Qed.

Lemma plgf_trivial_neq : forall A C D, Parallelogram_flat A A C D -> C = D /\ A <> C.
Proof.
intros.
unfold Parallelogram_flat in H.
spliter.
apply cong_symmetry in H1.
apply cong_identity in H1.
subst D.
split.
reflexivity.
induction H3; auto.
Qed.

Lemma plgf_trivial_trans : forall A B C, Parallelogram_flat A A B B -> Parallelogram_flat B B C C 
                                           -> Parallelogram_flat A A C C \/ A = C.
Proof.
intros.

induction(eq_dec_points A C).
right.
assumption.
left.
unfold Parallelogram_flat in *.
spliter.
repeat split; Col; Cong.
Qed.


(**********************************************************************************************************)

Lemma plgf_trivial : forall A B, A <> B -> Parallelogram_flat A B B A.
Proof.
intros.
repeat split; Col; Cong.
Qed.



Lemma plgf3_mid : forall A B C, Parallelogram_flat A B A C -> Midpoint A B C.
Proof.
intros.
unfold Parallelogram_flat in H.
spliter.

assert(B=C \/ Midpoint A B C).
eapply l7_20.
Col.
Cong.
induction H3.
tauto.
induction H4.
contradiction.
assumption.
Qed.

Lemma cong3_id : forall A B C D, A <> B -> Col A B C -> Col A B D -> Cong A B C D -> Cong A D B C -> Cong A C B D 
                             -> A = D /\ B = C \/ A = C /\ B = D.
Proof.
intros.

induction(eq_dec_points A C).
subst C.
apply cong_symmetry in H4.
apply cong_identity in H4.
subst D.
right.
split; reflexivity.

assert(exists M,  (Midpoint M A B /\ Midpoint M C D) \/ (Midpoint M A D /\ Midpoint M C B)).
apply col_cong_mid.
unfold Par.
right.
repeat split.

assumption.
intro.
subst D.

apply cong_identity in H4.
contradiction.
ColR.
ColR.
intro.
unfold Par_strict in H6.
spliter.
apply H9.
exists A.
split; Col.
assumption.
ex_and H6 M.

induction H7.

eapply midpoint_cong_uniqueness.
Col.
spliter.
split.
apply H6.
apply l7_2.
assumption.
Cong.

assert(Col A D C).
ColR.

assert(Cong A D C B).
Cong.

assert(HH:= midpoint_cong_uniqueness A D C B M H7 H6 H8).
induction HH.
spliter.
contradiction.
spliter.
contradiction.
Qed.


Lemma col_cong_mid1 : forall A B C D, A <> D -> Col A B C -> Col A B D -> Cong A B C D -> Cong A C B D 
                                 -> exists M, Midpoint M A D /\ Midpoint M B C.
Proof.
intros.

assert(exists M : Tpoint,
       Midpoint M A C /\ Midpoint M B D \/
       Midpoint M A D /\ Midpoint M B C).

induction(eq_dec_points A B).
subst B.
apply cong_symmetry in H2.
apply cong_identity in H2.
subst D.
assert(HH:=midpoint_existence A C).
ex_and HH M.
exists M.
left.
tauto.

assert (C <> D).
intro.
subst D.
apply cong_identity in H2.
contradiction.

apply (col_cong_mid A B C D).
right.
repeat split; Col; ColR.
intro.
unfold Par_strict in H6.
spliter.
apply H9.
exists C.
split; Col.
assumption.
ex_and H4 M.
induction H5.

assert(A = B /\ C = D \/ A = D /\ C = B).

apply (midpoint_cong_uniqueness A C B D M).
Col.
assumption.
assumption.
induction H5.
spliter.
subst B.
subst D.
exists M.
tauto.
spliter.
contradiction.
exists M.
assumption.
Qed.

Lemma col_cong_mid2 : forall A B C D, A <> C -> Col A B C -> Col A B D -> Cong A B C D -> Cong A D B C 
                                 -> exists M, Midpoint M A C /\ Midpoint M B D.
Proof.
intros.

assert(exists M : Tpoint,
       Midpoint M A C /\ Midpoint M B D \/
       Midpoint M A D /\ Midpoint M B C).

induction(eq_dec_points A B).
subst B.
apply cong_symmetry in H2.
apply cong_identity in H2.
subst D.
assert(HH:=midpoint_existence A C).
ex_and HH M.
exists M.
left.
tauto.

assert (C <> D).
intro.
subst D.
apply cong_identity in H2.
contradiction.

apply (col_cong_mid A B C D).
right.
repeat split; Col; ColR.
intro.
unfold Par_strict in H6.
spliter.
apply H9.
exists C.
split; Col.
assumption.
ex_and H4 M.
induction H5.
exists M.
assumption.

assert(A = B /\ D = C \/ A = C /\ D = B).

apply (midpoint_cong_uniqueness A D B C M).
Col.
assumption.
assumption.
induction H5.
spliter.
subst B.
subst D.
exists M.
tauto.
spliter.
contradiction.
Qed.

(*******************************************************************************************************)

Lemma plgs_not_col : forall A B C D, Parallelogram_strict A B C D ->
  ~ Col A B C /\ ~ Col B C D /\ ~ Col C D A /\ ~ Col A B D.
Proof.
intros.
repeat split.
apply parallelogram_strict_not_col in H; assumption.
apply parallelogram_strict_not_col_2 in H; assumption.
apply parallelogram_strict_not_col_3 in H; assumption.
apply parallelogram_strict_not_col_4 in H; assumption.
Qed.

Lemma not_col_sym_not_col : forall A B B' C , ~Col A B C -> Midpoint A B B' -> ~Col A B' C.
Proof.
intros.
intro.
apply H.
unfold Midpoint in H0.
spliter.
assert(A <> B).
intro.
subst B.
apply H.
Col.
assert(A <> B').
intro.
subst B'.
apply cong_identity in H2.
subst B.
tauto.
apply bet_col in H0.
ColR.
Qed.

Lemma plg_existence : forall A B C, A <> B -> exists D, Parallelogram A B C D.
Proof.
intros.
assert(HH:=midpoint_existence A C).
ex_and HH M.
prolong B M D B M.

assert(Midpoint M B D).
unfold Midpoint.
split; Cong.
exists D.

induction (eq_dec_points A C).
subst C.
apply l7_3 in H0.
subst M.
right.
apply bet_col in H1.
repeat split; Col; Cong.
right.
intro.
subst D.
apply l7_3 in H3.
contradiction.

apply (mid_plg _ _ _ _ M).
left.
assumption.
assumption.
assumption.
Qed.

Lemma plgs_diff : forall A B C D, Parallelogram_strict A B C D -> Parallelogram_strict A B C D /\ A <> B /\ B <> C /\ C <> D /\ D <> A /\ A <> C /\ B <> D.
Proof.
intros.
split.
assumption.
unfold Parallelogram_strict in H.
spliter.
unfold TS in H.
spliter.
repeat split; intro.
subst B.
apply H.
Col.
subst C.
apply H.
Col.
subst D.
apply H2.
Col.
subst D.
apply H2.
Col.
subst C.
apply H.
Col.
subst D.
ex_and H3 T.
apply between_identity in H4.
subst T.
contradiction.
Qed.

Lemma sym_par : forall A B M, A <> B -> forall A' B', Midpoint M A A' -> Midpoint M B B' -> Par A B A' B'.

Proof.
intros.
eapply (l12_17 _ _ _ _ M); assumption.
Qed.

Lemma symmetry_preserves_two_sides : forall A B X Y M A' B', Col X Y M -> TS X Y A B -> Midpoint M A A' -> Midpoint M B B'
                                               -> TS X Y A' B'.
Proof.
intros.

assert(X <> Y /\ ~Col A X Y /\ ~Col B X Y).
unfold TS in H0.
spliter.
repeat split; auto.
intro.
subst Y.
Col.
spliter.

assert(A <> M).
intro.
subst M.
apply H4.
Col.

assert(A' <> M).
intro.
subst M.
apply H6.
apply sym_equal.
apply is_midpoint_id.
apply l7_2.
assumption.

assert(B <> M).
intro.
subst M.
apply H5.
Col.

assert(B' <> M).
intro.
subst M.
apply H8.
apply sym_equal.
apply is_midpoint_id.
apply l7_2.
assumption.

assert(TS X Y A A').
unfold TS.
repeat split; auto.
intro.
apply H4.
unfold Midpoint in H1.
spliter.
apply bet_col in H1.

assert(Col M A' X).
ColR.

assert(Col M A' Y).
ColR.

eapply (col3 A' M); Col.
exists M.
split.
Col.
apply midpoint_bet.
assumption.

assert(TS X Y B B').
unfold TS.
repeat split; auto.
intro.
apply H5.
unfold Midpoint in H2.
spliter.
apply bet_col in H2.

assert(Col M B' X).
ColR.

assert(Col M B' Y).
ColR.

eapply (col3 B' M); Col.
exists M.
split.
Col.
apply midpoint_bet.
assumption.

assert(OS X Y A' B).
eapply l9_8_1.
apply l9_2.
apply H10.
apply l9_2.
assumption.
eapply l9_8_2.
apply H11.
apply one_side_symmetry.
assumption.
Qed.

Lemma symmetry_preserves_one_side : forall A B X Y M A' B', Col X Y M -> OS X Y A B -> Midpoint M A A' -> Midpoint M B B'
                                               -> OS X Y A' B'.
Proof.
intros.

assert(X <> Y /\ ~Col A X Y /\ ~Col B X Y).
unfold OS in H0.
ex_and H0 P.
unfold TS in H0.
unfold TS in H3.
spliter.
repeat split; auto.
intro.
subst Y.
Col.
spliter.

assert(A <> M).
intro.
subst M.
apply H4.
Col.

assert(A' <> M).
intro.
subst M.
apply H6.
apply sym_equal.
apply is_midpoint_id.
apply l7_2.
assumption.

assert(B <> M).
intro.
subst M.
apply H5.
Col.

assert(B' <> M).
intro.
subst M.
apply H8.
apply sym_equal.
apply is_midpoint_id.
apply l7_2.
assumption.

assert(TS X Y A A').
unfold TS.
repeat split; auto.
intro.
apply H4.
unfold Midpoint in H1.
spliter.
apply bet_col in H1.

assert(Col M A' X).
ColR.

assert(Col M A' Y).
ColR.

eapply (col3 A' M); Col.
exists M.
split.
Col.
apply midpoint_bet.
assumption.

assert(TS X Y B B').
unfold TS.
repeat split; auto.
intro.
apply H5.
unfold Midpoint in H2.
spliter.
apply bet_col in H2.

assert(Col M B' X).
ColR.

assert(Col M B' Y).
ColR.

eapply (col3 B' M); Col.
exists M.
split.
Col.
apply midpoint_bet.
assumption.
eapply l9_8_1.
apply l9_2.
apply H10.
apply l9_2.

eapply l9_8_2.
apply H11.
apply one_side_symmetry.
assumption.
Qed.

Lemma plgf_bet : forall A B A' B', Parallelogram_flat A B B' A' 
                                 -> Bet A' B' A /\ Bet B' A B 
                                 \/ Bet A' A B' /\ Bet A B' B
                                 \/ Bet A A' B /\ Bet A' B B'
                                 \/ Bet A B A' /\ Bet B A' B'.

Proof.
intros.
induction H.
spliter.

induction(eq_dec_points A B).
subst B.
apply cong_symmetry in H1.
apply cong_identity in H1.
subst B'.
left.
split;
Between.

assert(A' <> B').
intro.
subst B'.
apply cong_identity in H1.
contradiction.

assert(Col A' B' A).
ColR.
assert(Col A' B' B).
ColR.

induction H0.
right; right; right.
split.
assumption.
apply (col_cong2_bet1 A);
Col;
Cong.

induction H0.
right;right; left.
split.
Between.
eapply(col_cong2_bet2 _ A).
Col.
Between.
Cong.
Cong.

induction H.

assert(Bet A' B B').
eapply (outer_transitivity_between2 _ A); auto.

assert(B = B' /\ A' = A).
apply(bet_cong_eq A' A B B' H0 H8).
Cong.
spliter.
subst B'.
subst A'.
right;left.
split; Between.
induction H.

right;left.
split;auto.
eapply (between_inner_transitivity _ _ _ B);
Between.
Between.

induction(eq_dec_points A A').
subst A'.
apply cong_symmetry in H2.
apply cong_identity in H2.
subst B'.
right;left.
split; Between.

left.
split.

assert(Bet A B' A' \/ Bet A A' B').
eapply (l5_2 B).
auto.
Between.
Between.
induction H9.
Between.

assert(Bet B' A' B).
eapply (outer_transitivity_between _ _ A).
Between.
assumption.
auto.

assert(Bet B A' B').
eapply (outer_transitivity_between2 _ A).
Between.
assumption.
assumption.



assert(A = B /\ B' = A').
apply(bet_cong_eq); Between; Cong.
spliter.
contradiction.
assumption.
Qed.

Lemma plgs_existence : forall A B, A <> B -> exists C, exists D, Parallelogram_strict A B C D.
Proof.
intros.

assert(HH:=not_col_exists A B H).
ex_and HH C.
assert(HH:=plg_existence A B C H).
ex_and HH D.
exists C.
exists D.
induction H1.
assumption.
unfold Parallelogram_flat in H1.
spliter.
contradiction.
Qed.

Lemma Rectangle_not_triv : forall A,
 ~ Rectangle A A A A.
Proof.
intros.
unfold Rectangle.
unfold Plg.
intuition.
Qed.

Lemma Rectangle_triv : forall A B,
 A<>B ->
 Rectangle A A B B.
Proof.
intros.
unfold Rectangle.
split;Cong.
unfold Plg.
split.
intuition.
elim (midpoint_existence A B).
intros.
exists x.
tauto.
Qed.

Lemma Rectangle_not_triv_2 : forall A B,
 ~ Rectangle A B A B.
Proof.
intros.
unfold Rectangle.
intro.
spliter.
unfold Plg in H.
intuition.
Qed.

Lemma Square_not_triv : forall A,
 ~ Square A A A A.
Proof.
intros.
unfold Square.
intro.
spliter.
firstorder using Rectangle_not_triv.
Qed.

Lemma Square_not_triv_2 : forall A B,
 ~ Square A A B B.
Proof.
intros.
unfold Square.
intro.
spliter.
treat_equalities.
firstorder using Rectangle_not_triv.
Qed.

Lemma Square_not_triv_3 : forall A B,
 ~ Square A B A B.
Proof.
intros.
unfold Square.
intro.
spliter.
firstorder using Rectangle_not_triv_2.
Qed.



Lemma Square_Rectangle : forall A B C D,
 Square A B C D -> Rectangle A B C D.
Proof.
unfold Square;tauto.
Qed.

Lemma Square_Parallelogram :  forall A B C D,
 Square A B C D -> Parallelogram A B C D.
Proof.
intros.
apply Square_Rectangle in H.
apply Rectangle_Parallelogram in H.
assumption.
Qed.

Lemma Rhombus_Rectangle_Square : forall A B C D,
 Rhombus A B C D ->
 Rectangle A B C D ->
 Square A B C D.
Proof.
intros.
unfold Square.
unfold Rhombus in *.
tauto.
Qed.

Lemma rhombus_cong_square : forall A B C D,
 Rhombus A B C D ->
 Cong A C B D ->
 Square A B C D.
Proof.
intros.
apply Rhombus_Rectangle_Square.
assumption.
apply Rhombus_Plg in H.
apply plg_cong_rectangle;auto.
Qed.

Lemma Kite_comm : forall A B C D,
 Kite A B C D -> Kite C D A B.
Proof.
unfold Kite.
tauto.
Qed.

End Quadrilateral.