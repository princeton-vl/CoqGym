(* Gabriel Braun February 2013 *)

Require Export GeoCoq.Tarski_dev.Annexes.quadrilaterals_inter_dec.

Section Vectors.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Lemma eqv_refl : forall A B, EqV A B A B.
Proof.
intros.
unfold EqV.
induction (eq_dec_points A B).
right.
split; auto.
left.
right.
apply plgf_trivial.
assumption.
Qed.

Lemma eqv_sym : forall A B C D, EqV A B C D -> EqV C D A B.
Proof.
intros.
unfold EqV in *.
induction H.
left.
apply plg_sym.
apply plg_comm2.
assumption.
right.
tauto.
Qed.

Lemma eqv_trans : forall A B C D E F, EqV A B C D -> EqV C D E F -> EqV A B E F.
Proof.
intros.
unfold EqV in *.

induction H; induction H0.
assert(Parallelogram A B F E \/ A = B /\ D = C /\ E = F /\ A = E).
apply (plg_pseudo_trans A B D C E F); auto.
apply plg_comm2.
assumption.
induction H1.
left.
auto.
right.
tauto.
spliter.
subst D.
subst F.
induction (eq_dec_points A B).
right.
tauto.
left.
induction H.
induction H.
unfold TS in H.
spliter.
apply False_ind.
apply H3.
Col.
apply plgf_sym in H.
apply plgf_trivial_neq in H.
tauto.
spliter.
subst B.
subst D.
induction H0.
induction H.
unfold TS in H.
spliter.
apply False_ind.
apply H.
Col.
apply plgf_trivial_neq in H.
right.
spliter.
subst F.
tauto.
right.
tauto.
Qed.

Lemma eqv_comm : forall A B C D, EqV A B C D -> EqV B A D C.
Proof.
intros.
unfold EqV in *.
induction H.
left.
apply plg_comm2.
assumption.
right.
spliter.
subst B.
subst D.
tauto.
Qed.

Lemma vector_construction : forall A B C, exists D, EqV A B C D.
Proof.
intros.
induction (eq_dec_points A B).
exists C.
right.
tauto.
assert(HH:= midpoint_existence B C).
ex_and HH M.
prolong A M D A M.
exists D.
left.
apply (mid_plg _ _ _ _ M).

induction(eq_dec_points A D).
subst D.
right.
intro.
subst C.
apply l7_3 in H0.
apply between_identity in H1.
subst M.
contradiction.
left.
assumption.
split; Cong.
assumption.
Qed.

Lemma vector_construction_uniqueness :
 forall A B C D D',
 EqV A B C D ->
 EqV A B C D' ->
 D = D'.
Proof.
intros.
unfold EqV in *.
induction H; induction H0.
apply plg_comm2 in H.
apply plg_comm2 in H0.
apply (plg_uniqueness B A C); auto.
spliter.
subst B.
subst D'.
induction H.
induction H.
unfold TS in H.
spliter.
apply False_ind.
apply H.
Col.
apply (plgf_trivial_neq A D C ).
assumption.
spliter.
subst B.
subst D.
induction H0.
induction H.
unfold TS in H.
spliter.
apply False_ind.
apply H.
Col.
apply plgf_comm2 in H.
apply (plgf_trivial_neq A C D').
assumption.
spliter.
subst C.
auto.
Qed.

Lemma null_vector : forall A B C, EqV A A B C -> B = C.
Proof.
intros.
unfold EqV in H.
induction H.
induction H.
induction H.
unfold TS in H.
spliter.
apply False_ind.
apply H.
Col.
apply plgf_trivial_neq in H.
spliter.
subst C.
tauto.
tauto.
Qed.

Lemma vector_uniqueness : forall A B C, EqV A B A C -> B = C.
Proof.
intros.
unfold EqV in H.
induction H.
induction H.
induction H.
unfold TS in H.
spliter.
apply False_ind.
apply H2.
Col.
apply plgf_permut in H.
apply plgf_sym in H.
apply (plgf_trivial_neq A B C ).
assumption.
spliter.
subst A.
auto.
Qed.

Lemma eqv_trivial : forall A B , EqV A A B B.
Proof.
intros.
unfold EqV.
right.
tauto.
Qed.

Lemma eqv_permut :
  forall A B C D,
  EqV A B C D ->
  EqV A C B D.
Proof.
intros.
induction (eq_dec_points A C).
subst C.
assert(B = D).
apply (vector_uniqueness A).
assumption.
subst D.
apply eqv_trivial.

unfold EqV in *.
induction H.
left.
apply plg_permut.
apply plg_comm2.
assumption.
left.
spliter.
subst B.
subst D.
apply plg_trivial.
assumption.
Qed.

Lemma eqv_par :
 forall A B C D,
  A <> B ->
  EqV A B C D ->
  Par A B C D.
Proof.
intros.
unfold EqV in H0.
induction H0.
unfold Parallelogram in H0.
induction H0.
unfold Parallelogram_strict in H0.
spliter.
apply par_right_comm.
assumption.
unfold Parallelogram_flat in H0.
spliter.
right.
spliter.
repeat split; Col.
intro.
subst D.
apply cong_identity in H2.
contradiction.
ColR.
ColR.

spliter.
contradiction.
Qed.

Lemma eqv_opp_null :
  forall A B,
  EqV A B B A ->
  A = B.
Proof.
intros.
unfold EqV in H.
induction H.
apply plg_irreflexive in H.
tauto.
tauto.
Qed.

Lemma eqv_sum :
  forall A B C A' B' C',
  EqV A B A' B' ->
  EqV B C B' C' ->
  EqV A C A' C'.
Proof.
intros.

unfold EqV in *.
induction H.
induction H0.
apply plg_comm2 in H.
apply plg_permut in H.
apply plg_permut in H0.
apply plg_sym in H0.
assert(HH:= plg_pseudo_trans A A' B' B C C' H H0).
induction HH.
left.
apply plg_permut.
apply plg_comm2.
assumption.
spliter.
right.
subst A'.
subst C'.
tauto.
spliter.
subst C.
subst C'.
left.
assumption.
spliter.
subst B.
subst B'.
assumption.
Qed.

Lemma null_sum :
 forall A B C,
  SumV A B B A C C.
Proof.
intros.
unfold SumV.
intros D H.
assert(A = D).
apply (vector_uniqueness B).
apply H.
subst D.
apply eqv_trivial.
Qed.

Lemma chasles :
 forall A B C,
  SumV A B B C A C.
Proof.
intros.
unfold SumV.
intros D H.
assert(C = D).
apply (vector_uniqueness B).
assumption.
subst D.
apply eqv_refl.
Qed.

Lemma eqv_mid :
 forall A B C,
  EqV A B B C ->
  Midpoint B A C.
Proof.
intros.
unfold EqV in H.
induction H.
apply plg_mid in H.
ex_and H M.
apply l7_3 in H0.
subst M.
assumption.
spliter.
subst C.
subst B.
apply l7_3_2.
Qed.

Lemma mid_eqv :
  forall A B C, Midpoint A B C ->
  EqV B A A C.
Proof.
intros.
unfold EqV.
induction(eq_dec_points A B).
subst B.
apply is_midpoint_id in H.
subst C.
right.
tauto.
left.

apply (mid_plg _ _ _ _ A).
left.
intro.
subst C.
apply l7_3 in H.
contradiction.
assumption.
Midpoint.
Qed.


Lemma sum_sym :
  forall A B C D E F,
  SumV A B C D E F ->
  SumV C D A B E F.
Proof.
intros.
unfold SumV in *.
assert(HH:=vector_construction C D B).
ex_and HH D'.


assert(HH:= (H D' H0)).
clear H.

assert(EqV C B D D').
apply eqv_permut.
assumption.

assert(EqV A D B D'0).
apply eqv_permut.
assumption.

induction (eq_dec_points A D'0).
subst D'0.

apply eqv_comm in H1.
assert(HP:= (eqv_mid B A D H1)).

unfold EqV in H0.
induction H0.
apply plg_mid in H0.
ex_and H0 M.
assert( A = M).
apply (l7_17 B D).
apply HP.
Midpoint.
subst M.

apply mid_eqv in H0.
apply (eqv_trans _ _ A D').
apply H0.
assumption.

spliter.
subst D.
subst D'.
apply (eqv_trans _ _ A B).
apply eqv_sym.
apply eqv_comm.
apply H1.
assumption.

induction H0; induction H1.
apply plg_mid in H0.
apply plg_mid in H1.
ex_and H0 M0.
ex_and H1 M1.

assert(M1 = M0).
apply (l7_17 B D).
apply H5.
Midpoint.
subst M1.
assert(Parallelogram A D' D'0 C).
apply (mid_plg _ _ _ _ M0).
left.
assumption.
assumption.
Midpoint.
assert(EqV C D'0 A D').
unfold EqV.
left.
apply plg_comm2.
apply plg_sym.
assumption.
apply (eqv_trans _ _ A D').
apply H7.
assumption.
spliter.
subst B.
subst D'0.
assert(EqV C D A D').
apply eqv_permut.
assumption.
apply (eqv_trans _ _ A D').
apply H1.
assumption.
spliter.
subst D.
subst D'.

assert(EqV A B C D'0).
apply eqv_permut.
assumption.
apply (eqv_trans _ _ A B).
apply eqv_sym.
apply H0.
assumption.
spliter.
subst D.
subst D'.
subst B.
subst D'0.
apply null_vector in HH.
subst F.
apply eqv_trivial.
Qed.


Lemma opposite_sum :
  forall A B C D E F,
  SumV A B C D E F ->
  SumV B A D C F E.
Proof.
intros.
unfold SumV in *.
intros D0 H0.
assert(HH:=vector_construction C D B).
ex_and HH D'.
assert(HH:= (H D' H1)).
clear H.

assert(EqV D' B A D0).
apply (eqv_trans _ _ D C).
apply eqv_sym.
apply eqv_comm.
apply H1.
assumption.
apply eqv_permut in H.
eapply (eqv_trans _ _ D' A).
apply eqv_sym.
apply H.
apply eqv_comm.
assumption.
Qed.

Lemma null_sum_eq :
  forall A B C D,
  SumV A B B C D D ->
  A = C.
Proof.
intros.
unfold SumV in H.
assert(HH:= vector_construction B C B).
ex_and HH D'.
assert(HH:= (H D' H0)).
assert(A = D').
apply (null_vector D).
apply eqv_sym.
apply HH.
subst D'.
apply vector_uniqueness in H0.
auto.
Qed.

Lemma is_to_ise :
  forall A B C D E F,
  SumV A B C D E F ->
  SumV_exists A B C D E F.
Proof.
intros.
unfold SumV in H.
unfold SumV_exists.
assert(HH:= (vector_construction C D B)).
ex_and HH D'.
assert(HH:=(H D' H0)).
exists D'.
split.

apply eqv_sym.
assumption.
assumption.
Qed.

Lemma ise_to_is :
 forall A B C D E F,
  SumV_exists A B C D E F ->
  SumV A B C D E F.
Proof.
intros.
ex_and H D'.
unfold SumV.
intros.
assert(D'= D'0).
apply (vector_construction_uniqueness C D B).
apply eqv_sym.
apply H.
assumption.
subst D'0.
assumption.
Qed.

Lemma sum_exists :
 forall A B C D, exists E, exists F, SumV A B C D E F.
intros.
assert(HH:= vector_construction C D B).
ex_and HH F.
exists A.
exists F.
unfold SumV.
intros.
assert(D' = F).
apply (vector_construction_uniqueness C D B); auto.
subst D'.
apply eqv_refl.
Qed.

Lemma sum_uniqueness :
 forall A B C D E F E' F',
 SumV A B C D E F ->
 SumV A B C D E' F' ->
 EqV E F E' F'.
Proof.
intros.
unfold SumV in *.
assert(HH:= vector_construction C D B).
ex_and HH D'.
assert(HH:= (H D' H1)).
assert(HP := (H0 D' H1)).
apply (eqv_trans _ _ A D').
apply eqv_sym.
auto.
auto.
Qed.

Lemma same_dir_refl : forall A B, Same_dir A B A B.
intros.
unfold Same_dir.
induction (eq_dec_points A B).
left.
tauto.
right.
exists B.
split.
apply out_trivial.
auto.
apply eqv_refl.
Qed.

Lemma same_dir_ts :
  forall A B C D,
  Same_dir A B C D ->
  exists M, Bet A M D /\ Bet B M C.
Proof.
intros.
induction H.
spliter.
subst B.
subst D.
exists A.
split; Between.

ex_and H D'.
induction H0.

assert(exists M : Tpoint, Midpoint M A D' /\ Midpoint M B C).
apply plg_mid.
assumption.
ex_and H1 M.
unfold Midpoint in *.
spliter.

induction H0.
assert(HH:=plgs_two_sides A B D' C H0).
spliter.

assert(B <> C).
intro.
subst C.
unfold TS in H6.
spliter.
Col.
assert(~ Col B C D').
intro.
unfold TS in H6.
spliter.
apply H9.
Col.

assert(OS B C D' D).
apply l6_6 in H.
apply (out_one_side_1 _ _ _ _ C); Col.

assert(TS B C A D).
apply l9_2.
apply (l9_8_2 _ _ D').
apply l9_2.
apply H6.
auto.

assert(~ Col A B C).
induction H10.
assumption.
induction H10.
spliter.
ex_and H13 T.

assert(OS A B D' C /\ OS D' C A B).
apply(plgs_one_side A B D' C).
assumption.
spliter.

assert(~Col A B C).
assumption.

assert(Par_strict A B D' C /\ Par_strict A C B D').

apply(plgs_par_strict A B D' C).
assumption.
spliter.

assert(A <> B).
intro.
subst B.
apply H18.
exists C.
split; Col.

assert(Par C D A B).
apply (par_col_par_2 _ D').
unfold Out in H.
spliter.
auto.
apply out_col in H.
Col.
apply par_symmetry.
apply par_right_comm.
left.
assumption.

assert(Par_strict A B C D).
apply par_strict_symmetry.
induction H21.
auto.
spliter.
apply False_ind.
apply H17.
Col.

induction(col_dec A B T).
apply False_ind.
assert(B = T).
apply (l6_21 A B C B); Col.
subst T.
apply H22.
exists D.
apply bet_col in H14.
split; Col.

induction(col_dec C D T).
apply False_ind.
assert(C = T).
apply (l6_21 C D B C); Col.
subst T.
apply H22.
exists A.
apply bet_col in H14.
split; Col.

induction H13.

assert(OS B A T D).
apply (out_one_side_1 _ _ _ _ A); Col.

unfold Out.
repeat split.
intro.
subst T.
apply H23.
Col.
intro.
subst D.
apply H22.
exists A.
split; Col.
left.
auto.

assert(OS B A T C).
apply (one_side_transitivity _ _ _ D).
apply H25.
apply (par_strict_one_side _ _ _ C).
apply par_strict_comm.
apply H22.
Col.

assert(TS B A T C).
unfold TS.
repeat split; Col.
exists B.
split; Col.
apply l9_9 in H26.
contradiction.
assumption.

induction H13.

assert(OS C D T A).
apply (out_one_side_1 _ _ _ _ D).
auto.
Col.
unfold Out.
repeat split.
intro.
subst T.
apply H24.
Col.
intro.
subst D.
apply H22.
exists A.
split; Col.
left.
Between.
assert(OS C D T B).
apply (one_side_transitivity _ _ _ A).
apply H25.
apply (par_strict_one_side _ _ _ B).
apply par_strict_symmetry.
apply H22.
Col.

assert(TS C D T B).
unfold TS.
repeat split.
unfold Out in H.
spliter.
auto.

intro.
apply H24.
Col.
intro.
apply H22.
exists B.
split; Col.
exists C.
split.
Col.
Between.
apply l9_9 in H27.
contradiction.
exists T.
split; Between.

assert(HH:= plgf_bet A B C D' H0).

induction (eq_dec_points A D').
subst D'.
unfold Parallelogram_flat in H0.
spliter.
assert(B = C \/ Midpoint A B C).
apply l7_20.
Col.
Cong.
induction H9.
subst C.
tauto.
exists A.
split.
Between.
apply midpoint_bet.
assumption.

induction (eq_dec_points B C).
subst C.
unfold Parallelogram_flat in H0.
spliter.
assert(A = D' \/ Midpoint B A D').
apply l7_20.
Col.
Cong.
induction H10.
subst D'.
tauto.
exists B.
split.
induction H10.
unfold Out in H.
spliter.
induction H13.
apply (between_inner_transitivity _ _ _ D').
apply H10.
auto.
apply (outer_transitivity_between _ _ D').
apply H10.
auto.
auto.
Between.

induction HH.
spliter.
exists A.
split.
Between.
apply (outer_transitivity_between _ _ D'); Between.

induction H7.
spliter.
exists A.
split.
Between.
apply between_symmetry.
apply (outer_transitivity_between _ _ D'); Between.

induction H7.
spliter.
exists C.
split.
induction H.
spliter.
induction H10.
assert(Bet C B D \/ Bet C D B).
apply (l5_3 _ _ _ D'); auto.
induction H11.
apply (outer_transitivity_between _ _ B); Between.
apply (between_inner_transitivity _ _ _ B).
apply H7.
auto.
apply (outer_transitivity_between _ _ B); Between.
apply (between_exchange4 _ _ D').
apply H8.
auto.
Between.
spliter.

exists B.
split.
unfold Out in H.
spliter.
induction H10.
assert(Bet B C D).
apply (between_inner_transitivity _ _ _ D').
apply H8.
assumption.
eBetween.

apply (outer_transitivity_between _ _ C).
apply H7.
apply (outer_transitivity_between _ _ D' ).
apply H8.
auto.
auto.
auto.
Between.
spliter.
subst B.
subst D'.
exists A.
split; Between.
Qed.

Lemma one_side_col_out :
 forall A B X Y,
  Col A X Y ->
  OS A B X Y ->
  Out A X Y.
Proof.
intros.
assert(A <> B /\ ~ Col X A B /\ ~ Col Y A B /\ X <> A /\ Y <> A).
unfold OS in H0.
ex_and H0 T.
unfold TS in *.
spliter.
repeat split; auto.
intro.
subst B.
Col.
intro.
subst X.
apply H0.
Col.
intro;
spliter.
subst Y.
apply H1.
Col.
spliter.

induction H.
repeat split; auto.
induction H.
repeat split; auto.
right.
Between.

assert(TS A B X Y).
unfold TS.
repeat split; auto.
exists A.
split.
Col.
Between.
apply l9_9 in H6.
contradiction.
Qed.

Lemma par_ts_same_dir :
 forall A B C D, Par_strict A B C D ->
 (exists M, Bet A M D /\ Bet B M C) ->
 Same_dir A B C D.
Proof.
intros.
ex_and H0 M.
unfold Same_dir.
right.

assert(HH:=vector_construction A B C).
ex_and HH D'.
exists D'.
split.
2: auto.

assert(A <> B /\ C <> D).
unfold Par in H.
unfold Par_strict in H.
tauto.
spliter.

assert(A <> M).
intro.
subst M.
apply False_ind.
apply H.
exists C.
apply bet_col in H1.
split; Col.

induction (eq_dec_points B D').
subst D'.
assert( A = C).
apply (vector_uniqueness B).
apply eqv_comm.
apply H2.
subst C.

assert(Bet A D B \/ Bet A B D).
apply (l5_1 _ M).
apply H5.
auto.
Between.
unfold Out.
repeat split; auto.
induction H2.

assert(Par A B D' C).
apply plg_par in H2; auto.
spliter.
auto.

assert(Col C D D').
apply col_permutation_1.
apply (parallel_uniqueness A B _ _ C _ C).
left.
apply H.
2: apply par_right_comm.
2: apply H7.
Col.
Col.

induction H2.

assert(HH := (plgs_two_sides A B D' C H2)).
spliter.

assert(TS B C A D).
unfold TS.
unfold TS in H10.
spliter.
repeat split;
auto.
intro.
apply H11.
ColR.
exists M.
split.
apply bet_col in H1.
Col.
auto.

assert(OS B C D D').
apply (l9_8_1 _ _ _ _ A).
apply l9_2.
apply H11.
apply l9_2.
auto.

apply (one_side_col_out _ B).
Col.
apply invert_one_side.
apply H12.

apply False_ind.
unfold Parallelogram_flat in H2.
spliter.
apply H.
exists C.
split; Col.

spliter.
subst D'.
subst B.
tauto.
Qed.

Lemma same_dir_out : forall A B C, Same_dir A B A C -> Out A B C \/ A = B /\ A = C.
intros.
unfold Same_dir in H.
induction H.
right.
auto.
ex_and H D'.
unfold EqV in H0.
induction H0.
induction H0.
apply plgs_par_strict in H0.
spliter.
apply False_ind.
apply H1.
exists B.
split; Col.
apply plgf_permut in H0.
apply plgf_sym in H0.
apply plgf_trivial_neq in H0.
spliter.
subst D'.
left.
apply l6_6.
assumption.
spliter.
subst D'.
subst B.
unfold Out in H.
tauto.
Qed.

Lemma same_dir_out1 : forall A B C, Same_dir A B B C -> Out A B C \/ A = B /\ A = C.
intros.
unfold Same_dir in H.
induction H.
right.
spliter.
subst B.
tauto.
ex_and H D'.
unfold EqV in H0.

induction H0.
induction H0.
apply plgs_par_strict in H0.
spliter.
apply False_ind.
apply H1.
exists B.
split; Col.
unfold Parallelogram_flat in H0.
spliter.
assert(A = D' \/ Midpoint B A D').
apply l7_20.
Col.
Cong.
induction H5.
subst D'.
tauto.
left.
unfold Midpoint in H5.
spliter.
unfold Out.
repeat split.
intro.
subst B.
apply cong_symmetry in H6.
apply cong_identity in H6.
induction H4; tauto.
intro.
subst C.
unfold Out in H.
spliter.
induction H8.
apply H.
apply (between_equality _ _ D');
Between.
apply H7.
apply (between_equality _ _ A);
Between.
induction H.
spliter.
induction H8.
left.
apply (between_inner_transitivity _ _ _ D').
apply H5.
apply H8.
left.
apply (outer_transitivity_between _ _  D').
apply H5.
auto.
auto.
spliter.
subst B.
subst D'.
unfold Out in H.
tauto.
Qed.

Lemma same_dir_null : forall A B C, Same_dir A A B C -> B = C.
intros.
unfold Same_dir in H.
induction H.
tauto.
ex_and H D.
apply null_vector in H0.
subst D.
unfold Out in H.
tauto.
Qed.



Lemma plgs_out_plgs :
 forall A B C D B' C',
 Parallelogram_strict A B C D ->
 Out A B B' ->
 Out D C C' ->
 Cong A B' D C' ->
 Parallelogram_strict A B' C' D.
Proof.
intros.
assert(OS A D C B /\ OS C B A D).
apply plgs_one_side.
apply plgs_permut.
apply plgs_comm2.
assumption.

assert( A <> B /\ A <> B' /\ D <> C /\ D <> C').
unfold Out in *.
spliter.
repeat split; auto.
spliter.

assert(Par_strict A B C D).
apply plgs_par_strict in H.
spliter.
auto.

assert(Par_strict A B' D C').
assert(Par A B' D C').
apply (par_col_par_2 _ B).
auto.
apply out_col.
auto.
apply par_symmetry.
apply (par_col_par_2 _ C).
auto.
apply out_col.
auto.
apply par_symmetry.
apply par_right_comm.
left.
auto.
induction H10.
auto.
spliter.
apply False_ind.
apply out_col in H0.
apply out_col in H1.

assert(~Col A C D).
intro.
apply H9.
exists A.
split; Col.
apply H14.
ColR.

assert(OS A D B B').
apply (out_one_side_1 A _ _ _ A).
intro.
apply H9.
exists D.
split; Col.
Col.
auto.

assert(OS A D C C').
apply (out_one_side_1 _ D _ _ D).
intro.
apply H9.
exists A.
split; Col.
Col.
auto.

assert(OS A D B' C').
apply (one_side_transitivity _ _ _ B).
apply one_side_symmetry.
apply H11.
apply (one_side_transitivity _ _ _ C).
apply one_side_symmetry.
apply H3.
assumption.


assert(HH:=par_cong_mid_os  A B' D C' H10 H2 H13).
ex_and HH M.

apply (mid_plgs _ _ _ _ M).
intro.
apply H10.
exists C'.
split; Col.
assumption.
assumption.
Qed.

Lemma plgs_plgs_bet :
 forall A B C D B' C',
 Parallelogram_strict A B C D ->
 Bet A B B' ->
 Parallelogram_strict A B' C' D ->
 Bet D C C'.
Proof.
intros.
assert(Col C' C D /\ Col D C D).
apply (parallel_uniqueness A B C D C' D D); Col.
left.
apply plgs_par_strict in H.
spliter.
assumption.
apply (par_col_par_2 _ B').
intro.
subst B.
apply plgs_par_strict in H.
spliter.
apply H.
exists C.
split; Col.
apply bet_col in H0.
Col.
apply plgs_par_strict in H1.
spliter.
left.
assumption.
spliter.
clear H3.
induction H2.
Between.
induction H2.
apply False_ind.

apply plgs_permut in H.
apply plgs_permut in H1.

assert(HH1:=plgs_one_side B C D A H).
assert(HH2:=plgs_one_side B' C' D A H1).
spliter.
assert(OS D A C C').
apply (one_side_transitivity _ _ _ B).
apply one_side_symmetry.
apply H6.
apply one_side_symmetry.
apply (one_side_transitivity _ _ _ B').
apply one_side_symmetry.
apply H4.
apply (out_one_side_1 _ _ _ _ A).
intro.
apply plgs_par_strict in H1.
spliter.
apply H1.
exists B'.
split; Col.
Col.
repeat split.
intro.
subst B'.
apply H1.
Col.
intro.
subst B.
apply H.
Col.
right.
assumption.
assert(TS D A C C').
repeat split.
intro.
apply plgs_par_strict in H.
spliter.
apply H.
exists C.
split; Col.
intro.
apply plgs_par_strict in H1.
spliter.
apply H1.
exists C'.
split; Col.
exists D.
split.
Col.
assumption.
apply l9_9 in H8.
contradiction.

assert(Parallelogram_strict B C D A).
apply plgs_permut.
assumption.
assert(Parallelogram_strict D A B' C').
apply plgs_permut.
apply plgs_sym.
assumption.

induction (eq_dec_points C C').
subst C'.
Between.

assert(HH:= plgs_pseudo_trans B C D A B' C' H3 H4).
assert(Parallelogram_strict B C C' B').
induction HH.
assumption.
unfold Parallelogram_flat in H6.
spliter.
apply False_ind.

apply plgs_par_strict in H.
apply plgs_par_strict in H1.
spliter.
apply H.
exists B.
split.
Col.
apply bet_col in H2.
ColR.

assert(HH1:=plgs_one_side B C C' B' H6).
assert(HH2:=plgs_one_side B C D A H3).
spliter.

(*******************************)

assert(TS B C A B').
unfold TS.
repeat split.
intro.
apply plgs_par_strict in H.
spliter.
apply H.
exists C.
split; Col.
intro.
apply plgs_par_strict in H6.
spliter.
apply H6.
exists B'.
split; Col.
exists B.
split.
Col.
assumption.

assert(OS B C C' D).
apply (out_one_side_1 _ _ _ _ C).
intro.
apply plgs_par_strict in H6.
spliter.
apply H6.
exists C'.
split; Col.
apply col_trivial_2.
repeat split.
auto.
intro.
subst D.
apply plgs_par_strict in H3.
spliter.
apply H3.
exists C.
split; Col.
left.
Between.

assert(OS B C A B').
apply (one_side_transitivity _ _ _ D).
apply one_side_symmetry.
apply H7.
apply (one_side_transitivity _ _ _ C').
apply one_side_symmetry.
apply H12.
assumption.
apply l9_9 in H11.
contradiction.
Qed.

Lemma plgf_plgf_bet :
 forall A B C D B' C',
 Parallelogram_flat A B C D ->
 Bet A B B' ->
 Parallelogram_flat A B' C' D ->
 Bet D C C'.
Proof.
intros.
induction (eq_dec_points A B).
subst B.
assert(C = D /\ A <> C).
apply plgf_trivial_neq.
auto.
spliter.
subst D.
Between.

assert(HH:=not_col_exists A B H2).
ex_and HH P.
assert(HH:=plg_existence A B P H2).
ex_and HH Q.

assert(Parallelogram_strict A B P Q).
induction H4.
assumption.
unfold Parallelogram_flat in H4.
spliter.
contradiction.

assert(Parallelogram_strict C D Q P).

apply(plgf_plgs_trans C D A B P Q).
intro.
subst D.
assert(A = B /\ C <> A).
apply plgf_trivial_neq.
apply plgf_sym.
assumption.
tauto.
apply plgf_sym.
assumption.
assumption.

assert(A <> B').
intro.
subst B'.
apply between_identity in H0.
contradiction.

assert(HH:=vector_construction A B' Q).
ex_and HH P'.

induction H8.
2 : tauto.

assert(B <> P).
intro.
subst P.
apply H3.
Col.

assert(B' <> P').
intro.
subst P'.

induction H8.
apply plgs_par_strict in H8.
spliter.
apply H10.
apply plgs_par_strict in H5.
exists A.
split; Col.
apply plgf_permut in H8.
assert(Q = A /\ B' <> Q).
apply plgf_trivial_neq.
auto.
spliter.
subst Q.
apply H5.
Col.

assert(Par A B' P Q).
apply plg_par in H8; auto.
spliter.
apply bet_col in H0.

apply (par_col_par_2 _ B); auto.
apply plg_par in H4; auto.
spliter.
assumption.

assert(Col P' P Q /\ Col Q P Q).
apply(parallel_uniqueness A B' P Q P' Q Q ); Col.
apply plg_par in H8; auto.
spliter.
auto.
spliter.
clear H13.

assert(Parallelogram_strict A B' P' Q).
induction H8.
auto.
unfold Parallelogram_flat in H8.
spliter.
apply False_ind.
unfold Parallelogram_flat in *.
spliter.
apply bet_col in H0.
assert(Col B' P' Q).
ColR.

apply plgs_par_strict in H5.
spliter.
apply H5.
exists Q.
split.
ColR.
Col.

assert(Parallelogram_strict D C' P' Q).
apply (plgf_plgs_trans _ _ B' A).
intro.
subst C'.
apply plgf_sym in H1.
apply plgf_trivial_neq in H1.
tauto.
apply plgf_comm2.
apply plgf_sym.
apply H1.
apply plgs_comm2.
assumption.

assert(Bet Q P P').
apply(plgs_plgs_bet A B P Q B' P'); auto.
apply(plgs_plgs_bet Q P C D P' C').
apply plgs_sym.
auto.
auto.
apply plgs_comm2.
apply plgs_sym.
auto.
Qed.

Lemma plg_plg_bet :
 forall A B C D B' C',
 Parallelogram A B C D ->
 Bet A B B' ->
 Parallelogram A B' C' D ->
 Bet D C C'.
Proof.
intros.

induction(eq_dec_points A B).
subst B.
induction H.
apply False_ind.
apply H.
apply plgs_sym in H.
apply False_ind.
apply H.
Col.
apply plgf_trivial_neq in H.
spliter.
subst D.
Between.

induction (eq_dec_points B C).
subst C.
induction H.
apply False_ind.
apply plgs_sym in H.
apply H.
Col.
apply plgf_permut in H.
apply plgf_trivial_neq in H.
spliter.
subst D.
induction H1.
apply False_ind.
apply H.
Col.
apply plgf_permut in H.
apply plgf_sym in H.
apply plgf_trivial_neq in H.
spliter.
subst C'.
Between.

assert(A <> B').
intro.
subst B'.
apply between_identity in H0.
contradiction.

assert(B' <> C').
intro.
subst C'.
apply plg_permut in H1.
induction H1.
apply plgs_par_strict in H1.
spliter.
apply H1.
exists A.
split; Col.
apply plgf_trivial_neq in H1.
spliter.
subst D.
apply plg_permut in H.
induction H.
apply plgs_par_strict in H.
spliter.
apply H1.
exists A.
split; Col.
apply plgf_sym in H.
apply plgf_trivial_neq in H.
tauto.

assert(HH:=H).
assert(HH1:=H1).

apply plg_par in H; auto.
apply plg_par in H1; auto.
spliter.

assert(Par A B C' D).
apply (par_col_par_2 _ B'); auto.
apply bet_col in H0.
Col.

assert(Col C' C D /\ Col D C D).

apply(parallel_uniqueness A B C D C' D D); Col.
spliter.
clear H10.

induction HH; induction HH1.
apply (plgs_plgs_bet A B _ _ B').
apply H10.
apply H0.
auto.

apply False_ind.
unfold Parallelogram_flat in H11.
spliter.
apply plgs_par_strict in H10.
spliter.
apply bet_col in H0.
apply H10.
assert(Col A B C').
ColR.
exists C'.
split; Col.

apply False_ind.
unfold Parallelogram_flat in H10.
spliter.
apply plgs_par_strict in H11.
spliter.
apply bet_col in H0.
apply H11.
assert(Col A B' C).
ColR.
exists C.
split; Col.

apply (plgf_plgf_bet A B _ _ B').
apply H10.
apply H0.
auto.
Qed.


Lemma plgf_out_plgf :
 forall A B C D B' C',
 Parallelogram_flat A B C D ->
 Out A B B' ->
 Out D C C' ->
 Cong A B' D C' ->
 Parallelogram_flat A B' C' D.
Proof.
intros.
assert( A <> B /\ A <> B' /\ D <> C /\ D <> C').
unfold Out in *.
spliter.
repeat split; auto.
spliter.

assert(HH:=not_col_exists A B H3).
ex_and HH P.
assert(HH:=plg_existence A B P H3).
ex_and HH Q.
assert(Parallelogram_strict A B P Q).
induction H8.
assumption.
unfold Parallelogram_flat in H8.
spliter.
contradiction.

assert(Parallelogram_strict C D Q P).

apply(plgf_plgs_trans C D A B P Q).
auto.
apply plgf_sym.
assumption.
assumption.

assert(HH:=vector_construction A B' Q).
ex_and HH P'.
induction H11.

assert(B <> P).
intro.
subst P.
apply plgs_par_strict in H9.
spliter.
apply H9.
exists B.
split; Col.

assert(B' <> P').
intro.
subst P'.
induction H11.
apply plgs_par_strict in H11.
spliter.
apply H11.
exists B'.
split; Col.
unfold Parallelogram_flat in H11.
spliter.
apply cong_identity in H15.
subst Q.
apply H9.
Col.

assert(Col Q P P').
apply plg_par in H8; auto.
apply plg_par in H11; auto.
spliter.

assert(Par A B' P Q).
apply (par_col_par_2 _ B).
auto.
apply out_col.
apply H0.
assumption.

assert(Col P' P Q /\ Col Q P Q).
apply(parallel_uniqueness A B' P Q P' Q Q); Col.
spliter.
Col.


assert(Parallelogram_strict A B' P' Q).
induction H11.
assumption.
unfold Parallelogram_flat in H11.
spliter.
apply False_ind.

apply plgs_par_strict in H9.
spliter.
apply H9.
exists Q.
split.

apply out_col in H0.
ColR.
Col.

assert(P <> Q).
intro.
subst Q.
apply H9.
Col.

assert(P' <> Q).
intro.
subst Q.
apply H15.
Col.

assert(Parallelogram_strict D C' P' Q).
apply (plgs_out_plgs _ C P).
apply plgs_comm2.
apply H10.
auto.
repeat split; auto.

unfold Out in H0.
spliter.
induction H19.
left.

apply (plgs_plgs_bet A B P Q B' P' H9); auto.
right.

apply(plgs_plgs_bet A B' P' Q B P); auto.

apply plg_cong in H11.
spliter.
eCong.

assert(Parallelogram A B' C' D).
apply (plgs_pseudo_trans _ _ P' Q).
apply H15.
apply plgs_sym.
assumption.
induction H19.
apply False_ind.
apply plgs_par_strict in H19.
spliter.
unfold Parallelogram_flat in H.
spliter.
apply out_col in H0.
apply out_col in H1.

apply H19.
exists B.
split.

Col.
assert(Col B C D).
ColR.
ColR.
assumption.
spliter.
subst B'.
tauto.
Qed.




Lemma plg_out_plg : 
 forall A B C D B' C',
 Parallelogram A B C D ->
 Out A B B' ->
 Out D C C' ->
 Cong A B' D C' ->
 Parallelogram A B' C' D.
Proof.
intros.
induction H.
left.
apply (plgs_out_plgs _ B C).
apply H.
auto.
auto.
auto.
right.
apply (plgf_out_plgf _ B C).
apply H.
auto.
auto.
auto.
Qed.


Lemma same_dir_sym : forall A B C D, Same_dir A B C D -> Same_dir C D A B.
intros.

induction (eq_dec_points A B).
subst B.
apply same_dir_null in H.
subst D.
left.
tauto.

unfold Same_dir in *.
induction H.
left.
tauto.

ex_and H D'.
right.
assert(HH:=vector_construction C D A).
ex_and HH B'.
exists B'.
split.
unfold EqV in H1.
unfold EqV in H2.
unfold Out in *.
spliter.
induction H1; induction H2.


repeat split.
auto.
intro.
subst B'.
induction H2.
apply H2.
Col.
apply plgf_sym in H2.
apply plgf_trivial_neq in H2.
spliter.
auto.

induction H4.
right.
apply (plg_plg_bet C D _ _ D').
apply H2.
apply H4.
apply plg_sym.
apply plg_comm2.
assumption.

left.
apply (plg_plg_bet C D' _ _ D).
apply plg_sym.
apply plg_comm2.
apply H1.
apply H4.
assumption.

spliter.
subst D.
tauto.
spliter.
subst B.
tauto.
spliter.
subst D.
tauto.
assumption.
Qed.


Lemma same_dir_trans : forall A B C D E F, Same_dir A B C D -> Same_dir C D E F -> Same_dir A B E F.
intros.
unfold Same_dir in *.
induction H; induction H0; spliter.
left.
tauto.
ex_and H0 F'.
subst B.
subst D.
apply null_vector in H2.
subst F'.
unfold Out in H0.
tauto.
ex_and H D'.
subst D.
subst F.
unfold Out in H.
tauto.
ex_and H D'.
ex_and H0 F'.
right.


induction(eq_dec_points A B).
subst B.
apply null_vector in H1.
subst D'.
unfold Out in H.
tauto.

assert(HH:=vector_construction A B E).
ex_and HH F''.
exists F''.
split.

2: auto.
assert(C <> D /\ C <> D' /\ E <> F /\ E <> F').
unfold Out in *.
spliter.
repeat split;
auto.
spliter.

unfold EqV in *.
induction H1; induction H2; induction H4.
unfold Out in *.
spliter.
induction H10; induction H12.
repeat split.
auto.
intro.
subst F''.

induction H4.
apply H4.
Col.
apply plgf_sym in H4.
apply plgf_trivial_neq in H4.
tauto.

left.
assert(Bet E F' F'').

apply (plg_plg_bet C D _ _ D').
apply H2.
apply H12.

assert(Parallelogram C D' F'' E \/ C = D' /\ B = A /\ E = F'' /\ C = E).

apply(plg_pseudo_trans C D' B A E F'').
apply plg_sym.
apply plg_comm2.
auto.
apply plg_comm2.
auto.
induction H13.
2:tauto.
assumption.
apply (between_exchange4 _ _ F').
apply H10.
auto.

repeat split.
auto.
intro.
subst F''.
induction H4.
apply H4.
Col.
apply plgf_sym in H4.
apply plgf_trivial_neq in H4.
tauto.

assert(Bet E F'' F').
apply (plg_plg_bet C D' _ _ D).
3: apply H2.
2:apply H12.

assert(Parallelogram C D' F'' E \/ C = D' /\ B = A /\ E = F'' /\ C = E).
apply plg_pseudo_trans.
apply plg_sym.
apply plg_comm2.
auto.
apply plg_comm2.
auto.

induction H13.
assumption.
tauto.
apply (l5_3 _ _ _ F').
apply H10.
assumption.

repeat split.
auto.
intro.
subst F''.
induction H4.
apply H4.
Col.
apply plgf_sym in H4.
apply plgf_trivial_neq in H4.
tauto.

assert(Bet E F' F'').
apply (plg_plg_bet C D _ _ D').
apply H2.
apply H12.
assert(Parallelogram C D' F'' E \/ C = D' /\ B = A /\ E = F'' /\ C = E).
apply plg_pseudo_trans.
apply plg_sym.
apply plg_comm2.
auto.
apply plg_comm2.
auto.

induction H13.
assumption.
tauto.
apply (l5_1 _ F').
apply H8.
auto.
auto.

repeat split.
auto.
intro.
subst F''.
induction H4.
apply H4.
Col.
apply plgf_sym in H4.
apply plgf_trivial_neq in H4.
tauto.

assert(Bet E F'' F').
apply (plg_plg_bet C D' _ _ D).
3: apply H2.
2: apply H12.

assert(Parallelogram C D' F'' E \/ C = D' /\ B = A /\ E = F'' /\ C = E).
apply plg_pseudo_trans.
apply plg_sym.
apply plg_comm2.
auto.
apply plg_comm2.
auto.

induction H13.
auto.
tauto.
right.
apply (between_exchange4 _ _ F').
apply H13.
auto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
Qed.

Lemma same_dir_comm : forall A B C D, Same_dir A B C D -> Same_dir B A D C.
intros.

unfold Same_dir in *.
induction H.
left.
auto.
spliter.
split; auto.

right.
ex_and H D'.
assert(A <> B).
intro.
subst B.
apply null_vector in H0.
unfold Out in H.
spliter.
auto.

assert(HH:=vector_construction B A D).
ex_and HH C'.
exists C'.
split.
2: auto.

unfold Out in *.
spliter.

unfold EqV in *.

induction H4.
repeat split.
auto.
intro.
subst C'.
apply eqv_sym in H2.
apply null_vector in H2.
subst B.
tauto.
left.

induction H0; induction H2;try tauto.

assert(Parallelogram C D' D C' \/ C = D' /\ B = A /\ C' = D /\ C = C').

apply(plg_pseudo_trans C D' B A C' D).
apply plg_sym.
apply plg_comm2.
assumption.
assumption.
induction H5.

assert(Parallelogram_flat C D' D C').
induction H5.
apply False_ind.
apply plgs_par_strict in H5.
spliter.
apply H5.
exists D.
apply bet_col in H4.
split; Col.
assumption.

unfold Parallelogram_flat in H6.
spliter.

apply (col_cong2_bet1 D').
2:Between.
Col.
Cong.
Cong.
spliter.
subst B.
tauto.
spliter.
subst B.
tauto.

repeat split.
auto.
intro.
subst C'.
induction H2.
induction H2.
apply H2.
Col.
apply plgf_sym in H2.
apply plgf_trivial_neq in H2.
spliter.
auto.
spliter.
auto.


induction H0; induction H2;try tauto.

induction(eq_dec_points C C').
subst C'.
left.
Between.

assert(Parallelogram C D' D C' \/ C = D' /\ B = A /\ C' = D /\ C = C').

apply(plg_pseudo_trans C D' B A C' D).
apply plg_sym.
apply plg_comm2.
assumption.
assumption.
induction H6.

assert(Parallelogram_flat C D' D C').
induction H6.
apply False_ind.
apply plgs_par_strict in H6.
spliter.
apply H6.
exists D.
apply bet_col in H4.
split; Col.
assumption.

right.

assert(HH:= H7).
unfold Parallelogram_flat in H7.
spliter.

apply plgf_bet in HH.
induction HH.
spliter.

apply False_ind.

apply H3.
apply (between_equality _ _ D).
apply between_symmetry.
apply H13.
assumption.
induction H12.
spliter.

assert(D = D').
apply (between_equality _ _ C).
Between.
Between.
subst D'.

apply cong_identity in H10.
contradiction.

induction H12.
spliter.
eBetween.

spliter.
eBetween.
spliter.
subst B.
tauto.
spliter.
subst B.
tauto.
Qed.

Lemma bet_same_dir1 : forall A B C, A <> B -> B <> C -> Bet A B C -> Same_dir A B A C.
intros.
unfold Same_dir.
right.
exists B.
split.
unfold Out.
repeat split.
intro.
subst C.
apply between_identity in H1.
tauto.
auto.
right.
assumption.
apply eqv_refl.
Qed.

Lemma bet_same_dir2 : forall A B C, A <> B -> B <> C -> Bet A B C -> Same_dir A B B C.
intros.
unfold Same_dir.
right.
assert(HH:=vector_construction A B B).
ex_and HH C'.
exists C'.
split.
2: auto.
unfold EqV in H2.
induction H2.
2:tauto.

induction H2.
apply plgs_par_strict in H2.
spliter.
apply False_ind.
apply H3.
exists B.
split; Col.
assert(HH:= H2).
unfold Parallelogram_flat in HH.
apply plgf_bet in H2.
spliter.

unfold Out.
repeat split.
auto.
intro.
subst C'.
apply cong_identity in H5.
contradiction.

induction H2.

assert(Bet B A B).
spliter.
apply (outer_transitivity_between2 _ C').
Between.
auto.
induction H7.
auto.
tauto.
apply between_identity in H8.
subst B.
tauto.
induction H2.

assert(Bet B A B).
spliter.
apply (outer_transitivity_between _ _ C').
apply H2.
auto.
induction H7.
auto.
tauto.
apply between_identity in H8.
subst B.
tauto.

induction H2.

assert( A = C' \/ Midpoint B A C').
apply l7_20.
Col.
Cong.
induction H8.
induction H7.
tauto.
tauto.
unfold Midpoint in H8.
spliter.
apply (l5_2 A); auto.

assert( A = C' \/ Midpoint B A C').
apply l7_20.
Col.
Cong.
induction H8.
induction H7.
tauto.
tauto.
unfold Midpoint in H8.
spliter.
apply (l5_2 A); auto.
Qed.

Lemma plg_opp_dir : forall A B C D, Parallelogram A B C D -> Same_dir A B D C.
intros.

induction(eq_dec_points A B).
subst B.
induction H.
apply False_ind.
apply plgs_sym in H.
apply H.
Col.
apply plgf_trivial_neq in H.
spliter.
subst D.
left.
tauto.

unfold Same_dir.
right.
exists C.
split.
apply out_trivial.
intro.
subst D.
induction H.
apply H.
Col.
apply plgf_sym in H.
apply plgf_trivial_neq in H.
tauto.
unfold EqV.
left.
assumption.
Qed.

Lemma same_dir_dec : forall A B C D,
  Same_dir A B C D \/ ~ Same_dir A B C D.
Proof.
intros.
unfold Same_dir.
unfold EqV.
elim (eq_dec_points A B); intro HAB;
elim (eq_dec_points C D); intro HCD; try tauto.

  right; intro HFalse.
  elim HFalse; clear HFalse; intro HFalse.

    spliter; intuition.

    destruct HFalse as [E [HFalse HElim]].
    elim HElim; clear HElim; intro HElim.

      subst.
      apply plg_cong in HElim.
      destruct HElim as [HCong1 HCong2].
      treat_equalities.
      apply out_diff2 in HFalse; intuition.

      destruct HElim as [Hclear HCE]; clear Hclear; subst.
      apply out_diff2 in HFalse; intuition.

  right; intro HFalse.

  elim HFalse; clear HFalse; intro HFalse.

    spliter; intuition.

    destruct HFalse as [E [HFalse Hclear]]; clear Hclear.
    subst.
    apply out_diff1 in HFalse; intuition.

  assert (H := plg_existence B A C).
  assert (HPar : B <> A) by finish.
  apply H in HPar; clear H.
  destruct HPar as [E HPar].
  elim (out_dec C D E); intro Hout.

    left.
    right.
    exists E.
    split; try assumption.
    left.
    apply plg_comm2 in HPar.
    assumption.

    right.
    intro H.
    elim H; clear H; intro H.

      spliter; subst; intuition.

      destruct H as [F [Hout' HElim]].
      elim HElim; clear HElim; intro HElim.

        apply plg_comm2 in HElim.
        assert (HEF := plg_uniqueness B A C E F HPar HElim).
        subst; intuition.

        spliter; intuition.
Qed.

Lemma same_or_opp_dir : forall A B C D, Par A B C D -> Same_dir A B C D \/ Opp_dir A B C D.
intros.
induction (same_dir_dec A B C D).
left.
assumption.
right.
unfold Opp_dir.

unfold Same_dir.
right.
assert(HH:= vector_construction A B D).
ex_and HH C'.
exists C'.
split.
2:auto.
unfold EqV in H1.

induction (eq_dec_points B C').
subst C'.
induction H1.

induction H1.
apply False_ind.
apply plgs_permut in H1.
apply plgs_sym in H1.
apply H1.
Col.
apply plgf_permut in H1.
apply plgf_trivial_neq in H1.
spliter.
subst D.
induction H.
apply False_ind.
apply H.
exists A.
split; Col.
spliter.
induction H4.
unfold Out.
repeat split; auto.
left.
Between.
induction H4.
unfold Out.
repeat split; auto.
apply False_ind.
apply H0.
apply same_dir_sym.
apply bet_same_dir2; auto.
unfold Out.
repeat split.
auto.
auto.
right.
assumption.
spliter.
subst A.
subst D.
apply par_distinct in H.
tauto.

induction H1.

assert(Col C' C D /\ Col D C D).
apply plg_par in H1.
spliter.

apply(parallel_uniqueness A B C D C' D D); Col.
apply par_distinct in H.
tauto.
assumption.
spliter.
clear H4.

unfold Out.
repeat split.
apply par_distinct in H.
tauto.
intro.
subst C'.
induction H1.
apply H1.
Col.
apply plgf_sym in H1.
apply plgf_trivial_neq in H1.
spliter.
apply par_distinct in H.
tauto.

induction H3.
left.
Between.
induction H3.
apply False_ind.

assert(Same_dir A B D C').
apply plg_opp_dir.
assumption.

assert(Same_dir C D D C').
apply bet_same_dir2.
apply par_distinct in H.
spliter.
auto.
intro.
subst C'.
induction H1.
apply H1.
Col.
apply plgf_sym in H1.
apply plgf_trivial_neq in H1.
spliter.
apply par_distinct in H.
tauto.
assumption.
apply False_ind.
apply H0.
apply (same_dir_trans _ _ D C').
apply H4.
apply same_dir_sym.
auto.
right.
assumption.
apply par_distinct in H.
tauto.
Qed.

Lemma same_dir_id : forall A B, Same_dir A B B A -> A = B.
intros.
unfold Same_dir in H.
induction H.
tauto.
ex_and H C.
apply eqv_mid in H0.
unfold Midpoint in H0.
unfold Out in H.
spliter.
induction H3.
apply (between_equality _ _ C).
apply H0.
assumption.
apply False_ind.
apply H2.
apply (between_equality _ _ A).
Between.
assumption.
Qed.

Lemma opp_dir_id : forall A B, Opp_dir A B A B -> A = B.
intros.
unfold Opp_dir in H.
apply same_dir_id in H.
auto.
Qed.


Lemma same_dir_to_null : forall A B C D, Same_dir A B C D -> Same_dir A B D C -> A = B /\ C = D.
intros.

assert(Same_dir C D D C).
apply (same_dir_trans _ _ A B).
apply same_dir_sym.
apply H.
assumption.
apply same_dir_id in H1.
subst D.
apply same_dir_sym in H.
apply same_dir_null in H.
subst B.
tauto.
Qed.

Lemma opp_dir_to_null : forall A B C D, Opp_dir A B C D -> Opp_dir A B D C -> A = B /\ C = D.
unfold Opp_dir.
intros.
apply same_dir_to_null; auto.
Qed.

Lemma same_not_opp_dir : forall A B C D, A <> B -> Same_dir A B C D -> ~ Opp_dir A B C D.
intros.
intro.
apply same_dir_to_null in H0.
tauto.
assumption.
Qed.

Lemma opp_not_same_dir : forall A B C D, A <> B -> Opp_dir A B C D -> ~ Same_dir A B C D.
unfold Opp_dir.
intros.
intro.
apply same_dir_to_null in H0.
tauto.
assumption.
Qed.

Lemma vector_same_dir_cong : forall A B C D, A <> B -> C <> D -> exists X, exists Y, Same_dir A B X Y /\ Cong X Y C D.
intros.
exists A.
assert(HH:=segment_construction_3 A B C D H H0).
ex_and HH P.
exists P.
split; auto.
unfold Same_dir.
right.
exists B.
split.
apply l6_6.
assumption.
apply eqv_refl.
Qed.

End Vectors.
