Require Export GeoCoq.Tarski_dev.Ch12_parallel_inter_dec.

Section Orientation.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Definition proj := fun  T A B P => A <> B /\ (~Col A B T /\ Perp A B T P /\ Col A B P \/ Col A B T /\ P = T).

Lemma proj_exists : forall A B T, A <> B -> exists P, proj T A B P.
intros.
induction(col_dec A B T).
exists T.
unfold proj.
split.
assumption.
right.
split;
auto.
assert(HH:=l8_18_existence A B T H0).
ex_and HH P.
exists P.
unfold proj.
split.
assumption.
left.
repeat split;auto.
Qed.

Lemma proj_per : forall A B T P, A <> B -> proj T A B P -> Per T P A /\ Per T P B /\ Col A B P.
intros.
unfold proj in H0.
spliter.
induction H1.
spliter.
repeat split.

induction (eq_dec_points A P).
treat_equalities.
apply l8_5.

apply perp_in_per.
eauto with perp.

induction (eq_dec_points B P).
treat_equalities.

apply l8_5.

apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
apply perp_sym.
eapply perp_col.
assumption.

eauto with perp.
Col.
assumption.
spliter.
subst T.
repeat split.
Perp.
Perp.
assumption.
Qed.

Lemma proj_uniqueness : forall A B T P P', proj T A B P -> proj T A B P' -> P = P'.
intros.
unfold proj in *.
spliter.
induction H1; induction H2; spliter; assert(Col A P P').
ColR.
eapply (l8_18_uniqueness A B T P P');
auto.
subst T.
contradiction.
contradiction.
subst P'.
ColR.
subst P'.
contradiction.
subst T.
subst P'.
Col.
subst T.
subst P'.
reflexivity.
Qed.


Lemma proj_col : forall T P A B, proj T A B P -> Col P A B.
intros.
unfold proj in H.
spliter.
induction H0; spliter.
Col.
subst T.
Col.
Qed.

Lemma proj_col_proj : forall A B C T P, proj T A B P -> A <> C -> Col A B C -> proj T A C P.
intros.
unfold proj in *.
spliter.
induction H2; repeat split; auto; spliter.
left.
repeat split.
intro.
apply H2.
ColR.

eapply (perp_col _ B); auto.
ColR.
subst T.
right.
split; auto.
ColR.
Qed.

Lemma per_proj : forall A B T P, A <> B -> Per T P A -> Per T P B -> Col A B P -> proj T A B P.
intros.
unfold proj.
split; auto.
induction (col_dec A B T).
right.
split; auto.

assert(Col T P A).
ColR.
assert(Col T P B).
ColR.

induction(eq_dec_points A P).
subst P.
assert(T=A \/ B=A).
apply l8_9; auto.
induction H6.
auto.
subst B.
tauto.

assert(T=P \/ A=P).
apply l8_9; auto.
induction H7.
auto.
subst P.
tauto.

left.

induction (eq_dec_points A P).

subst P.

repeat split; auto.

apply per_perp_in in H1.
apply perp_in_comm in H1.
apply perp_in_perp_bis in H1.
induction H1.
Perp.

apply perp_not_eq_1 in H1.
tauto.
intro.
subst T.
contradiction.
assumption.

repeat split; auto.
apply per_perp_in in H0.
apply perp_in_comm in H0.
apply perp_in_perp_bis in H0.
induction H0.
eapply perp_col.
assumption.
eauto with perp.

Col.
apply perp_not_eq_1 in H0.
tauto.
intro.
subst T.
contradiction.
auto.
Qed.


Definition eqo := fun A B P A1 B1 P1 => ~Col A B P /\ ~Col A1 B1 P1 /\
                      forall C C1 B2 M B' C' K,
                             Perp A B C A  -> Per P C A -> Perp A1 B1 C1 A1 -> Per P1 C1 A1 ->
                             Out A1 B1 B2 -> Cong A B A1 B2 ->
                             Midpoint M A A1 -> Midpoint M B2 B' -> Midpoint M C1 C' -> Midpoint K B B' ->
                             Bet C A C' \/ OS A K C C'.



Definition eq_o := fun A B P A1 B1 P1 => ~Col A B P /\ ~Col A1 B1 P1 /\
                      forall C C1 B2 M B' C' K,
                             Perp A B C A -> proj P A C C -> Perp A1 B1 C1 A1 -> proj P1 A1 C1 C1 ->
                             Out A1 B1 B2 -> Cong A B A1 B2 ->
                             Midpoint M A A1 -> Midpoint M B2 B' -> Midpoint M C1 C' -> Midpoint K B B' ->
                             Bet C A C' \/ OS A K C C'.

Lemma eqo_eq_o : forall A B P A1 B1 P1, eqo A B P A1 B1 P1 -> eq_o A B P A1 B1 P1.
intros.
unfold eqo in H.
spliter.
unfold eq_o.
repeat split ; auto.
intros.
assert(HH:= H1 C C1 B2 M B' C' K).
apply HH; auto.
unfold proj in *.
spliter.
induction H13; induction H12.
spliter.
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
apply perp_sym.
Perp.
spliter.
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
apply perp_sym.
Perp.
spliter.
subst P.
apply l8_2.
apply l8_5.
spliter.
subst P.
apply l8_2.
apply l8_5.
unfold proj in *.
spliter.
induction H13; induction H12.
spliter.
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
apply perp_sym.
Perp.
spliter.
subst P1.
apply l8_2.
apply l8_5.
spliter.
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
apply perp_sym.
Perp.
spliter.
subst P1.
apply l8_2.
apply l8_5.
Qed.




Lemma eq_o_eqo : forall A B P A1 B1 P1, eq_o A B P A1 B1 P1 -> eqo A B P A1 B1 P1.
intros.
unfold eq_o in H.
spliter.
unfold eqo.
repeat split; auto.
intros.
eapply H1.
apply H2.
apply per_proj.
apply perp_not_eq_2 in H2.
auto.
assumption.
apply l8_5.
Col.
apply H4.
apply per_proj.
apply perp_not_eq_2 in H4.
auto.
assumption.
apply l8_5.
Col.
apply H6.
assumption.
apply H8.
apply H9.
assumption.
assumption.
Qed.



Lemma eq_o_one_side : forall A B X Y, eq_o A B X A B Y -> OS A B X Y.
intros.
unfold eq_o in H.
spliter.
assert(A <> B).
intro.
subst B.
apply H.
Col.

assert(HH:=ex_per_cong B A A X A B).
assert(exists P : Tpoint, Per P A B /\ Cong P A A B /\ OS B A P X).
apply HH;
auto.
Col.
intro.
apply H.
Col.
clear HH.
ex_and H3 T.

assert(A <> T).
intro.
subst T.
apply cong_symmetry in H4.
apply cong_identity in H4.
contradiction.

assert(Perp T A A B).
apply per_perp_in in H3.
apply perp_in_perp_bis in H3.
induction H3.
apply perp_not_eq_1 in H3.
tauto.
assumption.
auto.
assumption.

assert(HH:=proj_exists A T X H6).
ex_and HH PX.
assert(HH:=proj_exists A T Y H6).
ex_and HH PY.
prolong B A B' B A.
prolong PY A C' PY A.
assert(Col PX A T).
eapply proj_col.
apply H8.
assert(Col PY A T).
eapply proj_col.
apply H9.

assert(PX <> A).
intro.
subst PX.
apply proj_per in H8.
spliter.
apply H.
apply col_permutation_2.
eapply per2__col.
apply l8_2.
apply H3.
assumption.
assumption.
assumption.

assert(PY <> A).
intro.
subst PY.
apply proj_per in H9.
spliter.
apply H0.
apply col_permutation_2.
eapply per2__col.
apply l8_2.
apply H3.
assumption.
assumption.
assumption.

assert(~Col T A B).
apply per_not_col in H3.
assumption.
auto.
assumption.

assert(Col A PX PY).
ColR.

assert(~Col PX A B).
intro.
apply H18.
ColR.

assert(~Col PY A B).
intro.
apply H18.
ColR.

assert(A <> C').
intro.
subst C'.
apply cong_symmetry in H13.
apply cong_identity in H13.
contradiction.

assert(TS A B PY C').
unfold TS.
repeat split; auto.
intro.
apply H21.
apply bet_col in H12.
ColR.
exists A.
split.
Col.
assumption.

assert(HH:= H1 PX PY B A B' C' A).

assert(Bet PX A C' \/ OS A A PX C').
apply HH;
clear HH; clear H1.

apply per_perp_in in H3.
apply perp_in_comm in H3.
apply perp_in_perp_bis in H3.
induction H3.
apply perp_comm.
apply perp_sym.
eapply perp_col.
auto.
apply H1.
Col.
apply perp_not_eq_1 in H1.
tauto.
auto.
assumption.

eapply proj_col_proj.
apply H8.
auto.
Col.

apply per_perp_in in H3.
apply perp_in_comm in H3.
apply perp_in_perp_bis in H3.
induction H3.
apply perp_comm.
apply perp_sym.
eapply perp_col.
auto.
apply H1.
Col.
apply perp_not_eq_1 in H1.
tauto.
auto.
assumption.

eapply proj_col_proj.
apply H9.
auto.
Col.

apply out_trivial.
auto.
apply cong_reflexivity.
apply l7_3_2.
unfold Midpoint.
apply cong_symmetry in H11.
split;auto.
unfold Midpoint.
apply cong_symmetry in H13.
split;auto.
unfold Midpoint.
apply cong_symmetry in H11.
split;auto.

clear H1 HH.

assert(TS A B PX C').
unfold TS.
repeat split; auto.
intro.
apply H21.
apply bet_col in H12.
ColR.
exists A.
induction H24.
split.
Col.
assumption.
unfold OS in H1.
ex_and H1 U.
unfold TS in H1.
spliter.
assert_diffs; tauto.

unfold proj in H8.
spliter.
induction H25.
spliter.

assert(Par A B X PX).
apply l12_9_2D with T A.
apply perp_sym.
apply H7.
apply perp_right_comm.
Perp.

assert(Par_strict A B X PX).
induction H28.
assumption.
spliter.
apply False_ind.
apply H.
ColR.

unfold proj in H9.
spliter.
induction H30.
spliter.

assert(Par A B Y PY).
apply l12_9_2D with T A.
apply perp_sym.
apply H7.
apply perp_right_comm.
Perp.

assert(Par_strict A B Y PY).
induction H33.
assumption.
spliter.
apply False_ind.
apply H0.
ColR.
apply l12_6 in H29.
apply l12_6 in H34.

assert(TS A B X C').
eapply l9_8_2.
apply H1.
apply one_side_symmetry.
assumption.

assert(TS A B Y C').
eapply l9_8_2.
apply H23.
apply one_side_symmetry.
assumption.
eapply l9_8_1.
apply H35.
assumption.
spliter.
subst Y.
apply l12_6 in H29.
eapply one_side_transitivity.
apply H29.
eapply l9_8_1.
apply H1.
assumption.
spliter.
subst X.
unfold proj in H9.
spliter.
induction H26.
spliter.

assert(Par A B Y PY).
apply l12_9_2D with T A.
apply perp_sym.
apply H7.
apply perp_right_comm.
Perp.

assert(Par_strict A B Y PY).
induction H29.
assumption.
spliter.
apply False_ind.
apply H0.
ColR.
apply l12_6 in H30.
eapply one_side_transitivity.
eapply l9_8_1.
apply H1.
apply H23.
apply one_side_symmetry.
assumption.
spliter.
subst Y.
eapply l9_8_1.
apply H1.
assumption.
Qed.


Lemma eqo_one_side : forall A B X Y, eqo A B X A B Y -> OS A B X Y.
intros.
apply eqo_eq_o in H.
apply eq_o_one_side.
assumption.
Qed.


Lemma eq_o_refl : forall A B P, ~Col A B P -> eq_o A B P A B P.
intros.
unfold eq_o.
repeat split; auto.
intros.
unfold Midpoint in H8.
apply l7_3 in H6.
subst M.
spliter.
assert(proj P A C C1).
eapply proj_col_proj.
apply H3.
apply perp_not_eq_2 in H0.
auto.
eapply perp2__col.
apply perp_comm.
apply perp_sym.
apply H2.
apply perp_comm.
Perp.
assert(C=C1).
eapply proj_uniqueness.
apply H1.
assumption.
subst C1.
left.
assumption.
Qed.

Lemma eqo_refl : forall A B P, ~Col A B P -> eqo A B P A B P.
intros.
apply eq_o_eqo.
apply eq_o_refl.
assumption.
Qed.

Lemma per_id : forall A B B' C, A <> B -> B <> C -> B' <> C -> Per A B C -> Per A B' C -> Col C B B' -> B = B'.
intros.
assert(~ Col A B C).
eapply per_not_col.
assumption.
assumption;
assert(Per B B' C).
eapply (l8_3 A); try auto.
Col.

assert(A <> B').
intro.
subst B'.
apply H5.
Col.

assert(Per A B B').
eapply (per_col _ _ C); auto.
Col.
assert(Per A B' B).
eapply (per_col _ _ C); auto.
Col.
eapply l8_7.
apply H7.
assumption.
Qed.


Lemma proj_one_side : forall A B A' B' P Q, A <> A' -> proj A P Q A' -> proj B P Q B' -> Col B A A' \/ OS A A' B B'.
intros.

induction (col_dec B A A').
left.
assumption.
induction(eq_dec_points B B').
subst B'.
right.
apply one_side_reflexivity.
assumption.

assert(Par A A' B B').
unfold proj in *.
spliter.
induction H5; induction H4;spliter.
eapply l12_9_2D.
apply perp_sym.
apply H8.
Perp.
subst B'.
tauto.
subst A'.
tauto.
subst B'.
tauto.
assert(Par_strict A A' B B').
induction H4.
assumption.
spliter.
apply False_ind.
apply H2.
ColR.
right.
eapply l12_6.
assumption.
Qed.


Lemma proj_eq_col : forall A B P Q C, proj A P Q C -> proj B P Q C -> Col A B C.
intros.
unfold proj in *.
spliter.
induction H2; induction H1; spliter.
apply col_permutation_1.
eapply perp2__col.
apply perp_sym.
apply perp_comm.
apply H5.
apply perp_sym.
Perp.
subst B.
Col.
subst C.
Col.
subst C.
Col.
Qed.

Lemma proj_par : forall A B A' B' P Q, A <> A' -> B <> B' -> proj A P Q A' -> proj B P Q B' -> Par A A' B B'.
intros.
eapply l12_9_2D.
unfold proj in *.
spliter.
induction H4; induction H3; spliter.
apply perp_sym.
apply H7.
Perp.
subst A'.
tauto.
subst B'.
tauto.
unfold proj in *.
spliter.
induction H4; induction H3; spliter.
apply perp_sym.
apply H5.
subst B'.
tauto.
subst A'.
tauto.
subst A'.
tauto.
Qed.

Lemma proj_not_col : forall A A' P Q, A <> A' -> proj A P Q A' -> ~Col P Q A.
intros.
unfold proj in H0.
spliter.
induction H1.
spliter.
assumption.
spliter.
subst A'.
tauto.
Qed.

Lemma proj_comm : forall A B P Q, proj A P Q B -> proj A Q P B.
intros.
unfold proj in *.
spliter.
induction H0; spliter; split; auto.
left.
repeat split.
intro.
apply H0.
Col.
Perp.
Col.
subst B.
right.
split; Col.
Qed.

Lemma proj_not_eq : forall A B A' B' P Q, A' <> B' -> proj A P Q A' -> proj B P Q B' -> A <> B.
intros.
intro.
apply H.
eapply proj_uniqueness.
apply H0.
subst B.
assumption.
Qed.

Lemma proj_not_eq_not_col : forall A B A' B' P Q, A' <> B' -> A <> A' -> proj A P Q A' -> proj B P Q B' -> ~Col A A' B'.
intros.
unfold proj in H1.
spliter.
induction H3; spliter.
assert(Col P Q B').
apply col_permutation_1.
eapply proj_col.
apply H2.

induction(eq_dec_points P A').
subst P.

assert(Perp A' B' A A').
eapply perp_col.
assumption.
apply perp_left_comm.
eapply perp_col.
2: apply perp_left_comm.
2: apply H4.
auto.
Col.
Col.
assert(~Col A' A B').
eapply perp_not_col.
apply perp_comm.
Perp.
intro.
apply H8.
Col.

assert(Perp A' B' A A').
eapply perp_col.
assumption.
apply perp_left_comm.
eapply perp_col.
2: apply H4.
assumption.
assumption.
ColR.
assert(~Col A' A B').
eapply perp_not_col.
apply perp_comm.
Perp.
intro.
apply H9.
Col.
subst A'.
tauto.
Qed.

Lemma proj_par_strict : forall A B A' B' P Q, A <> A' -> B <> B' -> A' <> B' -> proj A P Q A' -> proj B P Q B' -> Par_strict A A' B B'.

intros.
assert(Par A A' B B').
eapply (proj_par A B A' B' P Q); auto.
induction H4.
assumption.
spliter.
unfold Par_strict.
repeat split; auto; try apply all_coplanar.
intro.
ex_and H8 X.

assert(~Col P Q A).
eapply proj_not_col.
apply H.
assumption.

assert(~Col P Q B).
eapply proj_not_col.
apply H0.
assumption.

assert(A <> B).
eapply proj_not_eq.
apply H1.
apply H2.
assumption.

assert(Col A' P Q).
eapply proj_col.
apply H2.

assert(Col B' P Q).
eapply proj_col.
apply H3.

apply H1.
eapply (l6_21 P Q).
apply H11.
apply H0.
Col.
Col.
Col.
Col.
Qed.

Lemma col_proj_col : forall A B A' B' P Q, A <> A' -> Col A B A' -> proj A P Q A' -> proj B P Q B' -> Col A B B'.
intros.
induction(eq_dec_points A B).
subst B.
Col.
unfold proj in *.
spliter.
induction H4; induction H5; spliter.
apply col_permutation_2.
eapply perp2__col.
apply perp_sym.
apply H6.
apply perp_left_comm.
eapply perp_col.
assumption.
apply perp_sym.
apply H8.
Col.
subst A'.
tauto.
subst B'.
Col.
subst B'.
Col.
Qed.

Lemma col_proj_proj : forall A B A' P Q, A <> A' -> Col A B A' -> proj A P Q A' -> proj B P Q A'.
intros.

unfold proj in *.
spliter.
induction H2;
spliter; split;auto.
induction(col_dec P Q B).
right.
split.
assumption.

induction(eq_dec_points A' P).
subst P.
assert(Perp_at A' A' Q A A').
eapply perp_perp_in.
assumption.
eapply l8_14_2_1b.
apply H6.
Col.
Col.
assert(Perp P A' A A').
eapply perp_col.
auto.
apply H3.
assumption.

assert(Perp_at A' A' P A A').
eapply perp_perp_in.
Perp.

induction(eq_dec_points B P).
subst P.

assert(Perp B Q A B).
apply perp_sym.
eapply perp_col.
intro.
subst B.
apply H2.
Col.
apply perp_sym.
apply H3.
Col.
eapply l8_14_2_1b.
apply H8.
Col.
Col.

assert(Perp P B A B).
eapply perp_col.
auto.
apply perp_sym.
eapply perp_col.
intro.
subst B.
contradiction.
apply perp_sym.
apply H3.
Col.
Col.
eapply l8_14_2_1b.
apply H8.
ColR.
Col.
left.
repeat split; auto.
apply perp_sym.
apply perp_left_comm.
eapply perp_col.
intro.
subst A'.
contradiction.
apply perp_sym.
apply perp_right_comm.
apply H3.
Col.
subst A'.
tauto.
Qed.



Lemma proj_id : forall A B A' B' P Q, A <> A' -> Col A B A' -> proj A P Q A' -> proj B P Q B' -> A'= B'.
intros.

assert(proj B P Q A').
eapply col_proj_proj.
apply H.
assumption.
assumption.
eapply proj_uniqueness.
apply H3.
assumption.
Qed.

Lemma proj_diff : forall A P Q A' , proj A P Q A' -> P <> Q.
intros.
unfold proj in H.
spliter.
assumption.
Qed.


Lemma proj3_col : forall A B C A' B' C' P Q , proj A P Q A' -> proj B P Q B' -> proj C P Q C' -> Col A' B' C'.
intros.
unfold proj in *.
spliter.

induction H4; induction H3; induction H2; spliter.
eapply (col3 P Q); Col.
subst C'.
eapply (col3 P Q); Col.
subst B'.
eapply (col3 P Q); Col.
subst C'.
subst B'.
eapply (col3 P Q); Col.
subst A'.
eapply (col3 P Q); Col.
subst C'.
subst A'.
eapply (col3 P Q); Col.
subst A'.
subst B'.
eapply (col3 P Q); Col.
subst A'.
subst B'.
subst C'.
eapply (col3 P Q); Col.
Qed.

Lemma proj3_id : forall A B C C' P Q, A <> B -> Col A B C -> proj A P Q A -> proj B P Q B -> proj C P Q C' -> C = C'.
intros.
assert(Col A B C').
eapply (proj3_col A B C A B C' P Q); auto.

assert(HH1:= H1).
assert(HH2:=H2).
assert(HH3:=H3).

unfold proj in HH1.
unfold proj in HH2.
unfold proj in HH3.
spliter.
induction H10; induction H8; induction H6; spliter.
apply perp_not_eq_2 in H15.
tauto.
apply perp_not_eq_2 in H14.
tauto.
apply perp_not_eq_2 in H14.
tauto.
apply perp_not_eq_2 in H13.
tauto.
apply perp_not_eq_2 in H13.
tauto.
apply perp_not_eq_2 in H12.
tauto.
assert(Col P A B).
ColR.
assert(Col Q A B).
ColR.


assert(Col P Q C).
eapply (col3 A B); Col;


eapply (l8_14_2_1b_bis _ _ _ _ C') in H7.
contradiction.
subst C.
reflexivity.
Qed.

Lemma proj_inv_exists : forall P Q A', P <> Q -> Col P Q A'  -> exists A, A <> A' /\ proj A P Q A'.
intros.
assert(HH0:= not_col_exists P Q H).
ex_and HH0 X.

induction(eq_dec_points A' P).
subst P.

assert(Q <> A').
intro.
apply H.
auto.
apply col_permutation_1 in H0.
assert(~Col Q A' X).
intro.
apply H1.
Col.
assert(HH:= ex_per_cong Q A' A' X A' Q H2 H H0 H3).
ex_and HH A.
exists A.
split.
intro.
subst A'.
apply cong_symmetry in H5.
apply cong_identity in H5.
contradiction.
eapply per_proj; auto.
apply l8_5.
Col.
assert(HH:= ex_per_cong P Q A' X P Q H H H0 H1).
ex_and HH A.
exists A.
split.
intro.
subst A'.
apply cong_symmetry in H4.
apply cong_identity in H4.
contradiction.
apply per_proj; auto.
eapply per_col.
2: apply H3.
assumption.
Col.
Qed.

Lemma proj_perp_id : forall A B C A' B' P Q, A <> C -> Col A B C -> 
                                                         proj A P Q A' -> proj B P Q B' -> proj C P Q A' ->
                                                         A' = B'.
intros.

induction(eq_dec_points A A').
subst A'.

eapply proj_id.
4:apply H2.
3: apply H3.
auto.
Col.

assert(Col A C A').
eapply proj_eq_col.
apply H1.
assumption.
assert(Col A B A').
ColR.

eapply proj_id.
apply H4.
apply H6.
apply H1.
assumption.
Qed.

Lemma proj_diff_not_col : forall A B A' B' P Q, A <> A' -> proj A P Q A' -> proj B P Q B' ->  (A' <> B' <-> ~Col A B A').
intros.
split.
intro.

intro.
assert(proj B P Q A').
eapply (col_proj_proj A); auto.
apply H2.
eapply proj_uniqueness.
apply H4.
assumption.
intro.
intro.
subst B'.
apply H2.
eapply (proj_eq_col _ _ P Q); auto.
Qed.

Lemma proj_diff_not_col_inv : forall A B A' B' P Q, A <> A' -> proj A P Q A' -> proj B P Q B' ->  (A' = B' <-> Col A B A').
intros.
split.
intro.
subst B'.
eapply (proj_eq_col A B P Q A'); auto.
intro.
eapply (proj_id A B A' B' P Q); auto.
Qed.

Lemma proj_preserves_bet1 : forall A B C B' C' P Q, Bet A B C -> 
                                                         proj A P Q A -> proj B P Q B' -> proj C P Q C' ->
                                                         Bet A B' C'.
intros.
induction(eq_dec_points A B).
subst B.
assert(A = B').
eapply proj_uniqueness.
apply H0.
assumption.
subst B'.
apply between_trivial2.
induction(eq_dec_points B C).
subst C.
assert(B' = C').
eapply proj_uniqueness.
apply H1.
assumption.
subst C'.
apply between_trivial.
assert(A <> C).
intro.
subst C.
apply between_identity in H.
contradiction.

assert(P <> Q).
eapply proj_diff.
apply H0.
assert(Col A P Q).
eapply proj_col.
apply H0.
assert(Col B' P Q).
eapply proj_col.
apply H1.
assert(Col C' P Q).
eapply proj_col.
apply H2.

assert(Col A B C).
eapply bet_col.
assumption.

induction(eq_dec_points B B').
subst B'.

assert(C = C').

apply (proj3_id A B C C' P Q); Col.
subst C'.
assumption.

induction (eq_dec_points A C').
subst C'.

assert(Col P A B').
ColR.
assert(proj B P Q A).
eapply col_proj_proj.
3: apply H2.
auto.
Col.
assert(A = B').
eapply proj_uniqueness.
apply H13.
assumption.
subst B'.
apply l7_3_2.

induction(eq_dec_points B' C').
subst C'.
apply between_trivial.

assert(HH:= proj_not_eq_not_col B C B' C' P Q H13 H11 H1 H2).

assert(A <> B').
intro.
subst B'.

assert(Col B C C').
eapply col_proj_col.
4:apply H2.
3: apply H1.
auto.
Col.
apply HH.
ColR.

assert(HH1:= proj_one_side B C B' C' P Q H11 H1 H2).

assert(Col A B' C').
eapply proj3_col.
apply H0.
apply H1.
apply H2.
induction HH1.

apply False_ind.
apply HH.
assert(Col A B B').
ColR.
ColR.

assert(TS B B' A C).
unfold TS.
repeat split.
assert(~Col B B' A).
eapply proj_not_eq_not_col; auto.
apply H1.
apply H0.
intro.
apply H17.
Col.
intro.
apply HH.
apply col_permutation_2.
eapply (col_transitivity_1 _ A).
auto.
Col.
ColR.
exists B.
split; Col.

assert(TS B B' A C').
apply l9_2.
eapply l9_8_2.
apply l9_2.
apply H17.
assumption.
unfold TS in H18.
spliter.
ex_and H20 BB.

assert(BB= B').
eapply l6_21.
apply not_col_permutation_1.
apply H19.
4: apply col_permutation_2.
4: apply bet_col.
4: apply H21.
auto.
Col.
Col.
Col.
subst BB.
assumption.
Qed.

Lemma proj_preserves_bet : forall A B C A' B' C' P Q, Bet A B C -> 
                                                         proj A P Q A' -> proj B P Q B' -> proj C P Q C' ->
                                                         Bet A' B' C'.
intros.


induction(eq_dec_points A B).
subst B.
assert(A' = B').
eapply proj_uniqueness.
apply H0.
assumption.
subst B'.
apply between_trivial2.
induction(eq_dec_points B C).
subst C.
assert(B' = C').
eapply proj_uniqueness.
apply H1.
assumption.
subst C'.
apply between_trivial.
assert(A <> C).
intro.
subst C.
apply between_identity in H.
contradiction.

induction (eq_dec_points A' C').
subst C'.

assert(A' = B').
eapply proj_perp_id.
4: apply H1.
3: apply H0.
3: apply H2.
assumption.
apply bet_col.
assumption.
subst B'.
apply l7_3_2.

assert(P <> Q).
eapply proj_diff.
apply H0.
assert(Col A' P Q).
eapply proj_col.
apply H0.
assert(Col B' P Q).
eapply proj_col.
apply H1.
assert(Col C' P Q).
eapply proj_col.
apply H2.

assert(Col A B C).
eapply bet_col.
assumption.

induction (eq_dec_points A A').
subst A'.
eapply (proj_preserves_bet1 A B C _ _ P Q); assumption.

assert(~Col A P Q).
intro.

apply proj_not_col in H0.
apply H0.
Col.
assumption.

induction (eq_dec_points B B').
subst B.

assert(C <> C').
intro.
subst C'.
apply H13.
assert(Col B' C P).
ColR.
assert(Col B' C Q).
ColR.
eapply (col3 B' C); Col.
apply col_permutation_1 in H9.

assert(~Col C P Q).
intro.
apply proj_not_col in H2.
apply H2.
Col.
assumption.

assert(HH:= proj_inv_exists P Q B' H7 H9).
ex_and HH B.

assert(HH:=proj_diff_not_col_inv B A B' A' P Q H16 H17 H0).
destruct HH.

assert(HH:=proj_diff_not_col_inv B C B' C' P Q H16 H17 H2).
destruct HH.

assert(HH:= proj_one_side B A B' A' P Q H16 H17 H0).
induction HH.
assert(B' = A').
apply H19.
Col.
subst B'.
apply between_trivial2.

assert(HH:= proj_one_side B C B' C' P Q H16 H17 H2).
induction HH.

assert(B' = C').
apply H21.
Col.
subst B'.
apply between_trivial.

(*********************************************)


assert(HH:=proj_diff_not_col_inv B A B' A' P Q H16 H17 H0).
destruct HH.

assert(HH:=proj_diff_not_col_inv B C B' C' P Q H16 H17 H2).
destruct HH.

assert(TS B B' A C).
unfold TS.
repeat split.

intro.
assert(B' = A').
apply H25.
Col.
subst B'.

assert(Col A' B C).
ColR.
assert(A' = C').
apply H27.
Col.
contradiction.

intro.
assert(B' = C').
apply H27.
Col.
subst B'.

assert(Col C' A C).
ColR.
assert(C' = A').
apply H25.
ColR.
subst C'.
tauto.

exists B'.
split; Col.


assert(TS B B' A' C).
eapply l9_8_2.
apply H28.
assumption.
assert(TS B B' C' A').
eapply l9_8_2.
apply l9_2.
apply H29.
assumption.
unfold TS in H30.
spliter.
ex_and H32 BB.

assert(BB= B').
eapply l6_21.
apply not_col_permutation_1.
apply H31.
4: apply col_permutation_2.
4: apply bet_col.
4: apply H33.
assumption.
Col.
Col.
eapply (proj3_col A C B A' C' B' P Q); auto.
subst BB.
Between.

induction(eq_dec_points C C').
subst C'.

apply between_symmetry.
eapply (proj_preserves_bet1 C B A _ _ P Q); try assumption.
Between.

assert(HH:=proj_diff_not_col_inv B A B' A' P Q H14 H1 H0).
destruct HH.

assert(HH:=proj_diff_not_col_inv B C B' C' P Q H14 H1 H2).
destruct HH.

assert(HH:= proj_one_side B A B' A' P Q H14 H1 H0).
induction HH.
assert(B' = A').
apply H17.
Col.
subst B'.
apply between_trivial2.

assert(HH:= proj_one_side B C B' C' P Q H14 H1 H2).
induction HH.

assert(B' = C').
apply H19.
Col.
subst B'.
apply between_trivial.

assert(HH:=proj_diff_not_col_inv B A B' A' P Q H14 H1 H0).
destruct HH.

assert(HH:=proj_diff_not_col_inv B C B' C' P Q H14 H1 H2).
destruct HH.

assert(TS B B' A C).
unfold TS.
repeat split.

intro.
assert(B' = A').
apply H23.
Col.
subst B'.

assert(Col A' B C).
ColR.
assert(A' = C').
apply H25.
Col.
contradiction.

intro.
assert(B' = C').
apply H25.
Col.
subst B'.

assert(Col C' A C).
ColR.
assert(C' = A').
apply H23.
ColR.
subst C'.
tauto.

exists B.
split; Col.


assert(TS B B' A' C).
eapply l9_8_2.
apply H26.
assumption.
assert(TS B B' C' A').
eapply l9_8_2.
apply l9_2.
apply H27.
assumption.
unfold TS in H28.
spliter.
ex_and H30 BB.

assert(BB= B').
eapply l6_21.
apply not_col_permutation_1.
apply H29.
4: apply col_permutation_2.
4: apply bet_col.
4: apply H31.
auto.
Col.
Col.
eapply (proj3_col A C B A' C' B' P Q); auto.
subst BB.
Between.
Qed.

Lemma one_side_eq_o : forall A B C D, A <> B -> OS A B C D -> eq_o A B C A B D.
intros.
assert(HH:= H0).
unfold OS in HH.
ex_and HH P.
unfold TS in H2.
assert(~ Col D A B).
spliter.
assumption.
spliter.
unfold TS in H1.
assert(~ Col C A B).
spliter.
assumption.
spliter.
clear H7 H8 H4 H5.
unfold eq_o.
repeat split.
intro.
apply H6.
Col.
intro.
apply H3.
Col.
intros.
apply l7_3 in H11.
subst M.
assert(HH:=H13).
unfold Midpoint in HH.
spliter.

assert(Col A C0 C1).
eapply perp2__col.
apply perp_sym.
apply perp_comm.
apply H4.
apply perp_sym.
Perp.

assert(C1 <> A).
apply perp_not_eq_2 in H7.
assumption.

assert(C0 <> A).
apply perp_not_eq_2 in H4.
assumption.

left.
induction H16.
eapply between_exchange3.
apply between_symmetry.
apply H16.
assumption.
induction H16.
eapply outer_transitivity_between2.
apply H16.
assumption.
assumption.


assert(~Col C1 A B).
eapply perp_not_col in H7.
intro.
apply H7.
Col.

assert(~Col C0 A B).
eapply perp_not_col in H4.
intro.
apply H4.
Col.

assert(TS A B C1 C0).
unfold TS.
repeat split; auto.

exists A.
split; Col.

assert(proj B A C1 A).
unfold proj.
split.
auto.
left.
repeat split.
intro.
apply H19.
Col.
apply perp_comm.
Perp.
Col.

assert(proj C A C1 C0).
eapply proj_col_proj.
apply H5.
auto.
apply bet_col in H16.
Col.

assert( HH:=proj_one_side B C A C0 A C1).
assert(Col C B A \/ OS B A C C0).
apply HH;
auto.
induction H24.
apply False_ind.
apply H6.
Col.

assert( HH1:=proj_one_side B D A C1 A C1).
assert(Col D B A \/ OS B A D C1).
apply HH1;
auto.
induction H25.
apply False_ind.
apply H3.
Col.
clear HH HH1.
assert(OS A B C0 C1).
eapply one_side_transitivity.
apply one_side_symmetry.
apply invert_one_side.
apply H24.
eapply one_side_transitivity.
apply H0.
apply invert_one_side.
assumption.
apply l9_9 in H21.
apply one_side_symmetry in H26.
contradiction.
Qed.


Lemma out_preserves_eq_o : forall A B B' P, ~Col A B  P -> Out A B B' -> eq_o A B P A B' P.
intros.
assert(A <> B /\ A <> B').

unfold Out in H0.
spliter.
split; auto.
spliter.
unfold eq_o.
repeat split.
assumption.
apply out_col in H0.
intro.
apply H.
ColR.
intros.
apply l7_3 in H9.
subst M.

assert(A <> C).
apply perp_not_eq_2 in H3.
auto.
assert(A <> C1).
apply perp_not_eq_2 in H5.
auto.

assert(Perp A B C1 A).
eapply perp_col.
assumption.
apply H5.
apply out_col in H0.
Col.

assert(Col A C C1).
eapply perp2__col.
apply perp_sym.
apply perp_comm.
apply H3.
apply perp_comm.
Perp.

assert(proj B A C1 A).
unfold proj.
split; auto.
left.
repeat split.
intro.
apply perp_not_col in H14.
apply H14.
Col.
apply perp_comm.
Perp.
Col.

assert(proj P A C C1).
eapply proj_col_proj.
apply H6.
assumption.
Col.
assert(C= C1).
eapply proj_uniqueness.
2:apply H17.
assumption.
subst C1.
clear H17 H6 H14.

left.
apply midpoint_bet.
assumption.
Qed.

Lemma cong_identity_inv : forall A B C, A <> B -> ~Cong A B C C.
intros.
intro.
apply H.
eapply cong_identity.
apply H0.
Qed.

Lemma midpoint_col : forall A B A' B' M, A <> B -> Midpoint M A A' -> Midpoint M B B' -> Col A B B' -> A' <> B' /\ Col A A' B' /\ Col B A' B'.
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

Lemma midpoint_par : forall A B A' B' M, A <> B -> Midpoint M A A' -> Midpoint M B B' -> Par A B A' B'.
intros.

assert(A' <> B').
intro.
apply H.
assert(Cong A' B' A B).
eapply l7_13.
apply H0.
assumption.
apply cong_symmetry in H3.
subst B'.
apply cong_identity in H3.
assumption.

induction(col_dec A B B').
assert(A' <> B' /\ Col A A' B' /\ Col B A' B').
eapply (midpoint_col _ _ _ _ M); auto.

unfold Par.
right.
split; auto.

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

unfold Par.
left.
unfold Par_strict.
repeat split; auto; try apply all_coplanar.
intro.
ex_and H10 X.

prolong X M X' M X.
assert(Col A' B' X').
eapply mid_preserves_col.
2: apply H0.
2: apply H1.
apply col_permutation_1.
apply H10.
unfold Midpoint.
split.
assumption.
apply cong_left_commutativity.
Cong.

assert(Col B' X X').
eapply (col_transitivity_1 _ A').
auto.
Col.
Col.
induction(eq_dec_points X X').
subst X'.
apply between_identity in H12.
subst X.

apply H3.
induction(eq_dec_points B M).
subst M.
apply cong_symmetry in H5.
apply cong_identity in H5.
subst B'.
Col.
apply col_permutation_2.
apply (col_transitivity_1 _ M); Col.

assert(Col X M B').
apply bet_col in H12.
apply (col_transitivity_1 _ X'); Col.

assert(Col X' M B').
apply bet_col in H12.
apply (col_transitivity_1 _ X); Col.

assert(Col M B X).
eapply (col_transitivity_1 ).
2: apply col_permutation_5.
2: apply H9.
intro.
subst B'.
apply cong_identity in H5.
subst B.


apply H3.
Col.
Col.

assert(Col X M A).
eapply (col_transitivity_1 ).
2: apply col_permutation_3.
2:apply H19.
intro.
subst X.

assert(Cong M X' M B').
eapply cong_transitivity.
apply H13.
Cong.
assert (HH:=l7_20 M X' B' H18 H20).
induction HH.
subst X'.
apply H3.
apply col_permutation_2.
apply (col_transitivity_1 _ M).
intro.
subst M.
apply cong_identity in H13.
contradiction.
Col.

assert(Col M B A').
ColR.
induction(eq_dec_points M A').
subst A'.
apply cong_identity in H7.
subst A.
Col.
ColR.
assert(X'= B).
eapply l7_9.
apply H21.
assumption.
subst X'.
tauto.
Col.
apply H3.
eapply col3.
2: apply H20.
intro.
subst X.
apply cong_identity in H13.
subst X'.
tauto.
Col.
Col.
Qed.

Lemma midpoint_par_strict : forall A B A' B' M, A <> B -> ~Col A B B' -> Midpoint M A A' -> Midpoint M B B' -> Par_strict A B A' B'.
intros.
assert(Par A B A' B').
eapply (midpoint_par A B A' B' M); assumption.
induction H3.
assumption.
spliter.
apply False_ind.

assert(HH:=midpoint_col B' A' B A M).
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

Lemma le_left_comm : forall A B C D, Le A B C D -> Le B A C D.
intros.
unfold Le in *.
ex_and H P.
exists P.
split.
assumption.
Cong.
Qed.

Lemma le_right_comm : forall A B C D, Le A B C D -> Le A B D C.
intros.
induction(eq_dec_points D C).
subst D.
apply le_zero in H.
subst B.
eapply le_trivial.

induction(eq_dec_points A B).
subst B.
apply le_trivial.

assert(HH:=segment_construction_3 D C A B H0 H1).
ex_and HH P'.
unfold Out in H2.
spliter.
induction H5.

assert(Le D C A B).
eapply l5_5_2.
exists P'.
split; auto.
apply le_left_comm in H6.
assert(Cong A B C D).
apply le_anti_symmetry.
auto.
auto.
unfold Le.
exists C.
split.
apply between_trivial.
Cong.
unfold Le.
exists P'.
split.
assumption.
Cong.
Qed.

Lemma le_comm : forall A B C D, Le A B C D -> Le B A D C.
intros.
apply le_left_comm.
apply le_right_comm.
assumption.
Qed.

Lemma le_cong_le : forall A B C A' B' C', Bet A B C -> Bet A' B' C' -> Le A B A' B' -> Cong B C B' C' -> Le A C A' C'.
intros.
eapply l5_5_2.
unfold Le in H1.
ex_and H1 P.
prolong A C T P B'.
exists T.
split.
assumption.

assert(Bet A B T).
eapply between_exchange4.
apply H.
assumption.

eapply l2_11.
apply H6.
2: apply H3.
eapply between_exchange4.
apply H1.
assumption.
apply cong_left_commutativity.
eapply l2_11.
4: apply cong_left_commutativity.
4:apply H2.
apply between_symmetry.
eapply between_exchange3.
apply H.
assumption.
eapply between_exchange3.
apply H1.
assumption.
Cong.
Qed.


Lemma cong_le_le : forall A B C A' B' C', Bet A B C -> Bet A' B' C' -> Le B C B' C' -> Cong A B A' B' -> Le A C A' C'.
intros.
apply le_comm.
eapply le_cong_le.
apply between_symmetry.
apply H.
apply between_symmetry.
apply H0.
apply le_comm.
assumption.
Cong.
Qed.


Lemma bet_le_le : forall A B C A' B' C', Bet A B C -> Bet A' B' C' -> Le A B A' B' -> Le B C B' C' -> Le A C A' C'.
intros.
assert(HH1:=H1).
assert(HH2:=H2).
unfold Le in HH1.
unfold Le in HH2.
ex_and HH1 X.
ex_and HH2 Y.
assert(Le A C A' Y).
eapply le_cong_le.
3: apply H1.
apply H.
(* assumption. *)

eapply between_inner_transitivity.
apply H0.
assumption.
assumption.

induction (eq_dec_points B' Y).
subst Y.

assert(Le A' B' A' C').
unfold Le.
exists B'.
split.
assumption.
apply cong_reflexivity.
eapply le_transitivity.
apply H7.
assumption.

assert(Bet A' Y C').
eapply outer_transitivity_between2.
2: apply H5.

eapply between_inner_transitivity.
apply H0.
assumption.
assumption.
eapply le_transitivity.
apply H7.
unfold Le.
exists Y.
split.
assumption.
apply cong_reflexivity.
Qed.


Lemma bet_double_bet : forall A B C B' C', Midpoint B' A B -> Midpoint C' A C -> Bet A B' C' -> Bet A B C.
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
assumption.
assumption.
assert(Le A B A C).
eapply bet_le_le.
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


Lemma bet_half_bet : forall A B C B' C', Bet A B C  -> Midpoint B' A B -> Midpoint C' A C -> Bet A B' C'.
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

Lemma midpoint_preserves_bet : forall A B C B' C', Midpoint B' A B -> Midpoint C' A C -> (Bet A B C <-> Bet A B' C').
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

Lemma symmetry_preseves_bet1 : forall A B M A' B', Midpoint M A A' -> Midpoint M B B' -> Bet M A B -> Bet M A' B'.
intros.

eapply l7_15.
2: apply H.
2: apply H0.
2: apply H1.
apply l7_3_2.
Qed.

Lemma symmetry_preseves_bet2 : forall A B M A' B', Midpoint M A A' -> Midpoint M B B' -> Bet M A' B' -> Bet M A B.
intros.
eapply l7_15.
apply l7_3_2.
apply l7_2.
apply H.
apply l7_2.
apply H0.
assumption.
Qed.

Lemma symmetry_preserves_bet : forall A B M A' B', Midpoint M A A' -> Midpoint M B B' -> (Bet M A' B' <-> Bet M A B).
intros.
split.
apply symmetry_preseves_bet2;
assumption.
intro.
eapply (symmetry_preseves_bet1 A B);
assumption.
Qed.

Lemma par_cong_mid : forall A B A' B', Par A B A' B' -> Cong A B A' B' -> exists M,  Midpoint M A A' /\ Midpoint M B B' \/ Midpoint M A B' /\ Midpoint M B A'.
intros.
induction H.

(*******Cas general**********)


assert(HH:= one_or_two_sides A A' B B').
assert(HH0:= H).
unfold Par_strict in HH0.
spliter.
assert(TS A A' B B' \/ OS A A' B B').
apply HH.
(* intro.
subst A'.
apply H4.
exists A.
split;
Col. *)
intro.
apply H4.
exists A'.
split;Col.
intro.
apply H4.
exists A.
split; Col.

induction H5.
clear HH.
assert(HH:= H5).
unfold TS in HH.
assert(~ Col B A A').
spliter.
assumption.
spliter.
ex_and H9 M.
exists M.
left.

assert(B <> B').
intro.
subst B'.
apply between_identity in H10.
subst M.
apply H4.
exists B.
split; Col.

induction (eq_dec_points B M).
subst M.
contradiction.

induction (eq_dec_points B' M).
subst M.
apply False_ind.
apply H8.
Col.

assert(A <> A').
intro.
subst A'.
apply False_ind.
apply H8.
Col.

assert(A <> M).
intro.
subst M.
apply H4.
exists B'.
split.
apply bet_col in H10.
Col.
Col.

assert(A' <> M).
intro.
subst M.
apply H4.
exists B.
apply bet_col in H10.
split.
Col.
Col.

(****************)

assert(HH:=(midpoint_existence A A')).
ex_and HH X.

prolong B X B'' B X.
assert(Midpoint X B B'').
unfold Midpoint.
split.
assumption.
Cong.

(*

assert(~ Col B A A').
intro.
apply H8.

apply bet_col in H10.
assert(Col B' A M).
eapply (col_transitivity_1 _ B).
auto.
Col.
Col.
ColR.
*)

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
apply H17.
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
induction H26.

(***************)

subst B''.

assert(X = M).
eapply (l6_21 A A' B B'); Col.
subst X.
split; auto.

assert(TS A A' B B'').
unfold TS.
repeat split; auto.
intro.
apply H8.
apply col_permutation_1.
eapply (col_transitivity_1 _ B'').
intro.
subst B''.
apply l7_2 in H26.
apply is_midpoint_id in H26.
contradiction.
Col.
Col.
exists X.
split.

unfold Midpoint in H17.
spliter.
apply bet_col in H17.
Col.
assumption.

assert(OS A A' B' B'').
eapply l9_8_1.
apply l9_2.
apply H5.
apply l9_2.
assumption.

assert(TS A A' B' B'').
unfold TS.
repeat split.
intro.
apply H8.
Col.
intro.
apply H8.

apply col_permutation_1.
eapply (col_transitivity_1 _ B'').
intro.
subst B''.
apply l7_2 in H26.
apply is_midpoint_id in H26.
contradiction.
Col.
Col.

exists A'.
split.
Col.
unfold Midpoint in H26.
spliter.
assumption.
apply l9_9 in H29.
contradiction.

clear HH H3.


(****************)

assert(HH:=(midpoint_existence A' B)).
ex_and HH X.
exists X.
right.

prolong A X B'' A X.
assert(Midpoint X A B'').
unfold Midpoint.
split.
assumption.
Cong.

assert(~Col A B A').
intro.
apply H4.
exists A'.
split; Col.

(*


assert(HH:= H5).
unfold OS in HH.
ex_and HH T.


assert(~Col A A' B).
unfold TS in H9.
spliter.
intro.
apply H11.
Col.

assert(~Col A A' B').
unfold TS in H10.
spliter.
intro.
apply H12.
Col.


assert(~Col B A B').
intro.
apply H4.
exists B'.
split;
Col.
*)

assert(Par_strict  A B B'' A').
apply (midpoint_par_strict A B  B'' A' X).
auto.
assumption.
assumption.
apply l7_2.
assumption.

assert(Col B'' B' A' /\ Col A' B' A').
apply (parallel_uniqueness B A B' A' B'' A' A').

(*
assert (Col A' A' B' /\ Col B'' A' B').
Col.
*)
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
apply H8.
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

induction H15.
subst B''.
split.
assumption.
apply l7_2.
assumption.

assert(OS A A' X B'').

eapply (out_one_side_1 _ _ X B'').
intro.
apply H9.
apply col_permutation_1.
eapply (col_transitivity_1 _ X).
intro.
subst X.
apply is_midpoint_id in H3.
subst A'.
apply H4.
exists B.
split; Col.
Col.
unfold Midpoint in H3.
spliter.
apply bet_col in H3.
Col.
Col.
unfold Out.
repeat split.
intro.
subst X.
apply cong_identity in H7.
subst B''.
unfold Par_strict in H10.
spliter.
apply H17.
exists A.
split; Col.
intro.
subst B''.
unfold Par_strict in H10.
spliter.
apply H18.
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
apply H4.
exists A.
split; Col.

unfold OS in H16.
ex_and H16 T.
unfold TS in H17.
spliter.
assumption.
exists A'.
split.
Col.
unfold Midpoint in H15.
spliter.
assumption.

assert(TS A A' X B').
eapply l9_8_2.
apply l9_2.
apply H17.
apply one_side_symmetry.
assumption.

assert(OS A A' X B).

eapply (out_one_side_1).
intro.
apply H9.
apply col_permutation_1.
eapply (col_transitivity_1 _ X).
intro.
subst X.
apply is_midpoint_id in H3.
subst A'.
apply H4.
exists B.
split; Col.
Col.
unfold Midpoint in H3.
spliter.
apply bet_col in H3.
Col.
apply col_trivial_2;assumption.
unfold Out.
repeat split.
intro.
subst X.
unfold TS in H18.
spliter.
apply H18.
Col.
intro.
subst A'.
unfold Par_strict in H10.
spliter.
apply H21.
exists B.
split; Col.
unfold Midpoint in H3.
spliter.
left.
assumption.

assert(OS A A' X B').
eapply one_side_transitivity.
apply H19.
assumption.
apply l9_9 in H18.
contradiction.

spliter.

induction (eq_dec_points A A').
subst A'.
assert(B = B' \/ Midpoint A B B').
eapply l7_20; auto.
induction H4.
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
induction H5.
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
induction H6.
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
induction H7.
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

induction H9.
induction H3.

assert( HH:= midpoint_existence A' B).
ex_and HH M.
exists M.
right.
split.

assert(Bet B M B').

eapply between_exchange4.
2: apply H3.
unfold Midpoint in H10.
spliter.
Between.

assert(Bet A M B').
eapply between_exchange2.
apply H9.
assumption.
assert(Cong A M B' M).
eapply (l2_11 A  B _  _ A').
eapply between_inner_transitivity.
apply H9.
assumption.
eapply between_inner_transitivity.
apply between_symmetry.
apply H3.
unfold Midpoint in H10.
spliter.
assumption.
Cong.
unfold Midpoint in H10.
spliter.
apply cong_left_commutativity.
Cong.
unfold Midpoint.
split.
assumption.
Cong.
apply l7_2.
assumption.

induction H3.

assert( HH:= midpoint_existence B B').
ex_and HH M.
exists M.
left.
split.

assert(Bet A' M B).
eapply between_exchange2.
apply H3.
unfold Midpoint in H10.
spliter.
Between.
assert(Bet M B A).
eapply between_exchange3.
unfold Midpoint in H10.
spliter.
apply between_symmetry.
apply H10.
Between.
assert(Bet A' M A).
eapply outer_transitivity_between.
apply H11.
assumption.
intro.
subst M.
apply is_midpoint_id in H10.
contradiction.
assert(Cong A M A' M).
eapply l2_11.
apply between_symmetry.
apply H12.
eapply between_inner_transitivity.
apply H3.

unfold Midpoint in H10.
spliter.
Between.
assumption.
unfold Midpoint in H10.
spliter.
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
split.
assert(Bet B M A).
eapply between_exchange4.
unfold Midpoint in H11.
spliter.
apply between_symmetry.
apply H11.
assumption.

assert(Bet B' B M).
eapply between_inner_transitivity.
apply between_symmetry.
apply H9.
assumption.

assert(Bet M A' A).
eapply between_exchange3.
2:apply H10.
unfold Midpoint in H11.
spliter.
Between.
assert(Bet B' M A').
eapply outer_transitivity_between2.
apply H13.
unfold Midpoint in H11.
spliter.
Between.
intro.
subst M.
apply l7_2 in H11.
apply is_midpoint_id in H11.
auto.
assert(Bet B' M A).
eapply outer_transitivity_between.
apply H15.
assumption.
intro.
subst A'.
apply is_midpoint_id in H11.
subst M.
tauto.

assert(Cong A M B' M).
eapply l4_3.
apply between_symmetry.
apply H12.
apply H15.
Cong.
unfold Midpoint in H11.
spliter.
Cong.
unfold Midpoint.
split.
Between.
Cong.
Midpoint.

induction H9.
induction H2.


assert(B' = B /\ A = A').
eapply bet_cong_eq.
assumption.
Between.
Cong.
spliter.
contradiction.
induction H2.

assert(Bet B' B A').
eapply bet_cong_bet.
apply H6.
Between.
Between.
Cong.

assert( HH:= midpoint_existence B B').
ex_and HH M.
exists M.
left.
split.

assert(Bet A' M B').
eapply between_exchange2.
apply between_symmetry.
apply H10.
unfold Midpoint in H11.
spliter.
assumption.

assert(Bet M B' A).
eapply between_exchange3.
unfold Midpoint in H11.
spliter.
apply H11.
assumption.
assert(Bet A' M A).
eapply outer_transitivity_between.
apply H12.
assumption.
intro.
subst M.
apply l7_2 in H11.
apply is_midpoint_id in H11.
apply sym_equal in H11.
contradiction.

assert(Bet A M B).
eapply outer_transitivity_between2.
apply between_symmetry.
apply H13.
unfold Midpoint in H11.
spliter.
Between.
intro.
subst M.
apply l7_2 in H11.
apply is_midpoint_id in H11.
apply sym_equal in H11.
contradiction.

assert(Cong A' M A M).
eapply l4_3.
apply H12.
apply H15.
Cong.
unfold Midpoint in H11.
spliter.
Cong.
unfold Midpoint.
split.
Between.
Cong.
assumption.

assert( HH:= midpoint_existence A B').
ex_and HH M.
exists M.
right.
split.
assumption.

assert(Bet A' A M).
eapply between_inner_transitivity.
apply between_symmetry.
apply H2.
unfold Midpoint in H10.
spliter.
assumption.

assert(Bet A M B).
eapply between_exchange4.
unfold Midpoint in H10.
spliter.
apply H10.
Between.

assert(Bet A' M B).
eapply outer_transitivity_between2.
apply H11.
assumption.
intro.
subst M.
apply is_midpoint_id in H10.
contradiction.

assert(Cong B M A' M).
eapply l4_3.
apply between_symmetry.
apply H12.
eapply between_exchange2.
apply between_symmetry.
apply H2.
unfold Midpoint in H10.
spliter.

assumption.
Cong.
unfold Midpoint in H10.
spliter.
Cong.
unfold Midpoint.
split.
Between.
Cong.

induction H8.

assert(Bet B' B A').
eapply outer_transitivity_between2.
apply H9.
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

induction H8.

assert( HH:= midpoint_existence A A').
ex_and HH M.
exists M.
left.
split.
assumption.

assert(Bet B A' M).
eapply between_inner_transitivity.
apply H8.
unfold Midpoint in H10.
spliter.
Between.

assert(Bet B M A).
eapply outer_transitivity_between2.
apply H11.
unfold Midpoint in H10.
spliter.
Between.
intro.
subst M.
apply l7_2 in H10.
apply is_midpoint_id in H10.
subst A'.
tauto.

assert(Bet B M B').
eapply between_exchange4.
apply H12.
Between.

assert(Cong B M B' M).
eapply l4_3.
apply H12.

assert(Bet B' A A').
eapply between_inner_transitivity.
apply H9.
Between.
eapply between_exchange2.
apply H14.
unfold Midpoint in H10.
spliter.
Between.
Cong.
unfold Midpoint in H10.
spliter.
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
induction H10.

assert( HH:= midpoint_existence A B').
ex_and HH M.
exists M.
right.
split.
assumption.

assert(Bet B M B').
eapply between_exchange2.
apply between_symmetry.
apply H9.
unfold Midpoint in H11.
spliter.
Between.
assert(Bet A' B' M).
eapply between_inner_transitivity.
apply between_symmetry.
apply H10.
unfold Midpoint in H11.
spliter.
Between.

assert(Bet A' M B).
eapply outer_transitivity_between2.
apply H13.
Between.
intro.
subst M.
apply l7_2 in H11.
apply is_midpoint_id in H11.
subst B'.
tauto.

assert(Cong M A' M B).
eapply l2_11.
apply between_symmetry.
apply H13.
eapply between_exchange3.
unfold Midpoint in H11.
spliter.
apply between_symmetry.
apply H11.
assumption.
unfold Midpoint in H11.
spliter.
Between.
Cong.
Cong.
unfold Midpoint.
split.
Between.
Cong.

assert( HH:= midpoint_existence A A').
ex_and HH M.
exists M.
left.
split.
assumption.

assert(Bet B A M).
eapply between_inner_transitivity.
apply between_symmetry.
apply H8.
unfold Midpoint in H11.
spliter.
Between.
assert(Bet B' M A).
eapply between_exchange2.
apply between_symmetry.
apply H10.
unfold Midpoint in H11.
spliter.
Between.
assert(Bet B' M B).
eapply outer_transitivity_between.
apply H13.
Between.
intro.
subst M.
apply is_midpoint_id in H11.
contradiction.
assert(Cong B' M B M).
eapply l2_11.
eapply between_inner_transitivity.
apply between_symmetry.
apply H10.
unfold Midpoint in H11.
spliter.
Between.
apply H12.
Cong.
unfold Midpoint in H11.
spliter.
Between.
Cong.
unfold Midpoint.
split.
Between.
Cong.
Qed.

Lemma per_preserves_bet_aux1 : forall P Q A B C B' C', P <> Q -> Bet A B C ->
                                      Col P Q A ->
                                      Per B B' P -> Col P Q B' ->
                                      Per C C' P -> Col P Q C' ->
                                      P <> A -> P <> B' -> P <> C' ->
                                      Bet A B' C'.
intros.

induction(eq_dec_points B B').
subst B'.

assert(Col A B C').
apply (col3 P Q); try auto.

assert(Col P A B).
eapply (col_transitivity_1 _ Q); try auto.

assert(Col Q A B).
eapply (col_transitivity_1 _ P).
auto.
Col.
Col.

induction(eq_dec_points A B).
subst B.
apply between_trivial2.

assert(Col P Q C).
eapply col3.
apply H12.
Col.
Col.
apply bet_col.
assumption.

assert(Col P C' C).
eapply col_transitivity_1.
apply H.
assumption.
assumption.

assert(P=C' \/ C=C').
eapply l8_9.
apply l8_2.
assumption.
assumption.

induction H15.
subst C'.
tauto.
subst C'.
assumption.

(* A=A' et B<>B' *)

induction(eq_dec_points A C).
subst C.
apply between_identity in H0.
subst B.
assert(B'=C').
eapply per_id.
4:apply H2.
assumption.
auto.
auto.
assumption.
eapply (col_transitivity_1 _ Q); auto.
subst C'.
apply between_trivial.

assert(C <> C').
intro.
subst C'.

assert(Col P A C).
eapply (col_transitivity_1 _ Q); try auto.

assert(Col A C B').
eapply col3.
apply H.
assumption.
assumption.
assumption.

assert(Col P B' B).
eapply col3.
3:apply H12.
assumption.
Col.
apply col_permutation_5.
apply bet_col.
assumption.
assert(B=B' \/ P=B').
eapply l8_9.
assumption.
Col.
induction H14.
subst B'.
tauto.
auto.

induction (eq_dec_points A B').
subst B'.
apply between_trivial2.

assert(A <> B).
intro.
subst B.
apply per_not_col in H2.
apply H2.
ColR.
assumption.
auto.

induction(col_dec C B B').
assert(C=B).

eapply (l6_21 B B').
assert(Per B B' A).
eapply (per_col _ _ P).
auto.
assumption.
ColR.
apply per_not_col in H15.
apply H15.
auto.
auto.
apply H13.
Col.
Col.
apply bet_col.
apply H0.
Col.
subst C.

assert(B'=C').
eapply per_id.
4:apply H2.
auto.
auto.
auto.
auto.
ColR.
subst C'.
apply between_trivial.


assert(Perp B' B' B' P \/ Perp B B' B' P).
eapply perp_in_perp_bis.

apply per_perp_in.
auto.
auto.
assumption.
induction H15.
apply perp_not_eq_1 in H15.
tauto.

assert(Perp C' C' C' P \/ Perp C C' C' P).
eapply perp_in_perp_bis.

apply per_perp_in.
auto.
auto.
assumption.
induction H16.
apply perp_not_eq_1 in H16.
tauto.

assert(Par B B' C C').
eapply l12_9_2D.
apply H15.
apply perp_sym.
apply perp_left_comm.
eapply perp_col.
auto.
apply perp_left_comm.
apply perp_sym.
apply H16.
eapply (col_transitivity_1 _ Q);
auto.
unfold Par in H17.

assert(Par_strict B B' C C').
induction H17.
assumption.
spliter.
apply False_ind.
apply H14.
ColR.
clear H17.


assert(OS B B' C C').
eapply l12_6.
assumption.

assert(Per B B' A).
eapply (per_col _ _ P); try auto.
ColR.

induction(eq_dec_points A C').
subst C'.

assert(TS B B' A C).
unfold TS.
repeat split; try auto.
apply per_not_col in H19.
intro.
apply H19.
Col.
auto.
auto.
exists B.
split.
Col.
assumption.
apply l9_2 in H20.
apply l9_9 in H20.
contradiction.


assert(TS B B' A C).
unfold TS.
repeat split; try auto.
apply per_not_col in H19.
intro.
apply H19.
Col.
auto.
auto.
exists B.
split.
Col.
assumption.

assert(TS B B' C' A).

eapply l9_8_2.
apply l9_2.
apply H21.
assumption.


unfold TS in H22.
spliter.
ex_and H24 T.


assert(T = B').
eapply l6_21.
apply not_col_permutation_1.
apply H23.
4: apply bet_col in H25.
4: apply col_permutation_2.
4: apply H25.
auto.
Col.
Col.
ColR.
subst T.
Between.
Qed.

Lemma perp_not_eq_3 : forall A B C, Perp A B B C -> A <> C.
intros.
apply perp_comm in H.
apply perp_perp_in in H.
assert(Per A B C).
apply perp_in_per.
Perp.
unfold Perp_at in H.
spliter.
intro.
subst C.
apply l8_8 in H0.
contradiction.
Qed.


Lemma per_preserves_bet_aux2 : forall P Q A B C A' C', P <> Q -> Bet A B C ->
                                      Per A A' P -> Col P Q A' ->
                                      Col P Q B ->
                                      Per C C' P -> Col P Q C' ->
                                      P <> A'-> P <> B -> P <> C' ->
                                      Bet A' B C'.
intros.

induction (eq_dec_points A A').
subst A'.

assert(Col A B C').
apply (col3 P Q); try auto.

assert(Col P A B).
eapply (col_transitivity_1 _ Q); try auto.

assert(Col Q A B).
eapply (col_transitivity_1 _ P).
auto.
Col.
Col.

induction(eq_dec_points A B).
subst B.
apply between_trivial2.

assert(Col P Q C).
eapply col3.
apply H12.
Col.
Col.
apply bet_col.
assumption.

assert(Col P C' C).
eapply col_transitivity_1.
apply H.
assumption.
assumption.

assert(P=C' \/ C=C').
eapply l8_9.
apply l8_2.
assumption.
assumption.

induction H15.
subst C'.
tauto.
subst C'.
assumption.


induction(eq_dec_points A C).
subst C.
apply between_identity in H0.
subst B.
apply False_ind.
apply H9.

apply l8_9 in H1.
induction H1.
assumption.
subst A'.
tauto.
ColR.


assert(~Col P Q A).
intro.
assert (Col A A' P).
ColR.
apply l8_9 in H1.
induction H1;tauto.
assumption.

assert(A <> B).
intro.
subst B.
contradiction.

induction (eq_dec_points C C').
subst C'.
assert(Col A' B C).
eapply (col3 P Q ); assumption.
assert(Col C A' P).
ColR.

assert(B=C).
eapply l6_21.
apply H11.
apply H12.
Col.
Col.
Col.
Col.
subst C.
apply between_trivial.

induction(eq_dec_points A' C').
subst C'.

assert(Per  A A' B).
eapply per_col.
2:apply H1.
auto.
ColR.
assert(Per C A' B).
eapply per_col.
2:apply H4.
auto.
ColR.

eapply l8_6 in H14.
subst B.
apply between_trivial.
apply H15.
Between.

assert(HH:=ex_per_cong P Q B A P Q).
assert(exists T, Per T B P /\ Cong T B P Q /\ OS P Q T A).
apply HH; auto.
ex_and H15 T.
clear HH.

assert(Perp B B B P \/ Perp T B B P).
eapply perp_in_perp_bis.

apply per_perp_in.
intro.
subst T.
apply cong_symmetry in H16.
apply cong_identity in H16.
contradiction.
auto.
auto.
induction H18.
apply perp_not_eq_1 in H18.
tauto.

assert(Perp C' C' C' P \/ Perp C C' C' P).
eapply perp_in_perp_bis.

apply per_perp_in.
auto.
auto.
assumption.
induction H19.
apply perp_not_eq_1 in H19.
tauto.

assert(Par T B C C').
eapply l12_9_2D.
apply H18.
apply perp_sym.
apply perp_left_comm.
eapply perp_col.
auto.
apply perp_left_comm.
apply perp_sym.
apply H19.
eapply (col_transitivity_1 _ Q);
auto.

assert(Perp A' A' A' P \/ Perp A A' A' P).
eapply perp_in_perp_bis.

apply per_perp_in.
auto.
auto.
assumption.
induction H21.
apply perp_not_eq_1 in H21.
tauto.

assert(Par T B A A').
eapply l12_9_2D.
apply H18.
apply perp_sym.
apply perp_left_comm.
eapply perp_col.
auto.
apply perp_left_comm.
apply perp_sym.
apply H21.
eapply (col_transitivity_1 _ Q);
auto.

assert(Par_strict T B C C').
induction H20.
assumption.
spliter.
apply False_ind.

apply H14.
eapply per_id.
4:apply H1.
assumption.
auto.
auto.
apply l8_2.
eapply per_col.
2: apply l8_2.
2:apply H4.
auto.

apply col_permutation_2.
eapply col_transitivity_1.
2:apply bet_col.
2:apply between_symmetry.
apply bet_col in H0.
2: apply H0.

assert(~Col P Q C).
intro.
assert (Col C C' P).
ColR.
apply l8_9 in H4.
induction H1;tauto.
assumption.

intro.
subst C.
contradiction.
Col.
ColR.


assert(Par_strict T B A A').
induction H22.
assumption.
spliter.
apply False_ind.

apply H14.
eapply sym_equal.
eapply per_id.
4:apply H4.
assumption.
auto.
auto.
apply l8_2.
eapply per_col.
2: apply l8_2.
2:apply H1.
auto.

apply col_permutation_2.
eapply col_transitivity_1.
2:apply bet_col.
apply bet_col in H0.
2: apply H0.
assumption.
Col.
ColR.

assert(OS T B C C').
apply l12_6.
assumption.
assert(OS T B A A').
apply l12_6.
assumption.

assert(TS T B A C).
unfold TS.
repeat split.
intro.
unfold Par_strict in H24.
spliter.
apply H30.
exists A.
split.
assumption.
Col.
intro.
unfold Par_strict in H23.
spliter.
apply H30.
exists C.
split.
assumption.
Col.
exists B.
split.
Col.
assumption.

assert(TS T B C' A).
eapply l9_8_2.
apply l9_2.
apply H27.
assumption.

assert(TS T B A' C').
eapply l9_8_2.
apply l9_2.
apply H28.
assumption.
unfold TS in H29.
spliter.
ex_and H31 BB.

assert(B=BB).
eapply (l6_21 T B A' C'); Col.
ColR.
subst BB.
assumption.
Qed.


Lemma par_col : forall A B C, Par A B A C -> Col A B C.
intros.
induction H.
unfold Par_strict in H.
spliter.
apply False_ind.
apply H2.
exists A.
split; Col.
spliter.
Col.
Qed.

Lemma per_diff : forall A B A' B' P, A <> B -> ~ Col A B A' ->
                             Per A A' P -> Per B B' P ->
                             A' <> P -> B' <> P -> A' <> B'.
intros.
intro.
subst B'.
apply H0.
eapply per2__col.
apply H1.
assumption.
assumption.
Qed.



Lemma per_preserves_bet : forall P Q A B C A' B' C', P <> Q -> Bet A B C ->
                                      Per A A' P -> Col P Q A' ->
                                      Per B B' P -> Col P Q B' ->
                                      Per C C' P -> Col P Q C' ->
                                      P <> A'-> P <> B' -> P <> C' ->
                                      Bet A' B' C'.
intros.

induction(eq_dec_points A A').
subst A'.
eapply (per_preserves_bet_aux1 P Q A B C B' C'); assumption.

induction(eq_dec_points B B').
subst B'.
eapply (per_preserves_bet_aux2 P Q A B C A' C'); assumption.

induction(eq_dec_points C C').
subst C'.
assert(HH:=(per_preserves_bet_aux1 P Q C B A B' A')).
apply between_symmetry.
apply HH; try assumption.
Between.

induction (eq_dec_points A B).
subst B.
assert(A'=B').
eapply (per_id A _ _ P); try auto.
ColR.
subst B'.
apply between_trivial2.

induction (eq_dec_points C B).
subst B.
assert(C'=B').
eapply (per_id C _ _ P); try auto.
ColR.
subst B'.
apply between_trivial.

assert(A <> C).
intro.
subst C.
apply between_identity in H0.
contradiction.

assert(Perp B' B' B' P \/ Perp B B' B' P).
eapply perp_in_perp_bis.
apply per_perp_in.
auto.
auto.
assumption.
induction H16.
apply perp_not_eq_1 in H16.
tauto.

assert(Perp C' C' C' P \/ Perp C C' C' P).
eapply perp_in_perp_bis.
apply per_perp_in.
auto.
auto.
assumption.
induction H17.
apply perp_not_eq_1 in H17.
tauto.

assert(Perp A' A' A' P \/ Perp A A' A' P).
eapply perp_in_perp_bis.
apply per_perp_in.
auto.
auto.
assumption.
induction H18.
apply perp_not_eq_1 in H18.
tauto.

assert(Par B B' C C').
eapply l12_9_2D.
apply H16.
apply perp_sym.
apply perp_left_comm.
eapply perp_col.
auto.
apply perp_left_comm.
apply perp_sym.
apply H17.
eapply (col_transitivity_1 _ Q);
auto.

assert(Par B B' A A').
eapply l12_9_2D.
apply H16.
apply perp_sym.
apply perp_left_comm.
eapply perp_col.
auto.
apply perp_left_comm.
apply perp_sym.
apply H18.
eapply (col_transitivity_1 _ Q);
auto.

(**************************************************************************************************)

(*induction(eq_dec_points A C).
subst C.
apply between_identity in H0.
subst B.
assert(A' = B').
eapply per_id.
4: apply H1.
auto.
auto.
auto.
auto.
ColR.
subst B'.
apply between_trivial2.*)

assert(Col A B C).
apply bet_col.
assumption.

induction(eq_dec_points A' C').
subst C'.

assert(Col A C A').
eapply per2__col.
apply H1.
auto.
assumption.

assert(Col A B A').
eapply (col_transitivity_1 _ C); try auto.
Col.

assert(Per B A' P).
apply l8_2.
eapply (per_col _ _ A).
auto.
apply l8_2.
assumption.
Col.


assert(A' = B').
eapply (per_id B _ _ P); try auto.
intro.
subst A'.
apply par_right_comm in H20.
apply par_col in H20.

assert(Per P B B').
eapply (per_col _ _ A).
auto.
apply l8_2.
assumption.
Col.
apply H11.
eapply l8_7.
apply H25.
apply l8_2.
assumption.
ColR.
subst B'.
apply between_trivial.

(************************************* General case *********************************)

assert(Par A A' C C').
eapply par_trans.
apply par_symmetry.
apply H20.
assumption.

assert(A' <> B').
intro.
subst B'.
apply H22.
assert(Col A B A').
eapply per2__col.
apply H1.
auto.
assumption.
assert(Col C A A').
ColR.
assert(Per P A' C).
eapply (per_col _ _ A).
auto.
apply l8_2.
assumption.
Col.
apply l8_2 in H26.
eapply (per_id).
4: apply H26.
intro.
subst C.
apply perp_comm in H17.
apply perp_not_col in H17.
apply H17.
ColR.
auto.
auto.
assumption.
ColR.

assert(C' <> B').
intro.
subst B'.
apply H22.
assert(Col B C C').
eapply per2__col.
apply H3.
auto.
assumption.
assert(Col A C C').
ColR.
assert(Per P C' A).
eapply (per_col _ _ C).
auto.
apply l8_2.
assumption.
Col.
apply l8_2 in H27.
eapply (per_id).
5: apply H27.
auto.
auto.
auto.
auto.
ColR.

assert(Par_strict B B' C C').
induction H19.
assumption.
spliter.

apply False_ind.

apply H25.

eapply per_id.
5: apply H3.
intro.
subst B.
apply perp_comm in H16.
apply perp_not_col in H16.
apply H16.
ColR.
auto.
auto.
apply l8_2.
eapply (per_col _ _ C).
auto.
apply l8_2.
assumption.
Col.
ColR.

assert(Par_strict B B' A A').
induction H20.
assumption.
spliter.

apply False_ind.

apply H24.

eapply per_id.
5: apply H3.
intro.
subst B.
apply perp_comm in H16.
apply perp_not_col in H16.
apply H16.
ColR.
auto.
auto.
apply l8_2.
eapply (per_col _ _ A).
auto.
apply l8_2.
assumption.
Col.
ColR.

assert(OS B B' A A').
apply l12_6.
assumption.
assert(OS B B' C C').
apply l12_6.
assumption.
assert(TS B B' A C).
unfold TS.
repeat split; auto.
intro.
apply H24.
eapply per_id.
4:apply H1.
auto.
auto.

auto.
apply l8_2.
eapply per_col.
2: apply l8_2.
2:apply H3.
auto.
Col.
ColR.
intro.
apply H25.
eapply per_id.
4: apply H5.
auto.
auto.
auto.
apply l8_2.
eapply per_col.
2:apply l8_2.
2: apply H3.
auto.
Col.
ColR.
exists B.
split.
Col.
assumption.

assert(TS B B' A' C).
eapply l9_8_2.
apply H30.
assumption.
assert(TS B B' A' C').
apply l9_2.
eapply l9_8_2.
apply l9_2.
apply H31.
assumption.
unfold TS in H32.
spliter.
ex_and H34 BB.

assert(BB = B').
eapply l6_21.
apply not_col_permutation_1.
apply H33.
4:apply col_permutation_2.
4:apply bet_col.
4:apply H35.
auto.
Col.
Col.
ColR.
subst BB.
assumption.
Qed.

Lemma ex_col : forall A B C, A <> B /\ A <> C /\ B <> C -> Col A B C -> exists D, Col A B D /\ A <> D /\ B <> D /\ C <> D.
intros.
spliter.
induction H0.
prolong A C D A C.
exists D.
repeat split.
apply bet_col.
eapply between_exchange4.
apply H0.
assumption.
intro.
subst D.
apply between_identity in H3.
contradiction.
intro.
subst D.
assert(B = C).
eapply between_equality.
apply between_symmetry.
apply H3.
Between.
contradiction.
intro.
subst D.
apply cong_symmetry in H4.
apply cong_identity in H4.
contradiction.

induction H0.
prolong B A D B A.
exists D.
repeat split.
apply bet_col in H3.
Col.
intro.
subst D.
apply cong_symmetry in H4.
apply cong_identity in H4.
subst B.
tauto.
intro.
subst D.
apply between_identity in H3.
subst B.
tauto.
intro.
subst D.
assert(A = C).
eapply between_equality.
apply between_symmetry.
apply H0.
Between.
contradiction.

prolong C B D C B.
exists D.
repeat split.
apply bet_col.
eapply between_exchange3.
apply H0.
assumption.
intro.
subst D.
assert(A = B).
eapply between_equality.
apply between_symmetry.
apply H3.
Between.
contradiction.
intro.
subst D.
apply cong_symmetry in H4.
apply cong_identity in H4.
subst C.
tauto.
intro.
subst D.
apply between_identity in H3.
subst C.
tauto.
Qed.


Lemma out_preserves_eqo1 : forall A B P B', ~Col A B P -> Out A B B' -> eqo A B P A B' P.
intros.
unfold eqo.
repeat split.
assumption.
assert(HH:=H0).
unfold Out in H0.
spliter.
apply out_col in HH.
intro.
apply H.
ColR.

intros.

assert(B=B2).
eapply l6_11_uniqueness.
3:apply H0.
unfold Out in H0.
spliter.
assumption.
2: apply H6.
unfold Out in H5.
spliter.
auto.
apply l6_6.
assumption.
apply cong_reflexivity.
subst B2.
apply l7_3 in H7.
subst M.

assert(Perp A B C1 A).
eapply perp_col.
intro.
subst B.
apply H.
Col.
apply H3.
apply out_col in H5.
assumption.

assert(A <> C).
apply perp_not_eq_2 in H1.
auto.

assert(A <> C1).
apply perp_not_eq_2 in H3.
auto.

assert(Col A C C1).
eapply perp2__col.
apply perp_sym.
apply perp_right_comm.
apply H1.
apply perp_sym.
Perp.

induction (eq_dec_points P C).
subst P.

apply l8_9 in H4.
induction H4.
subst C1.
unfold Midpoint in H9.
spliter.
left.
assumption.
subst C1.
apply perp_not_eq_2 in H3.
tauto.
Col.

assert(P <> C1).
intro.
subst P.
apply H14.
apply l8_9 in H2.
induction H2.
assumption.
subst C.
tauto.
Col.

assert(C1=C).
eapply per_id.
4:apply H4.
assumption.
auto.
auto.
assumption.
Col.
subst C1.
unfold Midpoint in H9.
spliter.
left.
assumption.
Qed.


Lemma out_preserves_eqo : forall A B P B' P', ~Col A B P -> Out A B B' -> Out A P P' -> eqo A B P A B' P'.
intros.

induction (eq_dec_points P P').
subst P'.
apply out_preserves_eqo1.
assumption.
assumption.

unfold eqo.
repeat split.
assumption.
intro.
apply H.
assert(Col A B B').
apply out_col.
assumption.
assert(Col A P P').
apply out_col.
assumption.

assert(Col A P B').
apply (col_transitivity_1 _ P').
intro.
subst P'.
unfold Out in H1.
spliter.
auto.
Col.
Col.
eapply (col_transitivity_1 _ B').
intro.
subst B'.
unfold Out in H0.
spliter.
auto.
Col.
Col.

intros.

assert(B = B2).
eapply l6_11_uniqueness.
4: apply H8.
3: apply H0.
intro.
subst B'.
unfold Out in H7.
spliter.
auto.
intro.
subst B2.
unfold Out in H7.
spliter.
auto.
apply l6_6.
assumption.
apply cong_reflexivity.
subst B2.

apply l7_3 in H9.
subst M.

assert(A <> C).
apply perp_not_eq_2 in H3.
auto.
assert(A <> C1).
apply perp_not_eq_2 in H5.
auto.

assert(Perp A B C1 A).
eapply perp_col.
intro.
subst B.
apply H.
Col.
apply H5.
apply out_col.
apply l6_6.
assumption.

assert(Col A C C1).

eapply perp2__col.
apply perp_sym.
apply perp_comm.
apply H3.
apply perp_comm.
Perp.

induction(eq_dec_points P C).
subst P.
assert(P'=C1).

apply l8_9 in H6.
induction H6.
assumption.
contradiction.
assert(HH:= H1).
unfold Out in H1.
spliter.
apply out_col in HH.
ColR.
subst P'.

left.

unfold Out in H1.
spliter.
induction H17.
eapply between_exchange3.
apply between_symmetry.
apply H17.
apply midpoint_bet.
assumption.
eapply outer_transitivity_between2.
apply between_symmetry.
apply H17.
apply midpoint_bet.
assumption.
assumption.

assert(~Col P C A).
apply per_not_col.
assumption.
auto.
assumption.

assert(C <> C1).
intro.
subst C1.
assert(Col P P' C).
eapply per2__col.
apply H4.
auto.
assumption.

apply H2.

eapply l6_21.
apply not_col_permutation_2.
apply H17.
5:apply col_permutation_2.
5:apply H18.
auto.
Col.
Col.
Col.

assert(HH:=ex_col A C C1).
assert(A <> C /\ A <> C1 /\ C <> C1).
repeat split; auto.
apply HH in H19.
ex_and H19 D.

left.
unfold Out in H1.
spliter.

induction H24.
assert(Bet A C C1).
apply (per_preserves_bet D A A P P' A C C1); try auto; try Col.
apply l8_2.
apply l8_5.
eapply per_col.
2:apply H4.
auto.
Col.
eapply per_col.
2:apply H6.
auto.
ColR.
ColR.
eapply between_exchange3.
apply between_symmetry.
apply H25.
apply midpoint_bet.
assumption.

assert(Bet A C1 C).
apply (per_preserves_bet D A A P' P A C1 C); try auto; try Col.
apply l8_2.
apply l8_5.
eapply per_col.
2:apply H6.
auto.
ColR.
ColR.
eapply per_col.
2:apply H4.
auto.
ColR.
eapply between_symmetry.
eapply outer_transitivity_between.
2: apply H25.
apply midpoint_bet.
apply l7_2.
assumption.
auto.
assumption.
Qed.


Lemma per_one_side : forall A B P Q C C', A <> P -> C' <> P -> ~Col A B C -> Col P Q A -> Col P Q C' -> Perp A B P Q -> Per C C' P -> OS A B C C'.
intros.
assert(A <> B).
apply perp_not_eq_1 in H4.
assumption.

assert(P <> Q).
apply perp_not_eq_2 in H4.
assumption.

induction (eq_dec_points C C').
subst C'.
apply one_side_reflexivity.
intro.
apply H1.
Col.

assert(Perp C C' C' P).
eapply per_perp_in in H5.
eapply perp_in_perp_bis in H5.
induction H5.
apply perp_not_eq_1 in H5.
tauto.
assumption.
auto.
auto.

assert(Perp C C' P Q).
apply perp_sym.
eapply perp_col.
assumption.
apply perp_sym.
apply perp_right_comm.
apply H9.
Col.
assert(Par C C' A B).
eapply l12_9_2D.
apply H10.
assumption.

assert(Par_strict C C' A B).
induction H11.
assumption.
spliter.
apply False_ind.
apply H1.
Col.
eapply l12_6.
apply par_strict_symmetry.
assumption.
Qed.


Lemma one_side_eqo : forall A B X Y, OS A B X Y -> eqo A B X A B Y.
intros.
unfold eqo.
repeat split.
eapply one_side_not_col123.
apply H.
apply one_side_symmetry in H.
eapply one_side_not_col123.
apply H.

intros.
apply l7_3 in H6.
subst M.

induction(eq_dec_points C C1).
subst C1.
left.
apply midpoint_bet.
assumption.

assert(A <> C).
apply perp_not_eq_2 in H0.
auto.

assert(A <> C1).
apply perp_not_eq_2 in H2.
auto.

assert(A <> C /\ A <> C1 /\ C <> C1).
repeat split; auto.

assert(Col A C C1).
eapply perp2__col.
apply perp_comm.
apply perp_sym.
apply H0.
apply perp_comm.
Perp.

assert(HH:=ex_col A C C1 H12 H13).
ex_and HH D.

assert(Perp A B D C).
apply perp_sym.
apply perp_left_comm.
eapply perp_col.
auto.
apply perp_sym.
apply H0.
Col.

assert(~Col A B X).
unfold OS in H.
ex_and H T.
unfold TS in H.
spliter.
intro.
apply H.
Col.

assert(~Col A B Y).
unfold OS in H.
ex_and H T.
unfold TS in H22.
spliter.
intro.
apply H22.
Col.

assert(OS A B X C).
eapply (per_one_side A B D); auto.
apply  col_permutation_3.
apply H14.
Col.
assumption.
eapply per_col.
2: apply H1.
auto.
Col.

assert(OS A B Y C1).
eapply (per_one_side A B D); auto.
apply col_permutation_3.
apply H14.
apply col_permutation_2.
eapply (col_transitivity_1 _ A);Col.
assumption.
eapply per_col.
2: apply H3.
auto.
apply col_permutation_2.
eapply (col_transitivity_1 _ C);
Col.

assert(OS A B C C1).
eapply one_side_transitivity.
apply one_side_symmetry.
apply H23.
eapply one_side_transitivity.
apply H.
assumption.

assert(A <> B).
apply perp_not_eq_1 in H0.
assumption.

assert(~ Col C1 A B).
unfold OS in H24.
ex_and H24 T.
unfold TS in H27.
spliter.
assumption.

assert(TS A B C1 C').
unfold TS.
repeat split; auto.

intro.
unfold Midpoint in H8.
spliter.

assert(C'=A).
eapply l6_21.
apply not_col_permutation_1.
apply H27.
4: apply bet_col.
4: apply H8.
auto.
Col.
Col.
Col.
subst C'.
apply cong_identity in H29.
subst C1.
tauto.
exists A.
unfold Midpoint in H8.
spliter.
split; auto.
Col.

assert(TS A B C C').
eapply l9_8_2.
apply H28.
apply one_side_symmetry.
assumption.

assert(Col A C C').
eapply (col_transitivity_1 _ C1).
assumption.
Col.
unfold Midpoint in H8.
spliter.
apply bet_col in H8.
Col.

unfold TS in H29.
spliter.
ex_and H32 AA.
assert(AA=A).
eapply l6_21.
apply not_col_permutation_1.
apply H31.
4: apply col_permutation_2.
4: apply bet_col.
4: apply H33.
intro.
subst C'.
apply between_identity in H33.
subst AA.
apply H31.
assumption.
Col.
Col.
Col.

subst AA.
left.
assumption.
Qed.

Lemma ex_col1 : forall A B C, A <> B -> Col A B C -> exists D, Col A B D /\ A <> D /\ B <> D /\ C <> D.
intros.
induction H0.
prolong A C D A C.
exists D.
repeat split.
apply bet_col.
eapply between_exchange4.
apply H0.
assumption.
intro.
subst D.
apply between_identity in H1.
subst C.
apply between_identity in H0.
contradiction.
intro.
subst D.
assert(B = C).
eapply between_equality.
apply between_symmetry.
apply H1.
Between.
subst C.
apply cong_symmetry in H2.
apply cong_identity in H2.
contradiction.
intro.
subst D.
apply cong_symmetry in H2.
apply cong_identity in H2.
subst C.
apply between_identity in  H0.
contradiction.

induction H0.
prolong B A D B A.
exists D.
repeat split.
apply bet_col in H1.
Col.
intro.
subst D.
apply cong_symmetry in H2.
apply cong_identity in H2.
subst B.
tauto.
intro.
subst D.
apply between_identity in H1.
subst B.
tauto.
intro.
subst D.
assert(A = C).
eapply between_equality.
apply between_symmetry.
apply H0.
Between.
subst C.
apply cong_symmetry in H2.
apply cong_identity in H2.
subst B.
tauto.

prolong C B D C B.
exists D.
repeat split.
apply bet_col.
eapply between_exchange3.
apply H0.
assumption.
intro.
subst D.
assert(A = B).
eapply between_equality.
apply between_symmetry.
apply H1.
Between.
contradiction.
intro.
subst D.
apply cong_symmetry in H2.
apply cong_identity in H2.
subst C.
apply between_identity in H0.
subst B.
tauto.
intro.
subst D.
apply between_identity in H1.
subst C.
apply between_identity in H0.
subst B.
tauto.
Qed.

End Orientation.