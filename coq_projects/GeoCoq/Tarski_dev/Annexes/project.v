(* Gabriel Braun March 2013 *)

Require Export GeoCoq.Tarski_dev.Annexes.vectors.

Section Projections.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Lemma project_id : forall A B X Y P P', Proj P P' A B X Y -> Col A B P -> P = P'.
Proof.
intros.
unfold Proj in H.
spliter.
induction H4.

apply False_ind.
apply H2.

induction(eq_dec_points P' A).
subst P'.
eapply  (par_col_par_2 _ P); Col.
Par.

eapply (par_col_par_2 _ P'); Col.
apply par_left_comm.
eapply (par_col_par_2 _ P); Col.
ColR.
Par.
assumption.
Qed.

Lemma project_not_id : forall A B X Y P P', Proj P P' A B X Y -> ~Col A B P -> P <> P'.
Proof.
intros.
intro.
apply H0.
subst P'.
unfold Proj in H.
spliter.
assumption.
Qed.

Lemma project_col : forall A B X Y P , Proj P P A B X Y -> Col A B P.
Proof.
intros.
unfold Proj in H.
spliter.
assumption.
Qed.

Lemma project_not_col : forall A B X Y P P', Proj P P' A B X Y -> P <> P' -> ~Col A B P.
Proof.
intros.
intro.
apply H0.
eapply project_id.
apply H.
assumption.
Qed.

Lemma project_par : forall A B X Y P Q P' Q', Proj P P' A B X Y -> Proj Q Q' A B X Y -> Par P Q X Y -> P' = Q'.
Proof.
intros.
assert(HH:=H).
assert(HH0:=H0).
unfold Proj in HH.
unfold Proj in HH0.
spliter.

apply par_distincts in H1.
spliter.

induction H11.

assert(Col P P P' /\ Col Q P P').
apply(parallel_uniqueness X Y P P' P Q P); Col.
Par.
Par.
spliter.

apply par_distincts in H11.
spliter.

induction H6.

assert(Col P Q Q' /\ Col Q Q Q').
apply(parallel_uniqueness X Y Q Q' P Q Q); Col.
Par.
Par.
spliter.

clean_duplicated_hyps.
clear H14.
clear H19.

apply par_distincts in H6.
spliter.

eapply (l6_21 A B P Q); Col.
intro.
apply H16.
apply(project_id A B X Y P P'); Col.

subst Q'.

eapply (l6_21 A B P Q); Col.
intro.
apply H16.
apply(project_id A B X Y P P'); Col.

induction H6.
apply par_distincts in H6.
spliter.

assert(Col P Q Q' /\ Col Q Q Q').
apply(parallel_uniqueness X Y Q Q' P Q Q); Col.
Par.
Par.
spliter.
clear H17.

subst P'.
eapply (l6_21 A B Q P); Col.
intro.
apply H14.
apply(project_id A B X Y Q Q'); Col.

subst P'.
subst Q'.

apply False_ind.
apply H4.

induction(eq_dec_points A P).
subst P.

eapply (par_col_par_2 _ Q); Col.

eapply (par_col_par_2 _ P); Col.
apply par_left_comm.
eapply (par_col_par_2 _ Q); Col.
ColR.
Qed.

Lemma ker_col : forall P Q P' A B X Y, Proj P P' A B X Y -> Proj Q P' A B X Y -> Col P Q P'.
Proof.
intros.
unfold Proj in *.
spliter.
clean_duplicated_hyps.
induction H8; induction H4; try(subst P';Col).
assert(Par P P' Q P').
eapply par_trans.
apply H0.
Par.
induction H2.
apply False_ind.
apply H2.
exists P'; Col.
spliter.
Col.
Qed.


Lemma ker_par : forall P Q P' A B X Y, P <> Q -> Proj P P' A B X Y -> Proj Q P' A B X Y -> Par P Q X Y.
Proof.
intros.
assert(Col P Q P').
eapply ker_col.
apply H0.
apply H1.

unfold Proj in *.
spliter.
clean_duplicated_hyps.
induction H10; induction H6.
eapply (par_col_par_2 _ P').
assumption.
Col.
assumption.
subst P'.
assumption.
subst P'.
Par.
subst P'.
apply False_ind.
apply H.
auto.
Qed.

Lemma project_uniqueness : forall P P' Q' A B X Y, Proj P P' A B X Y -> Proj P Q' A B X Y -> P' = Q'.
Proof.
intros.
assert(HH:=H).
assert(HH0:=H0).
unfold Proj in HH.
unfold Proj in HH0.
spliter.
clean_duplicated_hyps.

induction H10; induction H5.

apply par_distincts in H1.
apply par_distincts in H2.
spliter.
clear H5.

assert(Col P P P' /\ Col Q' P P').
apply(parallel_uniqueness  X Y P P' P Q' P); Col.
Par.
Par.
spliter.
clear H3.

apply (l6_21 A B P P'); Col.
intro.
apply H10.
eapply project_id.
apply H.
Col.
subst Q'.
apply sym_equal.
eapply project_id.
apply H.
Col.
subst P'.
eapply project_id.
apply H0.
Col.
subst P'.
subst Q'.
auto.
Qed.

Lemma project_existence : forall P A B X Y,
 X<>Y -> A<>B ->
 ~ Par X Y A B ->
 exists! P', Proj P P' A B X Y.
Proof.
intros.
assert (T:=parallel_existence X Y P H).
decompose [ex and] T;clear T.
assert (~ Par x x0 A B) by (
 intro;
 assert (Par X Y A B) by ( eapply par_trans;eauto; intuition);
 intuition).

apply (not_par_inter_exists x x0 A B) in H4.
DecompExAnd H4 P'.
exists P'.
unfold unique.


assert (Proj P P' A B X Y).
unfold Proj.
repeat split.
assumption.
assumption.
Par.
Col.
induction (eq_dec_points P P').
tauto.
left.
apply par_symmetry.
apply par_col2_par with x x0;Col.

split.
assumption.

intros.
eapply project_uniqueness;eauto.
Qed.

Lemma project_col_eq : forall P Q P' Q' A B X Y,
 P <> P' ->
 Col P Q P' ->
 Proj P P' A B X Y ->
 Proj Q Q' A B X Y ->
 P' = Q'.
Proof.
intros.
induction(eq_dec_points P Q).
subst Q.
eapply project_uniqueness.
apply H1.
apply H2.
eapply project_par.
apply H1.
apply H2.
unfold Proj in *.
spliter.
induction H11; induction H7.
eapply (par_col_par_2 _ P'); Col.
subst Q'.
eapply (par_col_par_2 _ P'); Col.
contradiction.
contradiction.
Qed.


Lemma par_col_project :
 forall P P' A B X Y ,
  A <> B ->
  ~ Par A B X Y ->
  Par P P' X Y ->
  Col A B P' ->
  Proj P P' A B X Y.
Proof.
intros.
apply par_distincts in H1.
spliter.
unfold Proj.
repeat split;auto.
Qed.


Lemma project_preserves_bet :
 forall A B X Y P Q R P' Q' R',
  Bet P Q R ->
  Proj P P' A B X Y ->
  Proj Q Q' A B X Y ->
  Proj R R' A B X Y ->
  Bet P' Q' R'.
Proof.
intros.
assert(HH0:= H0).
assert(HH1:=H1).
assert(HH2:=H2).
unfold Proj in HH0.
unfold Proj in HH1.
unfold Proj in HH2.
spliter.
clean_duplicated_hyps.

assert(Col P' Q' R').
apply (col3 A B); Col.

induction(eq_dec_points P Q).
assert(P' = Q').
subst Q.
eapply project_uniqueness.
apply H0.
assumption.
subst Q'.
Between.

induction (eq_dec_points R Q).
assert(R'=Q').
subst Q.
eapply project_uniqueness.
apply H2.
assumption.
subst Q'.
Between.

induction(eq_dec_points P' Q').
subst Q'.
Between.
induction(eq_dec_points R' Q').
subst Q'.
Between.

induction H17.
apply par_distincts in H10.
spliter.

induction H12.
apply par_distincts in H12.
spliter.
clear H20.

assert(Par P P' Q Q').
eapply par_trans.
apply H10.
Par.

assert(Par_strict  Q Q' P P').
induction H20.
apply par_strict_symmetry.
assumption.
spliter.
assert(Q'=P').

apply (project_col_eq Q P Q' P' A B X Y); Col.
subst Q'.
tauto.

assert(OS  Q Q' P P').

eapply (par_strict_one_side).
apply H21.
Col.

induction H7.
assert(Par R R' Q Q').
eapply par_trans.
apply H7.
Par.
assert(Par_strict Q Q' R R' ).
induction H23.
apply par_strict_symmetry.
assumption.
spliter.
assert(Q'=R').

apply(project_col_eq Q R Q' R' A B X Y); Col.
subst Q'.
tauto.
assert(OS Q Q' R R').
eapply (par_strict_one_side).
apply H24.
Col.

assert(TS Q Q' P R).
repeat split.
auto.
intro.
apply H21.
exists P.
split; Col.
intro.
apply H24.
exists R.
split; Col.
exists Q.
split; Col.

assert(TS Q Q' P' R').
eapply l9_8_2.
2: apply H22.
apply l9_2.
eapply l9_8_2.
apply l9_2.
apply H26.
assumption.

unfold TS in H27.
spliter.
ex_and H29 QQ.

assert(QQ=Q').
assert(Col P' QQ R').
apply bet_col.
assumption.
eapply (l6_21 Q Q' P' R'); Col.

intro.
subst R'.
apply between_equality in H30.
subst QQ.
contradiction.
Between.
subst QQ.
assumption.

subst R'.

assert(TS Q Q' P' R).

eapply l9_8_2.
2:apply H22.
repeat split; Col.
intro.
assert(Q'=P').
eapply project_col_eq.
apply H19.
2: apply H1.
2:apply H0.
Col.
subst Q'.
tauto.
intro.
assert(Q' = R).
eapply project_col_eq.
apply H19.
2:apply H1.
2:apply H2.
Col.
subst Q'.
tauto.
exists Q.
split; Col.
unfold TS in H7.
spliter.
ex_and H24 QQ.

assert(QQ=Q').
assert(Col P' QQ R).
apply bet_col.
assumption.
eapply (l6_21 Q Q' P' R); Col.

intro.
subst R.
apply between_equality in H25.
subst QQ.
contradiction.
Between.
subst QQ.
assumption.
subst Q'.

induction H7.

assert(HH:=parallel_existence X Y Q H14).
ex_and HH Qx.
ex_and H12 Qy.

assert(Par Qx Qy P P').
eapply par_trans.
apply par_symmetry.
apply H19.
Par.

assert(Par_strict Qx Qy P P').
induction H21.
assumption.
spliter.
assert(P' = Q).

induction(eq_dec_points Qx Q).
subst Qx.

eapply(project_col_eq P Qy P' Q A B X Y); Col.
apply par_col_project; auto.
apply par_left_comm.
Par.

eapply(project_col_eq P Qx P' Q A B X Y); Col.
apply par_col_project; auto.

eapply (par_col_par_2 _ Qy); Col.
Par.
contradiction.
assert(OS Qx Qy P P').
eapply (par_strict_one_side _ _ _ P'); Col.

assert(Par Qx Qy R R').
eapply par_trans.
apply par_symmetry.
apply H19.
Par.

assert(Par_strict Qx Qy R R').
induction H24.
assumption.
spliter.
assert(R' = Q).

induction(eq_dec_points Qx Q).
subst Qx.

eapply(project_col_eq R Qy R' Q A B X Y); Col.
apply par_col_project; auto.
apply par_left_comm.
Par.

eapply(project_col_eq R Qx R' Q A B X Y); Col.
apply par_col_project; auto.

eapply (par_col_par_2 _ Qy); Col.
Par.
contradiction.
assert(OS Qx Qy R R').
eapply (par_strict_one_side _ _ _ R'); Col.

assert(TS Qx Qy P R).
unfold TS.
repeat split.
auto.
intro.
apply H22.
exists P.
split; Col.
intro.
apply H25.
exists R.
split; Col.
exists Q.
split; Col.

assert(TS Qx Qy P' R').
eapply l9_8_2.
2:apply H23.
apply l9_2.
eapply l9_8_2.
eapply l9_2.
apply H27.
assumption.
unfold TS in H28.
spliter.
ex_and H30 QQ.

assert(QQ=Q).

assert(Col P' QQ R').
apply bet_col.
assumption.
eapply (l6_21 Qx Qy P' R'); Col.

intro.
subst R'.
apply between_equality in H31.
subst QQ.
contradiction.
Between.
subst QQ.
assumption.


subst R'.

apply False_ind.
assert(~ Col A B P).
eapply project_not_col.
apply H0.
assumption.
apply H7.

assert(Col A Q R).
ColR.
assert(Col B Q R).
ColR.

apply bet_col in H.
apply (col3 Q R); Col.
subst P'.

induction H12.
induction H7.

apply par_distincts in H10.
apply par_distincts in H7.
spliter.

assert(Par Q Q' R R').
eapply par_trans.
apply H10.
Par.
assert(Par_strict Q Q' R R').
induction H20.
assumption.
spliter.
apply False_ind.
apply H9.
eapply (project_col_eq R Q _ _ A B X Y); Col.
assert(OS Q Q' R R').
eapply (par_strict_one_side _ _ _ R'); Col.

assert(TS Q Q' P R').
apply l9_2.
eapply l9_8_2.
2:apply H22.
repeat split; Col.
intro.
assert(Q'=R').
eapply (project_col_eq Q R _ _ A B X Y); Col.
auto.
intro.
assert(Q' = P).
eapply (project_col_eq Q P _ _ A B X Y); Col.
auto.
exists Q.
split; Col.
Between.

unfold TS in H23.
spliter.
ex_and H25 QQ.

assert(QQ=Q').
assert(Col P QQ R').
apply bet_col.
assumption.
eapply (l6_21 Q Q' P R'); Col.

intro.
subst P.
apply between_equality in H26.
subst QQ.
contradiction.
Between.
subst QQ.
assumption.

subst R'.
apply par_distincts in H10.
spliter.
assert(Q' = Q).

eapply (l6_21 P R Q Q'); Col.
assert_cols.
intro.
assert(~Col A B Q).
eapply project_not_col.
apply H1.
auto.
assert(Col A P R).
ColR.
assert(Col B P R).
ColR.
apply H19.
eapply (col3 P R); Col.
intro.
subst R.
apply between_identity in H.
contradiction.
subst Q'.
assumption.
subst Q'.
induction H7.

apply par_distincts in H7.
spliter.

assert(R = R').

eapply (l6_21 P Q R R'); Col.
apply bet_col in H.
Col.
intro.
assert(~Col A B R).
eapply project_not_col.
apply H2.
auto.
assert(Col A P Q).
ColR.
assert(Col B P Q).
ColR.
apply H18.
eapply (col3 P Q); Col.
contradiction.
subst R'.
assumption.
Qed.

Lemma triangle_par :
 forall A B C A' B' C',
 ~ Col A B C ->
  Par A B A' B' ->
  Par B C B' C' ->
  Par A C A' C' ->
 CongA A B C A' B' C'.
Proof.
intros.

assert(HH:=midpoint_existence B B').
ex_and HH M.
prolong A' M A'' A' M.
prolong C' M C'' C' M.

assert(Midpoint M A' A'')
 by (split;Cong).
assert(Midpoint M C' C'')
 by (split;Cong).

assert(A' <> B').
intro.
subst A'.
apply par_distincts in H0.
spliter.
tauto.

assert(C' <> B').
intro.
subst C'.
apply par_distincts in H1.
spliter.
tauto.

assert(Par B' C' B C'').
apply (l12_17 _ _ _ _ M); Midpoint.

assert(Col B B C /\ Col C'' B C).
apply(parallel_uniqueness B' C' B C B C'' B); Col.
Par.

assert(Par B' A' B A'').
apply (l12_17 _ _ _ _ M); Midpoint.
assert(Col B B A /\ Col A'' B A).
apply(parallel_uniqueness B' A' B A B A'' B); Col.
apply par_symmetry.
apply par_comm.
assumption.

spliter.
clear H13.
clear H15.

assert(CongA A' B' C' A'' B C'').

apply (symmetry_preserves_conga _ _ _ _ _ _ M); Midpoint.
eapply conga_trans.
2: apply conga_sym.
2:apply H13.

show_distinct B A''.
assert_diffs;intuition.

show_distinct B C''.
assert_diffs;intuition.

assert(A <> B).
apply par_distincts in H0.
tauto.
assert(B <> C).
apply par_distincts in H1.
tauto.

assert(Par A C A'' C'').
eapply par_trans.
apply H2.
eapply (l12_17 _ _ _ _ M); Midpoint.

intro.
subst C'.
apply par_distincts in H2.
tauto.

apply par_distincts in H21.
spliter.


induction H17.
assert(Par_strict A C A'' C'').
induction H21.
assumption.
spliter.
apply False_ind.
apply H.

assert(C <> C'').
intro.
subst C''.
apply between_identity in H17.
subst C.
tauto.

assert(Col A C C'').
ColR.
apply bet_col in H17.
apply (col3 C C''); Col.

induction H16.

apply(l11_14 A B C A'' C''); Between.

apply False_ind.

induction (eq_dec_points A A'').
subst A''.
apply H24.
exists A.
split; Col.

induction H16.

assert(TS A C A'' B).
repeat split; Col.
intro.
apply H.
apply bet_col in H16.
apply bet_col in H17.
eapply (col3 A A''); Col.
exists A.
split; Col.
Between.

assert(OS A C B C'').
eapply (out_one_side_1 _ _ _ _ C); Col.
unfold Out.
repeat split; auto.
intro.
subst C''.
apply between_identity in H17.
subst C.
tauto.
left.
Between.
assert(TS A C A'' C'').
apply l9_2.
eapply l9_8_2.
apply l9_2.
apply H26.
assumption.
unfold TS in H28.
spliter.
ex_and H30 T.
apply H24.
exists T.
apply bet_col in H31.
split; Col.

assert(TS A'' C'' A B).
repeat split; Col.
intro.
apply H.
apply bet_col in H16.
apply bet_col in H17.

assert(Col A'' C'' B).
ColR.
assert(Col A'' C'' C).
ColR.
eapply (col3 A'' C''); Col.

intro.
apply bet_col in H16.
apply bet_col in H17.
apply H.

assert(Col B C A'').
ColR.
apply (col3 B A''); Col.

exists A''.
split; Col.

assert(OS A'' C'' B C).
apply out_one_side_1 with C''; Col.
intro.
apply H.


apply bet_col in H16.
apply bet_col in H17.
assert(Col A'' B C).
ColR.
apply (col3 A'' B); Col.
repeat split; auto.
intro.
subst.
unfold Par_strict in H24.
spliter.
apply H29.
exists C''; Col.

assert(TS A'' C'' A C).
apply l9_2.
eapply l9_8_2.
apply l9_2.
apply H26.
assumption.
unfold TS in H28.
spliter.
ex_and H30 T.
apply H24.
exists T.
apply bet_col in H31.
split; Col.

induction H17.
induction H16.

assert(Par_strict A C A'' C'').
induction H21.
assumption.
spliter.
apply False_ind.
apply H.

assert(A <> A'').
intro.
subst A''.
apply between_identity in H16.
contradiction.

assert(Col C A A'').
ColR.
apply bet_col in H16.
apply (col3 A A''); Col.


apply False_ind.

induction (eq_dec_points C C'').
subst C''.
apply H24.
exists C.
split; Col.

assert(TS A C C'' B).
repeat split; Col.
intro.
apply H.
apply bet_col in H16.
apply bet_col in H17.
eapply (col3 C C''); Col.
exists C.
split; Col.
Between.

assert(OS A C B A'').
eapply (out_one_side _ _ _ _); Col.
unfold Out.
repeat split; auto.
intro.
subst A''.
apply between_identity in H16.
contradiction.
left.
Between.
assert(TS A C A'' C'').

eapply l9_8_2.
apply l9_2.
apply H26.
assumption.
unfold TS in H28.
spliter.
ex_and H30 T.
apply H24.
exists T.
apply bet_col in H31.
split; Col.

induction H16.



eapply (out_conga A B C A B C).
apply conga_refl.
auto.
auto.
apply out_trivial.
auto.
apply out_trivial.
auto.
unfold Out.
repeat split; auto.
unfold Out.
repeat split; auto.

eapply (out_conga A B C A B C).
apply conga_refl.
auto.
auto.
apply out_trivial.
auto.
apply out_trivial.
auto.
unfold Out.
repeat split; auto.
right.
Between.
unfold Out.
repeat split; auto.

induction H16.

assert(Par_strict A C A'' C'').
induction H21.
assumption.
spliter.
apply False_ind.
apply H.

assert(A <> A'').
intro.
subst A''.
apply between_identity in H16.
contradiction.

assert(Col C A A'').
ColR.
apply bet_col in H16.
apply (col3 A A''); Col.

apply False_ind.

induction (eq_dec_points C C'').
subst C''.
apply H24.
exists C.
split; Col.


assert(TS A'' C'' C B).
repeat split; Col.
intro.
apply H.
apply bet_col in H16.
apply bet_col in H17.

assert(Col A'' C'' B).
ColR.
assert(Col A'' C'' A).
ColR.
eapply (col3 A'' C''); Col.

intro.
apply bet_col in H16.
apply bet_col in H17.
apply H.

assert(Col B C A'').
ColR.
apply (col3 B A''); Col.

exists C''.
split; Col.

assert(OS A'' C'' B A).
apply out_one_side.
left.
intro.
apply H.

apply bet_col in H16.
apply bet_col in H17.
assert(Col C B A'').
ColR.
apply (col3 A'' B); Col.
repeat split; auto.

intro.
subst.
unfold Par_strict in H24.
spliter.
apply H29.
exists A''.
Col.

assert(TS A'' C'' A C).
eapply l9_8_2.
apply l9_2.
apply H26.
assumption.
unfold TS in H28.
spliter.
ex_and H30 T.
apply H24.
exists T.
apply bet_col in H31.
split; Col.

induction H16.

eapply (out_conga A B C A B C).
apply conga_refl.
auto.
auto.
apply out_trivial.
auto.
apply out_trivial.
auto.
unfold Out.
repeat split; auto.
unfold Out.
repeat split; auto.
right.
Between.

eapply (out_conga A B C A B C).
apply conga_refl.
auto.
auto.
apply out_trivial.
auto.
apply out_trivial.
auto.
unfold Out.
repeat split; auto.
right.
Between.
unfold Out.
repeat split; auto.
right.
Between.
Qed.

Lemma par3_conga3 :
 forall A B C A' B' C',
 ~ Col A B C ->
 Par A B A' B' ->
 Par B C B' C' ->
 Par A C A' C' ->
 CongA_3 A B C A' B' C'.
Proof.
intros.
unfold CongA_3.
split.
apply triangle_par; auto.
split.
apply triangle_par.
intro.
apply H.
Col.
auto.
apply par_comm.
auto.
apply par_comm.
auto.
apply triangle_par.
intro.
apply H.
Col.
apply par_comm.
auto.
auto.
apply par_comm.
auto.
Qed.

Lemma cong_conga3_cong3 :
 forall A B C A' B' C',
 ~ Col A B C ->
 Cong A B A' B' ->
 CongA_3 A B C A' B' C' ->
 Cong_3 A B C A' B' C'.
Proof.
intros.
unfold CongA_3 in H1.
spliter.
assert(Cong A C A' C' /\ Cong B C B' C' /\ CongA C A B C' A' B').
apply( l11_50_2 A B C A' B' C' H); auto.
spliter.
repeat split; auto.
Qed.

Lemma project_par_eqv :
 forall P P' Q Q' A B X Y,
 Proj P P' A B X Y ->
 Proj Q Q' A B X Y ->
 Par P Q A B ->
 EqV P Q P' Q'.
Proof.
intros.
assert(HH:=H).
assert(HH0:=H0).
unfold Proj in HH.
unfold Proj in HH0.
spliter.
unfold EqV.
apply par_distincts in H1.
spliter.

left.
induction H1.

induction H6; induction H11.
assert(Par P P' Q Q').
eapply par_trans.
apply H11.
Par.

assert(Par P' Q' A B ).
right.
repeat split; Col.
intro.
subst Q'.

induction H14.
apply H14.
exists P'.
split; Col.
spliter.

apply H1.
exists P'.
split; Col.

clean_duplicated_hyps.

assert(Par P Q P' Q').
eapply par_trans.
left.
apply H1.
Par.

assert(Par_strict P Q P' Q').
apply par_symmetry in H2.
induction H2.
apply par_strict_symmetry.
assumption.
spliter.
apply False_ind.
apply H1.
exists P'.
split; Col.

apply plg_to_parallelogram.
apply pars_par_plg; auto.
apply par_strict_right_comm.
assumption.

subst P'.
apply False_ind.
apply H1.
exists P.
split; Col.
subst Q'.
apply False_ind.
apply H1.
exists Q.
split; Col.
subst P'.
subst Q'.
apply plg_trivial.
assumption.

spliter.
assert(P = P' /\ Q = Q').
split; eapply (project_id A B X Y); Col.
spliter.
subst P'.
subst Q'.
apply plg_trivial.
assumption.
Qed.



Lemma eqv_project_eq_eq :
 forall P Q R S P' Q' S' A B X Y,
  EqV P Q R S ->
  Proj P P' A B X Y ->
  Proj Q Q' A B X Y ->
  Proj R P' A B X Y ->
  Proj S S' A B X Y ->
  Q' = S'.
Proof.
intros.
spliter.

induction(eq_dec_points P Q).
subst Q.
apply null_vector in H.
subst S.

assert(Q' = P').
eapply project_uniqueness.
apply H1.
assumption.
subst Q'.

eapply project_uniqueness.
apply H2.
assumption.

assert(R <> S).
intro.
subst S.
apply H4.
eapply null_vector.
apply eqv_sym in H.
apply H.
assert(EqV P R Q S).
apply eqv_permut.
assumption.

induction(eq_dec_points P R).
subst R.
apply null_vector in H6.
subst S.
eapply project_uniqueness.
apply H1.
assumption.

assert( Q <> S).
intro.
subst S.
apply eqv_sym in H6.
apply null_vector in H6.
contradiction.

eapply project_par.
apply H1.
apply H3.

eapply par_trans.
apply par_symmetry.
apply eqv_par in H6; auto.
apply H6.
unfold Proj in H0.
unfold Proj in H2.
spliter.
induction H16; induction H12.

assert(Col R P P' /\ Col P' P P').

apply(parallel_uniqueness X Y P P' R P' P'); Col.
Par.
Par.
spliter.
clear H18.

eapply (par_col_par_2 _ P'); Col.
subst P'.
assumption.
subst P'.
Par.
subst P'.
subst R.
tauto.
Qed.


Lemma eqv_eq_project :
  forall P Q R S P' Q' A B X Y,
  EqV P Q R S ->
  Proj P P' A B X Y ->
  Proj Q Q' A B X Y ->
  Proj R P' A B X Y ->
  Proj S Q' A B X Y.
Proof.
intros.
assert(HH1:=H1).
unfold Proj in HH1.
spliter.
repeat split; Col.
apply eqv_permut in H.

induction(eq_dec_points S Q').
right.
assumption.
left.

induction(eq_dec_points P R).
subst R.
apply null_vector in H.
subst S.
unfold Proj in H1.
spliter.
induction H11.
assumption.
contradiction.

apply eqv_par in H; auto.

assert(Col P R P').
eapply ker_col.
apply H0.
assumption.

unfold Proj in H0.
spliter.

induction H14.
assert(Par P R X Y).
apply (par_col_par_2 _ P'); Col.

induction H7.

assert(Col Q Q Q' /\ Col S Q Q').
apply(parallel_uniqueness X Y Q Q' Q S Q); Col.
Par.
eapply par_trans.
2: apply H.
Par.
spliter.
apply par_left_comm.
eapply (par_col_par_2 _ Q); Col.
Par.

subst Q'.
eapply par_trans.
apply par_left_comm.
apply par_symmetry.
apply H.
assumption.
subst P'.

assert(Par P R X Y).
unfold Proj in H2.
spliter.
induction H17.
Par.
subst R.
tauto.


induction H7.
assert(Col Q Q Q' /\ Col S Q Q').
apply(parallel_uniqueness X Y Q Q' Q S Q); Col.
Par.
eapply par_trans.
apply par_symmetry.
apply H14.
assumption.
spliter.
apply (par_col_par_2 _ Q); Col.
eapply par_trans.
apply par_left_comm.
apply par_symmetry.
apply H.
assumption.
subst Q'.
eapply par_trans.
apply par_symmetry.
apply par_right_comm.
apply H.
assumption.
Qed.


Lemma project_par_dir : forall P P' A B X Y, P <> P' -> Proj P P' A B X Y -> Par P P' X Y.
intros.
unfold Proj in H0.
spliter.
induction H4; tauto.
Qed.

Lemma project_idem : forall P P' A B X Y, Proj P P' A B X Y -> Proj P' P' A B X Y.
intros.
unfold Proj in *.
spliter.
repeat split; Col.
Qed.

Lemma eqv_cong : forall A B C D, EqV A B C D -> Cong A B C D.
intros.
unfold EqV in H.
induction H.
apply plg_cong.
apply plg_permut.
apply plg_comm2.
assumption.
spliter.
subst B.
subst D.
Cong.
Qed.

Lemma project_preserves_eqv :
 forall P Q R S P' Q' R' S' A B X Y, EqV P Q R S ->
  Proj P P' A B X Y ->
  Proj Q Q' A B X Y ->
  Proj R R' A B X Y ->
  Proj S S' A B X Y ->
  EqV P' Q' R' S'.
Proof.
intros.

induction (eq_dec_points P Q).
subst Q.
apply null_vector in H.
subst S.
assert(R'=S').
eapply project_uniqueness.
apply H2.
apply H3.
subst S'.
assert(P' = Q').
eapply project_uniqueness.
apply H0.
apply H1.
subst Q'.
apply eqv_trivial.

assert(R <> S).
intro.
subst S.
apply eqv_sym in H.
apply null_vector in H.
contradiction.

induction (par_dec P Q A B).

assert(EqV P Q P' Q').
eapply project_par_eqv.
apply H0.
assumption.
assumption.

assert(EqV R S R' S').
eapply project_par_eqv.
apply H2.
assumption.

eapply par_trans.
apply par_symmetry.
apply eqv_par.
apply H4.
assumption.
assumption.
eapply eqv_trans.
apply eqv_sym.
apply H7.
eapply eqv_trans.
apply H.
assumption.

induction (par_dec P Q X Y).
assert(P' = Q').
eapply project_par.
apply H0.
apply H1.
assumption.

assert(Par R S X Y).
apply eqv_par in H; auto.
eapply par_trans.
apply par_symmetry.
apply H.
assumption.
assert(R' = S').
eapply project_par.
apply H2.
apply H3.
assumption.
subst Q'.
subst S'.
apply eqv_trivial.

assert(P' <> Q').
intro.
subst Q'.
apply H7.
eapply (ker_par P Q P' A B); auto.

assert(~ Par R S X Y).
intro.
apply H7.
apply eqv_par in H; auto.
eapply par_trans.
apply H.
assumption.

assert(R' <> S').
intro.
subst S'.
apply H9.
eapply (ker_par R S R' A B); auto.


assert(HH1:= vector_construction P Q P').
ex_and HH1 Q''.
assert(HH1:= vector_construction R S R').
ex_and HH1 S''.

assert(EqV P' Q'' R' S'').
eapply eqv_trans.
apply eqv_sym.
apply H11.
eapply eqv_trans.
apply H.
assumption.

assert(Q' <> Q'').
intro.
apply H6.
subst Q''.
apply eqv_par in H; auto.
apply eqv_par in H11; auto.
apply eqv_par in H12; auto.
assert(P' <> Q').
intro.
subst Q'.
apply par_distincts in H11.
tauto.
apply eqv_par in H13; auto.
assert(Par P' Q' A B).
right.
unfold Proj in *.
spliter.
repeat split; Col.

eapply par_trans.
apply H.
eapply par_trans.
apply H12.
eapply par_trans.
apply par_symmetry.
apply H13.
assumption.

assert(S' <> S'').
intro.
subst S''.
apply eqv_par in H; auto.
apply eqv_par in H11; auto.
apply eqv_par in H12; auto.
assert(R' <> S').
intro.
subst S'.
apply par_distincts in H12.
tauto.
apply eqv_par in H13; auto.
assert(Par R' S' A B).
right.
unfold Proj in *.
spliter.
repeat split; Col.
apply H6.

eapply par_trans.
apply H.
eapply par_trans.
apply H12.
assumption.
intro.
subst Q''.
apply null_vector in H13.
subst S'.
tauto.

assert(HP1:=eqv_permut P Q P' Q'' H11).
assert(HP2:=eqv_permut R S R'  S'' H12).
assert(HP3:=eqv_permut P' Q'' R'  S'' H13).

assert(Proj Q'' Q' A B X Y).
eapply eqv_eq_project.
apply H11.
apply H0.
assumption.
eapply project_idem.
apply H0.

assert(Proj S'' S' A B X Y).
eapply eqv_eq_project.
apply H12.
apply H2.
assumption.
eapply project_idem.
apply H2.
assert(HH1:= H16).
assert(HH2:= H17).
eapply project_par_dir in HH1; auto.
apply project_par_dir in HH2; auto.

assert(Par Q'' Q' S'' S').
eapply par_trans.
apply HH1.
Par.
assert(~ Col A B Q'').
apply(project_not_col A B X Y Q'' Q' H16).
auto.
assert(~ Col P' Q'' Q').
intro.
apply H19.
unfold Proj in *.
spliter.
assert(Col P' Q' A).
ColR.
assert(Col P' Q' B).
ColR.
apply (col3 P' Q'); Col.

assert(Cong_3 P' Q'' Q' R' S'' S').
eapply cong_conga3_cong3.
assumption.

apply eqv_cong.
assumption.

eapply par3_conga3.
assumption.
apply eqv_par.
intro.
subst Q''.
apply H20.
Col.
assumption.
assumption.
right.
unfold Proj in *.
spliter.
repeat split; try assumption.

apply (col3 A B); Col.
apply (col3 A B); Col.

assert(EqV Q'' Q' S'' S').
unfold EqV.
left.

induction(eq_dec_points Q' S').
subst S'.

assert(P' = R').

apply (eqv_project_eq_eq Q'' P' S'' R' Q' P' R' A B X Y); auto.
apply eqv_comm.
assumption.
eapply project_idem.
apply H0.
eapply project_idem.
apply H2.
subst R'.
apply null_vector in HP3.
subst S''.
apply plg_trivial.
auto.


induction(eq_dec_points P' R').
subst R'.
apply null_vector in  HP3.
subst S''.

assert(Q' = S').
eapply eqv_project_eq_eq.
apply H13.
2:apply H16.
eapply project_idem.
apply H0.
eapply project_idem.
apply H0.
assumption.
subst S'.
apply plg_trivial.
auto.

apply plg_to_parallelogram.
unfold Plg.

split.
left.
intro.
subst Q''.
apply H19.
unfold Proj in *.
spliter.
Col.

eapply par_cong_mid_os.
induction H18.
assumption.
spliter.
apply False_ind.

assert(~ Col A B S'').
apply(project_not_col A B X Y S'' S' H17).
auto.

apply H27.

unfold Proj in *.
spliter.
assert(Col Q' S' A).
ColR.
assert(Col Q' S' B).
ColR.
apply (col3 Q' S'); Col.
unfold Cong_3 in H21.
spliter.
Cong.
unfold EqV in H13.
induction H13.

apply plg_permut in H13.

assert(Parallelogram_strict  R' P' Q'' S'').
apply plg_sym in H13.
induction H13.
assumption.
unfold Parallelogram_flat in H13.
spliter.
apply False_ind.
apply H19.

unfold Proj in *.
spliter.

assert(Col P' R' A).
ColR.
assert(Col P' R' B).
ColR.
apply (col3 P' R'); Col.

assert(HH:= plgs_par_strict R' P' Q'' S'' H24).
spliter.

assert(Par_strict Q'' S'' Q' S').
eapply par_strict_col2_par_strict.
auto.
apply par_strict_symmetry.
apply H25.
unfold Proj in *.
spliter.
apply (col3 A B); Col.
unfold Proj in *.
spliter.
apply (col3 A B); Col.
apply l12_6.
assumption.

spliter.
subst Q''.
apply False_ind.
apply H20.
Col.

eapply eqv_sum.
apply H13.
assumption.
Qed.

Lemma perp_projp : forall P P' A B, Perp_at P' A B P P' -> Projp P P' A B.
intros.
unfold Projp.
split.
apply l8_14_2_1a in H.
apply perp_not_eq_1 in H.
assumption.
left.
split.
apply perp_in_col in H.
spliter.
assumption.
apply l8_14_2_1a in H.
assumption.
Qed.

Lemma proj_distinct : forall P P' A B, Projp P P' A B -> P' <> A \/ P' <> B.
intros.
unfold Projp in H.
spliter.
induction H0.
spliter.
induction(eq_dec_points P' A).
subst P'.
right.
apply perp_not_eq_1 in H1.
assumption.
left.
assumption.
spliter.

subst P'.
induction(eq_dec_points P A).
subst P.
right.
assumption.
left.
assumption.
Qed.

Lemma projp_is_project :
 forall P P' A B,
  Projp P P' A B ->
  exists X, exists Y, Proj P P' A B X Y.
Proof.
intros.

assert(A <> B).
unfold Projp in H.
tauto.
assert(HH:=perp_vector A B H0).
ex_and HH X.
ex_and H1 Y.
exists X.
exists Y.

assert(X <> Y).
apply perp_not_eq_2 in H2.
assumption.

unfold Proj.
repeat split; auto.
apply perp_not_par.
assumption.
unfold Projp in H.
spliter.
induction H3.
tauto.
spliter.
subst P'.
assumption.

unfold Projp in H.
spliter.
induction H3.
spliter.
left.
eapply l12_9_2D.
apply perp_sym.
apply H4.
Perp.
right.
tauto.
Qed.

Lemma projp_is_project_perp :
 forall P P' A B,
 Projp P P' A B ->
 exists X, exists Y, Proj P P' A B X Y /\ Perp A B X Y.
Proof.
intros.

assert(A <> B).
unfold Projp in H.
tauto.
assert(HH:=perp_vector A B H0).
ex_and HH X.
ex_and H1 Y.
exists X.
exists Y.

assert(X <> Y).
apply perp_not_eq_2 in H2.
assumption.
split.

unfold Proj.
repeat split; auto.
apply perp_not_par.
assumption.
unfold Projp in H.
spliter.
induction H3.
tauto.
spliter.
subst P'.
assumption.

unfold Projp in H.
spliter.
induction H3.
spliter.
left.
eapply l12_9_2D.
apply perp_sym.
apply H4.
Perp.
right.
tauto.
assumption.
Qed.

Lemma projp_to_project :
 forall P P' A B X Y,
  Perp A B X Y ->
  Projp P P' A B ->
  Proj P P' A B X Y.
Proof.
intros.
unfold Proj.

repeat split.
eapply perp_not_eq_1.
apply H.
eapply perp_not_eq_2.
apply H.
apply perp_not_par.
assumption.
unfold Projp in H0.
spliter.
induction H1.
spliter.
assumption.
spliter.
subst P'.
assumption.
unfold Projp in H0.
spliter.
induction H1.
spliter.
left.
eapply l12_9_2D.
apply perp_sym.
apply H2.
Perp.
spliter.
right.
assumption.
Qed.

Lemma project_to_projp :
 forall P P' A B X Y,
  Proj P P' A B X Y ->
  Perp A B X Y ->
  Projp P P' A B.
Proof.
intros.
unfold Proj in H.
spliter.
unfold Projp.
split.
apply perp_not_eq_1 in H0.
assumption.
induction H4.
left.
split.
assumption.
apply perp_sym.

eapply par_perp__perp.
apply par_symmetry.
apply H4.
Perp.
right.
subst P'.
split; auto.
Qed.

Lemma projp_project_to_perp :
 forall P P' A B X Y,
 P <> P' ->
 Projp P P' A B ->
 Proj P P' A B X Y ->
 Perp A B X Y.
Proof.
intros.
unfold Projp in H0.
unfold Proj in H1.
spliter.
induction H6;
induction H5.
spliter.
apply perp_sym.
eapply par_perp__perp.
apply H5.
Perp.
contradiction.
spliter.
contradiction.
contradiction.
Qed.

Lemma project_par_project :
 forall P P' A B X Y X' Y',
  Proj P P' A B X Y ->
  Par X Y X' Y' ->
  Proj P P' A B X' Y'.
Proof.
intros.
unfold Proj in *.
spliter.
apply par_distincts in H0.
spliter.
repeat split; Col.
intro.
apply H2.
eapply par_trans.
apply H7.
Par.
induction H4.
left.
eapply par_trans.
apply H4.
assumption.
right.
assumption.
Qed.

Lemma project_project_par :
 forall P P' A B X Y X' Y',
 P <> P' ->
 Proj P P' A B X Y ->
 Proj P P' A B X' Y' ->
 Par X Y X' Y'.
Proof.
intros.
unfold Proj in *.
spliter.
induction H9;
induction H5;
try contradiction.

eapply par_trans.
apply par_symmetry.
apply H9.
assumption.
Qed.

Lemma projp_id : forall P P' Q' A B, Projp P P' A B -> Projp P Q' A B -> P' = Q'.
intros.
unfold Projp in *.
spliter.
induction H1; induction H2.
spliter.
apply (l8_18_uniqueness A B P); Col.
apply perp_not_col2 in H4.
induction H4.
assumption.
contradiction.
spliter.
subst P'.
apply perp_not_col2 in H3.

induction H3; contradiction.
spliter.
subst Q'.
apply perp_not_col2 in H4.
induction H4; contradiction.
spliter.
subst P'.
subst Q'.
auto.
Qed.

Lemma projp_preserves_bet :
 forall A B C A' B' C' X Y,
  Bet A B C ->
  Projp A A' X Y ->
  Projp B B' X Y ->
  Projp C C' X Y ->
  Bet A' B' C'.
Proof.
intros.

eapply projp_is_project_perp in H0.
ex_and H0 T.
ex_and H3 U.

eapply (project_preserves_bet X Y T U A B C A' B' C').
apply H.
assumption.
eapply projp_to_project in H1.
apply H1.
assumption.
eapply projp_to_project in H2.
apply H2.
assumption.
Qed.


Lemma projp_preserves_eqv :
 forall A B C A' B' C' D D' X Y,
 EqV A B C D ->
 Projp A A' X Y ->
 Projp B B' X Y ->
 Projp C C' X Y ->
 Projp D D' X Y ->
 EqV A' B' C' D'.
Proof.
intros.

eapply projp_is_project_perp in H0.
ex_and H0 T.
ex_and H4 U.

eapply (project_preserves_eqv A B C D A' B' C' D' X Y T U).
apply H.
assumption.
eapply projp_to_project in H1.
apply H1.
auto.
eapply projp_to_project in H2.
apply H2.
auto.
eapply projp_to_project in H3.
apply H3.
auto.
Qed.

Lemma projp_idem : forall P P' A B,
 Projp P P' A B ->
 Projp P' P' A B.
Proof.
intros.
unfold Projp in *.
spliter.
split.
auto.
induction H0.
right.
spliter.
split.
assumption.
auto.
right.
spliter.
subst P'.
tauto.
Qed.

Lemma projp2_col : forall A B C P Q,
  Projp P A B C -> Projp Q A B C -> Col A P Q.
Proof.
intros A B C P Q H1 H2.
destruct H1 as [H1 H3]; destruct H2 as [H2 H4];
induction H3; induction H4; spliter; treat_equalities; Col.
apply perp2__col with B C; Perp.
Qed.

Lemma projp_projp_perp : forall P P1 P2 Q1 Q2,
  P1 <> P2 -> Projp P1 P Q1 Q2 -> Projp P2 P Q1 Q2 -> Perp P1 P2 Q1 Q2.
Proof.
intros P P1 P2 Q1 Q2 HP1P2 H1 H2.
destruct H1 as [H H1]; clear H; destruct H2 as [H H2]; clear H.
elim H1; clear H1; intro H1; elim H2; clear H2; intro H2;
spliter; treat_equalities; Perp; [|intuition].
apply perp_sym; apply perp_col0 with P1 P; Perp; Col.
apply col_permutation_2; apply perp2__col with Q1 Q2; Perp.
Qed.

Lemma col_projp_eq : forall A B P P', Col A B P -> Projp P P' A B -> P = P'.
Proof.
intros A B P P' HCol1 HProjp.
destruct HProjp as [HDiff HProjp]; elim HProjp; clear HProjp; intro HProjp;
[exfalso;  destruct HProjp as [HCol2 HPerp]|spliter; auto].
apply perp_not_col2 in HPerp; induction HPerp; intuition.
Qed.

Lemma projp_col : forall A B P P', Projp P P' A B -> Col A B P'.
Proof.
intros A B P P' H; destruct H as [H' H]; clear H'.
induction H; spliter; treat_equalities; Col.
Qed.

Lemma perp_projp2_eq : forall A A' B B' C D,
  Projp A A' C D ->
  Projp B B' C D ->
  Perp A B C D ->
  A' = B'.
Proof.
intros A A' B B' C D HA' HB' HPerp.
destruct HA' as [H HA']; clear H; destruct HB' as [H HB']; clear H.
elim HA'; clear HA'; intro HA'; elim HB'; clear HB'; intro HB'.

  {
  destruct HA' as [HColA' HA']; destruct HB' as [HColB' HB'].
  elim (perp_not_col2 A B C D HPerp); intro HNC.

    {
    apply l6_21 with A B C D; Col; try (intro; assert_diffs; intuition).

      {
      assert (HPar : Par A B A A')
        by (apply l12_9_2D with C D; Perp).
      elim HPar; clear HPar; intro HPar; [exfalso; apply HPar; exists A|spliter]; Col.
      }

      {
      assert (HPar : Par A B B B')
        by (apply l12_9_2D with C D; Perp).
      elim HPar; clear HPar; intro HPar; [exfalso; apply HPar; exists B|spliter]; Col.
      }
    }

    {
    apply l6_21 with A B D C; Col; try (intro; assert_diffs; intuition).

      {
      assert (HPar : Par A B A A')
        by (apply l12_9_2D with C D; Perp).
      elim HPar; clear HPar; intro HPar; [exfalso; apply HPar; exists A|spliter]; Col.
      }

      {
      assert (HPar : Par A B B B')
        by (apply l12_9_2D with C D; Perp).
      elim HPar; clear HPar; intro HPar; [exfalso; apply HPar; exists B|spliter]; Col.
      }
    }
  }

  {
  destruct HB' as [HColB H]; treat_equalities.
  apply perp_sym in HPerp; elim (perp_not_col2 C D A B HPerp);
  intro HNC; [|intuition]; destruct HA' as [HColA' HA'].
  apply l6_21 with C D A B; Col; try (intro; assert_diffs; intuition).
  assert (HPar : Par A B A A')
    by (apply l12_9_2D with C D; Perp).
  elim HPar; clear HPar; intro HPar; [exfalso; apply HPar; exists A|spliter]; Col.
  }

  {
  destruct HA' as [HColA H]; treat_equalities.
  apply perp_sym in HPerp; elim (perp_not_col2 C D A B HPerp);
  intro HNC; [intuition|]; destruct HB' as [HColB' HB'].
  apply l6_21 with C D B A; Col; try (intro; assert_diffs; intuition).
  assert (HPar : Par A B B B')
    by (apply l12_9_2D with C D; Perp).
  elim HPar; clear HPar; intro HPar; [exfalso; apply HPar; exists B|spliter]; Col.
  }

  {
  spliter; treat_equalities; apply perp_sym in HPerp;
  elim (perp_not_col2 C D A B HPerp); intuition.
  }
Qed.

Lemma col_par_projp2_eq : forall L11 L12 L21 L22 P P' P'',
  Col L11 L12 P ->
  Par L11 L12 L21 L22 ->
  Projp P P' L21 L22 -> Projp P' P'' L11 L12 ->
  P = P''.
Proof.
intros L11 L12 L21 L22 P P' P'' HCol1 HPar HP' HP''.
destruct HP' as [HDiff1 HP']; destruct HP'' as [HDiff2 HP''].
elim HP'; clear HP'; intro HP'; elim HP''; clear HP''; intro HP''.

  {
  destruct HP' as [HCol2 HPerp1]; destruct HP'' as [HCol3 HPerp2].
  assert (H : Par P P' P' P'').
    {
    apply l12_9_2D with L11 L12; Perp.
    apply perp_sym; apply par_perp__perp with L21 L22; Par.
    }
  elim H; clear H; intro H; [exfalso; apply H; exists P'; Col|].
  destruct H as [HDiff3 [HDiff4 [HCol4 H]]]; clear H.
  elim (perp_not_col2 L11 L12 P' P'' HPerp2); [intro HNC|intuition].
  apply l6_21 with L11 L12 P' P; Col.
  }

  {
  destruct HP' as [HCol2 HPerp1]; destruct HP'' as [HCol3 HPerp2]; treat_equalities.
  assert (HPerp2 : Perp L11 L12 P' P)
    by (apply par_perp__perp with L21 L22; Par; Perp).
  elim (perp_not_col2 L11 L12 P' P HPerp2); [intro HNC|intuition].
  apply l6_21 with L11 L12 P' P; Col.
  }

  {
  destruct HP' as [HCol2 HPerp1]; destruct HP'' as [HCol3 HPerp2]; treat_equalities.
  elim (perp_not_col2 L11 L12 P P'' HPerp2); [intro HNC|intuition].
  apply l6_21 with L11 L12 P P''; Col.
  }

  {
  spliter; treat_equalities; auto.
  }
Qed.

Lemma col_2_par_projp2_cong : forall A A' B B' L11 L12 L21 L22,
  Col L11 L12 A' -> Col L11 L12 B' ->
  Par L11 L12 L21 L22 ->
  Projp A' A L21 L22 -> Projp B' B L21 L22 ->
  Cong A B A' B'.
Proof.
intros A A' B B' L11 L12 L21 L22 HColA' HColB' HPar HProjpA HProjpB.
elim HPar; clear HPar; intro HPar.

  {
  elim (eq_dec_points A' B'); intro HDiffA'B'; treat_equalities;
  [assert (A = B) by (apply projp_id with A' L21 L22; auto); treat_equalities; Cong|].
  elim (eq_dec_points A B); intro HDiffAB; treat_equalities.

    {
    assert (HCol : Col A A' B') by (apply projp2_col with L21 L22; auto).
    assert (HColA : Col L21 L22 A) by (apply projp_col with A'; auto).
    exfalso; apply HDiffA'B'; apply l6_21 with L11 L12 A A'; Col; intro;
    treat_equalities; apply HPar; exists A; Col.
    }

    {
    assert (HPara : Plg A B B' A').
      {
      apply pars_par_plg.

        {
        apply par_strict_col2_par_strict with L11 L12; auto.
        apply par_strict_symmetry;
        apply par_strict_col2_par_strict with L21 L22; auto;
        [apply projp_col with A'|apply projp_col with B']; auto.
        }

        {
        unfold Projp in *.
        destruct HProjpA as [H HElim]; clear H;
        elim HElim; clear HElim; intro H; destruct H as [HColA HPerp1];
        [|exfalso; apply HPar; exists A'; Col].
        destruct HProjpB as [H HElim]; clear H;
        elim HElim; clear HElim; intro H; destruct H as [HColB HPerp2];
        [|exfalso; apply HPar; exists B'; Col].
        apply l12_9_2D with L21 L22; Perp.
        }
      }
    apply plg_to_parallelogram in HPara; apply plg_cong in HPara; spliter; Cong.
    }
  }

  {
  assert (A = A')
    by (apply eq_sym; apply col_projp_eq with L21 L22; auto; spliter; ColR).
  assert (B = B')
    by (apply eq_sym; apply col_projp_eq with L21 L22; auto; spliter; ColR).
  treat_equalities; Cong.
  }
Qed.

End Projections.
