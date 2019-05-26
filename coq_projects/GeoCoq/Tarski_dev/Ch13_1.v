  (* Gabriel Braun April 2013 *)

Require Export GeoCoq.Tarski_dev.Ch12_parallel.

Section L13_1.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** Pappus Desargues *)

Lemma per2_col_eq : forall A P P' B, A <> P -> A <> P' -> Per A P B -> Per A P' B -> Col P A P' -> P = P'.
Proof.
intros.
induction(eq_dec_points P B).
subst B.
assert( A = P' \/ P = P').
apply(l8_9 A P' P H2); Col.
induction H4.
contradiction.
assumption.
induction(eq_dec_points P' B).
subst B.
assert(A = P \/ P' = P).
apply(l8_9 A P P' H1); Col.
induction H5; auto.
contradiction.

apply per_perp_in in H1; auto.
apply per_perp_in in H2; auto.

apply perp_in_comm in H1.
apply perp_in_comm in H2.
apply perp_in_perp_bis in H1.
apply perp_in_perp_bis in H2.
induction H1; induction H2.
apply(l8_18_uniqueness P A B P P'); Col.
apply perp_not_col; auto.
apply perp_left_comm.
apply(perp_col A P' B P' P); Perp.
Col.
apply perp_distinct in H2.
tauto.
apply perp_distinct in H1.
tauto.
apply perp_distinct in H1.
tauto.
Qed.

Lemma per2_preserves_diff : forall O A B A' B', O <> A' -> O <> B' -> Col O A' B' -> Per O A' A -> Per O B' B -> A' <> B' -> A <> B.

Proof.
intros.
intro.
subst B.
apply H4.
apply(per2_col_eq O A' B' A);Col.
Qed.

Lemma per23_preserves_bet : forall A B C B' C', Bet A B C -> A <> B' -> A <> C' -> Col A B' C' -> Per A B' B -> Per A C' C -> Bet A B' C'.
Proof.
intros.
assert(HC:Col A B C).
apply bet_col in H; Col.

induction(eq_dec_points B B').
subst B'.

assert(Col A C' C).
ColR.

assert(A = C' \/ C = C').
apply l8_9; auto.
induction H6.
contradiction.
subst C'.
assumption.

assert(A <> C).
intro.
subst C.
apply l8_8 in H4.
contradiction.

assert(C <> C').
intro.
subst C'.

assert(Col A B' B).
ColR.

assert(A = B' \/ B = B').
apply l8_9; auto.
induction H8; contradiction.

assert(Perp A B' B' B).
apply per_perp_in in H3; auto.
apply perp_in_comm in H3.
apply perp_in_perp_bis in H3.
induction H3; Perp.
apply perp_distinct in H3.
tauto.

assert(Perp A C' C' C).
apply per_perp_in in H4; auto.
apply perp_in_comm in H4.
apply perp_in_perp_bis in H4.
induction H4; Perp.
apply perp_distinct in H4.
tauto.

assert(Par B B' C C').
apply(l12_9 B B' C C' A B');Perp; Cop.
apply perp_sym.
apply(perp_col _ C'); Perp.
ColR.

induction(eq_dec_points B C).
subst C.
assert(B' = C').
apply(per2_col_eq A B' C' B); Perp.
Col.
subst C'.
Between.

assert(~Col A B' B).
apply per_not_col in H3; auto.

assert(~Col A C' C).
apply per_not_col in H4; auto.

assert(B' <> C').
intro.
subst C'.
clean_trivial_hyps.

assert(Col B C B').
apply cop_per2__col with A; Perp.
exists C; left; split; Col.
apply H13; ColR.

induction H10.
apply l12_6 in H10.

assert(TS B B' A C).
repeat split;auto.
intro.
assert(A = B' \/ B = B').
apply l8_9; Col.
induction H12; tauto.
intro.
apply H13; ColR.
exists B.
split; Col.

assert(TS B B' A C').
apply l9_2.
apply(l9_8_2 B B' C C' A); auto.
apply l9_2.
assumption.
unfold TS in H16.
spliter.
ex_and H18 T.
assert(T = B').
apply bet_col in H19.
apply (l6_21 B B' A B'); Col.
ColR.
subst T.
assumption.
spliter.
apply False_ind.
apply H12.
ColR.
Qed.

Lemma per23_preserves_bet_inv : forall A B C B' C', Bet A B' C' -> A <> B' -> Col A B C -> Per A B' B -> Per A C' C -> Bet A B C.
Proof.
intros.

induction(eq_dec_points B B').
subst B'.
assert(Col A C' C).
apply bet_col in H.
ColR.
assert(A = C' \/ C = C').
apply(l8_9 A C' C); auto.
induction H5.
subst C'.
apply between_identity in H.
contradiction.
subst C'.
assumption.

assert(Perp A B' B' B).
apply per_perp_in in H2.
apply perp_in_comm in H2.
apply perp_in_perp_bis in H2.
induction H2.
Perp.
apply perp_distinct in H2.
tauto.
auto.
auto.


assert(Perp A C' C' C).
apply per_perp_in in H3.
apply perp_in_comm in H3.
apply perp_in_perp_bis in H3.
induction H3.
Perp.
apply perp_distinct in H3.
tauto.
intro.
subst C'.
apply between_identity in H.
contradiction.
intro.
subst C'.
induction(eq_dec_points A C).
subst C.
apply between_identity in H.
contradiction.
assert(Col A B' B).
apply bet_col in H.
ColR.
assert(A = B' \/ B = B').
apply(l8_9 A B' B); auto.
induction H8;contradiction.

assert(Perp A B' C' C).
apply bet_col in H.
apply(perp_col _ C'); Col.

assert( Par B' B C' C).
apply(l12_9 B' B C' C A B'); Cop.
Perp.
Perp.

induction(eq_dec_points B C).
subst C.
Between.

induction H8.
assert(B' <> C').
intro.
subst C'.
apply H8.
exists B'.
split; Col.


assert(HH:=l12_6 B' B C' C H8).

assert(TS B' B A C').
repeat split; auto.
intro.
assert(A = B' \/ B = B').
apply(l8_9 A B' B); auto.
induction H12;contradiction.
intro.
assert(Col A B' B).
assert_cols.
ColR.
assert(A = B' \/ B = B').
apply(l8_9 A B' B); auto.
induction H13;contradiction.
exists B'.
split; Col.

assert(TS B' B C A).
apply(l9_8_2 B' B C' C A); auto.
apply l9_2.
assumption.
unfold TS in H12.
spliter.
ex_and H14 T.

assert(A <> C).
intro.
subst C.
apply between_identity in H15.
subst T.
contradiction.

assert (T = B).
assert_cols.
apply (l6_21 A C B' B); Col.
intro.
assert(Col A B' B).
ColR.
assert(A = B' \/ B = B').
apply(l8_9 A B' B); auto.
induction H21;contradiction.
subst T.
Between.


spliter.
assert_cols.
assert(Col A B' B).
ColR.
assert(A = B' \/ B = B').
apply(l8_9 A B' B); auto.
induction H15;contradiction.
Qed.



Lemma per13_preserves_bet : forall A B C A' C', Bet A B C -> B <> A' -> B <> C' -> Col A' B C' -> Per B A' A -> Per B C' C -> Bet A' B C'.
Proof.
intros.
assert(Col A B C).
apply bet_col in H.
Col.

induction(eq_dec_points A A').
subst A'.
assert(Col B C' C).
ColR.

assert(B = C' \/ C = C').
apply l8_9; auto.
induction H7.
contradiction.
subst C'.
assumption.

assert(C <> C').
intro.
subst C'.
assert(Col A A' B).
ColR.
assert(B = A' \/ A = A').
apply l8_9; Col.
induction H8; tauto.

assert(Perp B A' A' A).
apply per_perp_in in H3; auto.
apply perp_in_comm in H3.
apply perp_in_perp_bis in H3.
induction H3.
Perp.
apply perp_distinct in H3.
tauto.

assert(Perp B C' C' C).
apply per_perp_in in H4; auto.
apply perp_in_comm in H4.
apply perp_in_perp_bis in H4.
induction H4.
Perp.
apply perp_distinct in H4.
tauto.

assert(Par A A' C C').
apply(l12_9 A A' C C' B A'); Perp; Cop.
apply perp_sym.
apply(perp_col _ C'); Perp.
ColR.

induction H10.
assert(HH:=par_strict_symmetry A A' C C' H10).
apply l12_6 in H10.
apply l12_6 in HH.

assert(~Col A A' B).
apply per_not_col in H3; auto.
intro.
apply H3.
Col.

assert(~Col C C' B).
apply per_not_col in H4; auto.
intro.
apply H4.
Col.

assert(OS A A' B C).
apply out_one_side.
left; auto.
repeat split.
intro.
subst A.
unfold OS in H10.
ex_and H10 X.
unfold TS in H13.
spliter.
apply H13.
Col.
intro.
subst C.
unfold OS in H10.
ex_and H10 X.
unfold TS in H10.
spliter.
apply H10.
Col.
left.
assumption.

assert(OS C C' B A).
apply out_one_side.
left; auto.
repeat split.
intro.
subst C.
apply H12.
Col.
intro.
subst C.
unfold OS in H10.
ex_and H10 X.
unfold TS in H10.
spliter.
apply H10.
Col.
left.
Between.

assert(OS A A' B C').
apply(one_side_transitivity _ _ _ C); auto.
assert(OS C C' B A').
apply(one_side_transitivity _ _ _ A); auto.

apply invert_one_side in H15.
apply invert_one_side in H16.
assert(HP:= col_one_side_out A' A B C' H2 H15).
assert(Out C' B A').
apply(col_one_side_out C' C B A'); Col.

unfold Out in *.
spliter.

induction H19.
Between.
induction H22.
Between.
apply False_ind.
apply H18.
apply (between_equality _ _ B); Between.
spliter.

induction(eq_dec_points A C).
subst C.
apply between_identity in H.
subst B.
clean_duplicated_hyps.
clean_trivial_hyps.
apply l8_8 in H4.
contradiction.
assert(Col B C' C).
ColR.
apply per_not_col in H4; auto.
contradiction.
Qed.

Lemma per13_preserves_bet_inv : forall A B C A' C', Bet A' B C' -> B <> A' -> B <> C' ->  Col A B C  -> Per B A' A -> Per B C' C -> Bet A B C.
Proof.
intros.
assert(Col A' B C').
apply bet_col in H.
Col.

induction(eq_dec_points A A').
subst A'.
assert(Col B C' C).
ColR.
assert(HH:=l8_9 B C' C H4 H6 ).
induction HH.
contradiction.
subst C'.
assumption.

assert(C <> C').
intro.
subst C'.
assert(Col B A' A).
ColR.
assert(HH:=l8_9 B A' A H3 H7).
induction HH;
contradiction.

assert(Perp B A' A' A).
apply per_perp_in in H3; auto.
apply perp_in_comm in H3.
apply perp_in_perp_bis in H3.
induction H3.
Perp.
apply perp_distinct in H3.
tauto.

assert(Perp B C' C' C).
apply per_perp_in in H4; auto.
apply perp_in_comm in H4.
apply perp_in_perp_bis in H4.
induction H4.
Perp.
apply perp_distinct in H4.
tauto.

assert(Par A A' C C').
apply(l12_9 A A' C C' B A'); Perp; Cop.
apply perp_sym.
apply(perp_col _ C'); Perp.
ColR.

induction H10.
assert(HH:=par_strict_symmetry A A' C C' H10).
apply l12_6 in H10.
apply l12_6 in HH.

assert(~Col A' A B).
apply per_not_col in H3; auto.
intro.
apply H3.
Col.

assert(~Col C' C B).
apply per_not_col in H4; auto.
intro.
apply H4.
Col.

assert(OS A' A B C').
apply out_one_side.
left; auto.
repeat split.
intro.
subst A'.
apply H11.
Col.
intro.
subst C'.
apply one_side_symmetry in H10.
unfold OS in H10.
ex_and H10 X.
unfold TS in H10.
spliter.
apply H10.
Col.
left.
assumption.

assert(OS C' C B A').
apply out_one_side.
left; auto.
repeat split.
intro.
subst C'.
apply H12.
Col.
intro.
subst C'.
apply one_side_symmetry in H10.
unfold OS in H10.
ex_and H10 X.
unfold TS in H10.
spliter.
apply H10.
Col.
left.
Between.

assert(OS A' A B C).
apply(one_side_transitivity _ _ _ C'); auto.
apply invert_one_side.
apply one_side_symmetry.
assumption.

assert(OS C C' B A).
apply(one_side_transitivity _ _ _ A'); auto.
apply invert_one_side.
assumption.
apply one_side_symmetry.
assumption.

apply invert_one_side in H15.

assert(HP:= col_one_side_out A A' B C H2 H15).

assert(Out C B A).
apply(col_one_side_out C C' B A); Col.

unfold Out in *.
spliter.

induction H19.
Between.
induction H22.
Between.
apply False_ind.
apply H18.
apply (between_equality _ _ B); Between.

(****************************)

spliter.
assert(Perp A' C' A A').
apply (perp_col _ B); Perp.
intro.
subst C'.
apply between_identity in H.
subst A'.
apply perp_distinct in H9.
tauto.
apply perp_not_col in H14.

apply False_ind.
apply H14.
ColR.
Qed.

Lemma per3_preserves_bet1 : forall O A B C A' B' C', Col O A B -> Bet A B C -> O <> A' -> O <> B' -> O <> C'
                                                    -> Per O A' A -> Per O B' B -> Per O C' C
                                                    -> Col A' B' C' -> Col O A' B' -> Bet A' B' C'.

Proof.
intros O A B C A' B' C'.
intro HC.
intros.

induction(eq_dec_points A B).
subst B.
assert(A' = B').
apply(per2_col_eq O A' B' A H0 H1 H3 H4); Col.
subst B'.
Between.

induction (eq_dec_points A A').
subst A'.
induction(eq_dec_points B B').
subst B'.
assert(Col O C C').
apply bet_col in H.
ColR.

assert(C = C').
apply bet_col in H.
assert(O = C' \/ C = C').
apply(l8_9 O C' C H5); Col.
induction H10.
contradiction.
assumption.
subst C'.
assumption.

induction(eq_dec_points A B').
subst B'.
Between.

assert(A <> C).
intro.
subst C.
apply between_identity in H.
contradiction.

assert( ~ Col O B' B).
apply(per_not_col O B' B H1); auto.

assert(C <> C').
intro.
subst C'.
clean_trivial_hyps.
apply H12.
apply bet_col in H.
ColR.

assert(Perp B B' O A).

apply per_perp_in in H4; auto.
apply perp_in_perp_bis in H4.
induction H4.
apply perp_distinct in H4.
tauto.
apply perp_sym.
apply perp_right_comm.
apply(perp_col O B' B' B A); auto.
Col.

assert(Perp C C' O A).

apply per_perp_in in H5; auto.
apply perp_in_perp_bis in H5.
induction H5.
apply perp_distinct in H5.
tauto.
apply perp_sym.
apply perp_right_comm.
apply(perp_col O C' C' C A); auto.
apply bet_col in H.
ColR.

assert(Par B B' C C').
apply(l12_9 B B' C C' O A); Cop.
induction H16.

assert(HH:=l12_6 B B' C C' H16).

assert(TS B B' A C).
unfold TS.
repeat split; Col.
assert(~Col B' A B).
apply(perp_not_col).
apply perp_left_comm.
apply(perp_col A O B B' B'); Col.
finish.
intro.
apply H17.
Col.
intro.
apply H16.
exists C.
split; Col.
exists B.
split; Col.
assert(TS B B' C' A).
apply(l9_8_2 B B' C C' A).

apply l9_2.
assumption.
assumption.
unfold TS in H18.
spliter.
ex_and H20 T.
assert(B'=T).
apply (l6_21 B B' A C'); Col.
intro.
subst C'.
apply between_identity in H21.
subst T.
contradiction.
subst T.
apply between_symmetry.
assumption.
spliter.

assert(Per O C' B).
apply(per_col O C' C B); Col.
assert(B'=C').
apply(per2_col_eq O B' C' B); Col.
ColR.
subst C'.
Between.

(*-------------------------------*)

induction(eq_dec_points A' B').
subst B'.
Between.

induction(eq_dec_points B C).
subst C.
assert(B' = C').
apply(per2_col_eq O B' C' B); auto.
ColR.
subst C'.
Between.

induction(eq_dec_points B B').
subst B'.
induction(eq_dec_points A' B).
subst B.
Between.

assert(C <> C').
intro.
subst C'.

assert( ~ Col O A' A).
apply(per_not_col O A' A ); auto.
apply H13.
apply bet_col in H.
ColR.

assert(Perp A A' O A').
apply per_perp_in in H3; auto.
apply perp_in_comm in H3.
apply perp_in_perp_bis in H3.
induction H3.
finish.
apply perp_distinct in H3.
tauto.

assert(Perp C C' O A').
apply per_perp_in in H5; auto.
apply perp_in_comm in H5.
apply perp_in_perp_bis in H5.
induction H5.
apply perp_sym.
apply (perp_col _ C'); auto.
finish.
ColR.
apply perp_distinct in H5.
tauto.

assert(Col O A A').
ColR.
assert(Par A A' C C').
apply(l12_9 A A' C C' O A'); Cop.
induction H17.


assert(HH:=l12_6 A A' C C' H17).

(*--------------------------------*)
assert(OS C C' A A').
apply(l12_6 C C' A A').
finish.
assert(OS C C' A B).
apply(out_one_side C C' A B).
left.
intro.
apply H17.
exists A.
split; Col.
unfold Out.
repeat split; auto.
intro.
subst C.
apply between_identity in H.
contradiction.
right.
Between.

assert(OS C C' A' B).
apply(one_side_transitivity C C' A' A); auto.
apply one_side_symmetry.
assumption.

assert(Out C' B A').
induction H6.
unfold Out.
repeat split.
intro.
subst C'.
clean_trivial_hyps.
unfold OS in H18.
ex_and H18 T.
unfold TS in H4.
spliter.
apply H4.
Col.
intro.
subst C'.
apply H17.
exists A'.
split; Col.
left.
Between.

induction H6.

assert(TS C C' B A').
unfold TS.
repeat split.
intro.
unfold OS in H19.
ex_and H19 T.
unfold TS in H22.
spliter.
contradiction.
intro.
apply H17.
exists A'.
split; Col.
exists C'.
split; Col.
apply one_side_symmetry in H20.
apply l9_9_bis in H20.
contradiction.

unfold Out.
repeat split.
intro.
subst C'.
apply H17.
exists A.
apply bet_col in H.
split; Col.
intro.
subst C'.
apply H17.
exists A'.
split; Col.
right; auto.

(*****************************)

assert(Out A' B C').
induction H6.
unfold Out.
repeat split.
intro.
subst A'.
clean_trivial_hyps.
apply H17.
exists C.
apply bet_col in H.
split; Col.
intro.
subst C'.
unfold Out in H21.
tauto.
left.
auto.

induction H6.
unfold Out in H21.
spliter.
unfold Out.
repeat split.
intro.
subst A'.
apply H17.
exists C.
apply bet_col in H.
split; Col.
auto.
induction H23.
left.
Between.

apply False_ind.
apply H22.
apply (between_equality _ _ B); Between.

(***************************)

assert(OS A A' B C).
apply(out_one_side A A' B C).
right.
intro.
apply H17.
exists C.
split; Col.
unfold Out.
repeat split; auto.
intro.
subst C.
apply between_identity in H.
contradiction.

assert(OS A A' C' B).
apply(one_side_transitivity A A' C' C);
apply one_side_symmetry; auto.


(***********************)
assert(TS A A' B C').
unfold TS.
repeat split.
intro.
unfold OS in H22.
ex_and H22 T.
unfold TS in H22.
spliter.
contradiction.
intro.
apply H17.
exists C'.
split; Col.
exists A'.
split; Col.
Between.
apply one_side_symmetry in H23.
apply l9_9_bis in H23.
contradiction.

unfold Out in *.
spliter.
clean_duplicated_hyps.

induction H26; induction H24.
assumption.
apply False_ind.
apply H21.
apply(between_equality _ _ A'); Between.
apply False_ind.
apply H10.
apply(between_equality _ _ C'); Between.
apply False_ind.
apply H25.
apply(between_equality _ _ B); Between.
spliter.


assert(~Col O C' C).
apply(per_not_col); auto.
apply False_ind.
apply H21.

assert(A<>C).
intro.
subst C.
apply between_identity in H.
subst B.
tauto.
apply bet_col in H.
ColR.

(********************************)

assert(Perp A A' O A').
apply per_perp_in in H3; auto.
apply perp_in_comm in H3.
apply perp_in_perp_bis in H3.
induction H3.
finish.
apply perp_distinct in H3.
tauto.

assert(Perp B B' O A').
apply per_perp_in in H4; auto.
apply perp_in_comm in H4.
apply perp_in_perp_bis in H4.
induction H4.
apply perp_sym.
apply (perp_col _ B'); Col.
finish.
apply perp_distinct in H4.
tauto.

assert(Par A A' B B').
apply(l12_9 A A' B B' O A'); Cop.

induction H15.
assert(HH:=l12_6 A A' B B' H15).



assert(TS B B' A C).
unfold TS.
repeat split; Col.
intro.
apply H15.
exists A.
split; Col.
intro.
apply H11.
apply (l6_21 B B' A C); Col.
intro.
apply H15.
exists A.
split; Col.
intro.
subst C.
apply between_identity in H.
subst B.
tauto.
exists B.
split; Col.

assert(OS B B' A A').
apply(l12_6 B B' A A').
finish.

assert(HP:= l9_8_2 B B' A A' C H16 H17).


induction(eq_dec_points C C').
subst C'.
unfold TS in HP.
spliter.
ex_and H20 T.

assert(T = B').
apply (l6_21 B B' A' C); Col.
intro.
subst A'.
apply between_identity in H21.
subst T.
contradiction.
subst T.
assumption.

assert(Perp C C' O A').
apply per_perp_in in H5; auto.
apply perp_in_comm in H5.
apply perp_in_perp_bis in H5.
induction H5.
apply perp_sym.
apply (perp_col _ C'); finish.
ColR.
apply perp_distinct in H5.
tauto.

assert(Par B B' C C').
apply(l12_9 B B' C C' O A'); auto.
exists O.
left.
split; ColR.
exists C'.
left.
split; ColR.
exists B'.
left.
split; Col.
exists B'.
left.
split; Col.
induction H20.

assert(HQ:=l12_6 B B' C C' H20).

assert(TS B B' C' A').
apply(l9_8_2 B B' C C' A'); auto.
apply l9_2.
assumption.
unfold TS in H21.
spliter.
ex_and H23 T.
assert(T = B').
apply (l6_21 B B' A' C'); Col.
intro.
subst C'.
apply between_identity in H24.
subst T.
contradiction.
subst T.
Between.
spliter.
unfold TS in HP.
spliter.
apply False_ind.
apply H25.
ColR.
spliter.

apply perp_left_comm in H13.
apply perp_not_col in H13.
apply False_ind.
apply H13.
ColR.
Qed.


Lemma per3_preserves_bet2_aux : forall O A B C B' C', Col O A C -> A <> C' ->
                               Bet A B' C' -> O <> A -> O <> B' -> O <> C'
                               -> Per O B' B -> Per O C' C
                               -> Col A B C -> Col O A C' -> Bet A B C.
Proof.
intros O A B C B' C'.
intro HX.
intros.
induction(eq_dec_points A B).
subst B.
Between.
induction(eq_dec_points B C).
subst C.
Between.

assert(Col O A B').
apply bet_col in H0.
ColR.
assert(Col O B' C').
apply bet_col in H0.
ColR.

induction(eq_dec_points B B').
subst B'.
assert(Col O C C').
apply bet_col in H0.
ColR.
assert(C = C').
apply(per_col_eq C C' O); finish.
subst C'.
assumption.
assert(C <> C').
intro.
subst C'.
apply per_not_col in H4; auto.
apply H4.
ColR.

assert(Perp O A C C').
apply per_perp_in in H5; auto.
apply perp_in_comm in H5.
apply perp_in_perp_bis in H5.
induction H5.
apply (perp_col _ C'); finish.
apply perp_distinct in H5.
tauto.

assert(Perp O A B B').
apply per_perp_in in H4; auto.
apply perp_in_comm in H4.
apply perp_in_perp_bis in H4.
induction H4.
apply (perp_col _ B'); finish.
apply perp_distinct in H4.
tauto.

assert(Par B B' C C').
apply(l12_9 B B' C C' O A);finish.

induction H16.
assert(HH:=l12_6 B B' C C' H16).
assert(TS B B' A C').
repeat split; finish.
intro.
assert(Per B B' A).
apply(per_col B B' O A); finish.
apply per_not_col in H18; auto.
apply H18.
Col.
intro.
subst B'.
clean_trivial_hyps.
apply H16.
exists C.
split; Col.
intro.
apply H16.
exists C'.
split; Col.
exists B'.
split; finish.

assert(TS B B' C A).
apply(l9_8_2 B B' C' C A).
apply l9_2; auto.
apply one_side_symmetry; auto.
unfold TS in H18.
spliter.
ex_and H20 T.
assert(B = T).
apply (l6_21 A C B' B); Col.
assert(A <> C).
intro.
subst C.
apply between_identity in H21.
subst T.
contradiction.
intro.
apply bet_col in H0.
apply H19.
ColR.
subst T.
Between.

spliter.

assert(B' <> C').
intro.
subst C'.
clean_trivial_hyps.
assert(Perp O B' C B').
apply(perp_col O A C B' B'); Col.
apply perp_left_comm in H0.
apply perp_not_col in H0.
apply H0.
ColR.

assert(Per C C' B').
apply(per_col C C' O B'); finish.
apply per_not_col in H21; auto.
apply False_ind.
apply H21.
Col.
Qed.

Lemma per3_preserves_bet2 : forall O A B C A' B' C', Col O A C -> A' <> C' ->
                               Bet A' B' C' -> O <> A' -> O <> B' -> O <> C'
                               -> Per O A' A -> Per O B' B -> Per O C' C
                               -> Col A B C -> Col O A' C' -> Bet A B C.

Proof.
intros O A B C A' B' C'.
intro HX.
intros.
induction(eq_dec_points A A').
subst A'.
apply (per3_preserves_bet2_aux O A B C B' C');auto.
induction(eq_dec_points C C').
subst C'.
apply between_symmetry.
apply(per3_preserves_bet2_aux O C B A B' A'); finish.

assert(Perp O A' C C').
apply per_perp_in in H6; auto.
apply perp_in_comm in H6.
apply perp_in_perp_bis in H6.
induction H6.
apply (perp_col _ C'); finish.
apply perp_distinct in H6.
tauto.

assert(Perp O A' A A').
apply per_perp_in in H4; auto.
apply perp_in_comm in H4.
apply perp_in_perp_bis in H4.
induction H4.
finish.
apply perp_distinct in H4.
tauto.

assert(Par A A' C C').
apply(l12_9 A A' C C' O A');finish.

induction H13.
assert(HH:=l12_6 A A' C C' H13).
apply par_strict_symmetry in H13.
assert(HP:=l12_6 C C' A A' H13).

induction(eq_dec_points B B').
subst B'.

assert(OS A' A B C').
apply out_one_side.
right.
intro.
apply H13.
exists C'.
split; Col.
repeat split.
intro.
subst A'.
apply H13.
exists C.
split; Col.
auto.
left; auto.
apply invert_one_side in H14.
assert(OS A A' B C).
apply (one_side_transitivity _ _ _ C').
assumption.
apply one_side_symmetry.
assumption.

assert(Out A B C).
apply (col_one_side_out A A');auto.

assert(OS C' C B A').
apply out_one_side.
right.
intro.
apply H13.
exists A'.
split; Col.
repeat split.
intro.
subst C'.
apply H13.
exists A.
split; Col.
auto.
left; Between.
apply invert_one_side in H17.
assert(OS C C' B A).
apply (one_side_transitivity _ _ _ A').
assumption.
apply one_side_symmetry.
assumption.
apply one_side_symmetry in H18.

assert(Out C A B).
apply (col_one_side_out C C');Col.
unfold Out in *.
spliter.


induction H23; induction H21.
assumption.
assumption.
assert(A = C).
apply (between_equality A C B); auto.
subst C.
apply False_ind.
apply H13.
exists A.
split; Col.
assert(B = C).
apply (between_equality B C A); Between.
subst C.
Between.

(****************************************************************************************)

assert(Perp O A' B B').
apply per_perp_in in H5; auto.
apply perp_in_comm in H5.
apply perp_in_perp_bis in H5.
induction H5.
apply (perp_col _ B'); finish.
apply bet_col in H0.
ColR.
apply perp_distinct in H5.
tauto.

assert(Par B B' A A').
apply(l12_9 B B' A A' O A'); Perp.
exists O.
left.
assert_diffs.
split; ColR.
exists A'.
left.
split; Col.
exists B'.
left.
split; ColR.
exists A'.
left.
split; Col.

induction H16.
assert(HQ:=l12_6 B B' A A' H16).

assert(Par B B' C C').
apply(l12_9 B B' C C' O A'); Perp.
exists O.
left.
assert_diffs.
split; ColR.
exists C'.
left.
split; Col.
exists B'.
left.
assert_diffs.
split; ColR.
exists A'.
left.
split; Col.
induction H17.
assert(HR:=l12_6 B B' C C' H17).

assert(TS B B' A' C').
repeat split; auto.
intro.
apply H16.
exists A'.
split; Col.
intro.
apply H17.
exists C'.
split; Col.
exists B'.
split; finish.
apply one_side_symmetry in HQ.
assert(HH1:= l9_8_2 B B' A' A C' H18 HQ).
apply l9_2 in HH1.
apply one_side_symmetry in HR.
assert(HH2:= l9_8_2 B B' C' C A HH1 HR).
unfold TS in HH2.
spliter.
ex_and H21 T.
assert(B = T).
apply (l6_21 B B' A C); Col.
intro.
subst C.
apply H13.
exists A.
split; Col.
subst T.
Between.
spliter.

induction(eq_dec_points B C).
subst C.
Between.
assert(Col A C C').
ColR.
apply False_ind.
apply H13.
exists A.
split; Col.
spliter.

induction(eq_dec_points A B).
subst B.
Between.
assert(Col C A A').
ColR.
apply False_ind.
apply H13.
exists C.
split; Col.
spliter.

assert(A <> C).
intro.
subst C.
apply H.
apply(per2_col_eq O A' C' A); Col.

assert(Col O C C').
ColR.
apply False_ind.
apply per_not_col in H6; auto.
apply H6.
Col.
Qed.


Lemma symmetry_preserves_per : forall A P B A' P', Per B P A -> Midpoint B A A' -> Midpoint B P P'
                                                   -> Per B P' A'.
Proof.
intros.
assert(HS:=symmetric_point_construction A P).
ex_and HS C.
assert(HS:=symmetric_point_construction C B).
ex_and HS C'.

assert(HH:= symmetry_preserves_midpoint A P C A' P' C' B H0 H1 H3 H2).
unfold Per.
exists C'.
split.
assumption.
unfold Per in H.
ex_and H X.
assert(X = C).
apply(symmetric_point_uniqueness A P X C); auto.
subst X.
unfold Midpoint in *.
spliter.
apply (cong_transitivity _ _ B A).
Cong.
apply(cong_transitivity _ _ B C).
assumption.
Cong.
Qed.

Lemma l13_1_aux : forall A B C P Q R,
   ~ Col A B C -> Midpoint P B C -> Midpoint Q A C -> Midpoint R A B ->
   exists X, exists Y, Perp_at R X Y A B /\ Perp X Y P Q /\ Coplanar A B C X /\ Coplanar A B C Y.
Proof.
intros A B C P Q R HC MBC MAC MAB.
assert(Q <> C).
intro.
subst Q.
unfold Midpoint in MAC.
spliter.
apply cong_identity in H0.
subst C.
apply HC.
Col.
assert(P <> C).
intro.
subst P.
unfold Midpoint in MBC.
spliter.
apply cong_identity in H1.
subst C.
apply HC.
Col.

assert(D1:Q<>R).
intro.
subst R.
assert(B=C).
apply(symmetric_point_uniqueness A Q); auto.
subst C.
apply l7_3 in MBC.
contradiction.

assert(D2:R <> B).
intro.
subst R.
unfold Midpoint in MAB.
spliter.
apply cong_identity in H2.
subst B.
apply HC.
Col.

assert(~Col P Q C).
intro.
apply HC.
unfold Midpoint in *.
spliter.
apply bet_col in H2.
apply bet_col in H4.
apply bet_col in H6.
ColR.

assert(HH:= l8_18_existence P Q C H1).
ex_and HH C'.

assert(HS1:=symmetric_point_construction C' Q).
ex_and HS1 A'.
assert(HS1:=symmetric_point_construction C' P).
ex_and HS1 B'.

assert(Cong C C' B B').
apply(l7_13 P C C' B B' MBC); finish.
assert(Cong C C' A A').
apply(l7_13 Q C C' A A'); finish.

assert(Per P B' B).
induction(eq_dec_points P C').
subst C'.
unfold Midpoint in H5.
spliter.
apply cong_symmetry in H8.
apply cong_identity in H8.
subst B'.
apply l8_2.
apply l8_5.

apply(symmetry_preserves_per C C' P B B'); finish.
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
apply perp_left_comm.
apply (perp_col _ Q); Col.

assert(Per Q A' A).
induction(eq_dec_points Q C').
subst C'.
unfold Midpoint in H4.
spliter.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst A'.
apply l8_2.
apply l8_5.
apply(symmetry_preserves_per C C' Q A A'); finish.
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
apply perp_left_comm.
apply (perp_col _ P); Col.
finish.

assert(Cl1: Col A' C' Q).
unfold Midpoint in H4.
spliter.
apply bet_col in H4.
Col.

assert(Cl2: Col B' C' P).
unfold Midpoint in H5.
spliter.
apply bet_col in H5.
Col.

assert(NE0: P <> Q).
apply perp_distinct in H3; tauto.

assert(NE1 : A' <> B').
intro.
subst B'.
apply NE0.
apply (l7_17 C' A'); auto.

assert(Cl3: Col A' B' P).
induction(eq_dec_points P C').
subst P.
unfold Midpoint in  H5.
spliter.
apply cong_symmetry in H10.
apply cong_identity in H10.
subst C'.
Col.
induction(eq_dec_points Q C').
subst Q.
unfold Midpoint in  H4.
spliter.
apply cong_symmetry in H11.
apply cong_identity in H11.
subst C'.
Col.
ColR.

assert(Cl4: Col A' B' Q).
induction(eq_dec_points P C').
subst P.
unfold Midpoint in  H5.
spliter.
apply cong_symmetry in H10.
apply cong_identity in H10.
subst C'.
Col.
induction(eq_dec_points Q C').
subst Q.
unfold Midpoint in  H4.
spliter.
apply cong_symmetry in H11.
apply cong_identity in H11.
subst C'.
Col.
ColR.

assert(Cl5:Col A' B' C').
ColR.

assert(NE2 : C <> C').
apply perp_distinct in H3.
tauto.

assert(NE3: A <> A').
intro.
subst A'.
apply cong_identity in H7.
contradiction.

assert(NE4: B <> B').
intro.
subst B'.
apply cong_identity in H6.
contradiction.

assert(Per P A' A).
induction(eq_dec_points A' Q).
subst Q.
unfold Midpoint in H4.
spliter.
apply cong_identity in H10.
subst C'.
clean_trivial_hyps.
apply perp_left_comm in H3.
apply perp_perp_in in H3.
apply perp_in_comm in H3.
apply perp_in_per in H3.
unfold Midpoint in MAC.
spliter.
apply bet_col in H2.
apply (per_col P A' C A); Col.
apply l8_2.
apply (per_col A A' Q P); finish.
ColR.

assert(Per Q B' B).
induction(eq_dec_points B' P).
subst P.
unfold Midpoint in H5.
spliter.
apply cong_identity in H11.
subst C'.
clean_trivial_hyps.
apply perp_perp_in in H3.
apply perp_in_comm in H3.
apply perp_in_per in H3.
unfold Midpoint in MBC.
spliter.
apply bet_col in H2.
apply (per_col Q B' C B); Col.
apply l8_2.
apply (per_col B B' P Q); finish.
ColR.

assert(Per A' B' B).
apply l8_2.
induction(eq_dec_points B' P).
subst P.
unfold Midpoint in H5.
spliter.
apply cong_identity in H12.
subst C'.
clean_trivial_hyps.
apply(per_col B B' Q A'); finish.
apply(per_col B B' P A'); finish.

assert(Per B' A' A).
apply l8_2.
induction(eq_dec_points A' Q).
subst Q.
unfold Midpoint in H4.
spliter.
apply cong_identity in H13.
subst C'.
clean_trivial_hyps.
apply(per_col A A' P B'); finish.
apply(per_col A A' Q B'); finish.


assert(NC1 : ~Col A' B' A).
apply per_not_col in H13; auto.
intro.
apply H13.
Col.

assert(NC2 : ~Col A' B' B).
apply per_not_col in H12; auto.

(****************************************)

assert(HM:=midpoint_existence A' B').
ex_and HM X.

assert(HP:=l10_15 A' B' X A).
destruct HP as [y []]; Col.

assert(HH:=ex_sym X y A).
ex_and HH B''.

assert( X <> y).
apply perp_distinct in H15.
spliter.
auto.


assert(Reflect B'' A X y).
unfold Reflect.
left.
repeat split;auto.
ex_and H18 M.
exists M.
split; finish.

assert(Reflect A' B' X y).
unfold Reflect.
left.
split; auto.
repeat split.
exists X.
split; finish.
left.
finish.
apply l10_4 in H20.

assert(HH:= l10_10 X y B''  B' A A' H20 H21).

assert(Per A' B' B'').
unfold Reflect in *.
induction H20; induction H21.
spliter.

apply(image_spec_preserves_per B' A' A A' B' B'' X y); auto.
apply l10_4_spec.
assumption.
spliter.
contradiction.
spliter.
contradiction.
spliter.
contradiction.

unfold Reflect in H21.
induction H21.
spliter.
unfold ReflectL in H23.


assert(OS A' B' A B'').
induction H17.
assert(Par A' B' A B'').
assert(Coplanar A y A' X).
apply col_cop__cop with B'; Col; Cop.
assert(Coplanar A y B' X).
apply col_cop__cop with A'; Col; Cop.
assert(~ Col A X y).
intro.
assert(A=B'').
apply (image_id X y); Col.
assert_diffs.
auto.
apply(l12_9 A' B' A B'' X y); Perp.
Cop.
apply coplanar_trans_1 with A; Cop.
Cop.
apply coplanar_trans_1 with A; Cop.
induction H24.
apply( l12_6 A' B' A B'' H24).
spliter.

apply per_not_col in H22; auto.
apply False_ind.
apply H22.
ColR.
intro.
subst B''.
apply cong_symmetry in HH.
apply cong_identity in HH.
subst A'.
apply cong_identity in H7.
subst C'.
tauto.

subst B''.
apply one_side_reflexivity.
intro.
apply NC1.
Col.

assert(OS A' B' A B).
unfold OS.
exists C.
split.
unfold TS.
repeat split; Col.
intro.
apply H1.
ColR.
exists Q.
split; Col.
unfold Midpoint in MAC.
tauto.
unfold TS.
repeat split; Col.
intro.
apply H1.
ColR.
exists P.
split; Col.
unfold Midpoint in MBC.
tauto.

(*********************************)


assert( Col B B'' B').
apply cop_per2__col with A'; Perp.
apply coplanar_perm_3.
apply coplanar_trans_1 with A; Col; Cop.
assert(Cong B B' A A').
apply cong_transitivity with C C'; Cong.

assert(B = B'' \/ Midpoint B' B B'').
apply( l7_20); Col.

apply cong_transitivity with A A'; Cong.
induction H28.
subst B''.

exists R.
exists X.

ex_and H18 M.
assert(R = M).
apply (l7_17 A B); auto.
subst M.

assert(A <> B).
intro.
subst B.
apply HC; Col.

assert(Col R A B).
unfold Midpoint in MAB.
spliter.
apply bet_col in H31.
Col.

assert(X <> R).
intro.
subst X.
assert(Par A B A' B').
assert(Coplanar A y A' R).
apply col_cop__cop with B'; Col; Cop.
assert(Coplanar A y B' R).
apply col_cop__cop with A'; Col; Cop.
assert(~ Col A R y).
intro.
assert(A=B).
apply (image_id R y); Col.
assert_diffs.
auto.
apply(l12_9 A B A' B' R y); Perp.
Cop.
Cop.
apply coplanar_trans_1 with A; Cop.
apply coplanar_trans_1 with A; Cop.
induction H17.
Perp.
contradiction.
induction H32.
apply H32.
exists R.

unfold Midpoint in H14.
spliter.
apply bet_col in H14.
split; Col.
spliter.
apply NC1.
Col.

split.

apply(l8_14_2_1b_bis R X A B R); Col.
induction H17.
apply perp_left_comm.
apply(perp_col _ y); auto.
contradiction.

split.

apply perp_left_comm.
apply(perp_col _ y);auto.
apply perp_sym.
induction(eq_dec_points B' P).
subst P.
apply(perp_col _ A');auto.
Perp.
Col.
apply(perp_col _ B');auto.
apply perp_left_comm.

apply(perp_col _ A');auto.
Perp.
Col.
ColR.

split.
exists R.
left.
split; Col.
assert(Col P Q X).
ColR.
apply coplanar_pseudo_trans with P Q C; Cop.

assert(TS A' B' B B'').
unfold TS.
repeat split; auto.
intro.
apply NC2; Col.
intro.
apply per_not_col in H22; auto.
apply H22.
Col.
intro.
subst B''.
unfold Midpoint in H28.
spliter.
apply cong_identity in H30.
subst B'.
unfold OS in H24.
ex_and H24 T.
unfold TS in H30.
spliter.
apply H30.
Col.
exists B'.
split; Col.
unfold Midpoint in H28.
tauto.
assert(OS A' B' B B'').
apply (one_side_transitivity A' B' B A ).
apply one_side_symmetry.
assumption.
assumption.
apply l9_9 in H29.
contradiction.
spliter.
contradiction.
Qed.

Lemma l13_1 : forall A B C P Q R,
   ~ Col A B C -> Midpoint P B C -> Midpoint Q A C -> Midpoint R A B ->
   exists X, exists Y, Perp_at R X Y A B /\ Perp X Y P Q.
Proof.
intros.
destruct (l13_1_aux A B C P Q R) as [X [Y]]; trivial.
spliter.
exists X.
exists Y.
split; assumption.
Qed.



Lemma per_lt : forall A B C, A <> B ->  C <> B -> Per A B C -> Lt A B A C /\ Lt C B A C.
  Proof.
    intros.
    assert(Lt B A A C /\ Lt B C A C).
      apply( l11_46 A B C); auto.
    spliter.
    split; apply lt_left_comm; assumption.
  Qed.

Lemma cong_perp_conga : forall A B C P,  Cong A B C B -> Perp A C B P -> CongA A B P C B P /\ TS B P A C.
Proof.
    intros.
    assert(A <> C /\ B <> P).
      split.
        apply perp_not_eq_1 in H0.
        assumption.
      apply perp_not_eq_2 in H0.
      assumption.
    spliter.
    assert(A <> B).
      intro.
      subst B.
      apply cong_symmetry in H.
      apply cong_identity in H.
      apply H1.
      auto.
    assert(C <> B).
      intro.
      subst B.
      apply cong_identity in H.
      contradiction.
    induction(col_dec A B C).
      assert(~ Col B A P).
        apply perp_not_col.
        apply perp_comm.
        apply (perp_col _ C); Col.
      assert(Per P B A).
        apply perp_in_per.
        apply perp_in_comm.
        apply perp_perp_in.
        apply perp_sym.
        eapply (perp_col _ C); Col.
      assert(Per P B C).
        apply perp_in_per.
        apply perp_in_comm.
        apply perp_perp_in.
        apply perp_sym.
        eapply (perp_col _ A); Col.
        Perp.
      apply l8_2 in H7.
      apply l8_2 in H8.
      split.
        apply l11_16; auto.
      assert( A = C \/ Midpoint B A C).
        eapply l7_20; Cong.
      induction H9.
        contradiction.
      unfold TS.
      repeat split.
        auto.
        intro.
        apply H6.
        Col.
        intro.
        apply H6.
        ColR.
      exists B.
      unfold Midpoint in H9.
      spliter.
      split; Between.
    assert(HH:= H0).
    unfold Perp in HH.
    ex_and HH T.
    apply perp_in_col in H6.
    spliter.
    assert(B <> T).
      intro.
      subst T.
      apply H5.
      Col.
    assert(Perp B T A C).
      apply (perp_col _ P); Perp.
    assert(A <> T).
      intro.
      subst T.
      apply perp_comm in H9.
      apply perp_perp_in in H9.
      apply perp_in_comm in H9.
      apply perp_in_per in H9.
      assert(Lt B A B C /\ Lt C A B C).
        apply( per_lt B A C); auto.
      spliter.
      unfold Lt in H10.
      spliter.
      apply H12.
      Cong.
    assert(C <> T).
      intro.
      subst T.
      apply perp_left_comm in H9.
      apply perp_perp_in in H9.
      apply perp_in_comm in H9.
      apply perp_in_per in H9.
      assert(Lt B C B A /\ Lt A C B A).
        apply( per_lt B C A); auto.
      spliter.
      unfold Lt in H11.
      spliter.
      apply H13.
      Cong.
    assert(Perp_at T B T T A).
      apply perp_in_comm.
      apply perp_perp_in.
      apply perp_sym.
      apply (perp_col _ C).
        assumption.
        apply perp_sym.
        apply perp_left_comm.
        apply (perp_col _ P); Perp.
      Col.
    assert(Perp_at T B T T C).
      apply perp_in_comm.
      apply perp_perp_in.
      apply perp_sym.
      apply (perp_col _ A).
        assumption.
        apply perp_sym.
        apply perp_left_comm.
        apply (perp_col _ P); Perp.
      Col.
    assert(Cong T A T C /\ CongA T A B T C B /\ CongA T B A T B C).
      apply( l11_52 A T B C T B); Cong.
        eapply l11_16; auto.
          apply perp_in_per.
          apply perp_in_comm.
          apply perp_in_sym.
          assumption.
        apply perp_in_per.
        apply perp_in_comm.
        apply perp_in_sym.
        assumption.
      assert(Lt B T B A /\ Lt A T B A).
        apply( per_lt B T A); auto.
        apply perp_in_per.
        assumption.
      spliter.
      apply le_comm.
      unfold Lt in H14.
      spliter.
      assumption.
    spliter.
    split.
      induction(bet_dec P B T).
        apply conga_comm.
        eapply l11_13; auto.
          apply H16.
          Between.
        Between.
      apply conga_comm.
      assert(Out B T P).
        unfold Out.
        repeat split; auto.
        induction H7.
          right.
          assumption.
        induction H7.
          left.
          Between.
        apply between_symmetry in H7.
        contradiction.
      eapply out_conga.
        apply H16.
        assumption.
        apply out_trivial.
        auto.
        assumption.
      apply out_trivial.
      auto.
    assert(A = C \/ Midpoint T A C).
      apply l7_20; Col.
    induction H17.
      contradiction.
    unfold TS.
    repeat split; Col.
      assert(~ Col T A B).
        apply perp_not_col.
        apply perp_in_perp_bis in H12.
        induction H12.
          apply perp_not_eq_1 in H12.
          tauto.
        Perp.
      intro.
      apply H18.
      ColR.
      assert(~ Col T C B).
        apply perp_not_col.
        apply perp_in_perp_bis in H13.
        induction H13.
          apply perp_not_eq_1 in H13.
          tauto.
        Perp.
      intro.
      apply H18.
      ColR.
    exists T.
    apply midpoint_bet in H17.
    split; Col.
Qed.




Lemma perp_per_bet : forall A B C P, ~Col A B C -> Col A P C -> Per A B C -> Perp_at P P B A C -> Bet A P C.
Proof.
intros.
assert( A <> C).
intro.
subst C.
apply H.
Col.
assert(Bet A P C /\ A <> P /\ C <> P).
apply(l11_47 A C B P); auto.
Perp.
tauto.
Qed.





Lemma ts_per_per_ts : forall A B C D, TS A B C D -> Per B C A -> Per B D A -> TS C D A B.
Proof.
intros.
assert(HTS:= H).
    unfold TS in H.
    assert (~ Col C A B).
      spliter.
      assumption.
    spliter.
    clear H.
    assert (A <> B).
      intro.
      subst B.
      Col.
    ex_and H4 P.
    assert_diffs.
    show_distinct C D.
contradiction.

unfold TS.
repeat split; auto.
intro.
assert(A = P).
apply bet_col in H5.
apply (l6_21 A B C D); Col.
subst P.
apply H6.
apply(per2_col_eq A C D B); finish.
intro.
assert(B = P).
apply bet_col in H5.
apply (l6_21 A B C D); Col.
subst P.
apply H6.
apply(per2_col_eq B C D A); finish.
exists P.
split.
finish.

assert(exists X : Tpoint, Col A B X /\ Perp A B C X).
apply(l8_18_existence A B C); Col.
ex_and H7 C'.

assert(exists X : Tpoint, Col A B X /\ Perp A B D X).
apply(l8_18_existence A B D); Col.
ex_and H12 D'.

assert( A <> C').
intro.
subst C'.
apply perp_perp_in in H8.
apply perp_in_comm in H8.
apply perp_in_per in H8.
assert(A = C).
apply (l8_7 B); Perp.
subst C.
tauto.

assert( A <> D').
intro.
subst D'.
apply perp_perp_in in H14.
apply perp_in_comm in H14.
apply perp_in_per in H14.
assert(A = D).
apply (l8_7 B); Perp.
subst D.
tauto.


assert(Bet A C' B).
apply(perp_per_bet A C B C'); Col.
Perp.
assert(Perp A C' C' C).
apply(perp_col _ B); Col; Perp.
apply perp_in_sym.
apply perp_in_right_comm.
apply(l8_15_1 A B C C'); auto.

assert(Bet A D' B).
apply(perp_per_bet A D B D'); Col.
Perp.
assert(Perp A D' D' D).
apply(perp_col _ B); Col; Perp.
apply perp_in_sym.
apply perp_in_right_comm.
apply(l8_15_1 A B D D'); auto.

induction(eq_dec_points C' P).
subst C'.
assumption.

induction(eq_dec_points D' P).
subst D'.
assumption.

induction(eq_dec_points A P).
subst P.
Between.
induction(eq_dec_points B P).
subst P.
Between.

assert(Bet C' P D').
apply(per13_preserves_bet C P D C' D'); Col.
ColR.
assert(Perp P C' C' C).
apply(perp_col _ A);auto.
apply perp_left_comm.
apply(perp_col _ B);Perp.
Col.
ColR.
apply perp_comm in H24.
apply perp_perp_in in H24.
apply perp_in_comm in H24.
apply perp_in_per in H24.
assumption.

assert(Perp P D' D' D).
apply(perp_col _ A);auto.
apply perp_left_comm.
apply(perp_col _ B);Perp.
Col.
ColR.
apply perp_comm in H24.
apply perp_perp_in in H24.
apply perp_in_comm in H24.
apply perp_in_per in H24.
assumption.

assert(HH:= l5_3 A C' D' B H18 H19).
induction HH.
eBetween.
apply between_symmetry in H24.
eBetween.
Qed.


Lemma l13_2_1 : forall A B C D E, TS A B C D -> Per B C A -> Per B D A -> Col C D E
    -> Perp A E C D -> CongA C A B D A B
    -> CongA B A C D A E /\ CongA B A D C A E /\ Bet C E D.
Proof.
    intros.
    intros.
    assert(HH:= H).
    unfold TS in HH.
    assert (~ Col C A B).
      spliter.
      assumption.
    spliter.
    assert(A <> C /\ A <> B /\ A <> D).
      unfold CongA in H4.
      spliter.
      repeat split; auto.
    spliter.
    assert(Cong B C B D /\ Cong A C A D /\ CongA C B A D B A).
      apply(l11_50_2 B A C B A D).
        intro.
        apply H6.
        Col.
        eapply l11_16; auto.
          apply l8_2.
          auto.
          intro.
          subst C.
          apply H6.
          Col.
          apply l8_2.
          auto.
        intro.
        subst D.
        apply H7.
        Col.
        apply conga_comm.
        auto.
      Cong.
    spliter.
    assert(Perp C D A B).
      apply( cong_conga_perp C A D B); Cong.
    assert(Col A B E).
      apply cop_perp2__col with C D.
        exists E.
        left.
        split; Col.
        apply perp_sym.
        apply H15.
      auto.
    assert(TS C D A B).
      apply ts_per_per_ts; auto.
    unfold TS in H17.
    spliter.
    ex_and H19 T1.
    ex_and H8 T.
    assert(T = T1).
      apply bet_col in H20.
      apply bet_col in H21.
      assert_diffs.
      apply (l6_21 A B C D); Col.
    subst T1.
    assert(T = E).
      assert_diffs.
      apply (l6_21 A B C D); Col.
    subst T.
    split.
      apply conga_left_comm.
      eapply out_conga.
        apply H4.
        apply out_trivial; auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
      unfold Out.
      repeat split; auto.
      intro.
      subst E.
      contradiction.
    split.
      apply conga_sym.
      apply conga_right_comm.
      eapply out_conga.
        apply H4.
        apply out_trivial; auto.
        unfold Out.
        repeat split; auto.
        intro.
        subst E.
        contradiction.
        apply out_trivial; auto.
      apply out_trivial; auto.
    assumption.
Qed.


  Lemma triangle_mid_par : forall A B C P Q, ~Col A B C -> Midpoint P B C -> Midpoint Q A C -> Par_strict A B Q P.
  Proof.
  intros.
   assert(HM:= midpoint_existence A B).
   ex_and HM R.
   assert(HH:= l13_1_aux A B C P Q R H H0 H1 H2).
   ex_and HH X.
   ex_and H3 Y.
assert(Coplanar X Y A P /\ Coplanar X Y A Q /\ Coplanar X Y B P /\ Coplanar X Y B Q).
  assert(Coplanar A B C A).
  exists A.
  left.
  split; Col.
  assert(Coplanar A B C B).
  exists B.
  left.
  split; Col.
  assert(Coplanar A B C P).
  exists B.
  left.
  split; Col.
  assert(Coplanar A B C Q).
  exists A.
  left.
  split; Col.
  repeat split; apply coplanar_pseudo_trans with A B C; assumption.
spliter.
assert(HH:= perp_in_col X Y A B R H3).
spliter.
   apply perp_in_perp_bis in H3.
unfold Midpoint in H2.
spliter.
apply bet_col in H2.
assert(X <> Y).
apply perp_distinct in H4.
tauto.

   induction H3.
   assert(Perp Y X A B).
apply (perp_col _ R); Perp.
Col.
apply perp_left_comm in H15.
assert(Par A B P Q).
   apply(l12_9 A B P Q X Y);Perp.
induction H16.
finish.
spliter.
assert(Col A B P).
ColR.
assert(P = B).
apply (l6_21 A B C P); Col.
unfold Midpoint in H0.
spliter.
apply bet_col in H0.
Col.
intro.
subst P.
contradiction.
subst P.
unfold Midpoint in H0.
spliter.
apply cong_symmetry in H21.
apply cong_identity in H21.
subst C.
contradiction.

assert(Perp X Y A B).
apply (perp_col _ R); Perp.
Col.
assert(Par A B P Q).
   apply(l12_9 A B P Q X Y);Perp.
induction H16.
finish.
spliter.
assert(Col A B P).
ColR.
assert(P = B).
apply (l6_21 A B C P); Col.
unfold Midpoint in H0.
spliter.
apply bet_col in H0.
Col.
intro.
subst P.
contradiction.
subst P.
unfold Midpoint in H0.
spliter.
apply cong_symmetry in H21.
apply cong_identity in H21.
subst C.
contradiction.
Qed.

Lemma cop4_perp_in2__col : forall A B A' B' X Y P,
  Coplanar X Y A A' -> Coplanar X Y A B' ->
  Coplanar X Y B A' -> Coplanar X Y B B' ->
  Perp_at P A B X Y -> Perp_at P A' B' X Y  -> Col A B A'.
Proof.
intros.
assert(HP1:= H3).
assert(HP2:=H4).
assert(Col A B P /\ Col X Y P).
apply perp_in_col in H3.
spliter.
split; Col.
spliter.
unfold Perp_at in H3.
unfold Perp_at in H4.
spliter.
induction(eq_dec_points A P);
induction(eq_dec_points P X).
subst A.
subst X.
assert(Per B P Y).
apply(H14 B Y); Col.
assert(Per A' P Y).
apply(H10 A' Y); Col.
apply col_permutation_2.
apply cop_per2__col with Y; Cop.
subst A.
assert(Per B P X).
apply(H14 B X); Col.
assert(Per A' P X).
apply(H10 A' X); Col.
apply col_permutation_2.
apply cop_per2__col with X; auto.
apply coplanar_perm_12.
apply col_cop__cop with Y; Col; Cop.
subst X.
assert(Per A P Y).
apply(H14 A Y); Col.
induction(eq_dec_points P A').
subst A'.
assert(Per B' P Y).
apply(H10 B' Y); Col.
assert(Col A B' P).
apply cop_per2__col with Y; Cop.
ColR.

assert(Per A' P Y).
apply(H10 A' Y); Col.
assert(Col A A' P).
apply cop_per2__col with Y; Cop.
ColR.

assert(Per A P X).
apply(H14 A X); Col.
induction(eq_dec_points P A').
subst A'.
assert(Per B' P X).
apply(H10 B' X); Col.
assert(Col A B' P).
apply cop_per2__col with X; auto.
apply coplanar_perm_12.
apply col_cop__cop with Y; Col; Cop.
ColR.

assert(Per A' P X).
apply(H10 A' X); Col.
assert(Col A A' P).
apply cop_per2__col with X; auto.
apply coplanar_perm_12.
apply col_cop__cop with Y; Col; Cop.
ColR.
Qed.


Lemma l13_2 : forall A B C D E, TS A B C D -> Per B C A -> Per B D A -> Col C D E -> Perp A E C D
    -> CongA B A C D A E /\ CongA B A D C A E /\ Bet C E D.
Proof.
    intros.
    assert(HH:= H).
    unfold TS in HH.
    assert(~ Col C A B).
      spliter.
      assumption.
    spliter.
    assert(C <> D).
      intro.
      subst D.
      assert(OS A B C C).
        apply one_side_reflexivity.
        assumption.
      apply l9_9 in H.
      contradiction.
    assert(exists C', CongA B A C D A C' /\ OS D A C' B).
      apply(angle_construction_1 B A C D A B).
        intro.
        apply H5.
        Col.
      intro.
      apply H6.
      Col.
    ex_and H9 E'.
    assert(A <> B /\ A <> C /\ A <> D).
      unfold CongA in H9.
      spliter; auto.
    spliter.
    assert(HH:=l11_22 C A E' B D A B E').
    assert(HH1:=ts_per_per_ts A B C D H H0 H1).
    unfold TS in HH1.
    assert (~ Col A C D).
      spliter.
      assumption.
    spliter.
    ex_and H7 T.
    ex_and H17 T2.
    assert(T = T2).
      apply (l6_21 A B C D); Col.
    subst T2.
    assert(InAngle B D A C).
      unfold InAngle.
      repeat split; auto.
      exists T.
      split.
        Between.
      right.
      unfold Out.
      repeat split.
        intro.
        subst T.
        assert(~ Col C D A /\ Per A E D).
          apply(l8_16_1 C D A D E H2).
            Col.
          apply perp_sym.
          assumption.
        spliter.
        apply H20.
        Col.
        auto.
      left.
      assumption.
    assert(LeA C A B C A D).
      unfold LeA.
      exists B.
      split.
        apply l11_24.
        assumption.
      apply conga_refl; auto.
    assert(InAngle E' D A C).
      eapply lea_in_angle.
        apply lea_comm.
        eapply l11_30.
        apply H21.
        apply conga_comm.
        assumption.
        apply conga_refl; auto.
      assert(HH1:=ts_per_per_ts A B C D H H0 H1).
      assert(OS D A C B).
        apply ts_ts_os.
          apply invert_two_sides.
          assumption.
        apply l9_2.
        assumption.
      eapply one_side_transitivity.
        apply H22.
      apply one_side_symmetry.
      assumption.
    unfold InAngle in H22.
    spliter.
    ex_and H25 E''.
    induction H26.
      subst E''.
      apply False_ind.
      apply H15.
      apply bet_col in H25.
      Col.
    assert(CongA B A C D A E'').
      eapply (out_conga B A C D A E').
        auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
      apply l6_6.
      auto.
    assert(A <> T).
      intro.
      subst T.
      apply H15.
      Col.
    induction(eq_dec_points E'' T).
      subst E''.
      apply l13_2_1; auto.
      eapply out_conga.
        apply conga_left_comm.
        apply H27.
        apply out_trivial; auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
      unfold Out.
      repeat split; auto.
    assert(D <> E'').
      intro.
      subst E''.
      apply conga_sym in H27.
      apply eq_conga_out in H27.
      apply out_col in H27.
      apply H5.
      Col.
    assert(C <> E'').
      intro.
      subst E''.
      assert(Out A B D \/ TS C A B D).
        apply(conga_cop__or_out_ts C A B D).
          Cop.
        apply conga_comm.
        assumption.
      induction H31.
        apply out_col in H31.
        apply H6.
        Col.
      assert(OS A C B D).
        apply ts_ts_os.
          assumption.
        apply ts_per_per_ts; auto.
      apply invert_one_side in H32.
      apply l9_9 in H31.
      contradiction.
    assert(A <> E'').
      intro.
      subst E''.
      unfold Out in H26.
      tauto.
    assert(~ Col E'' A B).
      intro.
      apply H29.
      apply bet_col in H25.
      apply (l6_21 A B C D); Col.
    assert(CongA C A E'' D A B).
      apply (l11_22 C A E'' B D A B E'').
      split.
        induction(one_side_dec A B C E'').
          right.
          split.
            auto.
          unfold OS.
          exists C.
          split.
            unfold TS.
            repeat split.
              auto.
              intro.
              apply H15.
              apply bet_col in H25.
              apply col_permutation_1.
              eapply (col_transitivity_1 _ E''); Col.
              intro.
              apply bet_col in H25.
              apply H15.
              apply col_permutation_2.
              eapply (col_transitivity_1 _ E''); Col.
            exists E''.
            split; Col.
          assert(TS A E'' T C).
            unfold TS.
            repeat split.
              auto.
              intro.
              apply H29.
              apply (l6_21 A B C D);Col.
              eapply (col_transitivity_1 _ T); Col.
              apply bet_col in H25.
              Col.
              intro.
              apply H15.
              ColR.
            exists E''.
            split.
              Col.
            assert(Bet C T E'' \/ Bet C E'' T).
              eapply l5_3.
                apply H18.
              Between.
            induction H35.
              assert(TS A B C E'').
                unfold TS.
                repeat split; auto.
                exists T.
                split.
                  Col.
                auto.
              apply l9_9 in H36.
              contradiction.
            Between.
          eapply (l9_5 _ _ T _ A); Col.
          unfold Out.
          repeat split; auto.
        left.
        apply cop__not_one_side_two_sides in H34; auto.
        split.
          auto.
        assert(OS A B D E'').
          eapply l9_8_1.
            apply l9_2.
            apply H.
          apply l9_2.
          assumption.
        assert(TS A E'' T D).
          unfold TS.
          repeat split.
            auto.
            intro.
            apply H33.
            apply col_permutation_2.
            apply(col_transitivity_1 _ T); Col.
            intro.
            apply bet_col in H25.
            apply H15.
            apply col_permutation_1.
            eapply (col_transitivity_1 _ E''); Col.
          exists E''.
          split.
            Col.
          assert(Bet D T E'' \/ Bet D E'' T).
            eapply l5_3.
              apply between_symmetry.
              apply H18.
            assumption.
          induction H36.
            assert(TS A B D E'').
              unfold TS.
              repeat split; auto.
              exists T.
              split; Col.
            apply l9_9 in H37.
            contradiction.
          Between.
        apply l9_2.
        eapply (l9_5 _ _ T _ A).
          auto.
          Col.
        unfold Out.
        repeat split; auto.
        apply col_cop__cop with D; Col; Cop.

      split.
        apply conga_left_comm.
        auto.
      apply conga_right_comm.
      apply conga_refl; auto.
    (***********************)
    prolong B C C' B C.
    prolong B D D' B D.
    assert(Cong_3 B A D D' A D).
      apply l8_2 in H1.
      unfold Per in H1.
      ex_and H1 D''.
      assert(Midpoint D B D').
        unfold Midpoint.
        split; Cong.
      assert(D' = D'').
        eapply symmetric_point_uniqueness.
          apply H40.
        auto.
      subst D''.
      repeat split; Cong.
    assert(CongA B A D D' A D).
      apply cong3_conga; auto.
    assert(Cong_3 B A C C' A C).
      apply l8_2 in H0.
      unfold Per in H0.
      ex_and H0 C''.
      assert(Midpoint C B C').
        unfold Midpoint.
        split; Cong.
      assert(C' = C'').
        eapply symmetric_point_uniqueness.
          apply H42.
        auto.
      subst C''.
      repeat split; Cong.
    assert(CongA B A C C' A C).
      apply cong3_conga; auto.
    assert(CongA E'' A C' D' A E'').
      apply l11_22 with C D.
      split.
        clear HH.
        (***************************************************)
        left.
        assert(OS C A D E'').
          eapply out_out_one_side.
            apply one_side_reflexivity.
            intro.
            apply H15.
            Col.
          unfold Out.
          repeat split; auto.
          right.
          Between.
        assert(OS C A B D).
          apply in_angle_one_side.
            intro.
            apply H15.
            Col.
            intro.
            apply H5.
            Col.
          apply l11_24.
          auto.
        assert(TS C A B C').
          unfold TS.
          repeat split.
            auto.
            intro.
            apply H5.
            Col.
            intro.
            apply H5.
            apply bet_col in H35.
            assert(C <> C').
              intro.
              subst C'.
              apply cong_symmetry in H36.
              apply cong_identity in H36.
              subst C.
              apply H16.
              Col.
            eapply (col_transitivity_1 _ C'); Col.
          exists C.
          split; Col.
        assert(OS C A B E'').
          eapply one_side_transitivity.
            apply H44.
          auto.
        assert(OS D A C E'').
          eapply out_out_one_side.
            apply one_side_reflexivity.
            intro.
            apply H15.
            Col.
          unfold Out.
          repeat split; auto.
        assert(OS D A B C).
          apply in_angle_one_side.
            intro.
            apply H15.
            Col.
            intro.
            apply H6.
            Col.
          auto.
        assert(TS D A B D').
          unfold TS.
          repeat split.
            auto.
            intro.
            apply H6.
            Col.
            intro.
            apply H6.
            apply bet_col in H37.
            assert(D <> D').
              intro.
              subst D'.
              apply cong_symmetry in H38.
              apply cong_identity in H38.
              subst D.
              apply H16.
              Col.
            eapply (col_transitivity_1 _ D'); Col.
          exists D.
          split; Col.
        assert(OS D A B E'').
          eapply one_side_transitivity.
            apply H48.
          auto.
        split.
          apply invert_two_sides.
          eapply l9_8_2.
            apply H45.
          auto.
        apply invert_two_sides.
        apply l9_2.
        eapply l9_8_2.
          apply H49.
        auto.
      split.
        eapply conga_trans.
          apply conga_comm.
          apply H34.
        apply H40.
      apply conga_sym.
      eapply conga_trans.
        apply conga_sym.
        apply H27.
      apply conga_right_comm.
      auto.
    assert(D' <> B).
      intro.
      subst D'.
      apply between_identity in H37.
      subst D.
      apply H16.
      Col.
    assert(C' <> B).
      intro.
      subst C'.
      apply between_identity in H35.
      subst C.
      apply H16.
      Col.
    assert(~ Col C' D' B).
      intro.
      apply H16.
      apply bet_col in H35.
      apply  bet_col in H37.
      assert(Col C' B D).
        ColR.
      ColR.
    assert(Par_strict C' D' C D).
      apply(triangle_mid_par C' D' B D C).
        auto.
        unfold Midpoint.
        split.
          Between.
        Cong.
      unfold Midpoint.
      split.
        Between.
      Cong.
    assert(TS A E'' C D).
      unfold TS.
      repeat split.
        auto.
        intro.
        apply H15.
        apply bet_col in H25.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ E''); Col.
        intro.
        apply H15.
        apply bet_col in H25.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ E''); Col.
      exists E''.
      split; Col.
      Between.
    assert(TS B A C D).
      apply in_angle_two_sides.
        intro.
        apply H5.
        Col.
        intro.
        apply H6.
        Col.
      apply l11_24.
      assumption.
    assert (OS A B C C').
      apply (out_one_side_1 _ _ _ _ B); Col.
      unfold Out.
      repeat split; auto.
      intro.
      subst C.
      apply H5.
      Col.
    assert (OS A B D D').
      apply (out_one_side_1 _ _ _ _ B); Col.
      unfold Out.
      repeat split; auto.
      intro.
      subst D.
      apply H6.
      Col.
    apply invert_two_sides in H49.
    assert(TS A B C' D).
      eapply l9_8_2.
        apply H49.
      auto.
    assert(TS A B C' D').
      apply l9_2.
      eapply l9_8_2.
        apply l9_2.
        apply H52.
      auto.
    assert(Perp  C' D' A E'').
      eapply cong_conga_perp.
        apply conga_right_comm in H43.
        apply conga_cop__or_out_ts in H43.
        induction H43.
          assert(OS A B C' D').
            eapply (out_one_side_1 _ _ _ _ A); Col.
            intro.
            assert(B <> C').
              intro.
              subst C'.
              apply H46.
              Col.
            apply H5.
            apply col_permutation_1.
            eapply col_transitivity_1.
              apply H55.
              apply bet_col in H35.
              Col.
            Col.
          apply l9_9 in H53.
          contradiction.
        apply invert_two_sides.
        assumption.
        apply coplanar_pseudo_trans with B C D; Cop.
        unfold Cong_3 in *.
        spliter.
        apply cong_transitivity with B A; Cong.
      apply conga_left_comm.
      assumption.


assert(Cong A C' A B).
apply l8_2 in H0.
unfold Per in H0.
ex_and H0 C''.
assert(C' = C'').
apply(symmetric_point_uniqueness B C C' C''); finish.
split; finish.
subst C''.
Cong.

assert(Cong A D' A B).
apply l8_2 in H1.
unfold Per in H1.
ex_and H1 D''.
assert(D' = D'').
apply(symmetric_point_uniqueness B D D' D''); finish.
split; finish.
subst D''.
Cong.

assert(Cong A C' A D').
apply cong_transitivity with A B; Cong.

assert(HM:=midpoint_existence C' D').
ex_and HM R.
assert(exists X Y : Tpoint, Perp_at R X Y C' D' /\ Perp X Y D C /\ Coplanar C' D' B X /\ Coplanar C' D' B Y).
apply l13_1_aux;
finish.
split; Between; Cong.
split; Between; Cong.
ex_and H59 X.
ex_and H60 Y.

assert(HXY:X <> Y).
apply perp_distinct in H60.
tauto.

assert(Perp C D A E'').

induction(eq_dec_points A R).
subst R.

assert(Perp_at A C' D' A E'').
assert_cols.
apply(l8_14_2_1b_bis C' D' A E'' A); Col.

assert(Coplanar B C' D' E'').
apply coplanar_pseudo_trans with B C D; Cop.
assert(Coplanar C' D' X E'').
apply coplanar_trans_1 with B; Col; Cop.
assert(Coplanar C' D' Y E'').
apply coplanar_trans_1 with B; Col; Cop.
assert(Coplanar C' D' X A).
exists A.
left.
split; Col.
assert(Coplanar C' D' Y A).
exists A.
left.
split; Col.
assert(Col X Y A).
apply(cop4_perp_in2__col X Y A E'' C' D' A); Perp.
assert(Col X Y E'').
apply(cop4_perp_in2__col X Y E'' A C' D' A); Perp.
apply perp_sym.
induction(eq_dec_points Y A).
subst Y.
apply(perp_col _ X).
auto.
Perp.
Col.
apply(perp_col _ Y).
auto.
apply perp_left_comm.
apply (perp_col _ X); Col.
Perp.
ColR.

assert(R <> C').
intro.
subst R.
unfold Midpoint in H58.
spliter.
apply cong_symmetry in H64.
apply cong_identity in H64.
subst D'.
apply perp_distinct in H54.
tauto.

assert(Per A R C').
unfold Per.
exists D'.
split; finish.
apply per_perp_in in H65; auto.
apply perp_in_sym in H65.
apply perp_in_perp_bis in H65.
induction H65.
apply perp_comm in H65.
assert(Perp C' D' R A).
apply(perp_col _ R).
intro.
subst D'.
apply perp_distinct in H54.
tauto.
assumption.
assert_cols.
Col.

assert(Perp_at R C' D' R A).
apply(l8_14_2_1b_bis C' D' R A R); Col.
assert_cols.
Col.

assert(Coplanar C' D' X A).
apply coplanar_trans_1 with B; Cop; Col.
assert(Coplanar C' D' Y A).
apply coplanar_trans_1 with B; Cop; Col.
assert(Coplanar C' D' X R).
exists R.
left.
split; Col.
assert(Coplanar C' D' Y R).
exists R.
left.
split; Col.
assert( Col X Y A).
apply(cop4_perp_in2__col X Y A R C' D' R); Perp.
assert( Col X Y R).
apply(cop4_perp_in2__col X Y R A C' D' R); Perp.

assert(Col A E'' R).
apply(cop_perp2__col A E'' R C' D'); Perp.
exists R.
left.
split; Col.

assert(Col A R X).
ColR.
assert(Col A R Y).
ColR.


apply perp_sym.
induction(eq_dec_points X A).
subst X.
apply (perp_col _ Y); finish.
ColR.
apply (perp_col _ X); finish.
apply perp_left_comm.
apply(perp_col _ Y); finish.
ColR.
apply perp_distinct in H65.
tauto.

    assert(Col A E E'').
      apply cop_perp2__col with C D; Perp.
      exists E.
      left.
      split; Col.
    assert(E'' = E).
      apply (l6_21 C D A E); Col.
      apply perp_not_eq_1 in H3.
      assumption.
    subst E''.
    split.
      auto.
    split.
      apply conga_sym.
      apply conga_right_comm.
      auto.
    Between.
Qed.

Lemma perp2_refl : forall A B P, A <> B -> Perp2 A B A B P.
Proof.
    intros.
    induction(col_dec A B P).
      assert(HH:=not_col_exists A B H).
      ex_and HH X.
      assert(HH:=l10_15 A B P X  H0 H1).
      ex_and HH Q.
      unfold Perp2.
      exists Q.
      exists P.
      split; Perp.
      Col.
    assert(HH:=l8_18_existence A B P H0).
    ex_and HH Q.
    unfold Perp2.
    exists P.
    exists Q.
    split; Perp.
    Col.
Qed.


Lemma perp2_sym : forall A B C D P, Perp2 A B C D P -> Perp2 C D A B P.
Proof.
    unfold Perp2.
    intros.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    exists Y.
    repeat split; Perp.
Qed.


Lemma perp2_left_comm : forall A B C D P, Perp2 A B C D P -> Perp2 B A C D P.
Proof.
    unfold Perp2.
    intros.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    exists Y.
    repeat split; Perp.
Qed.


Lemma perp2_right_comm : forall A B C D P, Perp2 A B C D P -> Perp2 A B D C P.
Proof.
    unfold Perp2.
    intros.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    exists Y.
    repeat split; Perp.
Qed.


Lemma perp2_comm : forall A B C D P, Perp2 A B C D P -> Perp2 B A D C P.
Proof.
    unfold Perp2.
    intros.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    exists Y.
    repeat split; Perp.
Qed.


Lemma perp2_pseudo_trans : forall A B C D E F P, Perp2 A B C D P -> Perp2 C D E F P -> ~ Col C D P ->
  Perp2 A B E F P.
Proof.
    intros.
    unfold Perp2 in *.
    ex_and H X.
    ex_and H2 Y.
    ex_and H0 X'.
    ex_and H4 Y'.
    assert(Par X Y X' Y').
      assert(Coplanar P C D X).
      induction(eq_dec_points X P).
        subst.
        exists P.
        left.
        split; Col.
      apply coplanar_perm_9.
      apply perp__coplanar.
      apply perp_col with Y; Col.
      assert(Coplanar P C D Y).
      induction(eq_dec_points Y P).
        subst.
        exists P.
        left.
        split; Col.
      apply coplanar_perm_9.
      apply perp__coplanar.
      apply perp_col with X; Perp; Col.
      assert(Coplanar P C D X').
      induction(eq_dec_points X' P).
        subst.
        exists P.
        left.
        split; Col.
      apply coplanar_perm_9.
      apply perp__coplanar.
      apply perp_col with Y'; Col.
      assert(Coplanar P C D Y').
      induction(eq_dec_points Y' P).
        subst.
        exists P.
        left.
        split; Col.
      apply coplanar_perm_9.
      apply perp__coplanar.
      apply perp_col with X'; Perp; Col.
      apply (l12_9 _ _ _ _ C D); Perp; apply coplanar_trans_1 with P; Col.
    exists X.
    exists Y.
    assert(Col X X' Y').
      induction H6.
        unfold Par_strict in H6.
        spliter.
        apply False_ind.
        apply H9.
        exists P.
        split; Col.
      spliter.
      auto.
    assert(Col Y X' Y').
      induction H6.
        unfold Par_strict in H6.
        spliter.
        apply False_ind.
        apply H10.
        exists P.
        split; Col.
      spliter.
      auto.
    repeat split; auto.
    assert(X <> Y).
      apply perp_not_eq_1 in H2.
      auto.
    induction(eq_dec_points X Y').
      subst Y'.
      apply (perp_col _ X').
        auto.
        Perp.
      ColR.
    apply (perp_col _ Y').
      auto.
      apply perp_left_comm.
      apply(perp_col _ X').
        auto.
        Perp.
      ColR.
    apply par_symmetry in H6.
    induction H6.
      unfold Par_strict in H6.
      spliter.
      apply False_ind.
      apply H13.
      exists P.
      split; Col.
    spliter.
    Col.
Qed.

Lemma perp2_preserves_bet23 : forall O A B A' B', Bet O A B -> Col O A' B' -> ~Col O A A' ->
    Perp2 A A' B B' O -> Bet O A' B'.

Proof.
intros.

assert(HD1: A <> A').
intro.
subst A'.
apply H1.
Col.

induction(eq_dec_points A' B').
subst B'.
Between.

assert(A <> B).
intro.
subst B.
unfold Perp2 in H2.
ex_and H2 X.
ex_and H4 Y.
assert(Col A A' B').
apply(cop_perp2__col A A' B' X Y); Perp.
exists O.
left.
split; Col.
apply H1.
ColR.

assert(Par A A' B B').
unfold Perp2 in H2.
ex_and H2 X.
ex_and H5 Y.
assert(Coplanar X Y A B).
exists O.
left.
split; Col.
apply (l12_9 _ _ _ _ X Y); Perp.
induction(col_dec B X Y).
exists A.
left.
assert_diffs.
split; ColR.
apply coplanar_trans_1 with B; Cop.
induction(col_dec A X Y).
exists B.
left.
assert_diffs.
split; ColR.
apply coplanar_trans_1 with A; Cop.
exists O.
left.
split; Col.
induction H5.
assert(OS A A' B B').
apply l12_6; Par.
assert(TS A A' O B).
repeat split; Col.
intro.
apply H5.
exists B.
split; Col.
exists A.
split; Col.

assert(TS A A' B' O).
apply( l9_8_2 A A' B B' O); auto.
apply l9_2.
auto.

unfold TS in H8.
spliter.
ex_and H10 T.
assert(T = A').
apply (l6_21 A A' O B'); Col.
intro.
subst B'.
apply between_identity in H11.
subst T.
contradiction.
subst T.
Between.

spliter.
apply False_ind.
apply H1.
ColR.
Qed.

Lemma perp2_preserves_bet13 : forall O B C B' C', Bet B O C -> Col O B' C' -> ~Col O B B' ->
    Perp2 B C' C B' O -> Bet B' O C'.

Proof.
intros.

induction(eq_dec_points C' O).
subst C'.
Between.
induction(eq_dec_points B' O).
Between.

assert(B <> O).
intro.
subst B.
apply H1.
Col.

assert(B' <> O).
intro.
subst B'.
apply H1.
Col.

assert(Col B O C).
apply bet_col.
Between.

induction(eq_dec_points B C).
subst C.
apply between_identity in H.
contradiction.

assert(Par B C' C B').
unfold Perp2 in H2.
ex_and H2 X.
ex_and H9 Y.
assert(Coplanar X Y B C).
exists O.
left.
split; Col.
assert(Coplanar X Y C' B').
exists O.
left.
split; Col.
apply (l12_9 _ _ _ _ X Y); Perp.
induction(col_dec C' X Y).
exists B'.
left.
assert_diffs.
split; ColR.
apply coplanar_trans_1 with C'; Cop.
induction(col_dec B X Y).
exists C.
left.
assert_diffs.
split; ColR.
apply coplanar_trans_1 with B; Cop.

assert(Par_strict B C' C B').
induction H9.
assumption.
spliter.
apply False_ind.
apply H1.
ColR.

assert(C<> O).
intro.
subst C.
assert(Par_strict B C' O C').
apply(par_strict_col_par_strict _ _ _ B'); auto.
apply H11.
exists C'.
Col.

assert(B' <> O).
intro.
subst B'.
assert(Par_strict B C' O B).
apply(par_strict_col_par_strict _ _ _ C); auto.
apply par_strict_right_comm.
assumption.
Col.
apply H12.
exists B.
split; Col.

unfold Perp2 in H2.
ex_and H2 X.
ex_and H13 Y.

assert(X <> Y).
apply perp_distinct in H13.
tauto.

induction(col_dec X Y B).
assert(Col X Y C).
ColR.

apply(per13_preserves_bet_inv  B' O C' C B); Between.
Col.

apply perp_in_per.
induction(eq_dec_points X C).
subst X.
assert(Perp C O B' C).
apply(perp_col _ Y); Perp.
ColR.
apply perp_perp_in in H18.
Perp.
assert(Perp X C C B').
apply(perp_col _ Y); Perp.
assert(Perp C O B' C).
apply(perp_col _ X); Perp.
ColR.
apply perp_perp_in in H20.
Perp.

apply perp_in_per.
induction(eq_dec_points X B).
subst X.
assert(Perp B O C' B).
apply(perp_col _ Y); Perp.
ColR.
apply perp_perp_in in H18.
Perp.
assert(Perp X B C' B).
apply(perp_col _ Y); Perp.
assert(Perp B O C' B).
apply(perp_col _ X); Perp.
ColR.
apply perp_perp_in in H20.
Perp.

assert(HP1:=l8_18_existence X Y B H16).
ex_and HP1 B0.
assert(~Col X Y C).
intro.
apply H16.
ColR.
assert(HP1:=l8_18_existence X Y C H19).
ex_and HP1 C0.

assert(B0 <> O).
intro.
subst B0.
assert(Par B O B C').
apply(l12_9 B O B C' X Y); Perp; Cop.
induction H22.
apply H22.
exists B.
split; Col.
spliter.
apply H1.
ColR.

assert(C0 <> O).
intro.
subst C0.
assert(Par C O C B').
apply(l12_9 C O C B' X Y); Perp; Cop.
induction H23.
apply H23.
exists C.
split; Col.
spliter.
apply H1.
ColR.

assert(Bet B0 O C0).

apply(per13_preserves_bet B O C B0 C0); auto.
Between.
ColR.
apply perp_in_per.
induction(eq_dec_points X B0).
subst X.
assert(Perp B0 O B B0).
apply(perp_col _ Y); Perp.
Col.
apply perp_perp_in in H24.
Perp.
assert(Perp X B0 B B0).
apply(perp_col _ Y); Perp.
assert(Perp B0 O B B0).
apply (perp_col _ X); Perp.
ColR.
apply perp_perp_in in H26.
Perp.

apply perp_in_per.
induction(eq_dec_points X C0).
subst X.
assert(Perp C0 O C C0).
apply(perp_col _ Y); Perp.
Col.
apply perp_perp_in in H24.
Perp.
assert(Perp X C0 C C0).
apply(perp_col _ Y); Perp.
assert(Perp C0 O C C0).
apply (perp_col _ X); Perp.
ColR.
apply perp_perp_in in H26.
Perp.

induction(eq_dec_points C' B0).
subst B0.
assert(B' = C0).
apply bet_col in H24.
apply (l6_21 C' O C C0); Col.
assert(Par C B' C C0).
apply(l12_9 C B' C C0 X Y); Perp; Cop.

induction H25.
apply False_ind.
apply H25.
exists C.
split; Col.
spliter.
Col.
intro.
apply H1.
ColR.
intro.
subst C0.
apply H1.
ColR.
apply(cop_perp2__col C C0 B' X Y); Perp.
exists C0.
left.
split; Col.
subst C0.
Between.

assert(B' <> C0).
intro.
subst C0.
apply H25.
apply (l6_21 B' O B B0); Col.
intro.
subst B0.
Col.
assert(Par B C' B B0).
apply(l12_9 B C' B B0 X Y); Perp; Cop.

induction H26.
apply False_ind.
apply H26.
exists B.
split; Col.
spliter.
Col.

assert(Col C C0 B').
apply(cop_perp2__col C C0 B' X Y); Perp.
exists C0.
left.
split; Col.
assert(Col B B0 C').
apply(cop_perp2__col B B0 C' X Y); Perp.
exists B0.
left.
split; Col.

apply(per13_preserves_bet_inv B' O C' C0 B0); Between.
Col.

apply perp_in_per.
induction(eq_dec_points X C0).
subst X.
assert(Perp C0 O C B').
apply (perp_col _ Y); Perp.
Col.
assert(Perp B' C0 C0 O).
apply(perp_col _ C); Perp.
Col.
apply perp_comm in H30.
apply perp_perp_in in H30.
Perp.

assert(Perp X C0 C B').
apply(perp_col _ Y); Perp.
assert(Perp C0 O C B').
apply (perp_col _ X); Perp.
ColR.
assert(Perp B' C0 C0 O).
apply(perp_col _ C); Perp.
Col.
apply perp_comm in H32.
apply perp_perp_in in H32.
Perp.


apply perp_in_per.

assert(Perp C' B0 X Y).
apply (perp_col _ B); Perp.
Col.
induction (eq_dec_points X O).
subst X.
assert(Perp O B0 B0 C').
apply(perp_col _ Y);Perp.
apply perp_comm in H30.
apply perp_perp_in in H30.
Perp.
 
assert(Perp X O C' B0).
apply(perp_col _ Y); Perp.
Col.
assert(Perp O B0 B0 C').
apply(perp_col _ X); Perp.
ColR.
apply perp_comm in H32.
apply perp_perp_in in H32.
Perp.

Qed.


Lemma is_image_perp_in : forall A A' X Y, A <> A' -> X <> Y -> Reflect A A' X Y ->
  exists P, Perp_at P A A' X Y.
Proof.
intros.
unfold Reflect in H.
induction H1.
spliter.
unfold ReflectL in H2.
spliter.
ex_and H2 P.
induction H3.
exists P.

apply perp_in_sym.
apply perp_in_right_comm.
apply(l8_14_2_1b_bis X Y A' A P); Col.
assert_cols.
Col.
subst A'.
tauto.
spliter.
contradiction.
Qed.

Lemma perp_inter_perp_in_n
     : forall A B C D : Tpoint,
       Perp A B C D ->
       exists P : Tpoint, Col A B P /\ Col C D P /\ Perp_at P A B C D.
Proof.
intros.
assert(A <> B /\ C <> D).
apply perp_distinct in H.
tauto.
spliter.
induction(col_dec A B C).
exists C.
split; Col.
split; Col.
apply(l8_14_2_1b_bis A B C D C); Col.

assert(HH:=l8_18_existence A B C H2).
ex_and HH P.
exists P.
assert(Col C D P).
apply(cop_perp2__col C D P A B); Perp.
exists P.
left.
split; Col.
split; Col.
split; Col.
apply(l8_14_2_1b_bis A B C D P); Col.
Qed.

Lemma perp2_perp_in : forall A B C D O, Perp2 A B C D O -> ~Col O A B /\ ~Col O C D ->
    exists P, exists Q, Col A B P /\ Col C D Q /\ Col O P Q /\ Perp_at P O P A B /\ Perp_at Q O Q C D.
  Proof.
    intros.
    unfold Perp2 in H.
    ex_and H X.
    ex_and H1 Y.
    assert(X <> Y).
      apply perp_not_eq_1 in H2.
      auto.
    assert(HH:= perp_inter_perp_in_n X Y A B H2).
    ex_and HH P.
    assert(HH:= perp_inter_perp_in_n X Y C D H3).
    ex_and HH Q.
    exists P.
    exists Q.
    split; auto.
    split; auto.
    split.
      apply (col3 X Y); Col.
    split.
      induction(eq_dec_points X O).
        subst X.
        apply perp_in_sym.
        apply(perp_in_col_perp_in A B O Y P P).
          intro.
          subst P.
          apply H.
          Col.
          Col.
        apply perp_in_sym.
        auto.
      assert(Perp_at P A B X O).
        apply(perp_in_col_perp_in A B X Y O P H11).
          Col.
        apply perp_in_sym.
        auto.
      apply perp_in_right_comm in H12.
      eapply (perp_in_col_perp_in _ _ _ _ P) in H12 .
        apply perp_in_sym.
        auto.
        intro.
        subst P.
        apply H.
        Col.
      ColR.
    induction(eq_dec_points X O).
      subst X.
      apply perp_in_sym.
      apply(perp_in_col_perp_in C D O Y Q Q).
        intro.
        subst Q.
        apply H0.
        Col.
        Col.
      apply perp_in_sym.
      auto.
    assert(Perp_at Q C D X O).
      apply(perp_in_col_perp_in C D X Y O Q H11).
        Col.
      apply perp_in_sym.
      auto.
    apply perp_in_right_comm in H12.
    eapply (perp_in_col_perp_in _ _ _ _ Q) in H12 .
      apply perp_in_sym.
      auto.
      intro.
      subst Q.
      apply H0.
      Col.
    ColR.
Qed.


Lemma l13_8 : forall O P Q U V, U <> O -> V <> O -> Col O P Q -> Col O U V
    -> Per P U O -> Per Q V O -> (Out O P Q <-> Out O U V).
Proof.
    intros.
    induction(eq_dec_points P U).
      subst P.
      assert(Col Q V O).
        ColR.
      assert(HH:= l8_9 Q V O H4 H5).
      induction HH.
        subst Q.
        tauto.
      subst V.
      tauto.
    assert(Q <> V).
      intro.
      subst Q.
      assert(HH:= per_not_col P U O H5 H H3).
      apply HH.
      ColR.
split.
intro.
unfold Out in H7.
spliter.
induction H9.

assert(HH:= per23_preserves_bet O P Q U V).
repeat split; auto.
left.
apply(per23_preserves_bet O P Q U V); auto.
Perp.
Perp.
repeat split; auto.
right.
apply(per23_preserves_bet O Q P V U); Col.
Perp.
Perp.

intro.
unfold Out in H7.
spliter.

repeat split.
intro.
subst P.
apply l8_8 in H3.
contradiction.
intro.
subst Q.
apply l8_8 in H4.
contradiction.
induction H9.
left.
apply(per23_preserves_bet_inv O P Q U V); Perp.
right.
apply(per23_preserves_bet_inv O Q P V U); Perp.
Col.
Qed.

Lemma perp_in_rewrite : forall A B C D P, Perp_at P A B C D ->
                                          Perp_at P A P P C \/
                                          Perp_at P A P P D \/
                                          Perp_at P B P P C \/
                                          Perp_at P B P P D.
Proof.
intros.
assert(HH:= perp_in_col A B C D P H).
spliter.
induction(eq_dec_points A P);
induction(eq_dec_points C P).
subst A .
subst C.
right;right;right.
Perp.
subst A.
right; right; left.
apply perp_in_right_comm.
assert(HP:=perp_in_col_perp_in P B C D P P H3 H1 H).
Perp.
subst C.
right; left.
apply perp_in_sym.
apply(perp_in_col_perp_in P D A B P P H2 H0).
Perp.
left.
assert(HP:= perp_in_col_perp_in A B C D P P H3 H1 H).
apply perp_in_sym.
apply perp_in_left_comm.
apply(perp_in_col_perp_in C P A B P P H2 H0).
Perp.
Qed.

Lemma gta_to_lta : forall A B C D E F, GtA A B C D E F -> LtA D E F A B C.
Proof.
unfold GtA.
tauto.
Qed.

Lemma lta_to_gta : forall A B C D E F, LtA A B C D E F -> GtA D E F A B C.
Proof.
unfold GtA.
tauto.
Qed.

Lemma perp_out_acute : forall A B C C', Out B A C' -> Perp A B C C' -> Acute A B C.
Proof.
intros.
assert(A <> B /\ C' <> B).
apply out_distinct.
assumption.
spliter.

assert(Perp B C' C C').
apply(perp_col _ A); Perp.
apply out_col in H.
Col.
assert(Per C C' B).
apply perp_in_per.
apply perp_sym in H3.
apply perp_left_comm in H3.
apply perp_perp_in in H3.
apply perp_in_comm.
assumption.
assert(Acute C' C B /\ Acute C' B C).
apply( l11_43 C' C B).

assert_diffs.
auto.
assumption.
left.
assumption.
spliter.

assert(C <> B).
intro.
subst C.
apply l8_8 in H4.
subst C'.
apply perp_distinct in H0.
tauto.

assert(CongA C' B C A B C ).
apply(out_conga A B C A B C C' C A C); auto.
apply conga_refl; auto.
apply out_trivial; auto.
apply out_trivial; auto.
apply out_trivial; auto.
apply (acute_conga__acute C' B C); auto.
Qed.

Lemma flat_all_lea : forall A B C, A <> B -> C <> B -> Bet A B C -> forall P, P <> B -> LeA A B P A B C.
Proof.
intros.
unfold LeA.
exists P.
spliter.
split.
unfold InAngle.
repeat split; auto.
exists B.
split; auto.
apply conga_refl; auto.
Qed.

Lemma perp_bet_obtuse : forall A B C C', B <> C' -> Perp A B C C' -> Bet A B C' -> Obtuse A B C.
Proof.
intros.
assert(HPO:=perp_out_acute).
assert(HBO:=acute_bet__obtuse).
assert(Col A B C').
apply bet_col in H1.
Col.
assert(Acute C' B C).
apply (HPO _ _ _ C').
apply out_trivial; auto.
apply perp_left_comm.
apply(perp_col _ A); Perp.
Col.
apply (HBO C').
Between.
intro.
subst B.
apply perp_distinct in H0.
tauto.
assumption.
Qed.

End L13_1.

Section L13_1_2D.

Context `{T2D:Tarski_2D}.

Lemma perp_in2__col : forall A B A' B' X Y P, Perp_at P A B X Y -> Perp_at P A' B' X Y  ->
  Col A B A'.
Proof.
intros A B A' B' X Y P.
apply cop4_perp_in2__col; apply all_coplanar.
Qed.

Lemma perp2_trans : forall A B C D E F P, Perp2 A B C D P -> Perp2 C D E F P -> Perp2 A B E F P.
Proof.
    intros.
    unfold Perp2 in *.
    ex_and H X.
    ex_and H1 Y.
    ex_and H0 X'.
    ex_and H3 Y'.
    assert(Par X Y X' Y').
      apply (l12_9_2D _ _ _ _ C D); Perp.
    exists X.
    exists Y.
    assert(Col X X' Y').
      induction H5.
        unfold Par_strict in H5.
        spliter.
        apply False_ind.
        apply H8.
        exists P.
        split; Col.
      spliter.
      auto.
    assert(Col Y X' Y').
      induction H5.
        unfold Par_strict in H5.
        spliter.
        apply False_ind.
        apply H9.
        exists P.
        split; Col.
      spliter.
      auto.
    repeat split; auto.
    assert(X <> Y).
      apply perp_not_eq_1 in H1.
      assert(X' <> Y').
        apply perp_not_eq_1 in H3.
        auto.
      auto.
    induction(eq_dec_points X Y').
      subst Y'.
      apply (perp_col _ X').
        auto.
        Perp.
      ColR.
    apply (perp_col _ Y').
      auto.
      apply perp_left_comm.
      apply(perp_col _ X').
        auto.
        Perp.
      ColR.
    apply par_symmetry in H5.
    induction H5.
      unfold Par_strict in H5.
      spliter.
      apply False_ind.
      apply H12.
      exists P.
      split; Col.
    spliter.
    Col.
Qed.

Lemma perp2_par : forall A B C D O, Perp2 A B C D O -> Par A B C D.
Proof.
    intros.
    unfold Perp2 in H.
    ex_and H X.
    ex_and H0 Y.
    apply (l12_9_2D _ _ _ _ X Y).
      Perp.
    Perp.
Qed.

End L13_1_2D.