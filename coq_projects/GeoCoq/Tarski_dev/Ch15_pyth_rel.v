Require Export GeoCoq.Tarski_dev.Ch16_coordinates.

Section PythagoreanFun.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Lemma Ps_Col : forall O E A, Ps O E A -> Col O E A.
Proof.
intros.
unfold Ps in H.
apply out_col in H;Col.
Qed.

Lemma PythRel_exists : forall O E E', ~ Col O E  E' -> forall A B,
 Col O E A -> Col O E B ->
 exists C, PythRel O E E' A B C.
Proof.
intros.
assert_diffs.
destruct (eq_dec_points O B).
- subst.
 exists A.
 unfold PythRel.
 split.
 unfold Ar2;auto.
 left;auto.
-
destruct (perp_exists O E O) as [X HX].
auto.
destruct (segment_construction_2 X O O B) as [B' [HB1 HB2]].
assert_diffs;auto.
destruct (segment_construction_2 E O A B') as [C [HC1 HC2]].
auto.
exists C.
unfold PythRel.
split.
unfold Ar2.
repeat split;auto.
destruct HC1.
auto using bet_col .
apply bet_col in H3. Col.
right.
exists B'.
split.

assert (Perp O X O B).
apply (perp_col1 O X O E B);Col.
Perp.
assert (Perp O B O B').
 apply (perp_col1 O B O X B').
 intro;treat_equalities.
 intuition.
 Perp.
 destruct HB1.
 apply bet_col in H6. Col.
 apply bet_col in H6. Col.
 Perp.
 split.
 Cong.
 Cong.
Qed.

Lemma opp_same_square : forall O E E' A B A2, Opp O E E' A B -> Prod O E E' A A A2 -> Prod O E E' B B A2.
intros.

assert(~Col O E E').
unfold Prod in H0.
spliter.
unfold Ar2  in H0.
tauto.

assert(exists ME : Tpoint, Opp O E E' E ME).
apply(opp_exists O E E' H1 E); Col;
assert(HH:= opp_prod O E E').
ex_and H2 ME.

assert(HH:= opp_prod O E E' ME A B H3 H).
assert(Prod O E E' B ME A).
apply(opp_prod O E E' ME B A H3).
apply opp_comm; auto.
assert(Prod O E E' ME B A).
apply prod_comm; auto.

assert(HP:=(prod_assoc O E E' A ME B B A A2 HH H4)).
destruct HP.
apply H5.
assumption.
Qed.


(**********)

Lemma PythOK : forall O E E' A B C A2 B2 C2, PythRel O E E' A B C -> 
 Prod O E E' A A A2 ->
 Prod O E E' B B B2 ->
 Prod O E E' C C C2 ->
 Sum O E E' A2 B2 C2.
Proof.
intros.

unfold PythRel in H.
spliter.
unfold Ar2 in H.
spliter.

induction H3.
spliter.
subst B.

assert(B2=O).
apply (prod_O_l_eq O E E' O); auto.
subst B2.

assert(A2 = C2).

induction H7.

subst C.
apply (prod_uniqueness O E E' A A); auto.
assert(Prod O E E' C C A2).
apply(opp_same_square O E E' A); auto.
apply (prod_uniqueness O E E' C C); auto.
subst C2.

apply (sum_A_O O E E' ); auto.
unfold Prod in H0.
spliter.
unfold Ar2 in H0; tauto.

(*
ex_and H3 B'.
assert(B2=O).
apply (prod_O_l_eq O E E' O); auto.
subst B2.
apply (sum_A_O O E E' ); auto.
unfold Prod in H0.
spliter.
unfold Ar2 in H0; tauto.
*)

assert(O <> E).
intro.
subst E.
apply H.
Col.

ex_and H3 B'.
assert(Per A O B').
apply l8_2.
apply (per_col _ _ B).
apply perp_distinct in H3.
tauto.
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
Perp.
ColR.

induction(eq_dec_points A O).
subst A.
assert(Cong O B O C).
apply cong_transitivity with O B'; Cong.
assert(B = C \/ Midpoint O B C).
apply l7_20; auto.
ColR.
induction H12.
subst C.
assert(B2 = C2).
apply(prod_uniqueness O E E' B B); auto.
subst C2.
assert(A2=O).
apply(prod_uniqueness O E E' O O); auto.
apply prod_0_l; auto.
subst A2.
apply sum_O_B; Col.
unfold Prod in H2.
spliter.
unfold Ar2 in H2.
tauto.
assert(A2=O).
apply(prod_uniqueness O E E' O O); auto.
apply prod_0_l; auto.
subst A2.
apply (midpoint_opp O E E') in H12;

unfold Midpoint in H12.
assert(C2 = B2).
apply(prod_uniqueness O E E' C C);auto.
apply (opp_same_square O E E' B C); auto.
subst C2.
apply sum_O_B; auto.
unfold Prod in H2.
spliter.
unfold Ar2 in H2.
tauto.
unfold Ar2.
repeat split; auto.

induction(out_dec O A E); induction(out_dec O B E);induction(out_dec O C E).

(****** A>0 ********* B>0 ********** C>0 ********)

apply(pythagoras O E E' A B' O A B C A2 B2 C2); auto.

unfold Length.
repeat split; auto.
unfold LeP.
left.
unfold LtP.
exists C.
split.
apply sum_diff.
apply sum_O_B; Col.
unfold Ps.
assumption.

unfold Length.
repeat split; Cong.
unfold LeP.
left.
unfold LtP.
exists A.
split.
apply sum_diff.
apply sum_O_B; Col.
unfold Ps.
assumption.

unfold Length.
repeat split; Cong.
unfold LeP.
left.
unfold LtP.
exists B.
split.
apply sum_diff.
apply sum_O_B; Col.
unfold Ps.
assumption.

(****** A>0 ********* B>0 ********** C<0 ********)

assert(exists OC : Tpoint, Opp O E E' C OC).
apply(opp_exists O E E' H C).
Col.
ex_and H15 OC.

assert(Ng O E C).
unfold Ng.
repeat split; auto.
intro.
subst C.

apply cong_symmetry in H9.
apply cong_identity in H9.
subst B'.
apply perp_right_comm in H3.
apply perp_not_col in H3.
apply H3.
ColR.
apply not_out_bet in H14.
assumption.
Col.

assert(Ps O E OC).
apply(opp_neg_pos O E E' C OC); auto.
apply(pythagoras O E E' A B' O A B OC A2 B2 C2); auto.

unfold Length.
repeat split; auto.
unfold Ps in H16.
apply out_col in H17.
Col.
unfold LeP.
left.
unfold LtP.
exists OC.
split; auto.
apply diff_A_O; auto.
unfold Ps in H17.
Col.

apply opp_midpoint in H16.
unfold Midpoint in H16.
spliter.
apply cong_transitivity with O C; Cong.

unfold Length.
repeat split; Cong.
unfold LeP.
left.
unfold LtP.
exists A.
split.
apply sum_diff.
apply sum_O_B; Col.
unfold Ps.
assumption.

unfold Length.
repeat split; Cong.
unfold LeP.
left.
unfold LtP.
exists B.
split.
apply sum_diff.
apply sum_O_B; Col.
unfold Ps.
assumption.
apply(opp_same_square O E E' C OC C2 H16 H2).

(****** A>0 ********* B<0 ********** C>0 ********)

assert(exists OB : Tpoint, Opp O E E' B OB).
apply(opp_exists O E E' H B).
Col.
ex_and H15 OB.

assert(Ng O E B).
unfold Ng.
repeat split; auto.
intro.
subst B.

apply cong_identity in H8.
subst B'.
apply perp_distinct in H3.
tauto.
apply not_out_bet in H13.
bet.
Col.

assert(Ps O E OB).
apply(opp_neg_pos O E E' B OB); auto.
apply(pythagoras O E E' A B' O A OB C A2 B2 C2); auto.

unfold Length.
repeat split; auto.
unfold Ps in H17.
apply out_col in H17.
Col.
unfold LeP.
left.
unfold LtP.
exists C.
split; auto.
apply diff_A_O; auto.
unfold Ps in H17.
Col.

unfold Length.
repeat split; Cong.
unfold LeP.
left.
unfold LtP.
exists A.
split.
apply sum_diff.
apply sum_O_B; Col.
unfold Ps.
assumption.

unfold Length.
repeat split; Cong;
Col.
unfold LeP.
left.
unfold LtP.
exists OB.
split; auto.
apply diff_A_O; auto.
Col.
apply opp_midpoint in H16.
unfold Midpoint in H16.
spliter.
apply cong_transitivity with O B; Cong.
apply(opp_same_square O E E' B OB B2 H16 H1).

(****** A>0 ********* B<0 ********** C<0 ********)

assert(exists OC : Tpoint, Opp O E E' C OC).
apply(opp_exists O E E' H C).
Col.
ex_and H15 OC.

assert(Ng O E C).
unfold Ng.
repeat split; auto.
intro.
subst C.

apply cong_symmetry in H9.
apply cong_identity in H9.
subst B'.
apply perp_right_comm in H3.
apply perp_not_col in H3.
apply H3.
ColR.
apply not_out_bet in H14.
assumption.
Col.

assert(Ps O E OC).
apply(opp_neg_pos O E E' C OC); auto.

assert(exists OB : Tpoint, Opp O E E' B OB).
apply(opp_exists O E E' H B).
Col.
ex_and H18 OB.

assert(Ng O E B).
unfold Ng.
repeat split; auto.
intro.
subst B.

apply cong_identity in H8.
subst B'.
apply perp_distinct in H3.
tauto.
apply not_out_bet in H13.
bet.
Col.

assert(Ps O E OB).
apply(opp_neg_pos O E E' B OB); auto.
apply(pythagoras O E E' A B' O A OB OC A2 B2 C2); auto.

unfold Length.
repeat split; auto.
unfold Ps in H17.
apply out_col in H17.
Col.
unfold LeP.
left.
unfold LtP.
exists OC.
split; auto.
apply diff_A_O; auto.
unfold Ps in H17.
Col.
apply opp_midpoint in H16.
unfold Midpoint in H16.
spliter.
apply cong_transitivity with O C; Cong.

unfold Length.
repeat split; Cong.
unfold LeP.
left.
unfold LtP.
exists A.
split.
apply sum_diff.
apply sum_O_B; Col.
unfold Ps.
assumption.

unfold Length.
repeat split; Cong;
Col.
unfold LeP.
left.
unfold LtP.
exists OB.
split; auto.
apply diff_A_O; auto.
Col.
apply opp_midpoint in H19.
unfold Midpoint in H19.
spliter.
apply cong_transitivity with O B; Cong.
apply(opp_same_square O E E' B OB B2 H19 H1).
apply(opp_same_square O E E' C OC C2 H16 H2).

(****** A<0 ********* B>0 ********** C>0 ********)

assert(exists OA : Tpoint, Opp O E E' A OA).
apply(opp_exists O E E' H A).
Col.
ex_and H15 OA.

assert(Ng O E A).
unfold Ng.
repeat split; auto.
apply not_out_bet in H12;auto.
Col.

apply(pythagoras O E E' A B' O OA B C A2 B2 C2); auto.

unfold Length.
repeat split; auto.
unfold LeP.
left.
unfold LtP.
exists C.
split.
apply sum_diff.
apply sum_O_B; Col.
unfold Ps.
assumption.

assert(Col O E OA).
unfold Opp in H16.
unfold Sum in H16.
spliter.
unfold Ar2 in H16.
tauto.

unfold Length.
repeat split; auto.
unfold LeP.
left.
unfold LtP.
exists OA.
split.
apply sum_diff.
apply sum_O_B; Col.
unfold Ps.
apply opp_midpoint in H16.
unfold Midpoint in H16.
spliter.
apply not_out_bet in H12.
assert(HP:=l5_2 A O E OA H11 H12 H16).
unfold Out.
repeat split; auto.
intro.
subst OA.
apply cong_identity in H18.
contradiction.
induction HP.
right; auto.
left; auto.
Col.

unfold Opp in H16.
apply opp_midpoint in H16.
unfold Midpoint in H16.
unfold Sum in H16.
spliter.
Cong.

unfold Length.
repeat split; Cong.
unfold LeP.
left.
unfold LtP.
exists B.
split.
apply sum_diff.
apply sum_O_B; Col.
unfold Ps.
assumption.
apply(opp_same_square O E E' A OA A2 H16 H0).

(****** A<0 ********* B>0 ********** C<0 ********)

assert(exists OC : Tpoint, Opp O E E' C OC).
apply(opp_exists O E E' H C).
Col.
ex_and H15 OC.

assert(Ng O E C).
unfold Ng.
repeat split; auto.
intro.
subst C.

apply cong_symmetry in H9.
apply cong_identity in H9.
subst B'.
apply perp_right_comm in H3.
apply perp_not_col in H3.
apply H3.
ColR.
apply not_out_bet in H14.
assumption.
Col.

assert(Ps O E OC).
apply(opp_neg_pos O E E' C OC); auto.

assert(exists OA : Tpoint, Opp O E E' A OA).
apply(opp_exists O E E' H A).
Col.
ex_and H18 OA.
assert(Ng O E A).
unfold Ng.
repeat split; auto.
apply not_out_bet in H12;auto.
Col.

assert(Col O E OA).
unfold Opp in H19.
unfold Sum in H19.
spliter.
unfold Ar2 in H19.
tauto.

apply(pythagoras O E E' A B' O OA B OC A2 B2 C2); auto.

unfold Length.
repeat split; auto.
unfold Ps in H17.
apply out_col in H17.
Col.
unfold LeP.
left.
unfold LtP.
exists OC.
split; auto.
apply diff_A_O; auto.
unfold Ps in H17.
Col.
apply opp_midpoint in H16.
unfold Midpoint in H16.
spliter.
apply cong_transitivity with O C; Cong.

unfold Length.
repeat split; auto.
unfold LeP.
left.
unfold LtP.
exists OA.
split.
apply sum_diff.
apply sum_O_B; Col.
unfold Ps.
apply opp_midpoint in H19.
unfold Midpoint in H19.
spliter.
apply not_out_bet in H12.
assert(HP:=l5_2 A O E OA H11 H12 H19).
unfold Out.
repeat split; auto.
intro.
subst OA.
apply cong_identity in H21.
contradiction.
induction HP.
right; auto.
left; auto.
Col.
apply opp_midpoint in H19.
unfold Midpoint in H19.
spliter.
Cong.

unfold Length.
repeat split; Cong.
unfold LeP.
left.
unfold LtP.
exists B.
split.
apply sum_diff.
apply sum_O_B; Col.
unfold Ps.
assumption.
apply(opp_same_square O E E' A OA A2 H19 H0).
apply(opp_same_square O E E' C OC C2 H16 H2).

(****** A<0 ********* B<0 ********** C>0 ********)

assert(exists OB : Tpoint, Opp O E E' B OB).
apply(opp_exists O E E' H B).
Col.
ex_and H15 OB.

assert(Ng O E B).
unfold Ng.
repeat split; auto.
intro.
subst B.

apply cong_identity in H8.
subst B'.
apply perp_distinct in H3.
tauto.
apply not_out_bet in H13.
bet.
Col.

assert(Ps O E OB).
apply(opp_neg_pos O E E' B OB); auto.

assert(exists OA : Tpoint, Opp O E E' A OA).
apply(opp_exists O E E' H A).
Col.
ex_and H18 OA.
assert(Ng O E A).
unfold Ng.
repeat split; auto.
apply not_out_bet in H12;auto.
Col.

assert(Col O E OA).
unfold Opp in H19.
unfold Sum in H19.
spliter.
unfold Ar2 in H19.
tauto.

apply(pythagoras O E E' A B' O OA OB C A2 B2 C2); auto.

unfold Length.
repeat split; auto.
unfold LeP.
left.
unfold LtP.
exists C.
split.
apply sum_diff.
apply sum_O_B; Col.
auto.

unfold Length.
repeat split; auto.
unfold LeP.
left.
unfold LtP.
exists OA.
split.
apply sum_diff.
apply sum_O_B; Col.
unfold Ps.
apply opp_midpoint in H19.
unfold Midpoint in H19.
spliter.
apply not_out_bet in H12.
assert(HP:=l5_2 A O E OA H11 H12 H19).
unfold Out.
repeat split; auto.
intro.
subst OA.
apply cong_identity in H21.
contradiction.
induction HP.
right; auto.
left; auto.
Col.
apply opp_midpoint in H19.
unfold Midpoint in H19.
spliter.
Cong.

unfold Length.
repeat split; Cong;
Col.
unfold LeP.
left.
unfold LtP.
exists OB.
split; auto.
apply diff_A_O; auto.
Col.
apply opp_midpoint in H16.
unfold Midpoint in H16.
spliter.
apply cong_transitivity with O B; Cong.
apply(opp_same_square O E E' A OA A2 H19 H0).
apply(opp_same_square O E E' B OB B2 H16 H1).


(****** A<0 ********* B<0 ********** C<0 ********)

assert(exists OC : Tpoint, Opp O E E' C OC).
apply(opp_exists O E E' H C).
Col.
ex_and H15 OC.

assert(Ng O E C).
unfold Ng.
repeat split; auto.
intro.
subst C.

apply cong_symmetry in H9.
apply cong_identity in H9.
subst B'.
apply perp_right_comm in H3.
apply perp_not_col in H3.
apply H3.
ColR.
apply not_out_bet in H14.
assumption.
Col.

assert(Ps O E OC).
apply(opp_neg_pos O E E' C OC); auto.

assert(exists OA : Tpoint, Opp O E E' A OA).
apply(opp_exists O E E' H A).
Col.
ex_and H18 OA.
assert(Ng O E A).
unfold Ng.
repeat split; auto.
apply not_out_bet in H12;auto.
Col.

assert(Col O E OA).
unfold Opp in H19.
unfold Sum in H19.
spliter.
unfold Ar2 in H19.
tauto.

assert(exists OB : Tpoint, Opp O E E' B OB).
apply(opp_exists O E E' H B).
Col.
ex_and H21 OB.

assert(Ng O E B).
unfold Ng.
repeat split; auto.
intro.
subst B.

apply cong_identity in H8.
subst B'.
apply perp_distinct in H3.
tauto.
apply not_out_bet in H13.
bet.
Col.

assert(Ps O E OB).
apply(opp_neg_pos O E E' B OB); auto.

apply(pythagoras O E E' A B' O OA OB OC A2 B2 C2); auto.

unfold Length.
repeat split; auto.
unfold Ps in H17.
apply out_col in H17.
Col.
unfold LeP.
left.
unfold LtP.
exists OC.
split; auto.
apply diff_A_O; auto.
unfold Ps in H17.
Col.
apply opp_midpoint in H16.
unfold Midpoint in H16.
spliter.
apply cong_transitivity with O C; Cong.

unfold Length.
repeat split; auto.
unfold LeP.
left.
unfold LtP.
exists OA.
split.
apply sum_diff.
apply sum_O_B; Col.
unfold Ps.
apply opp_midpoint in H19.
unfold Midpoint in H19.
spliter.
apply not_out_bet in H12.
assert(HP:=l5_2 A O E OA H11 H12 H19).
unfold Out.
repeat split; auto.
intro.
subst OA.
apply cong_identity in H24.
contradiction.
induction HP.
right; auto.
left; auto.
Col.
apply opp_midpoint in H19.
unfold Midpoint in H19.
spliter.
Cong.

unfold Length.
repeat split; Cong;
Col.
unfold LeP.
left.
unfold LtP.
exists OB.
split; auto.
apply diff_A_O; auto.
Col.
apply opp_midpoint in H22.
unfold Midpoint in H22.
spliter.
apply cong_transitivity with O B; Cong.
apply(opp_same_square O E E' A OA A2 H19 H0).
apply(opp_same_square O E E' B OB B2 H22 H1).
apply(opp_same_square O E E' C OC C2 H16 H2).
Qed.



Lemma PythRel_uniqueness : forall O E E' A B C1 C2,
 PythRel O E E' A B C1 ->
 PythRel O E E' A B C2 ->
 ((Ps O E C1 /\ Ps O E C2) \/ C1 = O)->
 C1 = C2.

Proof.
intros.
unfold PythRel in *.
spliter.
unfold Ar2 in *.
spliter.
clean_duplicated_hyps;
induction H2; induction H3.
spliter.
subst B.

induction H4; induction H3.
subst C1.
subst C2.
auto.
subst A.
induction H1.
spliter.
unfold Opp in H3.
apply sum_comm in H3; auto.

assert(HP:=sum_pos_pos O E E' C1 C2 O H1 H2 H3).
assert(HQ:=O_not_positive O E).
contradiction.


subst C1.
unfold Opp in H3.

apply (sum_A_O_eq O E E') in H3; auto.

subst C2.
induction H1.
spliter.
unfold Opp in H2.
assert(HP:=sum_pos_pos O E E' C1 A O H1 H3 H2).
assert(HQ:=O_not_positive O E).
contradiction.

subst C1.
unfold Opp in H2.
apply(sum_O_B_eq O E E') in H2; auto.
unfold Opp in *.
eapply (sum_uniquenessA O E E' H A C1 C2 O); auto.


ex_and H2 B'.
spliter.
subst B.
apply perp_distinct in H2.
tauto.
ex_and H0 B'.
spliter.
subst B.
apply perp_distinct in H0.
tauto.

ex_and H0 B1.
ex_and H2 B2.
assert(Cong O B1 O B2).
apply cong_transitivity with O B; Cong.

assert (O <> E).
intro.
subst E.
apply H;Col.

assert(HH:= perp2__col O B1 B2 O B H0 H2).

assert(B1 = B2 \/ Midpoint O B1 B2).
apply l7_20; Col.

induction H13.
subst B2.
clean_duplicated_hyps.
clean_trivial_hyps.

assert(Cong O C2 O C1).
apply cong_transitivity with A B1; Cong.

assert(C1 = C2 \/ Midpoint O C1 C2).
apply l7_20.
ColR.
Cong.
induction H5.
assumption.

induction H1.

unfold Ps in H1.
unfold Ps in H2.
spliter.
assert(Out O C1 C2).
apply (out2_out_1 _ _ _ E);
apply l6_6;
auto.
unfold Midpoint in H5.
spliter.
apply l6_4_1 in H5; auto.
tauto.

subst C1.
unfold Midpoint in H5.
spliter.
apply cong_symmetry in H5.
apply (cong_identity O C2 O);auto.

induction(eq_dec_points A O).
subst A.

assert(Cong O C1 O C2).
apply cong_transitivity with O B2; trivial.
apply cong_transitivity with O B1; Cong.
assert(C1 = C2 \/ Midpoint O C1 C2).
apply l7_20; eCol.

induction H15.
assumption.

induction H1.

unfold Ps in H1.
unfold Ps in H2.
spliter.
assert(Out O C1 C2).
apply (out2_out_1 _ _ _ E);
apply l6_6;
auto.
unfold Midpoint in H15.
spliter.
apply l6_4_1 in H15; auto.
tauto.

subst C1.
apply cong_symmetry in H5.
apply (cong_identity O C2 O);auto.
Cong.

assert(Per A O B1).
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.

apply (perp_col O B ).
auto.
Perp.
ColR.

unfold Per in H15.
ex_and H15 B2'.
assert(B2 = B2').
apply (symmetric_point_uniqueness B1 O); auto.
subst B2'.

assert(Cong O C1 O C2).
apply cong_transitivity with A B2; trivial.
apply cong_transitivity with A B1; Cong.

assert(C1 = C2 \/ Midpoint O C1 C2).
apply l7_20.
ColR.
Cong.

induction H18.
assumption.

induction H1.
spliter.

unfold Ps in H1.
unfold Ps in H19.
assert(Out O C1 C2).
apply (out2_out_1 _ _ _ E);
apply l6_6;
auto.
unfold Midpoint in H18.
spliter.
apply l6_4_1 in H18; auto.
tauto.

subst C1.
apply cong_symmetry in H17.
apply (cong_identity O C2 O);auto.
Qed.



End PythagoreanFun.



