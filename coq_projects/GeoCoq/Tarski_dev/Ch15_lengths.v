Require Export GeoCoq.Tarski_dev.Ch14_order.

Section T15.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

(** Lemma 15.2 *)
(** Cong corresponds to length equality.*)
(** Le corresponds to length inequality.*)

Lemma length_pos : forall O E E' A B L,
  Length O E E' A B L -> LeP O E E' O L.
Proof.
intros.
unfold Length in *.
tauto.
Qed.

Lemma length_id_1 : forall O E E' A B,
  Length O E E' A B O -> A=B.
Proof.
intros.
unfold Length in *.
spliter.
treat_equalities.
reflexivity.
Qed.

Lemma length_id_2 : forall O E E' A,
  O<>E -> Length O E E' A A O.
Proof.
intros.
unfold Length.
repeat split.
assumption.
Col.
unfold LeP.
tauto.
Cong.
Qed.

Lemma length_id : forall O E E' A B,
 Length O E E' A B O <-> (A=B /\ O<>E).
Proof.
intros.
split.
intros.
split.
eauto using length_id_1.
unfold Length in *.
tauto.
intros.
spliter. subst.
apply length_id_2.
assumption.
Qed.

Lemma length_eq_cong_1 : forall O E E' A B C D AB,
 Length O E E' A B AB -> Length O E E' C D AB -> Cong A B C D.
Proof.
intros.
unfold Length in *.
spliter.
apply cong_transitivity with O AB;Cong.
Qed.

Lemma length_eq_cong_2 : forall O E E' A B C D AB,
 Length O E E' A B AB -> Cong A B C D -> Length O E E' C D AB.
Proof.
intros.
unfold Length in *.
spliter.
repeat split;try assumption.
apply cong_transitivity with A B;Cong.
Qed.

Lemma ltP_pos : forall O E E' A, LtP O E E' O A  -> Ps O E A.
Proof.
intros.
unfold LtP in H.
ex_and H A'.

assert(~Col O E E' /\ Col O E A).
unfold Diff in H.
ex_and H X.
unfold Sum in H1.
spliter.
unfold Ar2 in H1.
tauto.
spliter.

assert(HH:= diff_A_O O E E' A H1 H2).
assert(A = A').
apply(diff_uniqueness O E E' A O A A'); assumption.
subst A'.
assumption.
Qed.

Lemma bet_leP : forall O E E' AB CD,
  Bet O AB CD -> LeP O E E' O AB -> LeP O E E' O CD -> LeP O E E' AB CD.
Proof.
intros.
unfold LeP in *.
induction H0; induction H1.

unfold LtP in H0.
unfold LtP in H1.
ex_and H0 P.
ex_and H1 Q.

assert(Ar2 O E E' AB CD P /\ Col O E Q).
unfold Diff in H0.
ex_and H0 X.
unfold Diff in H1.
ex_and H1 Y.
unfold Sum in H4.
unfold Sum in H5.
spliter.
unfold Ar2 in *.
spliter.
repeat split; Col.
unfold Ar2 in H4.
spliter.

assert(P = AB).
apply (diff_uniqueness O E E' AB O); auto.
apply diff_A_O; auto.
subst P.

assert(Q = CD).
apply (diff_uniqueness O E E' CD O); auto.
apply diff_A_O; auto.
subst Q.
clean_duplicated_hyps.

induction(eq_dec_points AB CD).
right.
assumption.
left.
clear H0 H1.


assert(HH:=opp_exists O E E' H4 AB H6).
ex_and HH AB'.

assert(exists P, Sum O E E' CD AB' P).
apply(sum_exists O E E' H4 CD AB'); Col.
unfold Opp in H0.
unfold Sum in H0.
spliter.
unfold Ar2 in H0.
tauto.
ex_and H1 P.


unfold LtP.
exists P.
split.
unfold Diff.
exists AB'.
split; auto.


assert(Diff O E E' CD AB P).
unfold Diff.
exists AB'.
split; auto.

apply diff_sum in H1.
induction (eq_dec_points AB O).
subst AB.
unfold Ps in H2.
unfold Out in H2.
spliter.
tauto.

assert(Parallelogram_flat O AB CD P).
apply (sum_cong O E E' H4 AB P CD H1).
left.
assumption.
unfold Parallelogram_flat in H10.
spliter.

assert(Bet CD P O).
apply(l4_6 O AB CD CD P O).
assumption.
repeat split; Cong.
unfold Ps.
unfold Out.
repeat split.
intro.
subst P.
assert(AB=CD).
apply cong_symmetry in H13.
apply (cong_identity _ _ O); Cong.
subst CD.
tauto.
intro.
subst E.
apply H4.
Col.
unfold Ps in H3.
unfold Out in H3.
spliter.
induction H17.
left.
apply (between_exchange4 O P CD E); Between.
apply (l5_3 O P E CD); Between.
subst CD.
apply between_identity in H.
subst AB.
right; auto.
subst AB.
left; assumption.
subst AB.
subst CD.
right; auto.
Qed.

Lemma leP_bet : forall O E E' AB CD,
  LeP O E E' AB CD -> LeP O E E' O AB -> LeP O E E' O CD -> Bet O AB CD.
Proof.
intros.
unfold LeP in H.
induction H.
unfold LtP in H.
ex_and H X.
apply diff_sum in H.

assert(Out O AB X \/ AB=O).
unfold LeP in H0.
induction H0.
left.
apply ltP_pos in H0.
unfold Ps in *.
eapply (l6_7 _ _ E); auto.
apply l6_6.
assumption.
right.
auto.

induction H3.

apply (l14_36_a O E E' AB X CD); auto.
subst AB.
apply between_trivial2.
subst CD.
apply between_trivial.
Qed.

Lemma length_Ar2 : forall O E E' A B AB,
  Length O E E' A B AB -> (Col O E AB /\ ~Col O E E') \/ AB = O.
Proof.
intros.
unfold Length in H.
spliter.

unfold LeP in H1.
induction H1.
left.
split.
assumption.
unfold LtP in H1.
ex_and H1 P.
unfold Diff in H1.
ex_and H1 Q.
unfold Sum in *.
spliter.
unfold Ar2 in *.
tauto.
right; auto.
Qed.

Lemma length_leP_le_1 : forall O E E' A B C D AB CD,
 Length O E E' A B AB -> Length O E E' C D CD -> LeP O E E' AB CD -> Le A B C D.
Proof.
intros.
unfold Length in *.
spliter.
assert(Bet O AB CD).
apply (leP_bet O E E'); assumption.

prolong D C M' A B.
assert(HH:=symmetric_point_construction M' C).
ex_and HH M.
unfold Midpoint in H11.
spliter.

assert(Cong A B C M).
apply (cong_transitivity _ _ C M'); Cong.

apply(le_transitivity _ _ C M).
unfold Le.
exists M.
split; Between.

assert(Le O AB O CD).
unfold Le.
exists AB.
split; Cong.

apply(l5_6 O AB O CD C M C D); Cong.
apply (cong_transitivity _ _ A B); Cong.
Qed.

Lemma length_leP_le_2 : forall O E E' A B C D AB CD,
 Length O E E' A B AB -> Length O E E' C D CD -> Le A B C D -> LeP O E E' AB CD.
Proof.
intros.

assert(HH1:= length_Ar2 O E E' A B AB H).
assert(HH2:= length_Ar2 O E E' C D CD H0).
spliter.
unfold Length in *.
spliter.
apply bet_leP; try assumption.

induction(eq_dec_points O CD).
subst CD.
apply cong_symmetry in H4.
apply cong_identity in H4.
subst D.
unfold Le in H1.
ex_and H1 X.
apply between_identity in H1.
subst X.
apply cong_identity in H4.
subst B.
apply cong_identity in H7.
subst AB.
Between.
assert(Le O AB O CD).

apply(l5_6 A B C D O AB O CD); Cong.
unfold Le in H8.
ex_and H9 M.

induction HH1; induction HH2.
spliter.

unfold Le in H1.
ex_and H1 P.

unfold LeP in *.
induction H6; induction H3.
unfold LtP in *.
ex_and H6 X.
ex_and H3 Y.
apply diff_sum in H6.
apply diff_sum in H3.
apply sum_cong in H6; auto.
apply sum_cong in H3; auto.
unfold Parallelogram_flat in *.
spliter.
apply cong_symmetry in H19.
apply cong_identity in H19.
subst Y.
apply cong_symmetry in H23.
apply cong_identity in H23.
subst X.
clean_trivial_hyps.

assert(AB = M \/ Midpoint O AB M).
apply(l7_20 O AB M); Cong.

unfold Ps in *.
assert(Out O AB CD).
apply (l6_7 O AB E CD); auto.
apply l6_6.
assumption.
apply out_col in H3.
apply bet_col in H9.
apply col_permutation_2.

apply (col_transitivity_1 _ CD); Col.
induction H3.
subst M.
assumption.
unfold Midpoint in H3.
spliter.

assert(Out O AB CD).
unfold Ps in *.

apply (l6_7 O AB E CD); auto.
apply l6_6.
assumption.
assert(Bet AB O CD).

eapply (outer_transitivity_between _ _ M); Between.
intro.
subst M.
apply cong_identity in H6.
subst AB.
tauto.
unfold Out in H18.
spliter.
induction H22.
assert(AB = O).
apply(between_equality _ _ CD); Between.
subst AB.
Between.
assert(Bet CD O CD).
apply (between_exchange3 AB); Between.
assert(O = CD).
apply between_equality in H23.
contradiction.
Between.
tauto.
right.
intro.
subst Y.
unfold Ps in H17.
unfold Out in H17.
tauto.
right.
intro.
subst X.
unfold Ps in H16.
unfold Out in H16.
tauto.
subst CD.
tauto.
subst AB.
Between.
subst CD.
tauto.
subst CD.
tauto.
subst AB.
Between.
subst CD.
tauto.
Qed.

Lemma l15_3 : forall O E E' A B C, Sum O E E' A B C -> Cong O B A C.
Proof.
intros.
assert(Ar2 O E E' A B C).
unfold Sum in H.
spliter.
assumption.
unfold Ar2 in H0.
spliter.
induction (eq_dec_points A O).
subst A.
assert(B = C).
apply (sum_uniqueness O E E' O B); auto.
apply sum_O_B; auto.
subst C.
Cong.
apply sum_cong in H; auto.
unfold Parallelogram_flat in H.
spliter.
Cong.
Qed.

(** Lemma 15.4. *)
(** Triangular equality. *)
Lemma length_uniqueness : forall O E E' A B AB AB',
  Length O E E' A B AB -> Length O E E' A B AB' -> AB = AB'.
Proof.
intros.
assert(Col O E AB /\ ~ Col O E E' \/ AB = O).
eapply (length_Ar2 O E E' A B AB); assumption.
assert(Col O E AB' /\ ~ Col O E E' \/ AB' = O).
eapply (length_Ar2 O E E' A B AB'); assumption.

unfold Length in *.
spliter.
assert(Cong O AB O AB').
apply cong_transitivity with A B; Cong.
assert(AB = AB' \/ Midpoint O AB AB').
apply(l7_20 O AB AB').
ColR.
Cong.
induction H10.
assumption.
unfold Midpoint in H10.
spliter.

induction H1; induction H2.
spliter.

unfold LeP in *.
induction H4; induction H7.
unfold LtP in H4.
unfold LtP in H7.
ex_and H4 X.
ex_and H7 Y.
apply diff_sum in H4.
apply diff_sum in H7.
assert(X = AB').
apply(sum_O_B_eq O E E'); Col.
subst X.
assert(Y = AB).
apply(sum_O_B_eq O E E'); Col.
subst Y.
unfold Ps in *.
assert(Out O AB AB').
eapply (l6_7 _ _ E).
assumption.
apply l6_6; assumption.
unfold Out in H16.
spliter.
induction H18.
assert(AB = O).
eapply (between_equality _ _ AB'); Between.
subst AB.
apply cong_symmetry in H11.
apply cong_identity in H11.
auto.
assert(AB' = O).
eapply (between_equality _ _ AB); Between.
subst AB'.
apply cong_identity in H11.
auto.
subst AB.
apply cong_symmetry in H9.
apply cong_identity in H9.
auto.
subst AB'.
apply cong_identity in H9.
auto.
subst AB'.
apply cong_identity in H9.
auto.
subst AB'.
apply cong_identity in H9.
auto.
subst AB.
apply cong_symmetry in H9.
apply cong_identity in H9.
auto.
subst AB.
subst AB'.
reflexivity.
Qed.

Lemma length_cong : forall O E E' A B AB, Length O E E' A B AB -> Cong A B O AB.
Proof.
intros.
unfold Length in H.
spliter.
Cong.
Qed.

Lemma length_Ps : forall O E E' A B AB,
  AB <> O -> Length O E E' A B AB -> Ps O E AB.
Proof.
intros.
unfold Length in H0.
spliter.
unfold LeP in H2.
induction H2.
unfold LtP in H2.
ex_and H2 X.
apply diff_sum in H2.
apply sum_cong in H2.
unfold Parallelogram_flat in H2.
spliter.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst X.
assumption.
unfold Sum in H2.
spliter.
unfold Ar2 in H2.
tauto.
right.
intro.
subst X.
unfold Ps in H4.
unfold Out in H4.
tauto.
subst AB.
tauto.
Qed.

Lemma length_not_col_null : forall O E E' A B AB,
  Col O E E' -> Length O E E' A B AB -> AB=O.
Proof.
intros.
unfold Length in H0.
spliter.
unfold LeP in H2.
induction H2.
unfold LtP in H2.
ex_and H2 X.
apply diff_sum in H2.
unfold Sum in H2.
spliter.
unfold Ar2 in H2.
spliter.
contradiction.
auto.
Qed.

Lemma triangular_equality_equiv :
  (forall O E A , O<>E -> (forall E' B C AB BC AC,
   Bet A B C ->
   Length O E E' A B AB -> Length O E E' B C BC -> Length O E E' A C AC ->
   Sum O E E' AB BC AC)) <->
  (forall O E E' A B C AB BC AC,
   O<>E -> Bet A B C ->
   Length O E E' A B AB -> Length O E E' B C BC -> Length O E E' A C AC ->
   Sum O E E' AB BC AC).
Proof.
split.
intros.
assert(HH:= H O E A H0).
apply (HH E' B C); auto.
intros.
assert(HH:= H O E E' A B C AB BC AC H0 H1 H2 H3 H4).
assumption.
Qed.

Lemma not_triangular_equality1 : forall O E A ,
  O<>E ->
  ~ (forall E' B C AB BC AC,
  Bet A B C ->
  Length O E E' A B AB -> Length O E E' B C BC -> Length O E E' A C AC ->
  Sum O E E' AB BC AC).
Proof.
intros.
intro.
assert(HH:=(H0 E A A O O O)).
assert(Bet A A A); Between.
assert(Length O E E A A O).
apply(length_id_2); auto.
assert(HHH:= (HH H1 H2 H2 H2)).
unfold Sum in HHH.
spliter.
ex_and H4 X.
ex_and H5 Y.
unfold Ar2 in H3.
spliter.
apply H3.
Col.
Qed.

Lemma triangular_equality : forall O E E' A B C AB BC AC,
  O<>E -> Bet A B C ->
  Is_length O E E' A B AB -> Is_length O E E' B C BC ->
  Is_length O E E' A C AC ->
  Sumg O E E' AB BC AC.
Proof.
intros O E E' A B C AB BC AC H H0 Hl1 Hl2 Hl3.

unfold Is_length in *.

induction Hl1; induction Hl2; induction Hl3; try(spliter; contradiction).
unfold Length in *.
spliter.
unfold LeP in *.
induction H11; induction H8; induction H5.

(* General Case *)

unfold LtP in *.
ex_and H11 X.
ex_and H8 Y.
ex_and H5 Z.
apply diff_sum in H11.
apply diff_sum in H8.
apply diff_sum in H5.
assert(AB = X).
apply (sum_uniqueness O E E' O X).
assumption.
unfold Sum in H11.
spliter.
unfold Ar2 in H11.
apply(sum_O_B); tauto.
subst X.

assert(BC = Y).
apply (sum_uniqueness O E E' O Y).
assumption.
unfold Sum in H8.
spliter.
unfold Ar2 in H8.
apply(sum_O_B); tauto.
subst Y.

assert(AC = Z).
apply (sum_uniqueness O E E' O Z).
assumption.
unfold Sum in H5.
spliter.
unfold Ar2 in H5.
apply(sum_O_B); tauto.
subst Z.

assert(forall A B : Tpoint,Col O E A -> Col O E B -> exists C : Tpoint, Sum O E E' A B C).
apply(sum_exists O E E' ).
unfold Sum in H11.
spliter.
unfold Ar2 in H11.
tauto.
assert(HS:= H16 AB BC H10 H7).
ex_and HS AC'.

assert(Bet O AB AC').
apply(l14_36_a O E E' AB BC AC' H17).
eapply (l6_7 _ _ E).
assumption.
apply l6_6.
assumption.

assert(HH:= l15_3 O E E' AB BC AC' H17).

assert(Cong O AC' A C).
apply(l2_11 O AB AC' A B C); Cong.
apply cong_transitivity with O BC; Cong.

assert(HP:= sum_pos_pos O E E' AB BC AC' H13 H14 H17).
assert(AC = AC').
apply(l6_11_uniqueness O A C E AC AC').
intro.
subst E.
tauto.
intro.
subst C.
apply between_identity in H0.
subst B.
apply cong_identity in H6.
subst AC.
unfold Ps in H15.
unfold Out in H15.
tauto.
unfold Ps in H15.
assumption.
Cong.
unfold Ps in HP.
assumption.
Cong.
subst AC'.
left.
assumption.

(* Case AC = O *)

subst AC.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst C.
apply between_identity in H0.
subst B.
apply cong_identity in H12.
subst AB.
apply cong_identity in H9.
subst BC.
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H0.
assert(X=O).
apply(sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H0.
spliter.
unfold Ar2 in H0.
tauto.
unfold Ps in H5.
apply out_col in H5.
Col.
assumption.
subst X.
unfold Ps in H5.
unfold Out in H5.
tauto.

(* BC = O *)

subst BC.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst C.
assert(Cong O AB O AC).
apply cong_transitivity with A B; Cong.
unfold LtP in H11.
ex_and H11 X.
apply diff_sum in H9.
assert(X = AB).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H9.
spliter.
unfold Ar2 in H9.
tauto.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold LtP in H5.
ex_and H5 Y.
apply diff_sum in H5.

assert(Y = AC).
apply (sum_uniqueness O E E' O Y).
apply sum_O_B.
unfold Sum in H9.
spliter.
unfold Ar2 in H9.
tauto.
unfold Ps in H13.
apply out_col in H13.
Col.
assumption.
subst Y.
assert(AB = AC).
apply(l6_11_uniqueness O A B E AB AC).
intro.
subst E.
unfold Ps in H13.
unfold Out in H13.
tauto.
intro.
subst B.
apply cong_identity in H6.
subst AC.
unfold Ps in H13.
unfold Out in H13.
tauto.
unfold Ps in H11.
assumption.
Cong.
unfold Ps in H13.
assumption.
Cong.
subst AB.
left.
apply sum_A_O.
unfold Sum in H9.
unfold Ar2 in H9.
tauto.
unfold Ps in H11.
apply out_col in H11.
Col.

(* Case AC = O /\ BC = O *)

subst AC.
subst BC.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst C.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst B.
apply cong_identity in H12.
subst AB.
left.
apply sum_O_O.
unfold LtP in H11.
ex_and H11 X.
apply diff_sum in H5.
unfold Sum in H5.
unfold Ar2 in H5.
tauto.

(* Case AB = O *)

subst AB.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.

assert(BC = AC).
apply(l6_11_uniqueness O A C E BC AC).
intro.
subst E.
tauto.
intro.
subst C.
apply cong_identity in H9.
subst BC.
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H8.
assert(X = O).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H8.
unfold Ar2 in H8.
tauto;
unfold Ps in H13.
unfold Ps in H9.
apply out_col in H9.
Col.
assumption.
subst X.
unfold Ps in H9.
unfold Out in H9.
tauto.
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H8.

assert(X = BC).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H8.
unfold Ar2 in H8.
tauto;
unfold Out in H13.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold Ps in H11.
assumption.
Cong.

unfold LtP in H5.
ex_and H5 X.
apply diff_sum in H5.
assert(X = AC).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H5.
unfold Ar2 in H5.
tauto;
unfold Out in H13.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold Ps in H11.
assumption.
Cong.
subst AC.
left.
apply sum_O_B.
unfold LtP in H5.
ex_and H5 X.
apply diff_sum in H5.
unfold Sum in H5.
unfold Ar2 in H5.
tauto.
Col.

(* Case AB = O /\ AC = O *)

subst AC.
subst AB.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst C.
apply cong_identity in H9.
subst BC.
left.
apply sum_O_O.
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H5.
unfold Sum in H5.
unfold Ar2 in H5.
tauto.

(* Case AB = O /\ BC = O *)

subst AB.
subst BC.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst C.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.
apply cong_identity in H6.
subst AC.
left.
apply sum_O_O.
unfold LtP in H5.
ex_and H5 X.
apply diff_sum in H5.
unfold Sum in H5.
unfold Ar2 in H5.
tauto.

(* Case AB = O /\ BC = O /\ AC= O *)


treat_equalities.
assert(HH:=col_dec O E E').
induction HH.
right.
split.
intro.
unfold Ar2 in H1.
spliter.
contradiction.
tauto.
left.
apply sum_O_O.
auto.
Qed.

Lemma length_O : forall O E E', O <> E -> Length O E E' O O O.
Proof.
intros.
unfold Length.
repeat split; Col.
unfold LeP.
right;auto.
Cong.
Qed.


Lemma triangular_equality_bis : forall O E E' A B C AB BC AC,
  A <> B \/ A <> C \/ B <> C -> O<>E -> Bet A B C ->
  Length O E E' A B AB -> Length O E E' B C BC -> Length O E E' A C AC ->
  Sum O E E' AB BC AC.
Proof.
intros O E E' A B C AB BC AC.
intro HH0.
intros.

unfold Length in *.
spliter.
unfold LeP in *.
induction H11; induction H8; induction H5.

(* General Case *)

unfold LtP in *.
ex_and H11 X.
ex_and H8 Y.
ex_and H5 Z.
apply diff_sum in H11.
apply diff_sum in H8.
apply diff_sum in H5.
assert(AB = X).
apply (sum_uniqueness O E E' O X).
assumption.
unfold Sum in H11.
spliter.
unfold Ar2 in H11.
apply(sum_O_B); tauto.
subst X.

assert(BC = Y).
apply (sum_uniqueness O E E' O Y).
assumption.
unfold Sum in H8.
spliter.
unfold Ar2 in H8.
apply(sum_O_B); tauto.
subst Y.

assert(AC = Z).
apply (sum_uniqueness O E E' O Z).
assumption.
unfold Sum in H5.
spliter.
unfold Ar2 in H5.
apply(sum_O_B); tauto.
subst Z.

assert(forall A B : Tpoint,Col O E A -> Col O E B -> exists C : Tpoint, Sum O E E' A B C).
apply(sum_exists O E E' ).
unfold Sum in H11.
spliter.
unfold Ar2 in H11.
tauto.
assert(HS:= H16 AB BC H10 H7).
ex_and HS AC'.

assert(Bet O AB AC').
apply(l14_36_a O E E' AB BC AC' H17).
eapply (l6_7 _ _ E).
assumption.
apply l6_6.
assumption.

assert(HH:= l15_3 O E E' AB BC AC' H17).

assert(Cong O AC' A C).
apply(l2_11 O AB AC' A B C); Cong.
apply cong_transitivity with O BC; Cong.

assert(HP:= sum_pos_pos O E E' AB BC AC' H13 H14 H17).
assert(AC = AC').
apply(l6_11_uniqueness O A C E AC AC').
intro.
subst E.
unfold Ps in H15.
unfold Out in H15.
tauto.
intro.
subst C.
apply between_identity in H0.
subst B.
apply cong_identity in H6.
subst AC.
unfold Ps in H15.
unfold Out in H15.
tauto.
unfold Ps in H15.
assumption.
Cong.
unfold Ps in HP.
assumption.
Cong.
subst AC'.
assumption.

(* Case AC = O *)

subst AC.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst C.
apply between_identity in H0.
subst B.
apply cong_identity in H12.
subst AB.
apply cong_identity in H9.
subst BC.
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H0.
assert(X=O).
apply(sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H0.
spliter.
unfold Ar2 in H0.
tauto.
unfold Ps in H5.
apply out_col in H5.
Col.
assumption.
subst X.
unfold Ps in H5.
unfold Out in H5.
tauto.

(* BC = O *)

subst BC.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst C.
assert(Cong O AB O AC).
apply cong_transitivity with A B; Cong.
unfold LtP in H11.
ex_and H11 X.
apply diff_sum in H9.
assert(X = AB).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H9.
spliter.
unfold Ar2 in H9.
tauto.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold LtP in H5.
ex_and H5 Y.
apply diff_sum in H5.

assert(Y = AC).
apply (sum_uniqueness O E E' O Y).
apply sum_O_B.
unfold Sum in H9.
spliter.
unfold Ar2 in H9.
tauto.
unfold Ps in H13.
apply out_col in H13.
Col.
assumption.
subst Y.
assert(AB = AC).
apply(l6_11_uniqueness O A B E AB AC).
intro.
subst E.
unfold Ps in H13.
unfold Out in H13.
tauto.
intro.
subst B.
apply cong_identity in H6.
subst AC.
unfold Ps in H13.
unfold Out in H13.
tauto.
unfold Ps in H11.
assumption.
Cong.
unfold Ps in H13.
assumption.
Cong.
subst AB.
apply sum_A_O.
unfold Sum in H9.
unfold Ar2 in H9.
tauto.
unfold Ps in H11.
apply out_col in H11.
Col.

(* Case AC = O /\ BC = O *)

subst AC.
subst BC.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst C.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst B.
apply cong_identity in H12.
subst AB.
apply sum_O_O.
unfold LtP in H11.
ex_and H11 X.
apply diff_sum in H5.
unfold Sum in H5.
unfold Ar2 in H5.
tauto.

(* Case AB = O *)

subst AB.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.

assert(BC = AC).
apply(l6_11_uniqueness O A C E BC AC).
intro.
subst E.
tauto.
intro.
subst C.
apply cong_identity in H9.
subst BC.
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H8.
assert(X = O).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H8.
unfold Ar2 in H8.
tauto;
unfold Ps in H13.
unfold Ps in H9.
apply out_col in H9.
Col.
assumption.
subst X.
unfold Ps in H9.
unfold Out in H9.
tauto.
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H8.

assert(X = BC).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H8.
unfold Ar2 in H8.
tauto;
unfold Out in H13.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold Ps in H11.
assumption.
Cong.

unfold LtP in H5.
ex_and H5 X.
apply diff_sum in H5.
assert(X = AC).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H5.
unfold Ar2 in H5.
tauto;
unfold Out in H13.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold Ps in H11.
assumption.
Cong.
subst AC.
apply sum_O_B.
unfold LtP in H5.
ex_and H5 X.
apply diff_sum in H5.
unfold Sum in H5.
unfold Ar2 in H5.
tauto.
Col.

(* Case AB = O /\ AC = O *)

subst AC.
subst AB.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst C.
apply cong_identity in H9.
subst BC.
apply sum_O_O.
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H5.
unfold Sum in H5.
unfold Ar2 in H5.
tauto.

(* Case AB = O /\ BC = O *)

subst AB.
subst BC.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst C.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.
apply cong_identity in H6.
subst AC.
apply sum_O_O.
unfold LtP in H5.
ex_and H5 X.
apply diff_sum in H5.
unfold Sum in H5.
unfold Ar2 in H5.
tauto.

(* Case AB = O /\ BC = O /\ AC= O *)

subst AB.
subst AC.
subst BC.

apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst C.
apply cong_identity in H6.
induction HH0; tauto.
Qed.

(** Lemma 15.5. *)
(** Known as Thales theorem or intercept theorem. *)
Lemma length_out : forall O E E' A B C D AB CD,
  A <> B -> C <> D -> Length O E E' A B AB -> Length O E E' C D CD ->
  Out O AB CD.
Proof.
intros.
unfold Length in *.
spliter.
unfold LeP in *.
induction H7; induction H4.
unfold LtP in *.
ex_and H7 X.
ex_and H4 Y.
apply diff_sum in H7.
apply diff_sum in H4.
assert(X = AB).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H4.
spliter.
unfold Ar2 in H4.
tauto.
unfold Ps in H9.
apply out_col in H9.
Col.
assumption.
subst X.
assert(Y = CD).
apply (sum_uniqueness O E E' O Y).
apply sum_O_B.
unfold Sum in H4.
spliter.
unfold Ar2 in H4.
tauto.
unfold Ps in H10.
apply out_col in H10.
Col.
assumption.
subst Y.
unfold Ps in *.
eapply (l6_7  _ _ E).
assumption.
apply l6_6.
assumption.
subst CD.
apply cong_symmetry in H5.
apply cong_identity in H5.
contradiction.
subst AB.
apply cong_symmetry in H8.
apply cong_identity in H8.
contradiction.
subst CD.
apply cong_symmetry in H5.
apply cong_identity in H5.
contradiction.
Qed.

Lemma image_preserves_bet1 : forall X Y A B C A' B' C',
  Bet A B C -> Reflect A A' X Y -> Reflect B B' X Y -> Reflect C C' X Y ->
  Bet A' B' C'.
Proof.
intros.
induction(eq_dec_points X Y).
subst Y.
unfold Reflect in *.
induction H0.
tauto.
induction H1.
tauto.
induction H2.
tauto.
spliter.
clean_duplicated_hyps.
apply(l7_15 A B C A' B' C' X).
apply l7_2.
auto.
apply l7_2; auto.
apply l7_2; auto.
assumption.
apply (image_preserves_bet A B C A' B' C' X Y).
unfold Reflect in H0.
induction H0.
tauto.
spliter.
contradiction.
unfold Reflect in *.
induction H0; induction H1; induction H2; try( spliter; contradiction).
spliter.
auto.
induction H0; induction H1; induction H2; try( spliter; contradiction).
spliter.
auto.
induction H0; induction H1; induction H2; try( spliter; contradiction).
spliter.
auto.
Qed.

Lemma image_preserves_col : forall X Y A B C A' B' C',
  Col A B C -> Reflect A A' X Y -> Reflect B B' X Y -> Reflect C C' X Y ->
  Col A' B' C'.
Proof.
intros.
induction H.
unfold Col.
left.
apply (image_preserves_bet1 X Y A B C A' B' C'); auto.
induction H.
unfold Col.
right; left.
apply (image_preserves_bet1 X Y B C A B' C' A'); auto.
unfold Col.
right; right.
apply (image_preserves_bet1 X Y C A B C' A' B'); auto.
Qed.

Lemma image_preserves_out : forall X Y A B C A' B' C',
  Out A B C -> Reflect A A' X Y -> Reflect B B' X Y -> Reflect C C' X Y ->
  Out A' B' C'.
Proof.
intros.
unfold Out in *.
spliter.
repeat split; auto.
intro.
subst B'.
assert(B = A).
apply (l10_2_uniqueness X Y A' B A H1 H0).
contradiction.

intro.
subst C'.
assert(C=A).
apply (l10_2_uniqueness X Y A' C A H2 H0).
contradiction.
induction H4.
left.
apply (image_preserves_bet1 X Y A B C); auto.
right.
apply (image_preserves_bet1 X Y A C B); auto.
Qed.


Lemma project_preserves_out : forall A B C A' B' C' P Q X Y,
  Out A B C -> ~Par A B X Y ->
  Proj A A' P Q X Y -> Proj B B' P Q X Y -> Proj C C' P Q X Y ->
  Out A' B' C'.
Proof.
intros.
repeat split.
intro.
subst B'.
unfold Out in H.
spliter.
unfold Proj in H1.
unfold Proj in H2.
spliter.
induction H9; induction H13.
assert(Par A A' B A').
apply (par_trans _ _ X Y); auto.
apply par_symmetry.
assumption.
induction H14.
apply H14.
exists A'.
split; Col.
spliter.
apply H0.
apply par_symmetry.
apply(par_col_par X Y A A' B).
intro.
subst B.
tauto.
apply par_symmetry.
assumption.
Col.
subst A'.
apply H0.
apply par_left_comm.
assumption.
subst A'.
contradiction.
subst A'.
contradiction.

assert(HC:Col A B C).
apply out_col in H.
assumption.
unfold Out in H.
spliter.
intro.
subst C'.
unfold Proj in H1 ,H3.
spliter.
induction H9; induction H13.
assert(Par A A' C A').
apply (par_trans _ _ X Y).
assumption.
apply par_symmetry.
assumption.
induction H14.
apply H14.
exists A'.
split; Col.
spliter.

apply H0.
apply par_symmetry.
apply (par_col_par X Y A A' B).
intro.
subst B.
tauto.
apply par_symmetry.
assumption.
ColR.
subst A'.
apply H0.
apply par_symmetry.
apply(par_col_par X Y A C B).
intro.
subst B.
tauto.
apply par_symmetry.
apply par_left_comm.
assumption.
Col.
subst A'.
apply H0.
apply par_symmetry.
apply(par_col_par X Y A C B).
intro.
subst B.
tauto.
apply par_symmetry.
assumption.
Col.
subst A'.
contradiction.
unfold Out in H.
spliter.
induction H5.
left.
apply (project_preserves_bet P Q X Y A B C A' B' C'); assumption.
right.
apply (project_preserves_bet P Q X Y A C B A' C' B'); assumption.
Qed.

Lemma conga_bet_conga : forall A B C D E F A' C' D' F',
  CongA A B C D E F -> A' <> B -> C' <> B -> D' <> E -> F' <> E ->
  Bet A B A' -> Bet C B C' -> Bet D E D' -> Bet F E F' ->
  CongA A' B C' D' E F'.
Proof.
intros.
assert(HH:= l11_13 A B C D E F A' D' H H4 H0 H6 H2).
apply conga_comm.
apply(l11_13 C B A' F E D' C' F'); auto.
apply conga_comm.
assumption.
Qed.

Lemma thales : forall O E E' P A B C D A1 B1 C1 D1 AD,
  O <> E -> Col P A B -> Col P C D -> ~ Col P A C -> Pj A C B D ->
  Length O E E' P A A1 -> Length O E E' P B B1 ->
  Length O E E' P C C1 -> Length O E E' P D D1 ->
  Prodg O E E' A1 D1 AD ->
  Prodg O E E' C1 B1 AD.
Proof.
intros.
induction(col_dec O E E').
unfold Prodg.
right.
split.
intro.
unfold Ar2 in H10.
spliter.
contradiction.
unfold Prodg in H8.
induction H8.
unfold Prod in H8.
spliter.
unfold Ar2 in H8.
spliter.
contradiction.
tauto.
induction H8.

induction(eq_dec_points P B).
subst B.
apply length_cong in H5.
apply cong_symmetry in H5.
apply cong_identity in H5.
subst B1.
unfold Pj in H3.
induction H3.
induction H3.
apply False_ind.
apply H3.
exists C.
split; Col.
spliter.
apply False_ind.
apply H2.
ColR.
subst D.
apply length_cong in H7.
apply cong_symmetry in H7.
apply cong_identity in H7.
subst D1.
assert (AD = O).
apply (prod_uniqueness O E E' A1 O).
assumption.
apply prod_0_r.
assumption.
unfold Prod in H8.
spliter.
unfold Ar2 in H3.
tauto.
subst AD.
left.
apply prod_0_r.
assumption.

unfold Length in H6.
spliter.
unfold LeP in H6.
induction H6.
unfold LtP in H6.
ex_and H6 X.
apply diff_sum in H6.
unfold Sum in H6.
spliter.
unfold Ar2 in H6.
tauto.
subst C1; Col.

induction(eq_dec_points A B).
{
subst B.
induction H3.
induction H3.
apply False_ind.
apply H3.
exists A.
split; Col.
spliter.
assert(C=D).
apply(l6_21 P C A C); Col.
subst D.
assert(A1=B1).
apply (length_uniqueness O E E' P A);auto.
subst B1.
assert(C1 = D1).
apply (length_uniqueness O E E' P C);auto.
subst D1.
left.
apply prod_comm.
assumption.
subst D.
apply False_ind.
apply H2; Col.
}

rename H11 into HAB.

assert(Hl0:= H4).
assert(Hl1:= H5).
assert(Hl2:= H6).
assert(Hl3:= H7).

unfold Length in H4.
unfold Length in H5.
unfold Length in H6.
unfold Length in H7.
spliter.
clean_duplicated_hyps.


assert(exists C' : Tpoint, Cong_3 P A C O A1 C' /\ OS O A1 E' C').
{
apply(l10_16 P A C O A1 E');
Cong.
apply length_Ar2 in Hl0.
induction Hl0.
spliter.
intro.
induction(eq_dec_points A1 O).
subst A1.
apply cong_symmetry in H22.
apply cong_identity in H22.
subst A.
apply H2.
Col.
apply H5.
ColR.
subst A1.
intro.
apply cong_symmetry in H22.
apply cong_identity in H22.
subst A.
apply H2.
Col.
}

ex_and H4 C1'.

assert(CongA P A C O A1 C1').
{
apply(cong3_conga).
intro.
subst A.
apply H2; Col.
intro.
subst C.
apply H2; Col.
assumption.
}

assert(HN:~Col O C1 C1').
{
intro.
unfold OS in H5.
ex_and H5 K.
unfold TS in H23.
spliter.
apply H23.
apply col_permutation_2.
apply (col_transitivity_1 _ C1).
intro.
subst C1.
treat_equalities.
apply H2.
Col.
ColR.
Col.
}

assert(HH:= midpoint_existence C1 C1').
ex_and HH M.

assert(HH:= l10_2_existence O M D1).
ex_and HH D1'.
unfold Reflect in H23.
induction H23.
spliter.
unfold ReflectL in H24.
spliter.
ex_and H24 N.

assert(Out O C1 D1).
{
apply (length_out O E E' P C P D).
intro.
subst C.
apply cong_identity in H16.
subst C1.
apply H2; Col.
intro.
subst D.
apply cong_identity in H13.
subst D1.
assert(AD=O).
{
apply (prod_uniqueness O E E' A1 O).
assumption.
apply prod_0_r.
unfold Prod in H8.
spliter.
unfold Ar2 in H8.
tauto.
Col.
}
subst AD.
induction H3.
induction H3.
apply H3.
exists A.
split; Col.
spliter.
apply H2.
ColR.
subst B; tauto.
assumption.
assumption.
}

(*********************)
assert(Out O A1 C1).
{
apply (length_out O E E' P A P C).
intro.
subst A.
apply cong_identity in H22.
subst A1.
apply H2; Col.
intro.
subst C.
apply cong_identity in H16.
subst C1.
unfold Out in H27.
tauto.
assumption.
assumption.
}
(*********************)

assert(M <> C1).
{
intro.
subst M.
eapply (symmetric_point_uniqueness _ _ C1) in H7.
subst C1'.
apply H2.
apply out_col.

apply(cong3_preserves_out O A1 C1 P A C H28).
unfold Cong_3 in *.
spliter.
repeat split; Cong.
apply l7_3_2.
}

assert(Per O M C1).
{
unfold Per.
exists C1'.
split.
assumption.
unfold Cong_3 in H4.
spliter.
apply (cong_transitivity _ _ P C); Cong.
}

apply per_perp_in in H30; auto.
apply perp_in_comm in H30.
apply perp_in_perp_bis in H30.


assert(Out O C1' D1').
{
apply(image_preserves_out O M O C1 D1).
assumption.
unfold Reflect.
left.
split; auto.
unfold ReflectL.
split.
exists O.
split; finish.
right.
auto.

unfold Reflect.
left.
split; auto.
unfold ReflectL.
split.
exists M.
split; finish.
left.
induction H30.
apply perp_sym.
apply perp_comm.
apply (perp_col _ M).
intro.
subst C1'.

apply l7_3 in H7.
contradiction.
finish.
unfold Midpoint in H7.
spliter.
finish.
apply perp_distinct in H30.
tauto.
unfold Reflect.
left.
split; auto.
unfold ReflectL.
split.
exists N.
split; finish.
left.
induction H25.
apply perp_right_comm.
assumption.
subst D1'.
apply l7_3 in H24.
subst D1.
induction H30.
apply perp_not_col in H24.
apply False_ind.
apply H24.
apply out_col in H27.
apply col_permutation_2.
apply (col_transitivity_1 _ N).
intro.
subst N.
apply cong_symmetry in H13.
apply cong_identity in H13.
subst D.
unfold Pj in H3.
induction H3.
induction H3.
apply H3.
exists A.
split; Col.
spliter.
apply H2.
ColR.
subst B.
tauto.
Col.
Col.
apply perp_distinct in H24.
tauto.
}

assert(Perp O N D1 N).
{
apply (perp_col O M D1 N).
intro.
subst N.
apply HN.
unfold Midpoint in H24.
spliter.
apply bet_col in H24.
apply out_col in H31.
apply out_col in H27.
eapply (col_transitivity_1 _ D1').
intro.
subst D1'.
apply cong_identity in H32.
subst D1.
treat_equalities.
induction H3.
induction H1.
apply H1.
exists A.
split; Col.
spliter.
apply H2.
ColR.
subst B.
tauto.
apply(col_transitivity_1 _ D1).
intro.
subst D1.
treat_equalities.
induction H3.
induction H1.
apply H1.
exists A.
split; Col.
spliter.
apply H2.
ColR.
subst B.
tauto.
Col.
Col.
ColR.
apply perp_sym.
apply (perp_col _ D1').
intro.
subst N.
unfold Midpoint in H24.
spliter.
treat_equalities.
apply HN.
apply out_col in H31.
apply out_col in H27.
apply (col_transitivity_1 _ D1).
intro.
subst D1.
treat_equalities.
induction H3.
induction H1.
apply H1.
exists A.
split; Col.
spliter.
apply H2.
ColR.
subst B.
tauto.
Col.
Col.
induction H25.
finish.
subst D1'.
apply l7_3 in H24.
subst N.
apply False_ind.
apply out_col in H31.
apply out_col in H27.
apply HN.
apply (col_transitivity_1 _ D1).
intro.
subst D1.
treat_equalities.
treat_equalities.
induction H3.
induction H1.
apply H1.
exists A.
split; Col.
spliter.
apply H2.
ColR.
subst B.
tauto.
Col.
Col.
unfold Midpoint in H24.
spliter.
apply bet_col in H24.
Col.
Col.
}
apply perp_left_comm in H32.

assert(Cong O D1 O D1').
{
apply perp_perp_in in H32.
apply perp_in_comm in H32.
apply perp_in_per in H32.
unfold Per in H32.
ex_and H32 D2.
assert(D2 = D1').
eapply (l7_9 _ _ N D1);
finish.
subst D2.
assumption.
}

assert(Pj C1 C1' D1 D1').
{
unfold Pj.
left.
induction H25; induction H30.
apply (l12_9_2D _ _ _ _ O M).
apply (perp_col _ M).
intro.
subst C1'.
apply HN.
Col.
finish.
unfold Midpoint in H7.
spliter.
finish.
finish.
apply perp_distinct in H30.
tauto.
subst D1'.
apply l7_3 in H24.
subst N.
apply perp_distinct in H32.
tauto.
subst D1'.
apply l7_3 in H24.
subst N.
apply perp_distinct in H32.
tauto.
}
assert(Cong_3 P C A O C1' A1).
{
unfold Cong_3 in *.
spliter.
repeat split; Cong.
}
assert(CongA P C A O C1' A1).
{
apply cong3_conga.
intro.
subst C.
apply H2.
Col.
intro.
subst C.
apply H2.
Col.
assumption.
}
unfold Cong_3 in H35.
spliter.
assert(Cong P A O A1 /\ (P <> A -> CongA C P A C1' O A1 /\ CongA C A P C1' A1 O)).
{
apply(l11_49 P C A O C1' A1); Cong.
}
spliter.
assert(P <> A).
{
intro.
subst A.
apply H2.
Col.
}
apply H40 in H41.
clear H40.
spliter.

assert(CongA C A P D B P).
{
induction(bet_dec C P D).
assert(Bet A P B).
apply(project_preserves_bet A P A C C P D).
assumption.
unfold Proj.
repeat split.
intro.
subst A.
apply H2.
Col.
intro.
subst C.
apply H2.
Col.
intro.
induction H43.
apply H43.
exists A.
split; Col.
spliter.
apply H2.
Col.
Col.
left.
apply par_left_comm.
apply par_reflexivity.
intro.
subst A.
apply H2.
Col.
unfold Proj.
repeat split.
intro.
subst A.
apply H2.
Col.
intro.
subst C.
apply H2.
Col.
intro.
induction H43.
apply H43.
exists A.
split; Col.
spliter.
apply H2.
Col.
Col.
right.
reflexivity.
unfold Proj.
repeat split.
intro.
subst A.
apply H2.
Col.
intro.
subst C.
apply H2.
Col.
intro.
induction H43.
apply H43.
exists A.
split; Col.
spliter.
apply H2.
Col.
Col.
left.
unfold Pj in H3.
induction H3.
apply par_symmetry.
apply par_right_comm.
assumption.
subst D.
apply False_ind.
apply H2.
ColR.

assert(CongA C A B D B A <-> Par A C B D).
apply(l12_21 A C B D).
unfold TS.
repeat split.
intro.
apply H2.
ColR.
intro.
apply H2.

assert(P <> D).
intro.
subst D.
induction H3.
induction H3.
apply H3.
exists A.
split; Col.
spliter.
apply H3.
apply (l6_21 P B A C); Col.
intro.
apply H2.
ColR.
subst B.
tauto.
ColR.

exists P.
split; Col.
destruct H44.
induction H3.
assert(HH3:=H3).
apply H45 in HH3.
apply(out_conga C A B D B A C P D P).
assumption.
apply out_trivial.
intro.
subst C.
apply H2.
Col.
repeat split.
intro.
subst B.
tauto.
intro.
subst A.
apply H2.
Col.
right.
assumption.
apply out_trivial.
intro.
subst D.
apply H2.
ColR.
repeat split.
assumption.
intro.
subst B.
apply H2.
tauto.
right; Between.
subst D.
apply False_ind.
apply H2.
ColR.

assert(Out P C D).
unfold Col in H1.
unfold Out.
repeat split.
intro.
subst C.
apply H42.
Between.
intro.
subst D.
apply H42.
Between.
induction H1.
left; assumption.
induction H1.
right; Between.
apply False_ind.
apply H42.
Between.

assert(Out P A B).
apply (project_preserves_out P C D  P A B  P A A C).
assumption.
intro.
induction H44.
apply H44.
exists C.
split; Col.
spliter.
contradiction.
unfold Proj.
repeat split.
intro.
subst A.
apply H2.
Col.
intro.
subst C.
apply H2.
Col.
intro.
induction H44.
apply H44.
exists A.
split; Col.
spliter.
contradiction.
Col.
right.
reflexivity.

unfold Proj.
repeat split.
intro.
subst A.
apply H2.
Col.
intro.
subst C.
apply H2.
Col.
intro.
induction H44.
apply H44.
exists A.
split; Col.
spliter.
contradiction.
Col.
left.
apply par_left_comm.
apply par_reflexivity.
intro.
subst C.
apply H2.
Col.
unfold Proj.
repeat split.
intro.
subst A.
apply H2; Col.
intro.
subst C.
apply H2; Col.
intro.
induction H44.
apply H44.
exists A.
split; Col.
spliter.
contradiction.
Col.
left.
induction H3.
apply par_left_comm.
apply par_symmetry.
assumption.
subst D.
apply False_ind.
apply H2.
ColR.

apply (l12_22 A C B D P).
assumption.
apply out_one_side.
left.
assumption.
assumption.
induction H3.
assumption.
subst D.
apply False_ind.
apply H2.
ColR.
}
assert(C <> A).
{
intro.
subst C.
unfold CongA in H42.
tauto.
}

assert(P <> A).
{
intro.
subst A.
unfold CongA in H42.
tauto.
}

assert(~Par P A C A).
{
intro.
induction H45.
apply H45.
exists A.
split; Col.
spliter.
apply H2.
Col.
}

assert(CongA C P A D P B).
{
induction(bet_dec C P D).

assert(Bet A P B).
apply (project_preserves_bet P A C A C P D A P B); auto.
repeat split; Col.
left.
right.
repeat split; Col.
repeat split; Col.
repeat split; Col.
unfold Pj in H3.
induction H3.
left.
finish.
right.
auto.
apply(l11_14 C P A D B); auto.
intro.
subst C.
unfold CongA in H36.
tauto.
intro.
subst D.
induction H3.
induction H3.
apply H3.
exists A.
split; Col.
spliter.
apply H2.
ColR.
subst B.
tauto.


assert(Out P C D).
apply(not_bet_out).
Col.
assumption.
assert(Out P A B).
apply(project_preserves_out P C D P A B P A C A).
repeat split.
intro.
subst C.
apply H46.
Between.
intro.
subst D.
apply H46.
Between.
unfold Out in H47.
spliter.
tauto.
intro.
induction H48.
apply H48.
exists C.
split; Col.
spliter.
apply H2.
Col.
repeat split; Col.
repeat split; Col.
left.
right.
repeat split; Col.
repeat split; Col.
left.
unfold Pj in H3.
induction H3.
finish.
subst D.
apply False_ind.
unfold CongA in H42.
tauto.

apply conga_sym.
apply(out_conga C P A C P A D B C A); finish.
apply conga_refl.
apply out_trivial.
unfold Out in H47.
tauto.
unfold Out in H48.
tauto.
apply out_trivial.
unfold Out in H47.
tauto.
}

assert(C1 <> C1').
{
intro.
subst C1'.
apply HN.
Col.
}

assert(O <> C1').
{
intro.
subst C1'.
unfold CongA in H36.
tauto.
}

assert(~Col O C1 C1').
{
intro.
induction H30.
apply perp_not_col in H30.
apply H30.
unfold Midpoint in H7.
spliter.
apply bet_col in H7.
ColR.
apply perp_distinct in H30.
tauto.
}
assert(~Par O C1' C1 C1').
{
intro.
induction H50.
apply H50.
exists C1'.
split; Col.
spliter.
contradiction.
}

assert(~Par O C1 C1 C1').
{
intro.
induction H51.
apply H51.
exists C1.
split; Col.
spliter.
contradiction.
}
assert(Out O C1' D1').
{
apply(project_preserves_out O C1 D1 O C1' D1' O C1' C1 C1'); auto.
repeat split; Col.
repeat split; Col.
left.
finish.
repeat split; Col.
left.
apply(l12_9_2D D1 D1' C1 C1' O M).
assert(Perp D1 D1' N O).
apply(perp_col D1 N N O D1').
intro.
subst D1'.
apply l7_3 in H24.
subst N.
apply perp_distinct in H32.
tauto.
finish.
unfold Midpoint in H24.
spliter.
apply bet_col in H24.
Col.
apply perp_sym.
apply(perp_col O N D1 D1' M).
assumption.
finish.
Col.
induction H30.
apply (perp_col C1 M O M C1'); finish.
unfold Midpoint in H7.
spliter.
apply bet_col in H7.
Col.
apply perp_distinct in H30.
tauto.
}
assert(CongA C1' O A1 D1' O B1).
{
apply(out_conga C1' O A1 C1' O A1 C1' A1 D1' B1); auto.
apply conga_refl.
auto.
intro.
subst A1.
unfold Out in H28.
tauto.
apply out_trivial.
auto.
apply out_trivial.
intro.
subst A1.
unfold Out in H28.
tauto.
apply(length_out O E E' P A  P B A1 B1); auto.
}
assert(CongA D1' O B1 D P B).
{
apply (conga_trans _ _ _ C P A).
apply (conga_trans _ _ _ C1' O A1).
apply conga_sym.
assumption.
apply conga_sym.
assumption.
assumption.
}
assert((D1' <> B1 -> CongA O D1' B1 P D B /\ CongA O B1 D1' P B D)).
{
apply (l11_49 D1' O B1 D P B).
assumption.
apply (cong_transitivity _ _ O D1); Cong.
assumption.
}

assert(D1' <> B1).
{
intro.
subst D1'.
induction H34.
induction H34.
apply H34.
exists C1.
split; Col.
ColR.
spliter.
apply H49.
ColR.
subst D1.
apply l7_3 in H24.
subst N.
apply perp_distinct in H32.
tauto.
}
apply H55 in H56.
spliter.
clear H55.
apply conga_comm in H57.

assert(CongA C1' A1 O D1' B1 O <-> Par A1 C1' B1 D1').
{
apply(l12_22 A1 C1' B1 D1' O).
apply (length_out O E E' P A P B); auto.
apply out_one_side.
left.
intro.
apply H49.
assert(A1 <> O).
intro.
subst A1.
unfold CongA in H53.
tauto.
ColR.
assumption.
}
destruct H55.
assert(Par A1 C1' B1 D1').
{
apply H55.
apply (conga_trans _ _ _ D B P).
apply (conga_trans _ _ _ C A P).
apply conga_sym.
assumption.
assumption.
apply conga_sym.
assumption.
}
clear H55 H58.
assert(Prod O C1 C1' A1 D1 B1).
{
unfold Prod.
repeat split.
assumption.
ColR.
ColR.
ColR.
exists D1'.
repeat split.
assumption.

apply out_col in H31.
ColR.
left.
finish.
}

assert(exists Y : Tpoint, Prod O E C1' A1 D1 Y /\ Prod O E C1' C1 B1 Y).
{
apply(prod_x_axis_unit_change O C1 C1' A1 D1 C1 B1 E).
repeat split; Col.
ColR.
ColR.
Col.
exists B1.
split; auto.
apply prod_1_l; Col.
ColR.
}
ex_and H58 Y.
assert(HH:=prod_y_axis_change O E C1' E' A1 D1 Y H58 H9).
{
assert(Y = AD).
apply(prod_uniqueness O E E' A1 D1); auto.
subst Y.
assert(HP:=prod_y_axis_change O E C1' E' C1 B1 AD H60 H9).
left.
assumption.
}
spliter.
subst M.
apply False_ind.
unfold Midpoint in H7.
spliter.
apply bet_col in H7.
Col.

right.
spliter.
split.
intro.
apply H8.
unfold Ar2 in H11.
spliter.
repeat split; Col.
unfold Length in H4.
tauto.
unfold Length in H7.
tauto.
unfold Length in H7.
tauto.
assumption.
Qed.

Lemma length_existence : forall O E E' A B,
  ~ Col O E E' -> exists AB, Length O E E' A B AB.
Proof.
intros.
assert(NEO : E <> O).
intro.
subst E.
apply H.
Col.
assert(HH:= segment_construction_2 E O A B NEO).
ex_and HH AB.
exists AB.
unfold Length.
assert(AB = O \/ Out O E AB).
induction(eq_dec_points AB O).
left; assumption.
right.
repeat split; auto.
assert(Col O E AB).
induction H2.
subst AB.
Col.
apply out_col.
assumption.
repeat split; Col.
unfold LeP.
induction H2.
right; auto.
left.
unfold LtP.
exists AB.
repeat split.
apply diff_A_O; Col.
unfold Out in H2.
tauto.
auto.
induction H0.
right; assumption.
left; assumption.
Qed.

(** Known as Euklid *)
Lemma l15_7 : forall O E E' A B C H AB AC AH AC2,
  O<>E -> Per A C B -> Perp_at H C H A B ->
  Length O E E' A B AB -> Length O E E' A C AC -> Length O E E' A H AH ->
  (Prod O E E' AC AC AC2 <-> Prod O E E' AB AH AC2).
Proof.
intros.

induction(eq_dec_points AB O).
subst AB.
assert(A = B).
apply (length_id_1 O E E'); assumption.
subst B.
apply perp_in_distinct in H2.
tauto.

assert(~Col O E E' /\ Col O E AB).
unfold Length in H3.
spliter.
unfold LeP in H8.
induction H8.
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H8.
apply sum_ar2 in H8.
unfold Ar2 in H8.
tauto.
subst AB.
tauto.
spliter.

induction(eq_dec_points H A).
subst H.
assert(AH=O).
apply (length_uniqueness O E E' A A); auto.
apply length_id_2.
assumption.
subst AH.
apply perp_in_per in H2.
assert(A = C).
apply (l8_7 B);
finish.
subst C.
assert(AC = O).
apply (length_uniqueness O E E' A A); auto.
subst AC.
split;intros;
assert(AC2=O).
apply (prod_uniqueness O E E' O O); auto.
apply prod_0_r; Col.
subst AC2.
apply prod_0_r; Col.
apply (prod_uniqueness O E E' AB O); auto.
apply prod_0_r; Col.
subst AC2.
apply prod_0_r; Col.



assert(C <> A).
intro.
subst C.
apply perp_in_right_comm in H2.
apply perp_in_id in H2.
contradiction.

assert(HH:= segment_construction_2 H A A C H9).
ex_and HH C'.
assert(Out A H C').
unfold Out.
repeat split; auto.
intro.
subst C'.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst C.
tauto.

assert(HH:= segment_construction_2 C A A H H10).
ex_and HH H'.
assert(Out A C H').
repeat split;auto.
intro.
subst H'.
apply cong_symmetry in H15.
apply cong_identity in H15.
subst H.
tauto.

assert(H <> C).
intro.
subst H.
apply perp_in_distinct in H2.
tauto.

assert(Cong H C H' C' /\ (H <> C -> CongA A H C A H' C' /\ CongA A C H A C' H')).
apply(l11_49 H A C H' A C').
apply (l11_10 H A C C A H).
apply conga_right_comm.
apply conga_refl; auto.
apply out_trivial; auto.
apply out_trivial; auto.
apply l6_6.
assumption.
apply l6_6.
assumption.
Cong.
Cong.
spliter.
assert(HH:= H19 H17).
clear H19.
spliter.

assert(Per A H C).
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
apply perp_comm.
apply (perp_col  _ B).
auto.
apply perp_in_perp_bis in H2.
induction H2.
apply perp_distinct in H2.
tauto.
apply perp_sym.
apply perp_left_comm.
assumption.
apply perp_in_col in H2.
tauto.

assert(HH:= l11_17 A H C A H' C' H21 H19).
assert(Par C B H' C').
apply(l12_9_2D C B H' C' A C).
apply per_perp_in in H1.
apply perp_in_comm in H1.
apply perp_in_perp_bis in H1.
induction H1.
finish.
apply perp_distinct in H1.
tauto.
auto.
intro.
subst C.
apply perp_in_id in H2.
contradiction.
apply per_perp_in in HH.
apply perp_in_comm in HH.
apply perp_in_perp_bis in HH.
apply perp_sym.
apply perp_right_comm.
apply(perp_col A H' C' H' C).
auto.
induction HH.
finish.
apply perp_distinct in H22.
tauto.
apply out_col in H16.
Col.
intro.
subst H'.
apply conga_distinct in H19.
tauto.
intro.
subst H'.
apply conga_distinct in H19.
tauto.

assert(HL1:=length_existence O E E' A H' H7).
ex_and HL1 AH'.
assert(HL1:=length_existence O E E' A C' H7).
ex_and HL1 AC'.
assert(exists P : Tpoint, Prod O E E' AC' AC P).

apply(prod_exists O E E' H7 AC' AC).
unfold Length in H24.
tauto.
unfold Length in H4.
tauto.
ex_and H25 P.

assert(Perp C H A B).
apply perp_in_perp_bis in H2.
induction H2.
apply perp_distinct in H2.
tauto.
assumption.

assert(Prodg O E E' AH' AB P).
apply(thales O E E' A C' B H' C  AC' AB AH' AC   P); Col.
apply perp_in_col in H2.
spliter.

apply out_col in H13.
ColR.
apply out_col in H16.
Col.
intro.
assert(Perp H A C H).
apply perp_comm.
apply(perp_col A B H C H).
intro.
subst H.
apply conga_distinct in H19.
tauto.
finish.
apply perp_in_col in H2.
tauto.
apply perp_not_col in H28.
apply H28.
assert(A <> C').
intro.
subst C'.
unfold CongA in H20.
tauto.
assert(Col A H H').
ColR.
assert(A <> H').
intro.
subst H'.
unfold CongA in H19.
tauto.
ColR.

left.
finish.
left.
assumption.

assert(Prod O E E' AH' AB P).
induction H27.
assumption.
spliter.
apply False_ind.
apply H27.
repeat split; Col.
unfold Length in H23.
tauto.


assert(Length O E E' A H' AH).
apply(length_eq_cong_2 O E E' A H A H' AH H5).
Cong.
assert(AH = AH').
apply (length_uniqueness O E E' A H'); auto.
subst AH'.

assert(Length O E E' A C' AC).
apply(length_eq_cong_2 O E E' A C A C' AC H4).
Cong.
assert(AC = AC').
apply (length_uniqueness O E E' A C'); auto.
subst AC'.

split.
intro.
assert(P = AC2).
apply (prod_uniqueness O E E' AC AC); auto.
subst P.
apply prod_comm.
assumption.

intro.
assert(P = AC2).
apply (prod_uniqueness O E E' AB AH); auto.
apply prod_sym.
assumption.
subst P.
assumption.
Qed.

Lemma l15_7_1 : forall O E E' A B C H AB AC AH AC2,
  O<>E -> Per A C B -> Perp_at H C H A B ->
  Length O E E' A B AB -> Length O E E' A C AC -> Length O E E' A H AH ->
  Prod O E E' AC AC AC2 ->
  Prod O E E' AB AH AC2.
Proof.
intros.
destruct(l15_7 O E E' A B C H AB AC AH AC2 H0 H1 H2 H3 H4 H5).
apply H7.
assumption.
Qed.

Lemma l15_7_2 : forall O E E' A B C H AB AC AH AC2,
  O<>E -> Per A C B -> Perp_at H C H A B ->
  Length O E E' A B AB -> Length O E E' A C AC -> Length O E E' A H AH ->
  Prod O E E' AB AH AC2 ->
  Prod O E E' AC AC AC2.
Proof.
intros.
destruct(l15_7 O E E' A B C H AB AC AH AC2 H0 H1 H2 H3 H4 H5).
apply H8.
assumption.
Qed.


Lemma length_sym : forall O E E' A B AB,
  Length O E E' A B AB -> Length O E E' B A AB.
Proof.
intros.
unfold Length in *.
spliter.
repeat split; auto.
Cong.
Qed.

Lemma pythagoras : forall O E E' A B C AC BC AB AC2 BC2 AB2,
  O <> E -> Per A C B ->
  Length O E E' A B AB ->
  Length O E E' A C AC ->
  Length O E E' B C BC ->
  Prod O E E' AC AC AC2 ->
  Prod O E E' BC BC BC2 ->
  Prod O E E' AB AB AB2 ->
  Sum  O E E' AC2 BC2 AB2.
Proof.
intros.
assert(~Col O E E' /\ Col O E AB2 /\ Col O E AC2 /\ Col O E BC).
unfold Prod in *.
spliter.
unfold Ar2 in H4 ,H5 ,H6.
repeat split; tauto.
spliter.

induction(col_dec A C B).
assert(HH:=l8_9 A C B H0 H11).
induction HH.
subst C.
assert(AB = BC).
apply(length_uniqueness O E E' A B).
assumption.
apply length_sym.
assumption.
subst BC.
assert(AB2 = BC2).
apply(prod_uniqueness O E E' AB AB); auto.
subst BC2.

assert(AC = O).
apply(length_uniqueness O E E' A A).
assumption.
apply length_id_2; assumption.
subst AC.
assert(AC2=O).
apply(prod_uniqueness O E E' O O).
assumption.
apply prod_0_l; Col.
subst AC2.
apply sum_O_B; Col.

subst C.
assert(AB = AC).
apply(length_uniqueness O E E' A B).
assumption.
assumption.
subst AC.
assert(AB2 = AC2).
apply(prod_uniqueness O E E' AB AB); auto.
subst AC2.

assert(BC = O).
apply(length_uniqueness O E E' B B).
assumption.
apply length_id_2; assumption.
subst BC.
assert(BC2=O).
apply(prod_uniqueness O E E' O O).
assumption.
apply prod_0_l; Col.
subst BC2.
apply sum_A_O; Col.



assert(exists X : Tpoint, Col A B X /\ Perp A B C X).
apply(l8_18_existence A B C); Col.
ex_and H12 P.
assert(Perp_at P A B C P).
apply(l8_14_2_1b_bis A B C P P H13); Col.
assert(Bet A P B /\ A <> P /\ B <> P).
apply(l11_47 A B C P H0).
finish.
spliter.

assert(HL1:= length_existence O E E' A P H7).
assert(HL2:= length_existence O E E' B P H7).
ex_and HL1 AP.
ex_and HL2 BP.

assert(Sum O E E' AP BP AB).
apply(triangular_equality_bis O E E' A P B AP BP AB); auto.
apply length_sym.
assumption.

assert(Prod O E E' AB AP AC2).
apply(l15_7_1 O E E' A B C P AB AC AP AC2 H H0); finish.

assert(Prod O E E' AB BP BC2).
eapply(l15_7_1 O E E' B A C P AB BC); finish.
apply length_sym;auto.

assert(HD:=distr_l O E E' AB AP BP AB AC2 BC2 AB2 H20 H21 H22 H6).
assumption.
Qed.


Lemma is_length_exists : forall O E E' X Y,
  ~ Col O E E' -> exists XY, Is_length O E E' X Y XY.
Proof.
intros O E E' X Y HNC.
elim (eq_dec_points X Y); intro HXY;
[treat_equalities; exists O; left; apply length_id_2; assert_diffs; auto|
destruct (length_existence O E E' X Y) as [XY HLength]; Col; exists XY; left; auto].
Qed.

(********************************************************)

Lemma lt_to_ltp : forall O E E' A B L C D M, Length O E E' A B L -> Length O E E' C D M 
              -> Lt A B C D -> LtP O E E' L M.
Proof.
intros.
induction(eq_dec_points L M).
{
  subst M.
  apply length_cong in H0.
  apply length_cong in H.
  unfold Lt in H1.
  spliter.
  apply False_ind.
  apply H2; eCong.
}
{
  assert(Le A B C D).
  {
    apply lt__le; auto.
  }
  assert(HH:= length_leP_le_2 O E E' A B C D L M H H0 H3).
  unfold LeP in HH.
  induction HH.
  {
    assumption.
  }
  {
    contradiction.
  }
}
Qed.

Lemma ltp_to_lep : forall O E E' L M, LtP O E E' L M -> LeP O E E' L M.
Proof.
intros.
unfold LeP.
left; auto.
Qed.


Lemma ltp_to_lt : forall O E E' A B L C D M, Length O E E' A B L -> Length O E E' C D M 
              -> LtP O E E' L M -> Lt A B C D.
Proof.
intros.
assert(LeP O E E' L M).
apply ltp_to_lep; auto.
unfold Lt.
split.
apply(length_leP_le_1 O E E' A B C D  L M); auto.
intro.
assert(HH:= length_eq_cong_2 O E E' A B C D L H H3).
assert(L = M).
{
  apply (length_uniqueness O E E' C D); auto.
}
subst M.
unfold LtP in H1.
ex_and H1 P.

assert(~Col O E E' /\  Col O E L).
{
  unfold Diff in H1.
  ex_and H1 X.
  unfold Sum in H5.
  unfold Ar2 in H5.
  spliter.
  tauto.
}
spliter.

assert(HP:= diff_null O E E' L H5 H6).
assert(P = O).
apply(diff_uniqueness O E E' L L P O); auto.
subst P.
unfold Ps in H4.
unfold Out in H4.
tauto.
Qed.


Lemma prod_col : forall O E E' A B AB ,Ar2 O E E' A B A -> Prod O E E' A B AB -> Col O E AB.
Proof.
intros.
unfold Prod in H0.
spliter.
unfold Ar2 in H0.
tauto.
Qed.


Lemma square_increase_strict : forall O E E' A B A2 B2, Ar2 O E E' A B A ->  Ps O E A -> Ps O E B 
                              -> LtP O E E' A B
                              -> Prod O E E' A A A2 -> Prod O E E' B B B2
                              -> LtP O E E' A2 B2.
Proof.

intros.
assert(HA2 : Col O E A2).
{
  apply (prod_col O E E' A A); auto.
  unfold Ar2 in *.
  tauto.
}
assert(HB2: Col O E B2).
{
  apply (prod_col O E E' B B); auto.
  unfold Ar2 in *.
  tauto.
}
unfold Ar2 in H.
spliter.
assert(HD:=diff_exists O E E' B A H H6 H7).
ex_and HD BmA.
assert(HS:=sum_exists O E E' H B A H6 H7).
ex_and HS BpA.
assert(HD:=diff_exists O E E' B2 A2 H HB2 HA2).
ex_and HD B2mA2.
assert(Col O E BpA).
{
  apply sum_ar2 in H9.
  unfold Ar2 in H9.
  tauto.
}
assert(Col O E BmA).
{
  apply diff_ar2 in H8.
  unfold Ar2 in H8.
  tauto.
}
assert(Col O E B2mA2).
{
  apply diff_ar2 in H10.
  unfold Ar2 in H10.
  tauto.
}

assert(HP:= prod_exists O E E' H BpA BmA H11 H12).
ex_and HP F.

assert(HC:= diff_of_squares O E E' B A B2 A2 B2mA2 BpA BmA F H4 H3 H10 H9 H8 H14).
subst F.
unfold LtP.
exists B2mA2.
split; auto.
apply (prod_pos_pos O E E' BpA BmA); auto.
apply (sum_pos_pos O E E' B A); auto.
apply (lt_diff_ps O E E' B A); auto.
Qed.

Lemma square_increase : forall O E E' A B A2 B2, Ar2 O E E' A B A ->  Ps O E A -> Ps O E B 
                              -> LeP O E E' A B
                              -> Prod O E E' A A A2 -> Prod O E E' B B B2
                              -> LeP O E E' A2 B2.
Proof.
intros.
unfold LeP in H2.
induction H2.
apply (square_increase_strict O E E' A B A2 B2) in H2; auto.
apply ltp_to_lep in H2; auto.
subst B.
assert(A2 = B2).
{
  apply (prod_uniqueness O E E' A A); auto.
}
subst B2.
unfold LeP.
right; auto.
Qed.


Lemma signeq__prod_pos : forall O E E' A B C, SignEq O E A B -> Prod O E E' A B C -> Ps O E C.
Proof.
intros.
unfold SignEq in H.
induction H.
spliter.
apply (prod_pos_pos O E E' A B); auto.

assert(HP:=H0).
spliter.
apply prod_to_prodp in H0.

unfold Prodp in H0.
spliter.
ex_and H3 B'.
assert(HPP:= HP).
unfold Prod in HP.
unfold Ar2 in HP.
spliter.
assert(Bet B' O E').
{
  assert(HQQ:=project_preserves_bet).
  apply(project_preserves_bet O E' E E' B O E B' O E'); auto.
  unfold Ng in H1.
  tauto.
  apply project_trivial; 
  try(intro;subst E';apply H5; Col).
  Col.
  intro.
  unfold Par in H10.
  induction H10.
  {
    unfold Par_strict in H10.
    spliter.
    apply H13.
    exists E'.
    split; Col.
  }
  {
    spliter.
    contradiction.
  }
  unfold Proj.
  repeat split; try(intro;subst E';apply H5; Col).
  intro.
  unfold Par in H10.
  induction H10.
  {
    unfold Par_strict in H10.
    spliter.
    apply H13.
    exists E'.
    split; Col.
  }
  {
    spliter.
    contradiction.
  }
  Col.
  left.
  apply par_reflexivity.
  intro.
  subst E'.
  apply H5; Col.
}

assert(Bet A O C).
{
  apply(project_preserves_bet O E A E' E' O B' A O C); Between.
 unfold Proj.
  repeat split; auto.
  intro.
  subst E.
  apply H5; Col.
  intro.
  subst A.
  contradiction.
  intro.
  unfold Par in H11.
  induction H11.
  {
    unfold Par_strict in H11.
    spliter.
    apply H14.
    exists A;
    split; Col.
  }
  {
    spliter.
    apply H5.
    ColR.
  }
  left.
  apply par_left_comm.
  apply par_reflexivity.
  intro.
  subst A.
  contradiction.
  apply project_trivial; Col.
  intro; subst E; apply H5; Col.
  intro;subst A;contradiction.
  intro.
  unfold Par in H11.
  induction H11.
  {
    unfold Par_strict in H11.
    spliter.
    apply H14.
    exists A.
    split; Col.
  }
  {
    spliter.
    apply H5; ColR.
  }
}
unfold Ps.
unfold Ng in H.
spliter.
apply l6_6.
assert(HH:= l6_2 E C A O).
apply HH; Between.
intro.
subst C.
apply prod_null in HPP.
unfold Ng in H1.
spliter.
induction HPP;
contradiction.
Qed.

Lemma pos_neg__prod_neg : forall O E E' A B C, Ps O E A -> Ng O E B -> Prod O E E' A B C -> Ng O E C.
Proof.
intros.
assert(HP:=H1).
spliter.
apply prod_to_prodp in H1.

unfold Prodp in H1.
spliter.
ex_and H3 B'.
assert(HPP:= HP).
unfold Prod in HP.
unfold Ar2 in HP.
spliter.
clear H6.
assert(Bet B' O E').
{
  apply(project_preserves_bet O E' E E' B O E B' O E'); auto.
  unfold Ng in H0.
  tauto.
  apply project_trivial; 
  try(intro;subst E';apply H5; Col).
  Col.
  intro.
  unfold Par in H6.
  induction H6.
  {
    unfold Par_strict in H6.
  spliter.
    apply H12.
    exists E'.
    split; Col.
  }
  {
    spliter.
    contradiction.
  }
  unfold Proj.
  repeat split; try(intro;subst E';apply H5; Col).
  intro.
  unfold Par in H6.
  induction H6.
  {
    unfold Par_strict in H6.
    spliter.
    apply H12.
    exists E'.
    split; Col.
  }
  {
    spliter.
    contradiction.
  }
  Col.
  left.
  apply par_reflexivity.
  intro.
  subst E'.
  apply H5; Col.
}

assert(Bet A O C).
{
  apply(project_preserves_bet O E A E' E' O B' A O C); Between.
 unfold Proj.
  repeat split; auto.
  intro.
  subst E.
  apply H5; Col.
  intro.
  subst A.
  contradiction.
  intro.
  unfold Par in H10.
  induction H10.
  {
    unfold Par_strict in H10.
    spliter.
    apply H13.
    exists A;
    split; Col.
  }
  {
    spliter.
    apply H5.
    ColR.
  }
  left.
  apply par_left_comm.
  apply par_reflexivity.
  intro.
  subst A.
  contradiction.
  apply project_trivial; Col.
  intro; subst E; apply H5; Col.
  intro;subst A;contradiction.
  intro.
  unfold Par in H10.
  induction H10.
  {
    unfold Par_strict in H10.
    spliter.
    apply H13.
    exists A.
    split; Col.
  }
  {
    spliter.
    apply H5; ColR.
  }
}

unfold Ng.
repeat split.
intro.
subst C.
apply prod_null in HPP.
induction HPP.
unfold Ps in H.
unfold Out in H.
tauto.
subst B.
unfold Ng in H0.
tauto.
intro.
subst E.
apply H5; Col.
unfold Ps in H.
unfold Out in H.
spliter.
induction H12;
eBetween.
Qed.


Lemma sign_dec : forall O E A, Col O E A -> O <> E -> A = O \/ Ps O E A \/ Ng O E A.
Proof.
intros.
induction(eq_dec_points A O).
left; auto.
assert(HH:= third_point O E A H).

induction HH.
  {
    right;right.
    unfold Ng.
    repeat split; auto.
  }
   
  {
    right;left.
    unfold Ps.
    unfold Out.
    repeat split; auto.
  }
Qed.


Lemma not_signEq_prod_neg : forall O E E' A B C, A <> O -> B <> O -> ~SignEq O E A B -> Prod O E E' A B C -> Ng O E C.
Proof.
intros.
assert(HP:=H2).
unfold Prod in HP.
unfold Ar2 in HP.
spliter.
clear H4.
assert(O <> E).
{
  intro; subst E; apply H1; Col.
  apply False_ind; Col.
}
assert(HA:=sign_dec O E A H5 H4).
assert(HB:= sign_dec O E B H6 H4).
induction HA; induction HB; try contradiction.
induction H8;induction H9.
{
  apply False_ind.
  apply H1.
  unfold SignEq.
  left; auto.
}
{
  apply(pos_neg__prod_neg O E E' A B); auto.
}
{
  apply prod_comm in H2.
  apply(pos_neg__prod_neg O E E' B A); auto.
}
{
  apply False_ind.
  apply H1.
  unfold SignEq.
  right; auto.
}
Qed.



Lemma prod_pos__signeq : forall O E E' A B C, A <> O -> B <> O -> Prod O E E' A B C -> Ps O E C -> SignEq O E A B.
Proof.
intros.
assert(HP:= H1).
unfold Prod in HP.
unfold Ar2 in HP.
spliter.
clear H4.
assert(HA:= sign_dec O E A H5).
assert(HB:= sign_dec O E B H6).
assert(O <> E).
{
  intro.
  subst E.
  apply H3; Col.
}

induction HA;auto.
contradiction.
induction HB; auto.
contradiction.

induction H8; induction H9.
{
  unfold SignEq.
  left.
  split; auto.
}
{
  apply pos_neg__prod_neg in H1; auto.
  apply pos_not_neg in H2.
  contradiction.
}
{
  apply prod_comm in H1.
  apply pos_neg__prod_neg in H1; auto.
  apply pos_not_neg in H2.
  contradiction.
}
{
  unfold SignEq.
  right.
  split; auto.
}
Qed.

Lemma prod_ng___not_signeq : forall O E E' A B C, A <> O -> B <> O -> Prod O E E' A B C -> Ng O E C -> ~SignEq O E A B.
Proof.
intros.
assert(HP:= H1).
unfold Prod in HP.
unfold Ar2 in HP.
spliter.
clear H4.
assert(HA:= sign_dec O E A H5).
assert(HB:= sign_dec O E B H6).
assert(O <> E).
{
  intro.
  subst E.
  apply H3; Col.
}

induction HA;auto.
induction HB; auto.

induction H8; induction H9.
{
  apply False_ind.
  apply signeq__prod_pos in H1.
  apply pos_not_neg in H1.
  contradiction.
  unfold SignEq.
  left; auto.
}
{
  intro.
  unfold SignEq in H10.
  induction H10.
  {
    spliter.
    apply pos_not_neg in H11.
    contradiction.
  }
  {
    spliter.
    apply pos_not_neg in H8.
    contradiction.
  }
}
{
  intro.
  unfold SignEq in H10.
  induction H10.
  {
    spliter.
    apply pos_not_neg in H8; auto.
  }
  {
    spliter.
    apply pos_not_neg in H9.
    contradiction.
  }
}
{
  apply signeq__prod_pos in H1.
  apply pos_not_neg in H1; auto.
  unfold SignEq.
  right.
  split; auto.
}
Qed.

Lemma ltp__diff_pos : forall O E E' A B D, LtP O E E' A B -> Diff O E E' B A D -> Ps O E D.
Proof.
intros.
unfold LtP in H.
ex_and H D'.
assert(D = D').
{
  apply (diff_uniqueness O E E' B A); auto.
}
subst D'.
assumption.
Qed.

Lemma diff_pos__ltp : forall O E E' A B D, Diff O E E' B A D -> Ps O E D -> LtP O E E' A B.
Proof.
intros.
unfold LtP.
exists D.
split; auto.
Qed.


Lemma square_increase_rev : forall O E E' A B A2 B2, Ps O E A -> Ps O E B 
                              -> LtP O E E' A2 B2
                              -> Prod O E E' A A A2 -> Prod O E E' B B B2
                              -> LtP O E E' A B.
Proof.

intros.
assert(HP2:= H2).
assert(HP3:=H3).
unfold Prod in HP2.
unfold Prod in HP3.
spliter.
unfold Ar2 in *.
spliter.
clean_duplicated_hyps.
clear H7 H5.
assert(HS:=sum_exists O E E' H6 B A H8 H11).
ex_and HS SS.
assert(HD:= diff_exists O E E' B A H6 H8 H11).
ex_and HD DD.

assert(exists C : Tpoint, Prod O E E' SS DD C).
{
  apply(prod_exists O E E' H6 SS DD).
  unfold Sum in H4.
  unfold Ar2 in H4.
  tauto.
  unfold Diff in H5.
  ex_and H5 X.
  unfold Sum in H7.
  spliter.
  unfold Ar2 in H7.
  tauto.
}

ex_and H7 PSD.

assert(HH:= diff_exists O E E' B2 A2 H6 H10 H13).
ex_and HH D2.

assert(HH:= diff_of_squares O E E' B A B2 A2 D2 SS DD PSD H3 H2 H7 H4 H5 H9).
subst PSD.

assert(HH:=(ltp__diff_pos O E E' A2 B2 D2 H1 H7)).

apply(prod_pos__signeq) in H9; auto.

unfold SignEq in H9.
induction H9.
{
  spliter.
  apply diff_pos__ltp in H5; auto.
}
{
  spliter.
  apply False_ind.
  assert(HS:= sum_pos_pos O E E' B A SS H0 H H4).
  apply pos_not_neg in HS.
  contradiction.
}
intro.
subst SS.
apply sum_pos_pos in H4; auto.
unfold Ps in H4.
unfold Out in H4.
tauto.
intro.
subst DD.
apply diff_null_eq in H5.
subst B.

assert(Prod O E E' SS O O).
{
  apply (prod_0_r O E E' SS).
  Col.
  unfold Sum in H4.
  unfold Ar2 in H4.
  spliter; tauto.
}
assert(D2 = O).
{
  apply (prod_uniqueness O E E' SS O); auto.
}
subst D2.
assert(B2 = A2).
{
  apply(diff_null_eq O E E'); auto.
}
subst B2.
unfold LtP in H1.
ex_and H1 DF.
assert(HD:= diff_null O E E' A2 H6 H13).
assert(DF=O).
{
  apply(diff_uniqueness O E E' A2 A2); auto.
}
subst DF.
unfold Ps in H12.
unfold Out in H12.
tauto.
Qed.


Lemma ltp__ltps: forall O E E' A B, LtP O E E' A B -> LtPs O E E' A B.
Proof.
intros.
unfold LtP in H.
ex_and H D.
unfold LtPs.
exists D.
split; auto.

apply diff_sum.
assumption.
Qed.

Lemma ltps__ltp: forall O E E' A B, LtPs O E E' A B -> LtP O E E' A B.
Proof.
intros.
unfold LtPs in H.
ex_and H D.
unfold LtP.
exists D.
split; auto.
apply sum_diff.
assumption.
Qed.

Lemma ltp__lep_neq : forall O E E' A B, LtP O E E' A B -> LeP O E E' A B /\ A <> B.
Proof.
intros.
unfold LeP.
split.
left; auto.
(*apply ltp__ltps in H.*)
unfold LtP in H.
ex_and H D.
intro.
subst B.
assert(HD:= H).
unfold Diff in HD.
ex_and HD B'.
unfold Sum in H2.
unfold Ar2 in H2.
spliter.
clear H3.
assert(Diff O E E' A A O).
apply diff_null; auto.
assert(D = O).
apply (diff_uniqueness O E E' A A); auto.
subst D.
unfold Ps in H0.
unfold Out in H0.
tauto.
Qed.


Lemma lep_neq__ltp : forall O E E' A B,  LeP O E E' A B /\ A <> B -> LtP O E E' A B.
Proof.
intros.
spliter.
unfold LeP in H.
induction H.
assumption.
contradiction.
Qed.


Lemma sum_preserves_ltp : forall O E E' A B C AC BC, LtP O E E' A B -> Sum O E E' A C AC -> Sum O E E' B C BC -> LtP O E E' AC BC.
Proof.
intros.
apply ltp__lep_neq in H.
spliter.
apply lep_neq__ltp.
split.
apply(compatibility_of_sum_with_order O E E' A B C AC BC H H0 H1).
intro.
subst BC.
assert(HS:= H0).
unfold Sum in HS.
unfold Ar2 in HS.
spliter.
clear H4.
assert(A = B).
{
  apply (sum_uniquenessA O E E' H3 C A B AC); auto.
}
contradiction.
Qed.

Lemma sum_preserves_lep : forall O E E' A B C AC BC, LeP O E E' A B -> Sum O E E' A C AC -> Sum O E E' B C BC -> LeP O E E' AC BC.
Proof.
intros.
induction(eq_dec_points A B).
{
  subst B.
  assert(HH:=sum_uniqueness O E E' A C  AC BC H0 H1).
  subst BC.
  apply leP_refl.
}
{
  assert(LtP O E E' A B).
  {
    apply(lep_neq__ltp O E E' A B ); auto.
  }
  apply ltp_to_lep.
  apply (sum_preserves_ltp O E E' A B C AC BC); auto.
}
Qed.

Lemma sum_preserves_ltp_rev : forall O E E' A B C AC BC, Sum O E E' A C AC -> Sum O E E' B C BC -> LtP O E E' AC BC
                                ->  LtP O E E' A B.
Proof.
intros.
assert(HS1:= H).
assert(HS2:= H0).
unfold Sum in HS1.
unfold Sum in HS2.
unfold Ar2 in *.
spliter.
clear H8.
clear H3.

assert(HH:= opp_exists O E E' H2 C H10).
ex_and HH C'.
assert (OP:=H3).
unfold Opp in OP.
unfold Sum in OP.
unfold Ar2 in *.
spliter.
clear H12.

unfold Opp in H3.
apply sum_comm in H3; Col.

assert(HH:= sum_exists O E E' H7 AC C' H11 H13).
ex_and HH D.
assert(HH:=sum_assoc O E E' A C C' AC O D H H3).
destruct HH.
assert(Sum O E E' A O D).
{
  apply H17; auto.
}
assert(HS:=sum_A_O_eq O E E' H2 A D H18).
subst D.

assert(HH:= sum_exists O E E' H7 BC C' H6 H13).
ex_and HH D.
assert(HH:=sum_assoc O E E' B C C' BC O D H0 H3).
destruct HH.
assert(Sum O E E' B O D).
{
  apply H21; auto.
}
assert(HS:=sum_A_O_eq O E E' H2 B D H22).
subst D.
apply(sum_preserves_ltp O E E'  AC BC C' A B H1 H12 H19).
Qed.


Lemma sum_preserves_lep_rev : forall O E E' A B C AC BC, Sum O E E' A C AC -> Sum O E E' B C BC -> LeP O E E' AC BC
                                ->  LeP O E E' A B.
Proof.
intros.

intros.
assert(HS1:= H).
assert(HS2:= H0).
unfold Sum in HS1.
unfold Sum in HS2.
unfold Ar2 in *.
spliter.
clear H8.
clear H3.
unfold LeP in *.
induction H1.
{
  left.
  apply (sum_preserves_ltp_rev O E E' A B C AC BC); auto.
}
{
  subst BC.
  right.
  apply (sum_uniquenessA O E E' H7 C A B AC); auto.
}
Qed.

Lemma cong2_lea__le :   forall A B C D E F : Tpoint,
  Cong A B D E -> Cong A C D F -> LeA F D E C A B -> Le E F B C.
Proof.
intros.

assert(LtA F D E C A B \/ CongA F D E C A B).
{
  unfold LtA.
  induction (conga_dec F D E C A B).
  {
    right; assumption.
  }
  {
    left.
    split;
    auto.
  }
}
induction H2.
{
  assert(Lt E F B C).
  {
    apply(t18_18 A B C D E F);auto.
  }
  apply lt__le.
  assumption.
}
assert(Cong F E C B /\ (F <> E -> CongA D F E A C B /\ CongA D E F A B C)).
apply(l11_49 F D E C A B); Cong.
spliter.
unfold Le.
exists C.
split;Cong.
Between.
Qed.

Lemma lea_out_lea : forall A B C D E F A' C' D' F', Out B A A' -> Out B C C' -> Out E D D' -> Out E F F'
                      -> LeA A B C D E F -> LeA A' B C' D' E F'.
Proof.
intros.
unfold LeA in *.
ex_and H3 P.
exists P.
split.
apply (l11_25 P D E F D' F' P);
try(apply l6_6); auto.
apply out_trivial.
unfold CongA in H4.
tauto.
apply (out_conga A B C D E P); auto.
apply out_trivial.
unfold CongA in H4.
tauto.
Qed.

Lemma lta_out_lta : forall A B C D E F A' C' D' F', Out B A A' -> Out B C C' -> Out E D D' -> Out E F F'
                      -> LtA A B C D E F -> LtA A' B C' D' E F'.
Proof.
intros.
unfold LtA in *.
spliter.
split.
apply(lea_out_lea A B C D E F A' C' D' F');auto.
intro.
apply H4.
apply (out_conga A' B C' D' E F');
try(apply l6_6); auto.
Qed.


Lemma pythagoras_obtuse : forall O E E' A B C AC BC AB AC2 BC2 AB2 S2,
  O<>E -> Obtuse A C B ->
  Length O E E' A B AB -> Length O E E' A C AC -> Length O E E' B C BC ->
  Prod O E E' AC AC AC2 -> Prod O E E' BC BC BC2 -> Prod O E E' AB AB AB2 ->
  Sum  O E E' AC2 BC2 S2 -> LtP O E E' S2 AB2.
intros.
unfold Obtuse in H0.
ex_and H0 A'.
ex_and H8 B'.
ex_and H0 C'.
assert(A' <> B' /\ C' <> B' /\ C <> A /\ C' <> B' /\ C <> B).
{
  unfold GtA in H8.
  unfold LtA in H8.
  spliter.
  unfold LeA in H8.
  ex_and H8 P.
  unfold CongA in H10.
  unfold InAngle in H8.
  repeat split;
  try tauto.
  spliter.
  auto.
  spliter.
  auto.
}
spliter.
assert(HH:=l6_11_existence B' C A A' H9 H11).
ex_and HH AA.
assert(HH:=l6_11_existence B' C B C' H12 H13).
ex_and HH CC.
assert(Lt AA CC A B).
{
  apply(t18_18 C A B B' AA CC);Cong.
  unfold GtA in H8.
  apply lta_comm.
  apply(lta_out_lta A' B' C' A C B);
  try(apply l6_6; auto).
  apply out_trivial; auto.
  apply out_trivial; auto.
  auto.
}
assert(~Col O E E').
{
  unfold Prod in H5.
  unfold Ar2 in H5; tauto.
}
assert(exists S1 : Tpoint, Length O E E' AA CC S1).
{
  apply(length_existence O E E' AA CC);auto.
}
destruct H20 as [S1 H21].
(* ex_and H20 S1. *)
assert(exists SS : Tpoint, Prod O E E' S1 S1 SS).
{
  apply(prod_exists O E E' H19 S1 S1);
  unfold Length in H21;tauto.
} 
ex_and H20 SS.
apply (per_col _ _ _ CC) in H0;auto.
apply l8_2 in H0.
apply (per_col _ _ _ AA) in H0;auto.

assert(Sum O E E' AC2 BC2 SS).
{
  apply(pythagoras O E E' AA CC B' AC BC S1 AC2 BC2 SS H); auto.
  apply l8_2; auto.
  apply(length_eq_cong_2  O E E' A C AA B'); Cong.
  apply(length_eq_cong_2  O E E' B C CC B'); Cong.

}

assert(S2=SS).
{
  apply (sum_uniqueness O E E' AC2 BC2);auto.
}
treat_equalities.
assert(HH:= lt_to_ltp O E E' AA CC S1 A B AB H21 H1 H18).


assert(Ps O E S1).
{

  assert(AA <> B').
  {
    intro.
    treat_equalities.
    unfold Out in H14.
    contradiction.
  }
  assert(CC <> B').
  {
    intro.
    treat_equalities.
    unfold Out in H16.
    contradiction.
  }

  assert(AA <> CC).
  intro.
  treat_equalities.
  apply l8_8 in H0.
  treat_equalities.
  tauto.

  apply length_Ps in H21; auto.
  intro.
  apply sym_equal in H24.
  treat_equalities.
  apply length_cong in H21.
  treat_equalities.
  tauto.
}

apply(square_increase_strict O E E' S1 AB S2 AB2); auto.
unfold Length in H1.
unfold Length in H21.
spliter.


repeat split; Col.

apply (length_Ps O E E' A B); auto.
intro.
apply sym_equal in H20.
treat_equalities.
apply ltP_neg in HH.
apply pos_not_neg in H12.
contradiction.
apply out_col in H14; Col.
apply out_col in H16; Col.
Qed.

Lemma pythagoras_obtuse_or_per : forall O E E' A B C AC BC AB AC2 BC2 AB2 S2,
  O<>E -> Obtuse A C B \/ Per A C B ->
  Length O E E' A B AB -> Length O E E' A C AC -> Length O E E' B C BC ->
  Prod O E E' AC AC AC2 -> Prod O E E' BC BC BC2 -> Prod O E E' AB AB AB2 ->
  Sum  O E E' AC2 BC2 S2 -> LeP O E E' S2 AB2.
intros.
induction H0.
{
  apply ltp_to_lep.
  apply (pythagoras_obtuse O E E' A B C AC BC AB AC2 BC2 AB2 S2); auto.
}
{
  assert(HH:= pythagoras O E E' A B C AC BC AB AC2 BC2 AB2 H H0 H1 H2 H3 H4 H5 H6).
  assert(S2 = AB2).
  {
    apply (sum_uniqueness O E E' AC2 BC2); auto.
  }
  subst S2.
  apply leP_refl.
}
Qed.

Lemma pythagoras_acute : forall O E E' A B C AC BC AB AC2 BC2 AB2 S2,
  O<>E -> Acute A C B ->
  Length O E E' A B AB -> Length O E E' A C AC -> Length O E E' B C BC ->
  Prod O E E' AC AC AC2 -> Prod O E E' BC BC BC2 -> Prod O E E' AB AB AB2 ->
  Sum  O E E' AC2 BC2 S2 -> LtP O E E' AB2 S2.
intros.
unfold Acute in H0.
ex_and H0 A'.
ex_and H8 B'.
ex_and H0 C'.

assert(A <> C /\ B <> C).
{
  split;
  intro;
  treat_equalities;
  unfold LtA in H8;
  spliter;
  unfold LeA in H8;
  ex_and H8 P;
  unfold CongA in *;
  tauto.
}
spliter.
assert(~Col O E E').
{
  unfold Prod in H5.
  unfold Ar2 in H5; tauto.
}

induction(eq_dec_points A B).
{
  treat_equalities.
  assert(Length O E E' A A O).
  {
      apply length_id_2; auto.
  }
  assert(AB = O).
  {
    apply (length_uniqueness O E E' A A); auto.
  }
  apply sym_equal in H12.
  treat_equalities.
  apply(prod_O_l_eq) in H6.
  subst AB2.
  apply length_Ps in H2.
  apply length_Ps in H3.
  assert(Ps O E AC2).
  {
    apply (signeq__prod_pos O E E' AC AC); auto.
    unfold SignEq.
    left.
    split; auto.
  }
  assert(Ps O E BC2).
  {
    apply (signeq__prod_pos O E E' BC BC); auto.
    unfold SignEq.
    left.
    split; auto.
  }
  apply sum_pos_pos in H7; auto.
  unfold LtP.
  exists S2.
  split; auto.
  apply(diff_A_O O E E'  S2 ); auto.
  unfold Ps in H2.
  apply out_col in H2; Col.
  intro.
  subst BC.
  apply length_cong in H3.
  treat_equalities; tauto;
  apply sym_equal in H6.
  intro.
  subst AC.
  apply length_cong in H2.
  treat_equalities; tauto.
}
{
  assert(A' <> B' /\ C' <> B'  /\ C' <> B').
  {

    unfold LtA in H8.
    spliter.
    unfold LeA in H8.
    ex_and H8 P.
    unfold CongA in H10.
    unfold InAngle in H8.
    repeat split;
    tauto.
  }
  spliter.
  assert(exists X : Tpoint, Out B' X A' /\ Cong B' X C A).
  {
    apply(l6_11_existence B' C A A' H13); auto.
  }
  ex_and H16 AA.
  assert(exists X : Tpoint, Out B' X C' /\ Cong B' X C B).
  {
    apply(l6_11_existence B' C B C'); auto.
  }
  ex_and H18 CC.
  assert(Lt A B AA CC).
  {
    apply(t18_18 B' AA CC C A B );Cong.
    apply lta_comm.
    apply(lta_out_lta  A C B A' B' C');
    try(apply l6_6; auto).
    apply out_trivial; auto.
    apply out_trivial; auto.
    auto.
  }

  assert(exists S1 : Tpoint, Length O E E' AA CC S1).
  {
    apply(length_existence O E E' AA CC);auto.
  }
  destruct H21 as [S1 H22].
  assert(exists SS : Tpoint, Prod O E E' S1 S1 SS).
  {
    apply(prod_exists O E E' H11 S1 S1);
    unfold Length in H22;tauto.
  } 
  ex_and H21 SS.
  apply (per_col _ _ _ CC) in H0;auto.
  apply l8_2 in H0.
  apply (per_col _ _ _ AA) in H0;auto.

  assert(Sum O E E' AC2 BC2 SS).
  {
    apply(pythagoras O E E' AA CC B' AC BC S1 AC2 BC2 SS H); auto.
    apply l8_2; auto.
    apply(length_eq_cong_2  O E E' A C AA B'); Cong.
    apply(length_eq_cong_2  O E E' B C CC B'); Cong.
  }

  assert(S2=SS).
  {
    apply (sum_uniqueness O E E' AC2 BC2);auto.
  }
  treat_equalities.
  assert(HH:= lt_to_ltp O E E' A B AB AA CC S1 H1 H22 H20).

  apply(square_increase_strict O E E' AB S1 AB2 S2); auto.
  unfold Length in H1.
  unfold Length in H22.
  spliter.
  repeat split; Col.
  apply (length_Ps O E E' A B) in H1.
  auto.
  intro.
  apply sym_equal in H15.
  treat_equalities.
  apply (length_cong O E E') in H1.
  treat_equalities.
  tauto.

  assert(AA <> B').
    {
      intro.
      treat_equalities.
      unfold Out in H14.
      contradiction.
    }
    assert(CC <> B').
    {
      intro.
      treat_equalities.
      unfold Out in H16.
      contradiction.
    }

  assert(AA <> CC).
  intro.
  treat_equalities.
  apply l8_8 in H0.
  treat_equalities.
  tauto.
  apply length_Ps in H22; auto.
  intro.
  apply sym_equal in H25.
  treat_equalities.
  apply length_cong in H22.
  treat_equalities.
  tauto.
  apply out_col in H16; Col.
  apply out_col in H18; Col.
}
Qed.

Lemma pyth_context : forall O E E' A B C : Tpoint, ~Col O E E' -> exists AB BC AC AB2 BC2 AC2 SS,
                      Col O E AB /\ Col O E BC /\ Col O E AC
                    /\ Col O E AB2 /\ Col O E BC2 /\ Col O E AC2
                    /\  Length O E E' A B AB /\ Length O E E' B C BC /\ Length O E E' A C AC
                    /\ Prod O E E' AB AB AB2 /\ Prod O E E' BC BC BC2 /\ Prod O E E' AC AC AC2
                    /\ Sum O E E' AB2 BC2 SS .
Proof.
intros.
assert(Lab:=length_existence O E E' A B H).
ex_and Lab AB.
assert(Lbc:=length_existence O E E' B C H).
ex_and Lbc BC.
assert(Lac:=length_existence O E E' A C H).
ex_and Lac AC.

assert(Col O E AB /\ Col O E BC /\ Col O E AC).
unfold Length in *; tauto.
spliter.
assert(Pab:= prod_exists O E E' H AB AB H3 H3).
ex_and Pab AB2.
assert(Pbc:= prod_exists O E E' H BC BC H4 H4).
ex_and Pbc BC2.
assert(Pac:= prod_exists O E E' H AC AC H5 H5).
ex_and Pac AC2.

assert(Col O E AB2 /\ Col O E BC2 /\ Col O E AC2).
unfold Prod in *.
unfold Ar2 in *.
tauto.
spliter.
assert(HS:= sum_exists O E E' H AB2 BC2 H9 H10).
ex_and HS SS.

exists AB.
exists BC.
exists AC.
exists AB2.
exists BC2.
exists AC2.
exists SS.
tauto.
Qed.


Lemma length_pos_or_null : forall O E E' A B AB, Length O E E' A B AB -> Ps O E AB \/ A = B.
Proof.
intros.
induction(eq_dec_points A B).
{
  right; auto.
}
{
  apply length_Ps in H.
  left; auto.
  intro.
  subst AB.
  unfold Length in H.
  spliter.
  treat_equalities.
  tauto.
}
Qed.

Lemma not_neg_pos : forall O E A, E <> O -> Col O E A -> ~Ng O E A -> Ps O E A \/ A = O.
Proof.
intros.
induction(eq_dec_points A O).
{
  right; auto.
}
{
  left.
  unfold Out.
  apply l6_4_2.
  split; Col.
  intro.
  apply H1.
  unfold Ng.
  repeat split; auto.
}
Qed.

Lemma sum_pos_null : forall O E E' A B, ~Ng O E A -> ~Ng O E B -> Sum O E E' A B O -> A = O /\ B = O.
Proof.
intros.
assert(Col O E A /\ Col O E B /\ O <> E /\ ~Col O E E').
{
  unfold Sum in H1.
  unfold Ar2 in H1.
  spliter.
  repeat split;Col.
  intro.
  subst E.
  Col.
}
spliter.
assert(Ps O E A \/ A = O).
{
  induction(eq_dec_points A O).
  {
    right; auto.
  }
  {
    left.
    apply (not_neg_pos O E A) in H; Col.
    induction H.
    {
      auto.
    }
    {
      contradiction.
    }
  }
}
assert(Ps O E B\/ B = O).
{
  induction(eq_dec_points B O).
  {
    right; auto.
  }
  {
    left.
    apply (not_neg_pos O E B) in H0; Col.
    induction H0.
    {
      auto.
    }
    {
      contradiction.
    }
  }
}
induction H6; induction H7.
{
  assert(HH:= sum_pos_pos O E E' A B O H6 H7 H1).
  unfold Ps in HH.
  unfold Out in HH.
  tauto.
}
{
  subst B.
  assert(HH:=sum_A_O O E E' H5 A H2).
  split; auto.
  apply (sum_uniqueness O E E' A O); auto.
}
{
  subst A.
  assert(HH:=sum_O_B O E E' H5 B H3).
  split; auto.
  apply (sum_uniqueness O E E' O B );auto.
}
{
  tauto.
}
Qed.




Lemma length_not_neg : forall O E E' A B AB, Length O E E' A B AB -> ~Ng O E AB.
Proof.
intros.
intro.
assert(HH:= length_cong O E E' A B AB H).
apply length_pos_or_null in H.
induction H.
{
  apply pos_not_neg in H.
  contradiction.
}
{
  unfold Ng in H0.
  spliter.
  subst B.
  treat_equalities.
  tauto.
}
Qed.

Lemma signEq_refl : forall O E A, O <> E -> Col O E A -> A = O \/ SignEq O E A A.
Proof.
intros.
assert(HH:= sign_dec O E A H0 H).
unfold SignEq.
induction HH.
{
  left; auto.
}
{
  induction H1.
  {
    right; left; auto.
  }
  {
    right; right; auto.
  }
}
Qed.

Lemma square_not_neg : forall O E E' A A2, Prod O E E' A A A2 -> ~Ng O E A2.
Proof.
intros.
intro.
assert(O <> E /\ Col O E A).
{
  unfold Prod in H.
  unfold Ar2 in H.
  spliter.
  split; Col.
  intro; subst E; Col.
}
spliter.
assert(HP:=signEq_refl O E A H1 H2).
spliter.
induction HP.
{
  subst A.
  assert(HH:=prod_O_l_eq O E E' O A2 H).
  unfold Ng in H0.
  spliter.
  contradiction.
}
{
  assert(HH:= signeq__prod_pos O E E' A A A2 H3 H).
  apply pos_not_neg in HH.
  contradiction.
}
Qed.


Lemma root_uniqueness : forall O E E' A B C, ~Ng O E A -> ~Ng O E B -> Prod O E E' A A C -> Prod O E E' B B C -> A = B.
Proof.
intros O E E' A B C PA PB.
intros.
assert(~ Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C).
{
  unfold Prod in *.
  unfold Ar2 in *.
  tauto.
}
spliter.
assert(HS:= sum_exists O E E' H1 A B H2 H3).
ex_and HS ApB.
assert(HD:= diff_exists O E E' A B H1 H2 H3).
ex_and HD AmB.
assert(Col O E ApB /\ Col O E AmB).
{
  unfold Sum in H5.
  unfold Diff in H6.
  ex_and H6 X.
  unfold Sum in H7.
  unfold Ar2 in *.
  tauto.
}
spliter.
assert(HP:= prod_exists O E E' H1 ApB AmB H7 H8).
ex_and HP PP.
assert(Diff O E E' C C O).
{
  apply diff_null; auto.
}
assert(HH:= diff_of_squares O E E' A B C C O ApB AmB PP H H0 H10 H5 H6 H9).
treat_equalities.
assert(HH:= prod_null O E E' ApB AmB H9).
induction (eq_dec_points A O).
{
  subst A.
  apply prod_O_l_eq in H.
  subst C.
  apply prod_null in H0.
  induction H0; subst B; auto.
}
{
  assert(E <> O).
  {
    intro.
    subst E; Col.
  }
  induction (eq_dec_points B O).
  {
    subst B.
    apply prod_O_l_eq in H0.
    subst C.
    apply prod_null in H.
    induction H; subst A; auto.
  }
  {
    induction HH.
    {
      assert(Ps O E A \/ A = O).
      {
        apply(not_neg_pos O E A); auto.
      }
      assert(Ps O E B \/ B = O).
      {
        apply(not_neg_pos O E B); auto.
      }
      induction H15; induction H16; try(contradiction).
      {
        assert(HP:=sum_pos_pos O E E' A B ApB H15 H16 H5).
        unfold Ps in HP.
        unfold Out in HP.
        subst ApB.
        tauto.
      }
    }
    {
      subst AmB.
      apply diff_null_eq in H6.
      auto.
    }
  }
}
Qed.

Lemma inter_tangent_circle : forall P Q O M, P <> Q -> Cong P O Q O -> Col P O Q
                      -> Le P M P O -> Le Q M Q O
                      -> M = O.
Proof.
intros.
assert(P = Q \/ Midpoint O P Q).
apply(l7_20 O P Q H1);Cong.
induction H4.
contradiction.
unfold Midpoint in *.
spliter.
assert(Le Q M P O).
{
  apply (l5_6 Q M Q O Q M  P O H3); Cong.
}
assert(Le P M O P).
{
  apply(l5_6 P M P O P M O P); Cong.
}
assert(Le Q M O Q).
{
  apply(l5_6 Q M Q O Q M O Q); Cong.
}
unfold Le in H7.
unfold Le in H8.
ex_and H7 A.
ex_and H8 B.
assert(Bet A O B); eBetween.
assert(Le P Q A B).
{
  apply(triangle_inequality_2 P M Q A O B); Cong.
}

assert(Le A B P Q).
{
  apply(bet2_le2__le O O P Q A B); Between.
  unfold Le.
  exists A; Cong.
  exists B; Cong.
}
assert(Cong A B P Q).
{
  apply le_anti_symmetry; auto.
}

assert(B = Q /\ P = A).
apply(bet_cong_eq P A B Q);eBetween.
spliter.
subst A.
subst B.
clean_trivial_hyps.
assert(Cong Q M O P); eCong.
assert(Cong Q M P M); eCong.
assert(O = M).
{
  apply(l4_18 P Q O M); Col;
  induction(eq_dec_points M O); Cong.
}
auto.
Qed.

Lemma inter_circle_per : forall P Q A T M, Cong P A Q A 
                          -> Le P M P A -> Le Q M Q A 
                          ->  Projp A T P Q -> Per P T M -> Le T M T A.

Proof.
intros.
assert(HH:=lower_dim).
set(O:=PA) in *.
set(E:=PB) in *.
set(E':=PC) in *.
assert(HD:~Col O E E').
intro.
apply HH.
unfold Col in H4.
tauto.
clear HH.

induction(eq_dec_points P T).
{
  subst T.
  auto.
}

{
  unfold Projp in H2.
  spliter.
  induction H5.
  spliter.

  assert(HX:O<>E).
  {
    ColR.
  }
  assert(Per P T A).
  {
    apply (perp_col _ _ _ _ T) in H6; auto.
    apply perp_left_comm in H6.
    apply perp_perp_in in H6.
    apply perp_in_comm in H6.
    apply perp_in_per in H6.
    assumption.
  }

  assert(Py:= pyth_context O E E' P T A HD).
  ex_and Py PT .
  ex_and H8 TA .
  ex_and H9 AP.
  ex_and H8 PT2.
  ex_and H9 TA2.
  ex_and H8 AP2.
  ex_and H9 SS.

  assert(Pyth : Sum O E E' PT2 TA2 AP2).
  {
    apply(pythagoras O E E' P A T PT TA AP PT2 TA2 AP2 HX); auto.
    apply length_sym;auto.
  }
  assert(HE: SS = AP2).
  {
    apply(sum_uniqueness O E E' PT2 TA2); auto.
  }
  subst SS.
  apply sum_comm in Pyth; auto.
  apply sum_diff in Pyth.

  assert(Py:= pyth_context O E E' P T M HD).
  ex_and Py PT' .
  ex_and H21 TM .
  ex_and H22 PM.
  ex_and H21 PT2'.
  ex_and H22 TM2.
  ex_and H21 PM2.
  ex_and H22 SS'.
  assert(PT=PT').
  {
    apply (length_uniqueness O E E' P T); auto.
  }
  subst PT'.
  assert(PT2=PT2').
  {
    apply (prod_uniqueness O E E' PT PT); auto.
  }
  subst PT2'.
  clean_duplicated_hyps.
  assert(PythM : Sum O E E' PT2 TM2 PM2).
  {
    apply(pythagoras O E E' P M T PT TM PM PT2 TM2 PM2 HX); auto.
    apply length_sym;auto.
  }
  assert(SS'=PM2).
  {
    apply (sum_uniqueness O E E' PT2 TM2); auto.
  }
  subst SS'.
  induction(eq_dec_points T M).
  {
    subst T.
    apply le_trivial.
  }
  
  {
    induction(eq_dec_points P M).
    {
      subst M.

      assert(HH:= length_id_2 O E E' P HX).
      assert(PM = O).
      {
        apply (length_uniqueness O E E' P P); auto.
      }
      subst PM.
      assert(PM2=O).
      {
         apply(prod_O_l_eq O E E' O);auto.
      }
      subst PM2.
      apply(sum_pos_null) in H33.
      spliter.
      subst PT2.
      apply prod_null in H17.
      induction H17.
      {
        subst PT.
        apply length_cong in H14.
        treat_equalities.
        tauto.
      }
      {
        subst PT.
        apply length_cong in H14.
        treat_equalities.
        tauto.
      }
       apply (square_not_neg O E E' PT); auto.
       apply (square_not_neg O E E' TM); auto.
    }
    {
      assert(LeP O E E' PM AP).
      {
        apply(length_leP_le_2 O E E' P M P A PM AP); auto.
      }
      assert(LeP O E E' PM2 AP2).
      {
        apply(square_increase O E E' PM AP); auto.
        unfold Ar2.
        repeat split; auto.
        apply (length_Ps O E E' P M); auto.
        intro.
        treat_equalities.
        set(O:=PA) in *.
        subst PM.
        assert(PM2=O).
        {
          apply(prod_O_l_eq O E E' O);auto.
        }
        subst PM2.
        apply length_id_1 in H29.
        contradiction.
        apply length_pos_or_null in H16.
        induction H16.
        {
          assumption.
        }
        {
          treat_equalities.
          assert(HH:= length_id_2 O E E' Q  HX).
          assert(HP:=length_uniqueness O E E' Q Q O PM HH H29).
          treat_equalities.
          apply(prod_O_l_eq)in H32.
          subst PM2.
          apply sum_pos_null in H33.
          spliter; tauto.
          apply(square_not_neg O E E' PT PT2 H17).
          apply(square_not_neg O E E' TM TM2 H31).
        }
      }
      apply sum_comm in H33; auto.
      apply sum_comm in H20; auto.
      assert(HH:=sum_preserves_lep_rev O E E' TM2 TA2 PT2 PM2 AP2 H33 H20 H30).
      induction(eq_dec_points TA TM).
      {
        treat_equalities.
        assert(Cong T M T A).
        {
          apply(length_eq_cong_1 O E E' _ _ _ _ TA); auto.
        }
        apply cong__le; auto.
      }
      assert(LtP O E E' TM2 TA2).
      {
        apply(lep_neq__ltp O E E').
        split; auto.
        intro.
        apply H34.
        subst TM2.
        apply(root_uniqueness O E E' TA TM TA2); auto.
        apply(length_not_neg O E E' T A); auto.
        apply(length_not_neg O E E' T M); auto.
      }

      assert(LtP O E E' TM TA).
      {
        apply (square_increase_rev O E E' TM TA TM2 TA2); auto.
        apply length_Ps in H28; auto.
        intro.
        subst TM.
        apply length_id_1 in H28.
        tauto.
        apply length_Ps in H15; auto.
        intro.
        subst TA.
        apply length_id_1 in H15.
        subst T.
        apply perp_distinct in H6.
        tauto.
      }
      apply lt__le.
      apply (ltp_to_lt O E E' T M TM T A TA); auto.
    }
  }
  {
    spliter.
    assert(HH:=(inter_tangent_circle P Q A M H2 H)).
    assert(M = A).
    {
      apply HH; Col.
    }
    subst M.
    apply le_reflexivity.
  }
}
Qed.

Lemma inter_circle_obtuse : forall P Q A T M, Cong P A Q A 
                          -> Le P M P A -> Le Q M Q A 
                          ->  Projp A T P Q -> Obtuse P T M \/ Per P T M -> Le T M T A.

Proof.
intros.
assert(HH:=lower_dim).
set(O:=PA) in *.
set(E:=PB) in *.
set(E':=PC) in *.
assert(HD:~Col O E E').
intro.
apply HH.
unfold Col in H4.
tauto.
clear HH.

induction(eq_dec_points P T).
{
  subst T.
  auto.
}
{
  unfold Projp in H2.
  spliter.
  induction H5.
  spliter.

  assert(HX:O<>E).
  {
    ColR.
  }
  assert(Per P T A).
  {
    apply (perp_col _ _ _ _ T) in H6; auto.
    apply perp_left_comm in H6.
    apply perp_perp_in in H6.
    apply perp_in_comm in H6.
    apply perp_in_per in H6.
    assumption.
  }

  assert(Py:= pyth_context O E E' P T A HD).
  ex_and Py PT .
  ex_and H8 TA .
  ex_and H9 AP.
  ex_and H8 PT2.
  ex_and H9 TA2.
  ex_and H8 AP2.
  ex_and H9 SS.

  assert(Py:= pyth_context O E E' P T M HD).
  ex_and Py PT' .
  ex_and H21 TM .
  ex_and H22 PM.
  ex_and H21 PT2'.
  ex_and H22 TM2.
  ex_and H21 PM2.
  ex_and H22 SS'.
  assert(PT=PT').
  {
    apply (length_uniqueness O E E' P T); auto.
  }
  subst PT'.
  assert(PT2=PT2').
  {
    apply (prod_uniqueness O E E' PT PT); auto.
  }
  subst PT2'.
  clean_duplicated_hyps.

  assert(Pyth : Sum O E E' PT2 TA2 AP2).
  {
    apply(pythagoras O E E' P A T PT TA AP PT2 TA2 AP2 HX); auto.
    apply length_sym;auto.
  }
  assert(HE: SS = AP2).
  {
    apply(sum_uniqueness O E E' PT2 TA2); auto.
  }
  subst SS.
  assert(Pyth1 : LeP O E E' SS' PM2).
  {
    apply(pythagoras_obtuse_or_per O E E' P M T PT TM PM PT2 TM2 PM2 SS'); auto.
    apply length_sym; auto.
  }
  induction(eq_dec_points T M).
  {
    subst M.
    apply le_trivial.
  }
  {
    induction(eq_dec_points P M).
    {
      subst M.
      assert(HH:= length_id_2 O E E' P HX).
      assert(PM = O).
      {
        apply (length_uniqueness O E E' P P); auto.
      }
      subst PM.
      assert(PM2=O).
      {
         apply(prod_O_l_eq O E E' O);auto.
      }
      subst PM2.

      assert(Ps O E SS').
      {
        apply(sum_pos_pos O E E' PT2 TM2 SS'); auto.
        apply (square_pos O E E' PT); auto.
        intro.
        subst PT.
        apply length_cong in H14.
        apply cong_identity in H14.
        contradiction.

        apply (square_pos O E E' TM); auto.
        intro.
        subst TM.
        apply length_cong in H28.
        apply cong_identity in H28.
        contradiction.
      }
      unfold LeP in Pyth1.
      induction Pyth1.
      apply (ltP_neg) in H27.
      apply pos_not_neg in H24.
      contradiction.
      subst SS'.
      unfold Ps in H24.
      unfold Out in H24;tauto.
    }
    assert(LeP O E E' PM AP).
    {
      apply(length_leP_le_2 O E E' P M P A PM AP); auto.
    }
    assert(LeP O E E' PM2 AP2).
    {
      apply(square_increase O E E' PM AP); auto.
      repeat split; auto.
      apply length_pos_or_null in H29.
      induction H29.
      {
        auto.
      }
      {
        treat_equalities; tauto.
      }

      apply length_pos_or_null in H16.
      induction H16.
      {
        auto.
      }
      {
        treat_equalities; tauto.
      }
    }
    assert(LeP O E E' SS' AP2).
    {
      apply (leP_trans O E E' SS' PM2 AP2); auto.
    }
    assert(LeP O E E' TM2 TA2).
    {
      apply(sum_preserves_lep_rev O E E' TM2 TA2 PT2 SS' AP2); auto.
      apply sum_comm; auto.
      apply sum_comm; auto.
    }
    
    assert(Ps O E  TM).
    {
      apply length_pos_or_null in H28.
      induction H28.
      {
        auto.
      }
      {
        treat_equalities; tauto.
      }
    }
    assert(Ps O E  TA).
    {
      apply length_pos_or_null in H15.
      induction H15.
      {
        auto.
      }
      {
        subst T.
        apply perp_distinct in H6; tauto.
      }
    }


    assert(LeP  O E E' TM TA).
    {
      induction(eq_dec_points TM TA).
      {
        subst TM.
        apply leP_refl.
      }
      {
        apply ltp_to_lep.
        apply (square_increase_rev O E E' TM TA TM2 TA2); auto.
        apply(lep_neq__ltp O E E').
        split; auto.
        intro.
        apply H38.
        subst TM2.
        apply (root_uniqueness O E E' TM TA TA2); auto.
        intro.
        apply pos_not_neg in H36.
        contradiction.
        intro.
        apply pos_not_neg in H37.
        contradiction.
      }
    }
    apply(length_leP_le_1 O E E' T M  T A TM TA); auto.
  }
  {
    spliter.
    assert(HH:=(inter_tangent_circle P Q A M H2 H)).
    assert(M = A).
    {
      apply HH; Col.
    }
    subst M.
    apply le_reflexivity.
  }
}
Qed.

Lemma circle_projp_between : forall P Q A T, Cong P A Q A 
                          ->  Projp A T P Q -> Bet P T Q.
Proof.
intros.

induction(eq_dec_points P T).
{
  subst T; Between.
}
{
  unfold Projp in H0.
  spliter.
  induction H2.
  {
    spliter.
    assert(Per A T P).
    {
      apply (perp_col _ _ _ _ T) in H3; auto.
      apply perp_left_comm in H3.
      apply perp_perp_in in H3.
      apply perp_in_comm in H3.
      apply perp_in_per in H3.
      apply l8_2.
      assumption.
    }
    assert(HM:=midpoint_existence P Q).
    ex_and HM T'.
    assert(Per A T' P).
    {
      unfold Per.
      exists Q.
      split; Cong.
    }
    assert(T' = T \/ ~ Col T P Q).
    {
      apply(col_per2_cases A T' P Q T); Col.
      intro.
      treat_equalities.
      apply perp_distinct in H3; tauto.
    }
    induction H7.
    subst T'.
    Between.
    assert(Col T A T').
    {
      apply(col_perp2_ncol__col A T A T' P Q); Col.
      Perp.
      apply per_perp_in in H6.
      apply perp_in_comm in H6.
      apply perp_in_perp in H6.
      apply perp_sym in H6.
      apply perp_sym.
      apply (perp_col _ T'); Perp; Col.
      intro.
      treat_equalities.
      unfold Midpoint in H5; spliter.
      apply H7; ColR.
      intro.
      subst T'.
      apply is_midpoint_id in H5.
      contradiction.
      intro.
      apply H7.
      ColR.
    }
    assert(T=T').
    {
      apply(per2_col_eq A T T' P); Perp.
      intro.
      treat_equalities.
      apply perp_distinct in H3; tauto.
      intro.
      treat_equalities.
      unfold Midpoint in H5; spliter.
      apply H7; ColR.
    }
    subst T'.
    Between.
  }
  spliter.
  subst T.
  assert(P = Q \/ Midpoint A P Q).
  {
    apply(l7_20 A P Q); Col.
    Cong.
  }
  induction H3.
  {
    contradiction.
  }
  Between.
}
Qed.


Lemma inter_circle : forall P Q A T M, Cong P A Q A 
                          -> Le P M P A -> Le Q M Q A 
                          ->  Projp A T P Q -> Le T M T A.
Proof.
intros.
assert(HH:= circle_projp_between P Q A T H H2).
induction(eq_dec_points T M).
  {
    subst M.
    apply le_trivial.
  }
  {
    induction(eq_dec_points P T).
    {
      treat_equalities; auto.
    }
    assert(HA:= angle_partition P T M H4 H3).
    induction(eq_dec_points Q T).
    {
      treat_equalities; auto.
    }
    {
      induction HA.
      {
        assert(HB:= acute_bet__obtuse P T M Q HH H5 H6).
        apply(inter_circle_obtuse Q P); Cong.
        unfold Projp in *.
        spliter.
        split; auto.
        induction H7.
        {
          left.
          spliter.
          split; Col; Perp.
        }
        {
          right.
          spliter.
          split; Col.
        }
      }
      {
        apply(inter_circle_obtuse P Q); Cong.
        induction H6.
        {
          right; auto.
        }
        {
          left; auto.
        }
      }
    }
  }
Qed.


Lemma projp_lt : forall P Q A T, Cong P A Q A 
                          ->  Projp A T P Q -> Lt T A P A.
Proof.
intros.

unfold Projp in H0.
spliter.
induction H1.
{
  spliter.

  induction(eq_dec_points P T).
  {
    subst T.
    assert(Lt Q P Q A /\ Lt A P Q A).
    {
      apply(per_lt Q P A).
      auto.
      apply perp_distinct in H2.
      tauto.
      Perp.
    }
    spliter.
    unfold Lt in H4.
    spliter.
    apply False_ind.
    apply H5.
    Cong.
  }
  {
    assert(Lt P T P A /\ Lt A T P A).
    {
      apply(per_lt P T A); auto.
      apply perp_distinct in H2.
      tauto.
      apply (perp_col  _ _ _ _ T)  in H2;
      Perp.
    }
    spliter.
    apply lt_left_comm.
    auto.
  }
}
{
  spliter.
  subst T.
  induction(eq_dec_points P A).
  subst P.
  apply cong_symmetry in H.
  apply cong_identity in H.
  subst Q.
  tauto.
  apply lt1123; auto.
}
Qed.



End T15.
