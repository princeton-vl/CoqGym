(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008-2009                                      *)
(***************************************************************************)

Require Export euclidean_constructions.
Require Export area_elimination_lemmas.
Require Export ratios_elimination_lemmas.

(* lemme 3_2 chou *)
Lemma l_24_a : forall A B P D,
Col A D B -> perp A B P D ->
A<>B -> B<>D ->
 A**D / D**B = Py P A B / Py P B A.
Proof.
intros.
unfold Py.
unfold perp, Py4, Py in *.
uniformize_dir_seg.
basic_simpl.
IsoleVar (A ** P * A ** P) H0.
rewrite H0.
basic_simpl.
assert (A**D+D**B = A**B).
eapply chasles;auto.
assert (A**B * A**B = A**D * A**D + B**D* B**D + 2 * A**D*D**B).
rewrite <- H3.
uniformize_dir_seg.
basic_simpl.
ring.
uniformize_dir_seg.
rewrite H4.
cut (B ** P * B ** P + P ** D * P ** D - B ** D * B ** D + A ** D * A ** D -
 P ** D * P ** D +
 (A ** D * A ** D + B ** D * B ** D + 2 * A ** D * - B ** D) -
 B ** P * B ** P = 2* A**D * A**B).
intro Ha.
rewrite Ha.
cut ((B ** P * B ** P +
 (A ** D * A ** D + B ** D * B ** D + 2 * A ** D * - B ** D) -
 (B ** P * B ** P + P ** D * P ** D - B ** D * B ** D + A ** D * A ** D -
  P ** D * P ** D) = 2 * D**B * A**B)).
intro Hb.
rewrite Hb.
uniformize_dir_seg.
field;repeat split;auto with Geom.
rewrite <- H3.
uniformize_dir_seg.
ring.
rewrite <- H3.
uniformize_dir_seg.
ring.
Qed.

Lemma perp4_perp : forall A B P, 
perp A B P A -> Py P A B = 0.
Proof.
intros.
unfold perp in H.
rewrite py4_simpl_6 in H.
assumption.
Qed.

Lemma perp_not_eq_not_perp : forall A B P D, perp A B P D ->
Col A D B ->
 A <> B ->  B <> D -> A <> D -> 
Py P A B <> 0.
Proof.
intros.
unfold not;intro.
assert (perp A B P A).
unfold perp, Py4.
unfold Py in *.
uniformize_dir_seg.
basic_simpl.
IsoleVar (A ** B * A ** B) H4.
rewrite H4.
ring.
unfold perp, Py4, Py in *.
uniformize_dir_seg.
basic_simpl.
IsoleVar (B ** P * B ** P) H4.
rewrite H4 in H.
ring_simplify in H.
replace (A ** B) with (A**D + D**B) in H.
uniformize_dir_seg.
ring_simplify in H.
replace (- (2) * A ** D * A ** D + 2 * A ** D * B ** D ) with 
(2* A**D * (B**D - A**D)) in H by ring.
assert ((2* A**D * B**A) <> 0).
repeat (apply nonzeromult);auto with Geom.
replace (B ** D - A ** D) with (B**D + D**A) in H.
replace (B ** D + D ** A) with (B**A) in H.
intuition.
symmetry;
auto with Geom.
uniformize_dir_seg;ring.
auto with Geom.
Qed.

(* lemma 3_2 chou *)
Lemma l_24_b : forall A B P D,
Col A D B -> perp A B P D ->
A<>B -> 
 A**D / A**B = Py P A B / (2 * A**B * A**B).
Proof.
intros.
cases_equality B D.
subst D.
unfold Py.
field_simplify_eq; auto with Geom.
unfold perp, Py4, Py in H0.
basic_simpl.
uniformize_dir_seg.
IsoleVar (A ** B * A ** B) H0.
replace (2 * A ** B * A ** B) with (2* (A ** B * A ** B)) by ring.
rewrite H0.
ring.

cases_equality A D.
subst D.
basic_simpl.
rewrite perp4_perp by auto.
field.
split;auto with Geom.
assert (Py P A B <> 0).

eapply perp_not_eq_not_perp;eauto.
assert (Py P B A <> 0).
apply (perp_not_eq_not_perp B A P D);auto with Geom.

replace (A**D / A**B) with (1/ (A**B / A**D)) by (field;auto with Geom).
replace (2 * A ** B * A ** B) with (Py A B A) by (unfold Py;uniformize_dir_seg;basic_simpl;ring).
replace (A**B) with (A**D + D**B) by auto with Geom.
replace ((A ** D + D ** B) / A ** D) with (1 + D ** B / A ** D) by (field;auto with Geom).
replace (D ** B / A ** D) with (1/ (A**D / D**B)) by (field; auto with Geom).
rewrite (l_24_a A B P D) by auto.
replace (1 / (1 + 1 / (Py P A B / Py P B A))) with ((Py P A B / (Py P A B + Py P B A))).
replace (Py P A B + Py P B A) with (Py A B A).
auto.
unfold Py;basic_simpl;uniformize_dir_seg;ring.
field.
repeat split;auto.
replace (Py P A B + Py P B A) with (Py A B A).
unfold Py.
uniformize_dir_seg.
basic_simpl.
replace (A ** B * A ** B + A ** B * A ** B) with (2*  A ** B * A ** B) by ring.
repeat (apply nonzeromult);auto with Geom.
unfold Py;basic_simpl;uniformize_dir_seg;ring.
Qed.

(* lemma 3_2 chou *)
Lemma l_24_c : forall A B P D,
Col A D B -> perp A B P D ->
A<>B -> 
 D**B / A**B = Py P B A / (2 * A**B * A**B).
Proof.
intros.
assert (B ** D / B ** A = Py P B A / (2 * B ** A * B ** A)).
apply l_24_b ;auto with Geom.
replace (D ** B / A ** B) with (B ** D / B ** A) by auto with Geom.
rewrite H2.
replace (2*B ** A * B ** A) with (2*A ** B * A ** B) .
auto.
uniformize_dir_seg;ring.
Qed.

Lemma l_24_c_on_foot : forall P U V Y,
on_foot Y P U V ->
U**Y / U**V = Py P U V / Py U V U.
Proof.
intros.
unfold on_foot in H.
use H.
replace (U ** Y / U ** V) with (Y**U/ V**U) by auto with Geom.
rewrite (l_24_c V U P) by auto with Geom.
replace (2 * V ** U * V ** U) with (Py U V U).
auto.
unfold Py;basic_simpl;uniformize_dir_seg;ring.
Qed.

Lemma per_area: forall A B C,
  per A B C -> 
  2 * 2 * S A B C * S A B C = A**B * A**B * B**C * B**C.
Proof.
intros.
cases_equality B C.
subst.
basic_simpl.
auto.
assert (on_foot B A B C).
unfold on_foot.
repeat split.
cut (perp B C B A).
auto with Geom.
unfold perp, Py4.
basic_simpl.
replace (Py C B A) with (Py A B C) by auto with Geom.
rewrite H.
ring.
auto with Geom.
auto.
apply on_foot_area.
auto.
Qed.

Lemma per_col_eq : forall A B C,
 per A B C -> Col A B C -> A = B \/ B = C.
Proof.
intros.
unfold per in H.
rewrite col_pyth in H by assumption.
cases_equality A B.
left;auto.
right.
IsoleVar (B**C) H.
2:solve_conds;auto with Geom.
replace (0 / (2 * B ** A)) with 0 in H 
  by (field;solve_conds;auto with Geom).
auto with Geom.
Qed.

Lemma perp_col_perp : forall P Q B C,
 Q<>B ->
 per P Q B -> Col Q B C -> per P Q C.
Proof.
intros.
cut (perp P Q Q C).
auto with Geom.
assert (perp P Q Q B) by auto with Geom.
cut (perp Q C P Q).
auto with Geom.
apply (perp_para_perp  Q B P Q Q C);auto with Geom.
Qed.

Lemma l_3_4 : forall A B C P,
 Col A B C -> Py P A C <> 0 ->
 Py P A B / Py P A C = A**B/ A**C.
Proof.
intros.
cases_equality A B.
subst.
basic_simpl.
field.
cases_equality B C.
subst.
basic_simpl;auto.
auto with Geom.
assert (A<>C).
intro.
subst.
basic_simpl;intuition.

elim (proj_ex P A B H1).
intros Q HQ.
unfold on_foot in *.
use HQ.

cases_equality A Q.
subst.
clear H5.
unfold perp, Py4 in H3.
basic_simpl.
IsoleVar (Py P Q B) H3.
basic_simpl.


assert (T:=perp_col_perp P Q B C H6 H3 H).
intuition.

assert (perp A C Q P).
apply (perp_para_perp A B Q P A C);auto with Geom.
unfold parallel.
basic_simpl.
auto with Geom.
assert (perp Q P A C)by auto with Geom.
unfold perp, Py4 in *.
IsoleVar (Py P A B) H3.
IsoleVar (Py P A C) H8.
basic_simpl.
rewrite H3.
rewrite H8.
rewrite (col_pyth Q A B) by assumption.
rewrite (col_pyth Q A C).
field.
repeat split;auto with Geom.
assert (Col A Q C).
apply  (col_trans_1 A B Q C H1); auto with Geom.
auto with Geom.
Qed.

Require Export Classical.

Lemma per_dec : forall A B C,
 per A B C \/ ~ per A B C.
Proof.
intros.
elim (classic (Py A B C = 0));
intuition.
Qed.

Ltac cases_per A B C := elim (per_dec A B C);intros.

Lemma l_3_4_b : forall A B C P,
 Col A B C ->
 Py P A B * A**C =  Py P A C * A**B.
Proof.
intros.
cases_per P A C.
unfold per in H0.

rewrite H0.
cases_equality A C.
subst;basic_simpl;auto.
assert (Py P A B = 0).
apply (perp_col_perp P A C B H1);auto with Geom.
rewrite H2.
basic_simpl;auto.

assert (T:=l_3_4 A B C P H H0).
IsoleVar (Py P A B) T.
rewrite T.
field.
intro.
assert (A=C).
auto with Geom.
subst.
basic_simpl.
auto.
auto.
Qed.

Lemma l_28_b : forall A B U V Y,
U <> V ->
Col Y U V -> 
Py A B Y = U**Y/U**V * Py A B V + Y**V/U**V * Py A B U.
Proof.
intros.
set (r1 := U ** Y / U ** V).
set (r2 := Y ** V / U ** V).
assert (r2 = 1 -r1).
   unfold r1, r2.
   rewrite <- (chasles Y U V).
   uniformize_dir_seg.
   field;auto with Geom.
   assumption.

cut (B**Y * B**Y = r2 * U**B * U**B + r1 * V**B * V**B - r1 * r2 * U**V * U**V).
intro Ha.
cut (A**Y * A**Y = r2 * U**A * U**A + r1 * V**A * V**A - r1 * r2 * U**V * U**V).
intro Hb.
unfold Py.
rewrite Ha.
rewrite Hb.
uniformize_dir_seg.
basic_simpl.
assert ( (A ** B * A ** B) = (r1 + r2) * (A ** B * A ** B)) by (rewrite H1;ring).
rewrite H2 at 1.
field.

(* first cut *)
rewrite H1.
replace ((1 - r1) * U ** A * U ** A + r1 * V ** A * V ** A -
r1 * (1 - r1) * U ** V * U ** V)
with (U ** A * U ** A + r1 * (V ** A * V ** A - U ** A * U ** A - U ** V * U ** V) 
      + r1 *r1 *  U ** V * U ** V) by ring.
replace (U ** A * U ** A + r1 * (V ** A * V ** A - U ** A * U ** A - U ** V * U ** V) +
r1 * r1 * U ** V * U ** V) with
(U ** A * U ** A + r1 * r1 * U**V * U**V - r1 * Py A U V)
by (unfold Py; uniformize_dir_seg; ring).

cut (r1 * Py A U V = Py A U Y).
intro Hab.
rewrite Hab.
unfold Py.
uniformize_dir_seg.
basic_simpl.
cut (r1 * U**V = U**Y).
intro Hb.
assert (r1 * r1 * U ** V * U ** V = U**Y * U**Y)
by (rewrite <- Hb;ring).

rewrite H2.
ring.

unfold r1;field; auto with Geom.

assert (Py A U V * U ** Y = Py A U Y * U ** V).
apply (l_3_4_b U V Y A).
auto with Geom.

rename H2 into T.
IsoleVar (Py A U Y) T.
rewrite T.
unfold r1;field; auto with Geom.
auto with Geom.

(* second cut *)
rewrite H1.
replace ((1 - r1) * U ** B * U ** B + r1 * V ** B * V ** B -
r1 * (1 - r1) * U ** V * U ** V)
with (U ** B * U ** B + r1 * (V ** B * V ** B - U ** B * U ** B - U ** V * U ** V) 
      + r1 *r1 *  U ** V * U ** V) by ring.
replace (U ** B * U ** B + r1 * (V ** B * V ** B - U ** B * U ** B - U ** V * U ** V) +
r1 * r1 * U ** V * U ** V) with
(U ** B * U ** B + r1 * r1 * U**V * U**V - r1 * Py B U V)
by (unfold Py; uniformize_dir_seg; ring).

cut (r1 * Py B U V = Py B U Y).
intro Hab.
rewrite Hab.
unfold Py.
uniformize_dir_seg.
basic_simpl.
cut (r1 * U**V = U**Y).
intro Hb.
assert (r1 * r1 * U ** V * U ** V = U**Y * U**Y)
by (rewrite <- Hb;ring).

rewrite H2.
ring.

unfold r1;field; auto with Geom.
assert (Py B U V * U ** Y = Py B U Y * U ** V).
apply (l_3_4_b U V Y B).
auto with Geom.
rename H2 into T.
IsoleVar (Py B U Y) T.
rewrite T.
unfold r1;field; auto with Geom.
auto with Geom.
Qed.

Lemma l3_5_py : forall A B U V Y,
  U <> V ->
  Col Y U V ->  
  Py A Y B = U**Y / U**V * Py A V B + Y**V/ U**V * Py A U B 
  - (U**Y/ U**V) * (Y**V / U**V) * Py U V U.
Proof.
intros.
set (r1 := U ** Y / U ** V).
set (r2 := Y ** V / U ** V).
assert (r2 = 1 -r1).
   unfold r1, r2.
   rewrite <- (chasles Y U V).
   uniformize_dir_seg.
   field;auto with Geom.
   assumption.

cut (B**Y * B**Y = r2 * U**B * U**B + r1 * V**B * V**B - r1 * r2 * U**V * U**V).
intro Hb.
cut (A**Y * A**Y = r2 * U**A * U**A + r1 * V**A * V**A - r1 * r2 * U**V * U**V).
intro Ha.
unfold Py.
rewrite Ha.
replace (Y ** B * Y ** B) with (B ** Y * B ** Y)
  by (uniformize_dir_seg;field).
rewrite Hb.
uniformize_dir_seg.
basic_simpl.
rewrite H1.
ring.

rewrite H1.
replace ((1 - r1) * U ** A * U ** A + r1 * V ** A * V ** A -
r1 * (1 - r1) * U ** V * U ** V)
with (U ** A * U ** A + r1 * (V ** A * V ** A - U ** A * U ** A - U ** V * U ** V) 
      + r1 *r1 *  U ** V * U ** V) by ring.
replace (U ** A * U ** A + r1 * (V ** A * V ** A - U ** A * U ** A - U ** V * U ** V) +
r1 * r1 * U ** V * U ** V) with
(U ** A * U ** A + r1 * r1 * U**V * U**V - r1 * Py A U V)
by (unfold Py; uniformize_dir_seg; ring).

(* first cut *)
cut (r1 * Py A U V = Py A U Y).
intro Hab.
rewrite Hab.
unfold Py.
uniformize_dir_seg.
basic_simpl.
cut (r1 * U**V = U**Y).
intro Hbb.
assert (r1 * r1 * U ** V * U ** V = U**Y * U**Y)
by (rewrite <- Hbb;ring).

rewrite H2.
ring.

unfold r1;field; auto with Geom.

assert (Py A U V * U ** Y = Py A U Y * U ** V).
apply (l_3_4_b U V Y A).
auto with Geom.

rename H2 into T.
IsoleVar (Py A U Y) T.
rewrite T.
unfold r1;field; auto with Geom.
auto with Geom.

(* second cut *)
rewrite H1.
replace ((1 - r1) * U ** B * U ** B + r1 * V ** B * V ** B -
r1 * (1 - r1) * U ** V * U ** V)
with (U ** B * U ** B + r1 * (V ** B * V ** B - U ** B * U ** B - U ** V * U ** V) 
      + r1 *r1 *  U ** V * U ** V) by ring.
replace (U ** B * U ** B + r1 * (V ** B * V ** B - U ** B * U ** B - U ** V * U ** V) +
r1 * r1 * U ** V * U ** V) with
(U ** B * U ** B + r1 * r1 * U**V * U**V - r1 * Py B U V)
by (unfold Py; uniformize_dir_seg; ring).

cut (r1 * Py B U V = Py B U Y).
intro Hab.
rewrite Hab.
unfold Py.
uniformize_dir_seg.
basic_simpl.
cut (r1 * U**V = U**Y).
intro Hb.
assert (r1 * r1 * U ** V * U ** V = U**Y * U**Y)
by (rewrite <- Hb;ring).

rewrite H2.
ring.

unfold r1;field; auto with Geom.
assert (Py B U V * U ** Y = Py B U Y * U ** V).
apply (l_3_4_b U V Y B).
auto with Geom.
rename H2 into T.
IsoleVar (Py B U Y) T.
rewrite T.
unfold r1;field; auto with Geom.
auto with Geom.
Qed.

Lemma midpoint_ratio_1 : forall O B D,
mid_point O B D ->  B<>D -> B ** O / B ** D = 1/2.
Proof.
intros.
unfold mid_point in *.
use H.
assert (B**D = B**O + O**D).
symmetry;auto with Geom.
rewrite H.
rewrite H2.
field.
split;auto with Geom.
replace (O ** D + O ** D) with (2*O**D) by ring.
apply nonzeromult.
auto with Geom.
intro.
assert (O=D);auto with Geom.
subst O.
basic_simpl.
assert (B=D); auto with Geom.
Qed.

Lemma midpoint_ratio_2 : forall O B D,
mid_point O B D ->  B<>D -> O ** D / B ** D = 1/2.
Proof.
intros.
unfold mid_point in *.
use H.
rewrite <- H2.
apply midpoint_ratio_1.
unfold mid_point;auto.
auto.
Qed.

Lemma l_28_midpoint : forall O A B P Q,
 mid_point O A B ->
 2 * Py O P Q = Py A P Q + Py B P Q.
Proof.
intros.
cases_equality A B.
subst A.
assert (O=B).
auto with Geom.
subst O.
ring.

assert (Col O A B).
unfold mid_point in *.
use H;auto with Geom.
assert (T:=l_28_b Q P A B O H0 H1).
replace (Py O P Q) with (Py Q P O) by auto with Geom.
rewrite T.
uniformize_pys.
replace (A ** O / A ** B) with (1/2).
replace (O ** B / A ** B) with (1/2).
field;auto with Geom.
symmetry.
apply (midpoint_ratio_2);auto.
symmetry.
apply (midpoint_ratio_1);auto.
Qed.

Lemma l_28_b_midpoint : forall O A B P Q,
 mid_point O A B ->
 2 * Py P O Q = Py P A Q + Py P B Q - 1/ 2 * Py A B A.
Proof.
intros.
cases_equality A B.
subst A.
basic_simpl.
assert (O=B) by auto with Geom.
subst O.
ring.
rewrite ( l3_5_py P Q A B O) by
 (unfold mid_point in *;intuition;auto with Geom).
replace (A ** O / A ** B) with (1/2)
 by (symmetry;apply (midpoint_ratio_1);auto).
replace (O ** B / A ** B) with (1/2)
 by (symmetry;apply (midpoint_ratio_2);auto).
field.
auto with Geom.
Qed.

Lemma l_27_a : forall A B C D P Q, weak_3_parallelogram A B C D ->
Py A P Q + Py C P Q = Py B P Q + Py D P Q.
Proof.
intros.
unfold weak_3_parallelogram in H.
elim H; intros O HO; clear H.
use HO.
assert (T:= l_28_midpoint O A C P Q H).
assert (U:= l_28_midpoint O B D P Q H0).
congruence.
Qed.

Lemma l_27_b : forall A B C D P Q, weak_3_parallelogram A B C D ->
Py4 A P B Q = Py4 D P C Q.
Proof.
intros.
unfold Py4.
apply (l_27_a A B C D P Q) in H.
IsoleVar (Py A P Q) H.
rewrite H.
ring.
Qed.

Lemma midpoint_is_midpoint: forall I A B, 
 mid_point I A B -> A<>B -> is_midpoint I A B.
Proof.
intros.
assert (A ** I / A ** B = 1 / 2) by
(apply (midpoint_ratio_1 I A B);auto).
unfold is_midpoint, on_line_d, mid_point in *.
use H.
repeat split;auto with Geom.
IsoleVar (A**I) H1.
rewrite H1.
field;auto with Geom.
auto with Geom.
Qed.

Lemma midpoint_on_line_d: forall I A B, 
 mid_point I A B -> A<>B -> on_line_d A I B (0-1).
Proof.
intros.
unfold mid_point in *.
unfold on_line_d.
use H.
repeat split;auto with Geom.
intro.
subst.
basic_simpl.
assert (A=B);auto with Geom.
rewrite <- H2.
uniformize_dir_seg.
ring.
Qed.

Lemma symmetric_point_unicity : forall O B C D, 
 mid_point O B D ->
 mid_point O D C ->
 B=C.
Proof.
intros.
unfold mid_point in *.
use H.
use H0.
cases_equality D O.
 subst.
 basic_simpl.
 assert (O=C).
 auto with Geom.
 subst.
 auto with Geom.
assert (Col O B C) by
(apply (col_trans_1 O D B C);auto with Geom).
assert (O**B=O**C).
uniformize_dir_seg.
rewrite <- H3.
rewrite <- H2.
ring.

cases_equality O B.
subst.
basic_simpl.
auto with Geom.
symmetry.
apply (A2b O B C B 1);auto with Geom.
basic_simpl.
auto.
basic_simpl.
auto.
Qed.


Lemma weak_3_parallelogram_parallel : forall A B C D,
   weak_3_parallelogram A B C D -> parallel B C A D.
Proof.
intros.
unfold weak_3_parallelogram in H.
elim H;intros O HO;use HO;clear H.

cases_equality A D.
subst.
auto with Geom.

cases_equality B C.
subst.
auto with Geom.

cases_equality A C.
subst.
assert (O=C).
auto with Geom.
subst.
unfold mid_point in *.
use H1.
auto with Geom.

cases_equality B D.
subst.
assert (O=D).
auto with Geom.
subst.
unfold mid_point in *.
use H0.
auto with Geom.

apply (midpoint_is_midpoint) in H0.
2:auto.
apply (midpoint_on_line_d) in H1.
2:auto.
unfold is_midpoint in *.


unfold parallel, S4.
replace (S B A C) with (S A C B) by auto with Geom.
rewrite (elim_area_on_line_d A C O D B (0-1)).
2:auto.
replace (S B C D) with (S C D B) by auto with Geom.
rewrite (elim_area_on_line_d C D O D B (0-1)).
2:auto.
clear H1.
basic_simpl.
ring_simplify_eq.
unfold is_midpoint in *.
rewrite (elim_area_on_line_d A C A C O (1/2)) .
2:auto.
basic_simpl.
rewrite (elim_area_on_line_d C D A C O (1/2)) .
2:auto.
basic_simpl.
uniformize_signed_areas.
field;auto with Geom.
Qed.

Lemma eq_half_eq_zero : forall x : F, x = 1/2 * x -> x=0.
Proof.
intros.
assert (x-1/2 * x=0).
rewrite H at 1.
field;auto with Geom.
replace (x-1/2*x) with (1/2*x) in H0.
2:field;auto with Geom.
IsoleVar x H0.
replace ( 0 / (1 / 2)) with 0 in H0.
auto.
field;split;auto with Geom.
intro.
intuition.
intro.
assert (1/2*2=0*2).
rewrite H1.
auto.
ring_simplify in H2.
replace (2 * (1 / 2)) with 1 in H2.
intuition.
field;auto with Geom.
Qed.

Lemma weak_3_parallelogram_eq_side : forall A B C D,
   weak_3_parallelogram A B C D -> B**C= A**D.
Proof.
intros.
assert (T:=H).
unfold weak_3_parallelogram in H.
elim H;intros O HO;use HO;clear H.

assert (W0:=H0).
assert (W1:=H1).

cases_equality A D.
subst.
basic_simpl.
assert (B=C).
eauto using symmetric_point_unicity.
auto with Geom.

cases_equality B C.
subst.
basic_simpl.
assert (A=D).
eauto using symmetric_point_unicity.
symmetry;auto with Geom.

cases_equality A C.
subst.
assert (O=C).
auto with Geom.
subst.
unfold mid_point in *.
use H1.
auto.
cases_equality B D.
subst.
assert (O=D).
auto with Geom.
subst.
unfold mid_point in *.
use H0.
auto.
apply (midpoint_is_midpoint) in H0.
2:auto.
apply (midpoint_on_line_d) in H1.
2:auto.

assert (parallel B C A D).
apply (weak_3_parallelogram_parallel);auto.
cut (B**C/A**D= 1).
intros.
IsoleVar (B**C) H6.
rewrite H6.
ring.
auto with Geom.

unfold is_midpoint in *.
replace (B ** C / A ** D) with (C**B / D**A) by auto with Geom.

cases_col C O D.
rewrite (elim_length_ratio_on_line_d_1 C D A O D B (0-1));auto with Geom.

replace ((C ** O / O ** D + (0 - 1)) / (D ** A / O ** D) ) with 
             ((C ** O / O ** D) / (D ** A / O ** D) + (0 - 1)/(D ** A / O ** D)).
2:field;split;unfold on_line_d in *; use H1;auto with Geom.

replace ((0 - 1) / (D ** A / O ** D)) with (D**O/D**A).
2:uniformize_dir_seg;field;split;unfold on_line_d in *; use H1;auto with Geom.
2:assert (D<>O) by auto with Geom;auto with Geom.



unfold on_line_d in *.
use H0. use H1.
field_simplify_eq.
2:auto with Geom.

cases_equality O C.
subst.
assert (A**C=0).
apply eq_half_eq_zero.
auto.
assert (A=C) by auto with Geom.
subst.
intuition.

assert (Col O D A).
apply (col_trans_1 O C D A);auto with Geom.

replace (D**O) with (D**A+A**O).
2:apply chasles;auto with Geom.

cut (C**O = O**A).
intro.
rewrite H13.
uniformize_dir_seg.
ring.

unfold mid_point in W0.
use W0.
uniformize_dir_seg.
rewrite H14.
ring.

rewrite (elim_length_ratio_on_line_d_2 C D A O D B (0-1));auto with Geom.
unfold S4.
replace (S C O D) with (S D C O) by auto with Geom.
replace (S D O A) with (S A D O) by auto with Geom.
basic_simpl.

rewrite (elim_area_on_line_d D C A C O (1/2)).
2:auto.
basic_simpl.
rewrite (elim_area_on_line_d A D A C O (1/2)).
2:auto.
basic_simpl.
uniformize_signed_areas.
field.
split;auto with Geom.
intro.
assert (Col C A D) by auto with Geom.
unfold on_line_d in *.
use H0.
assert (Col C A O) by auto with Geom.
assert (Col C O D).
apply (col_trans_1  C A O D);auto with Geom.
intuition.
Qed.


Lemma l3_6 : forall A B C D, 
  weak_3_parallelogram A B C D ->
 A**C * A**C + B**D * B**D = 2*A**B * A**B + 2*B**C*B**C.
Proof.
intros.
cases_equality B D.

subst.
basic_simpl.
unfold weak_3_parallelogram in H.
use H.
unfold mid_point in H2.
use H2.
uniformize_dir_seg.
assert (D=x).
auto with Geom.
subst x.
unfold mid_point in H1.
use H1.
rewrite H3.
uniformize_dir_seg.
basic_simpl.
ring_simplify_eq.
rewrite <- (chasles A C D) in H3.
IsoleVar (A**C) H3.
rewrite H3.
ring.
auto.

assert (B**C= A**D).
apply weak_3_parallelogram_eq_side;auto.


unfold weak_3_parallelogram in H.
elim H;intros O (hA,hb);clear H.
assert (Py A O A =
       B ** O / B ** D * Py A D A + O ** D / B ** D * Py A B A -
       B ** O / B ** D * (O ** D / B ** D) * Py B D B).
apply (l3_5_py A A B D O);
unfold mid_point in *;intuition;auto with Geom.
replace (B ** O / B ** D) with (1/2) in *
  by (symmetry;apply midpoint_ratio_1;auto).
replace (O ** D / B ** D)  with (1/2) in *
  by (symmetry;apply midpoint_ratio_2;auto).
assert (A**C = 2* A**O).
unfold  mid_point in *.
use hA.
replace (A**C) with (A**O + O**C) by auto with Geom.
rewrite H3.
ring.
rewrite H2.
replace (2 * A ** O * (2 * A ** O)) with (2*(2*A ** O * A**O)) by ring.
replace (2*A ** O * A**O) with (Py A O A) 
 by (unfold Py;uniformize_dir_seg;basic_simpl;try ring).
rewrite H.
unfold Py;uniformize_dir_seg;basic_simpl.
replace (A**D) with (B**C).
field;auto with Geom.
Qed.

Lemma l3_6_b : forall A B C D, 
  weak_3_parallelogram A B C D ->
  Py A B C = - Py B A D.
Proof.
intros.
unfold Py.
assert (T:=l3_6 A B C D H).
IsoleVar (A ** C * A ** C) T.
rewrite T.
uniformize_dir_seg.
ring_simplify_eq.
replace (B**C) with (A**D).
ring.
symmetry;
apply weak_3_parallelogram_eq_side;auto.
Qed.


Lemma l_27_c : forall A B C D P Q, weak_3_parallelogram A B C D ->
Py P A Q + Py P C Q = Py P B Q + Py P D Q + 2 * Py B A D.
Proof.
intros.
assert (X:= H).
unfold weak_3_parallelogram in H.
elim H; intros O HO; clear H.
use HO.
assert (T:= l_28_b_midpoint O A C P Q H).
assert (U:= l_28_b_midpoint O B D P Q H0).
assert (Py P A Q + Py P C Q - 1 / 2 * Py A C A =  Py P B Q + Py P D Q - 1 / 2 * Py B D B) by congruence.
clear T U.
assert (2* Py B A D =  1/2 * (Py A C A - Py B D B)).
replace (2 * Py B A D) with (Py B A D + Py B A D) by ring.
replace (Py B A D) with (- Py A B C).
unfold Py.
uniformize_dir_seg;basic_simpl.
field_simplify_eq.
ring_simplify_eq.
2:auto with Geom.
assert (T:=l3_6 A B C D X).
IsoleVar (B ** D * B ** D) T.
replace (2 * B ** D * B ** D) with (2 * (B ** D * B ** D)) by ring.
rewrite T.
ring.
assert (U:=l3_6_b A B C D X).
rewrite U;ring.

rewrite H2.
IsoleVar (Py P A Q + Py P C Q) H1.
rewrite H1.
field.
auto with Geom.
Qed.

Lemma l3_8_a : forall A B C D P, weak_3_parallelogram A B C D ->
Py P A B = Py4 P D A C.
Proof.
intros.
replace (Py4 P D A C) with (Py4 C A D P) by auto with Geom.
unfold Py4.
assert (T:=l_27_a A B C D A P H).
basic_simpl.
rewrite T.
uniformize_pys.
ring.
Qed.

Lemma l3_8_b : forall A B C D P, weak_3_parallelogram A B C D ->
Py P A B = Py P D C - Py A D C.
Proof.
intros.
rewrite (l3_8_a A B C D) by auto.
auto with Geom.
Qed.

Lemma l_28_a : forall A B U V Y,
Col Y U V -> U <> V ->
S A B Y = U**Y/U**V * S A B V + Y**V/U**V * S A B U.
Proof.
intros.
replace (S A B Y) with (S Y A B) by auto with Geom.
rewrite (l2_9 A B U V Y) by auto.
uniformize_signed_areas.
auto.
Qed.

Lemma on_foot_per : forall A B C F, 
  on_foot F A B C ->
  per A F B.
Proof.
intros.
unfold on_foot in H.
use H.
assert (perp A F B C) by auto with Geom.
cut (perp A F F B).
auto with Geom.
cut (perp F B A F).
auto with Geom.
apply (perp_para_perp B C A F F B);auto with Geom.
Qed.

Lemma herron_qin : forall A B C,
S A B C * S A B C = 1 / (2*2*2*2) * (Py A B A * Py A C A - Py B A C * Py B A C).
Proof.
intros.
cases_equality B C.
subst.
basic_simpl.
uniformize_pys.
basic_simpl.
ring.

elim (proj_ex A B C H).
intros F HF.

cases_equality B F.
subst.
assert (T:=on_foot_area A F C F HF).
field_simplify_eq.
2:repeat apply nonzeromult;auto with Geom.
replace (2 * (2 * (2 * 2)) * S A F C * S A F C) with
(2*2*(2 * 2 * S A F C * S A F C)) by ring.
rewrite T.

unfold on_foot in HF.
use HF.
clear H2 H3.
assert (perp F C A F) by auto with Geom.
unfold perp, Py4 in *.
IsoleVar (Py C A F) H1.
replace (Py C A F) with (Py F A C) in H1 by auto with Geom.
rewrite H1.
uniformize_pys.
basic_simpl.

assert (Py A C A = Py A F A + Py F C F).
unfold Py.
basic_simpl.
uniformize_dir_seg.
basic_simpl.
replace (A ** C * A ** C + A ** C * A ** C) with (2*(A**C*A**C)) by ring.
replace (A ** F * A ** F + A ** F * A ** F) with (2*(A ** F * A ** F)) by ring.
replace (C ** F * C ** F + C ** F * C ** F) with (2*(C**F*C**F)) by ring.
replace ( 2 * (A ** F * A ** F) + 2 * (C ** F * C ** F))
with (2*(A ** F * A ** F + C ** F * C ** F)) by ring.
assert (A ** C * A ** C = A ** F * A ** F + C ** F * C ** F).
assert (Py A F C = 0).
replace 0 with (-0) by ring.
rewrite <- H0.
ring.
unfold Py in H2.
uniformize_dir_seg.
basic_simpl.
IsoleVar (A ** F * A ** F + C ** F * C ** F) H2.
rewrite H2.
ring.
rewrite H2;auto.
rewrite H2.
unfold Py.
uniformize_dir_seg.
basic_simpl.
ring.

assert (Col B F C).
unfold on_foot in HF.
use HF;auto with Geom.
assert (T:= l_3_4_b B F C A H1).
replace (Py A B F) with (Py F B F) in T.

replace (Py F B F) with (2*B**F*B**F) in T.
2:unfold Py;uniformize_dir_seg;basic_simpl;ring.
IsoleVar (Py A B C) T.
2:auto with Geom.

replace (2 * B ** F * B ** F * B ** C / B ** F) with 
 ( 2 * B ** F * B ** C) in T.
2:field;auto with Geom.

replace (S A B C * S A B C) with (1/2 *1/2*A**F*A**F*B**C*B**C).
2: replace (1 / 2 * 1/2*A**F*A**F*B**C* B ** C ) with 
               (1/2 * 1/2 *  (A ** F * A**F * B ** C *B**C )) by ring.
2: (rewrite <- on_foot_area).
2:field;auto with Geom.
2:auto.


replace ( 1 / 2 * 1/2 *  A ** F * A ** F * B ** C * B**C ) with
((1/2)* (A**F * A**F) * (1/2)* (B**C * B**C))
   by (field;solve_conds;auto with Geom).

replace (A**F * A**F) with (A**B * A**B - B**F * B**F).
field_simplify_eq.
replace (2 * (2 * (2 * 2)) * B ** F * B ** F * B ** C * B ** C) 
with ( 2 * 2 * (2*B ** F *B ** C) * (2*B ** F * B ** C)) by ring. 
rewrite <- T.
unfold Py.
uniformize_dir_seg.
basic_simpl.
ring.
solve_conds.

assert (per A F B).
apply (on_foot_per A B C F);auto.
unfold per,Py in *.
uniformize_dir_seg.
IsoleVar (A**B*A**B) H3.
rewrite H3.
ring.

assert (per A F B).
apply (on_foot_per A B C F);assumption.
unfold Py;uniformize_dir_seg;basic_simpl.
unfold per, Py in H2.
IsoleVar (A**B*A**B) H2.
rewrite H2.
uniformize_dir_seg.
basic_simpl.
ring.

Qed.

Lemma l3_9_aux : forall B D P Q R S Y ,
 Col Y B D ->
 B<>D ->
 B ** Y = Q ** S ->
 weak_3_parallelogram B Y S Q ->
 Py4 P Q R S = Q ** S / B ** D * Py4 P B R D.
Proof.
intros.
rewrite <- H1.
replace (Py4 P Q R S) with (Py4 P B R Y).

2:replace (Py4 P B R Y) with (Py4 B P Y R) by auto with Geom.
2:rewrite (l_27_b B Y S Q P R H2).
2:auto with Geom.

unfold Py4.

assert ( Py P B Y * B ** D = Py P B D * B ** Y).
apply (l_3_4_b B Y D P); auto with Geom.
IsoleVar (Py P B Y) H3.
2:auto with Geom.
rewrite H3.
assert (Py R B Y * B ** D = Py R B D * B ** Y).
apply (l_3_4_b  B Y D R);auto with Geom.
IsoleVar (Py R B Y) H5.
rewrite H5.
field;auto with Geom.
Qed.

Lemma l3_9 : forall P Q R S A B C D,
  parallel P R A C ->
  parallel Q S B D ->
  B<>D -> A<>C -> ~ perp A C B D ->
  Py4 P Q R S / Py4 A B C D = (P**R / A**C) * (Q**S / B**D).
Proof.
intros.
assert (exists Y : Point,
         Col Y A C /\ A ** Y = P ** R /\ weak_3_parallelogram A Y R P).
apply (on_line_dex_spec_strong_f A C P R);auto with Geom.
elim H4;intros X HX;clear H4; use HX.
assert (exists Y : Point,
         Col Y B D /\ B ** Y = Q ** S /\ weak_3_parallelogram B Y S Q).
apply (on_line_dex_spec_strong_f B D Q S);auto with Geom.
elim H5;intros Y HY;clear H5; use HY.

assert (Ha:Py4 P Q R S  = Q**S / B**D * Py4 P B R D).

eapply l3_9_aux with (Y:=Y); auto with Geom.

assert (Hb:Py4 P B R D  = P**R / A**C * Py4 A B C D).

replace (Py4 P B R D) with (Py4 B P D R) by auto with Geom.
rewrite (l3_9_aux A C B P D R X H4 H2 H6 H7).
replace (Py4 B A D C) with (Py4 A B C D) by auto with Geom.
field;auto with Geom.

rewrite Ha.
rewrite Hb.
field;solve_conds;auto with Geom.
Qed.


Lemma l3_10 : forall A B C D,
 parallel A B C D ->
 C<>D ->
 A**B/C**D = Py4 A C B D / - Py C D C.
Proof.
intros.
replace (A ** B / C ** D) with ((A ** B / C ** D) * (C**D / C**D))
 by (field;auto with Geom).
rewrite <- (l3_9 A C B D C C D D);auto with Geom.
unfold Py4.
basic_simpl.
uniformize_pys.
field.
cut (Py C D C <> 0).
intuition.
auto with Geom.
unfold perp, Py4.
basic_simpl.
intro.
assert (Py D C D = 0).
replace (0) with (-0) by ring.
rewrite <- H1.
ring.
assert (D=C).
auto with Geom.
intuition.
Qed.

Lemma l3_10b : forall A B C D,
 parallel A B C D ->
 C<>D ->
 A**B/C**D = Py4 B C A D / Py C D C.
Proof.
intros.
rewrite l3_10 by assumption.
replace (Py4 B C A D) with (- Py4 A C B D) by auto with Geom.
field.
split;auto with Geom.
Qed.

Lemma perp_not_parallel : forall A B C D,
  perp A B C D ->
  A <> B -> C <> D ->
  ~ parallel A B C D.
Proof.
intros.
unfold perp in H.
intro.
assert (T:=l3_10 A B C D H2 H1).
rewrite H in T.
IsoleVar (A**B) T.
2:auto with Geom.
replace (C ** D * (0 / - Py C D C)) with 0 in T.
assert (A=B) by auto with Geom.
subst A.
intuition.
field.
cut (Py C D C <>  0).
intro.
intuition.
auto with Geom.
Qed.

Lemma not_perp_to_itself : forall A B,
A <> B ->~ perp A B A B.
Proof.
intros.
unfold perp, Py4 in *.
basic_simpl.
intro.
IsoleVar (Py B A B) H0.
basic_simpl.
assert (A=B).
unfold Py in *.
uniformize_dir_seg.
basic_simpl.
replace (A ** B * A ** B + A ** B * A ** B) with (2*(A ** B * A ** B)) in * by ring.
IsoleVar (A ** B) H0.
replace (0 / 2 / A ** B) with 0 in *.
auto with Geom.
field.
split;auto with Geom.
auto with Geom.
auto with Geom.
intuition.
Qed.

Lemma parallel_not_perp : forall A B C D,
  parallel A B C D ->
  A <> B -> C <> D ->
  ~ perp A B C D.
Proof.
intros.
intro.
assert (perp C D C D).
apply (perp_para_perp A B C D C D);assumption.
apply (not_perp_to_itself C D);auto.
Qed.



Lemma l_25_a : forall A B P Q Y,
  P<>Q -> Q<>Y -> Py Q A B <> 0 ->
 on_inter_line_perp Y A P Q A B ->
 P**Y / Q**Y = Py P A B / Py Q A B.
Proof.
intros.
unfold on_inter_line_perp in *.
use H2.
assert (A<>B).
intro;subst;basic_simpl;intuition.
elim (proj_ex P A B H2).
intros P1 HP1.
unfold on_foot in *.
use HP1.
elim (proj_ex Q A B H2).
intros P2 HP2.
unfold on_foot in *.
use HP2.
assert (Pa:=H5).
assert (Pb:=H4).
assert (Pc:=H7).
unfold perp, Py4 in H4, H5, H7.
IsoleVar (Py P A B) H4.
IsoleVar (Py Q A B) H7.
basic_simpl.
rewrite H4, H7.
rewrite col_pyth by assumption.
assert (A<>P2).
intro;subst;basic_simpl;intuition.
rewrite col_pyth by assumption.
replace (2 * A ** P1 * A ** B / (2 * A ** P2 * A ** B)) with (A**P1/A**P2)
 by (field;repeat split;auto with Geom).

assert (parallel P P1 Y A).
assert (T:=perp_perp_para Y A A B P1 P H12 Pa Pb).
auto with Geom.

assert (parallel Y A Q P2).
apply (perp_perp_para Y A A B Q P2 H12 Pa).
auto with Geom.

(* ici *)
cases_equality A Y.
subst.
clear H13 H14 Pa H5 H9 H12.
assert (parallel P1 P P2 Q).
apply (perp_perp_para P1 P Y B P2 Q H2 Pb Pc).


cases_col Y Q P2.
rename H9 into HCol.

assert (parallel P Q P2 Q).
unfold parallel, S4.
basic_simpl.

assert (Col Q P P2).
apply (col_trans_1 Q Y P P2);auto with Geom.
assert (Col P P2 Q).
auto with Geom.
auto.

cases_equality P2 Q.
subst.
clear H9 H5 H7 Pc.
assert (Col Y P B).
apply (col_trans_1 Y Q P B);auto with Geom.
assert (parallel P1 P Y B).
cut (parallel Y B P1 P).
auto with Geom.
unfold parallel, S4.
assert (Col Y B P) by auto with Geom.
rewrite H7.
basic_simpl.
assert (Col Y P1 B).
auto with Geom.
auto with Geom.

cases_equality P1 P.
subst.
uniformize_dir_seg.
field;split;auto with Geom.

cut False.
intuition.

apply parallel_not_perp in H7.
intuition.
auto with Geom.
auto with Geom.

assert (perp P Q Y B).
apply (perp_para_perp P2 Q  Y B P Q);auto with Geom.
assert (perp Y B P Q) by auto with Geom.
intuition.



assert (Y ** P / Y ** Q = Y ** P1 / Y ** P2).
apply (thales_2 Y Q P P2 P1);auto with Geom.
apply (col_trans_1 Y B P2 P1);auto with Geom.
rewrite <- H12.
uniformize_dir_seg.
field;split;auto with Geom.


rewrite (l1_25 P Y Q P1 A P2).

uniformize_dir_seg.
field;solve_conds.
cut (P2**A<>0).
auto with Geom.
auto with Geom.
auto with Geom.

intro.

assert (per B A Q).
apply (perp_col_perp B A Y Q); auto with Geom.
unfold per.
replace (Py B A Y) with (Py Y A B) by auto with Geom.
auto.
unfold per in H17.
replace (Py B A Q) with (Py Q A B) in H17 by auto with Geom.
intuition.

auto with Geom.
assert (Col A P1 P2).
apply (col_trans_1 A B P1 P2);auto with Geom.
auto with Geom.
auto.
auto.
Qed.

Lemma l_25_b : forall A B P Q Y,
  P<>Q -> Q<>Y -> Py Q A B <> 0 ->
 on_inter_line_perp Y A P Q A B ->
 P**Y / P**Q = Py P A B / Py4 P A Q B.
Proof.
intros.
assert (T:= l_25_a A B P Q Y H H0 H1 H2).
unfold on_inter_line_perp in *.
use H2.
replace (P**Y) with (P**Q + Q**Y) in T by auto with Geom.
replace ((P ** Q + Q ** Y) / Q ** Y) with (P**Q/Q**Y + 1) in T 
  by (field;auto with Geom).
replace (P**Y) with (P**Q + Q**Y) by auto with Geom.

replace ((P ** Q + Q ** Y) / P ** Q) with (Q**Y/P**Q + 1) 
  by (field;auto with Geom).
unfold Py4.
IsoleVar (Py P A B) T.
rewrite T.
field.
repeat split;auto with Geom.
replace (Py Q A B * (P ** Q + Q ** Y) - Py Q A B * Q ** Y) with
(Py Q A B *  (P ** Q)) by ring.
apply nonzeromult.
auto.
auto with Geom.
Qed.

Lemma l_25_c : forall A B P Q Y,
  P<>Q -> Q<>Y -> Py Q A B <> 0 ->
 on_inter_line_perp Y A P Q A B ->
 Q**Y / P**Q = Py Q A B / Py4 P A Q B.
Proof.
intros.
assert (T:= l_25_a A B P Q Y H H0 H1 H2).
unfold on_inter_line_perp in *.
use H2.
replace (P**Y) with (P**Q + Q**Y) in T by auto with Geom.
replace ((P ** Q + Q ** Y) / Q ** Y) with (P**Q/Q**Y + 1) in T 
  by (field;auto with Geom).
replace (P**Y) with (P**Q + Q**Y) by auto with Geom.

replace ((P ** Q + Q ** Y) / P ** Q) with (Q**Y/P**Q + 1) 
  by (field;auto with Geom).
unfold Py4.
IsoleVar (Py P A B) T.
rewrite T.
field.
repeat split;auto with Geom.
replace (Py Q A B * (P ** Q + Q ** Y) - Py Q A B * Q ** Y) with
(Py Q A B *  (P ** Q)) by ring.
apply nonzeromult.
auto.
auto with Geom.
Qed.

