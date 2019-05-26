(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.*)
(* Julien Narboux (Julien.Narboux@inria.fr)                                     *)
(* LIX/INRIA FUTURS 2004-2008                                                     *)
(***************************************************************************)

Set Nested Proofs Allowed.
Require Export area_elimination_lemmas.
Require Import Classical.

(** For the first time, we need decidability of the parallel predicate *)

Lemma parallel_dec : forall A B C D, parallel A B C D \/ ~ parallel A B C D.
Proof.
intros.
apply classic.
Qed.

Ltac cases_parallel A B C D := elim (parallel_dec A B C D);intros.

Definition Det3 (x1 x2 x3 y1 y2 y3 z1 z2 z3 : F) : F :=
  x1 * (y2 * z3) - x1 * (y3 * z2) - x2 * (y1 * z3) + x2 * (y3 * z1) +
  x3 * (y1 * z2) - x3 * (y2 * z1).

Lemma freepoint_elimination_aux : forall O U V B Y:Point, ~ Col O U V ->
S O B Y = 1/ (S O U V) * (S O B V * S O U Y + S O B U * S O Y V).
Proof with Geometry.
intros.

cases_parallel U V O Y.
rename H into T.
assert (O**Y / U**V = S U O Y / S O V U).
apply l2_15...
assert (S O B Y = S O B O + (O**Y/U**V) * S4 O U B V).
apply elim_area_on_parallel.
unfold on_parallel;repeat split...
eauto with Geom.
rewrite H in H1.
basic_simpl.
unfold S4 in *.
assert (parallel O Y U V).
Geometry.
unfold parallel, S4 in *.
IsoleVarRing (S O Y V) H2.
rewrite H2.
rewrite H1.
uniformize_signed_areas.
field.
split...

assert (exists W, inter_ll W U V O Y).
apply inter_ll_ex...
DecompEx H1 W.

cases_equality W O.
subst W.
unfold inter_ll in *.
intuition.
rename H1 into Hdiff.

assert (S B O W = 1 / S4 U O V Y * (S U O Y * S B O V + S V Y O * S B O U)).
apply  elim_area_inter_ll...
replace (S4 U O V Y) with (- S4 O U Y V) in H1.
2:Geometry.
replace ((S U O Y * S B O V + S V Y O * S B O U)) with 
(S O B V * S O U Y + S O B U * S O Y V) in H1.
2:uniformize_signed_areas;field.
unfold inter_ll in *;DecompAndAll.
assert (O ** W / O ** Y = S O U V / S4 O U Y V).
apply co_side_ter...
cases_col B O W.

cases_equality V W.
subst W.
assert (Col O Y B).
eapply col_trans_1 with (B:=V)...
unfold Col in *.
uniformize_signed_areas.
rewrite H4.
rewrite H5.
rewrite H7.
ring.

cases_equality O B.
subst B.
basic_simpl.
ring.

cases_col  V O B.
assert (Col O Y B).
eapply col_trans_1 with (B:= W)...
assert (Col O Y V).
eapply col_trans_1 with (B:= B)...
unfold Col in *.
uniformize_signed_areas.
rewrite H9.
rewrite H10.
rewrite H11.
ring.

assert (U**W/V**W = S U O B / S V O B).
apply co_side...

cases_col V O Y.

cases_equality Y O.
subst Y.
basic_simpl.
ring.

assert (Col Y W V).
eapply col_trans_1 with (B:= O)...
assert (Col W U Y).
eapply col_trans_1 with (B:= V)...

cases_equality Y W.
Unset Regular Subst Tactic.
subst W.
Set Regular Subst Tactic.
clear H13 H12 H5.
assert (Col O V B).
eapply col_trans_1 with (B:= Y)...
unfold Col in *.
uniformize_signed_areas.
rewrite H4.
replace (S V O B) with (-0).
rewrite H11.
ring.
rewrite <- H5.
ring.

assert (Col Y U O).
eapply col_trans_1 with (B:= W)...
assert (Col O U V).
eapply col_trans_1 with (B:= Y)...
intuition.

assert (U**W/V**W = S U O Y / S V O Y).
apply co_side...
rewrite H10 in H12.

assert (Col O B Y).
eapply col_trans_1 with (B:= W)...
rewrite H13.
uniformize_signed_areas.
RewriteVar (S O B U) H12.
2:Geometry.
field.
split...

(** Second case *)
assert (O**Y / O**W = S B O Y / S B O W).
apply A6...
assert (O**Y / O**W = S4 O U Y V / S O U V).
replace (O ** Y / O ** W) with (1/(O ** W / O ** Y)). 
rewrite H2.
field.
Geometry.
repeat apply nonzeromult...
field.
split...
unfold not;intro.
assert (O=Y).
Geometry.
subst Y.
assert (parallel U V O O)...
rewrite H7 in H8.
set (S O B V * S O U Y + S O B U * S O Y V) in *.
rewrite H1 in H8.
replace (S B O Y) with (-S O B Y) in H8.
2:Geometry.

RewriteVar (S O B Y) H8.
field;split...
apply nonzeromult...
apply nonzerodiv...

unfold not;intro.
rewrite H9 in H1.
basic_simpl.
assert (Col O Y B).
eapply col_trans_1 with (B:=W)...
Geometry.

Qed.




Lemma  free_points_area_elimination :
    forall O U V A B Y : Point, 
    S O U V <> 0 ->
    S A B Y =
    Det3 (S O U A) (S O V A) 1 (S O U B) (S O V B) 1 (S O U Y) (S O V Y) 1 /
    S O U V.
Proof with Geometry.
intros.
unfold Det3.
replace (S A B Y) with (S A B O + S A O Y + S O B Y)...

replace (S A O Y) with (- S O A Y).
2:symmetry;Geometry.
replace (S O A Y) with (1/ (S O U V) * (S O A V * S O U Y + S O A U * S O Y V)).
2:symmetry;eapply freepoint_elimination_aux...
replace (S O B Y) with (1/ (S O U V) * (S O B V * S O U Y + S O B U * S O Y V)).
2:symmetry;eapply freepoint_elimination_aux...
replace (S A B O) with (S O A B).
2:Geometry.
replace (S O A B) with (1/ (S O U V) * (S O A V * S O U B + S O A U * S O B V)).
2:symmetry;eapply freepoint_elimination_aux...
uniformize_signed_areas.
field...
Qed.

Lemma free_points_ratio_elimination_1 : forall O U V A B C D : Point,
  parallel A B C D ->
  C<>D ->
  S O U V <> 0 ->
  S U A B <> 0 ->
  A**B / C**D = (S O U A * S O V B + S O U A * S O U V - S O V A * S O U B -
 S O U B * S O U V) /
(S O U A * S O V D - S O U A * S O V C + S O V A * S O U C -
 S O V A * S O U D + S O U V * S O U C - S O U V * S O U D).
Proof.
intros.

cases_equality A B.
subst.
basic_simpl;intuition.

assert (A**B / C**D = (S O A B + S O U A - S O U B) / (S U C D - S A C D)
 /\ (S U C D - S A C D) <> 0 ).
   elim (on_line_dex_spec_strong_f A B C D H H3).
   intros D' Hn. decompose [and] Hn;clear Hn.
   rewrite <- H6.
   assert (A<>D').
   intro;subst; basic_simpl; auto with Geom.
   assert (~ Col U A D').
     intro.
     assert (Col A B U).
       eapply (col_trans_1);eauto with Geom.
       assert (Col U A B); auto with Geom.

   rewrite (A6 A B D' U H5 H8) by auto with Geom.

   rewrite (A5 U A B O).
   assert (S U A D' = S U C D - S A C D) by
     (apply (l2_12a_strong_3 A D' D C U);auto).
   split.
   uniformize_signed_areas.
   rewrite H9; field; rewrite <- H9; auto with Geom.
   rewrite <- H9;auto with Geom.   

use H4.
rewrite H5.
rewrite (free_points_area_elimination O U V O A B) in * by assumption.
rewrite (free_points_area_elimination O U V U C D) in * by assumption.
rewrite (free_points_area_elimination O U V A C D) in * by assumption.
unfold Det3 in *.
replace (S O V U) with (- S O U V) in * by auto with Geom.
basic_simpl.
field.
split;auto.
clear H5.
replace ((0 - - (S O U V * S O U C) - S O U V * S O U D + S O U C * S O V D -
      S O V C * S O U D) / S O U V -
     (S O U A * S O V C - S O U A * S O V D - S O V A * S O U C +
      S O V A * S O U D + S O U C * S O V D - S O V C * S O U D) / S O U V
)
with ((0 - - (S O U V * S O U C) - S O U V * S O U D + S O U C * S O V D -
      S O V C * S O U D - (S O U A * S O V C - S O U A * S O V D - S O V A * S O U C +
      S O V A * S O U D + S O U C * S O V D - S O V C * S O U D)) / S O U V) in H6 by (field;auto).
replace (0 - - (S O U V * S O U C) - S O U V * S O U D + S O U C * S O V D -
      S O V C * S O U D -
      (S O U A * S O V C - S O U A * S O V D - S O V A * S O U C +
       S O V A * S O U D + S O U C * S O V D - S O V C * S O U D)) with (S O U A * S O V D - S O U A * S O V C + S O V A * S O U C - S O V A * S O U D +
S O U V * S O U C - S O U V * S O U D) in H6 by ring.
intro Hx; rewrite Hx in H6; clear Hx.
basic_simpl;
intuition.
Qed.


Lemma free_point_ratio_elimination_2 : forall O U V A B C D : Point,
  parallel A B C D ->
  C<>D ->
  S O U V <> 0 ->
  S V A B <> 0 ->
  A**B / C**D = (S O V A * S O U B + S O V A * S O V U - S O U A * S O V B -
 S O V B * S O V U) /
(S O V A * S O U D - S O V A * S O U C + S O U A * S O V C -
 S O U A * S O V D + S O V U * S O V C - S O V U * S O V D).
Proof.
intros.
assert (S O V U <> 0).
intro; apply H1;uniformize_signed_areas;auto with Geom.
rewrite (free_points_ratio_elimination_1 O V U A B C D) by auto.
reflexivity.
Qed.

Lemma free_points_ratio_elimination_3 : forall O U V A B C D : Point,
  parallel A B C D ->
  A<>B ->
  C<>D ->
  S O U V <> 0 ->
  S U C D <> 0 ->
  A**B / C**D = (S O U C * S O V B - S O U C * S O V A + S O V C * S O U A -
  S O V C * S O U B + S O U V * S O U A - S O U V * S O U B)/
  (S O U C * S O V D + S O U C * S O U V - S O V C * S O U D -
  S O U D * S O U V).
Proof.
intros.
assert (A**B / C**D =  (S U A B - S C A B) / (S O C D + S O U C - S O U D) 
 /\ (S O C D + S O U C - S O U D) <> 0 ).
assert (parallel C D A B) by auto with Geom.
   elim (on_line_dex_spec_strong_f C D A B H4 H1).
   intros D' Hn. decompose [and] Hn;clear Hn.
   rewrite <- H7.
   assert (C<>D').
   intro;subst; basic_simpl; auto with Geom.

   rewrite (A6 C D' D U H1) by auto with Geom.
   rewrite (A5 U C D O).
   assert (T:=A5 U C D O).
   assert (S U C D' = S U A B - S C A B) by
     (apply (l2_12a_strong_3 C D' B A U);auto).
   split.
   uniformize_signed_areas.
   rewrite H9.
   field.
   replace (S O C D + S U C O - - S U O D) 
      with (S U C O + S U O D + S O C D) by ring.
   rewrite <- T;auto.
   replace (S O C D + S O U C - S O U D) 
      with (S U C O + S U O D + S O C D)
        by (uniformize_signed_areas;ring).
   rewrite <- T;auto.

use H4.
rewrite H5.
rewrite (free_points_area_elimination O U V U A B) in * by assumption.
rewrite (free_points_area_elimination O U V C A B) in * by assumption.
rewrite (free_points_area_elimination O U V O C D) in * by assumption.
unfold Det3 in *.
replace (S O V U) with (- S O U V) in * by auto with Geom.
basic_simpl.
field.
split;auto.
clear H5.

replace ((S O U C * S O V D - S O V C * S O U D) / S O U V + S O U C - S O U D)
with ((S O U C * S O V D + S O U C * S O U V - S O V C * S O U D - S O U D * S O U V) / (S O U V))
in H6 by (field;auto).
intro.
rewrite H4 in H6.
basic_simpl;
intuition.
Qed.

Lemma free_points_ratio_elimination_4 : forall O U V A B C D : Point,
  parallel A B C D ->
  A<>B ->
  C<>D ->
  S O U V <> 0 ->
  S V C D <> 0 ->
  A**B / C**D = (S O V C * S O U B - S O V C * S O U A + S O U C * S O V A -
 S O U C * S O V B + S O V U * S O V A - S O V U * S O V B) /
(S O V C * S O U D + S O V C * S O V U - S O U C * S O V D -
 S O V D * S O V U).
intros.
assert (S O V U <> 0).
intro; assert (Col O U V) by auto with Geom;intuition.
rewrite (free_points_ratio_elimination_3 O V U A B C D) by auto.
reflexivity.
Qed.

Lemma free_points_ratio_elimination_5 : forall O U V A B C D: Point,
  parallel A B C D ->
  C<>D ->
  ~ Col O U V ->
  ~ Col A C D ->
  A**B / C**D = (S O U C * S O V A - S O U C * S O V B - S O V A * S O U B +
 S O V B * S O U A - S O V C * S O U A + S O V C * S O U B) /
(S O U C * S O V A - S O U C * S O V D - S O V A * S O U D -
 S O V C * S O U A + S O V C * S O U D + S O U A * S O V D) .
Proof.
intros.
rewrite (l2_15 A B C D) by auto with Geom.
assert (~ Col A D C) by auto with Geom.
unfold Col in H3.
rewrite (free_points_area_elimination O U V C A B) in * by assumption.
rewrite (free_points_area_elimination O U V A D C) in * by assumption.
unfold Det3 in *.
field.
split;auto.
basic_simpl.
replace (S O U A * S O V D - S O U A * S O V C - S O V A * S O U D +
      S O V A * S O U C + S O U D * S O V C - S O V D * S O U C)
   with (S O U C * S O V A - S O U C * S O V D - S O V A * S O U D - S O V C * S O U A +
S O V C * S O U D + S O U A * S O V D) in * by ring.
intro Hx; rewrite Hx in *.
replace (0 / S O U V) with 0 in * by (field;auto).
intuition.
Qed.

(*
set (X_C := S O U C).
set (X_A := S O U A).
set (X_B := S O U B).
set (X_D := S O U D).
set (Y_C := S O V C).
set (Y_A := S O V A).
set (Y_B := S O V B).
set (Y_D := S O V D).
*)

Lemma free_points_ratio_elimination_6 : forall O U V A B C D: Point,
  parallel A B C D ->
  C<>D ->
  ~ Col O U V ->
  ~ Col O A C ->
  Col A C D ->
  A**B / C**D = (S O U A * S O V B - S O V A * S O U B) /
(S O U C * S O V D - S O V C * S O U D).
Proof.
intros.
assert (~ Col O C D).
  intro.

  assert (Col C A O).
    apply (col_trans_1 C D A O );auto with Geom.
    intuition.

assert (Col B C D).
  cut (Col C D B).
  auto with Geom.
  apply (par_col_col_1 C D A B); auto with Geom.
rewrite <- (l2_7 C D A B O);auto.
unfold Col in H4.
rewrite (free_points_area_elimination O U V O A B) in * by assumption.
rewrite (free_points_area_elimination O U V O C D) in * by assumption.
unfold Det3 in *.
basic_simpl.
field.
split;auto.
intro Hx; rewrite Hx in *.
replace (0 / S O U V) with 0 in * by (field;auto).
intuition.
Qed.

Lemma free_points_ratio_elimination_6_non_zero_denom: forall O U V A B C D: Point,
  parallel A B C D ->
  C<>D ->
  ~ Col O U V ->
  ~ Col O A C ->
  Col A C D ->
  S O U C * S O V D - S O V C * S O U D <> 0.
Proof.
intros.
assert (~ Col O C D).
  intro.

  assert (Col C A O).
    apply (col_trans_1 C D A O );auto with Geom.
    intuition.
unfold Col in H4.
rewrite (free_points_area_elimination O U V O C D) in * by assumption.
unfold Det3 in *.
basic_simpl.
intro Hx; rewrite Hx in *.
replace (0 / S O U V) with 0 in * by (field;auto).
intuition.
Qed.


Lemma free_points_ratio_elimination_7 : forall O U V A B C D: Point,
  parallel A B C D ->
  C<>D ->
  ~ Col O U V ->
  ~ Col U A C ->
  Col A C D ->
  A**B / C**D = 
 (S O U V * (S O U B - S O U A) - S O U A * S O V B + S O U B * S O V A) /
 (S O U V * (S O U D - S O U C) - S O U C * S O V D + S O U D * S O V C).
Proof.
intros.

rewrite (free_points_ratio_elimination_6 U O V A B C D) by auto with Geom.
assert (S U O C * S U V D - S U V C * S U O D <> 0)
by (apply (free_points_ratio_elimination_6_non_zero_denom U O V A B C D);auto with Geom).

rewrite (free_points_area_elimination O U V U V A) in * by assumption.
rewrite (free_points_area_elimination O U V U V B) in * by assumption.
rewrite (free_points_area_elimination O U V U V C) in * by assumption.
rewrite (free_points_area_elimination O U V U V D) in * by assumption.
unfold Det3 in *.
basic_simpl.
replace (S O V U) with (- S O U V) in * by auto with Geom.
replace (S U O A) with (- S O U A) in * by auto with Geom.
replace (S U O B) with (- S O U B) in * by auto with Geom.
replace (S U O C) with (- S O U C) in * by auto with Geom.
replace (S U O D) with (- S O U D) in * by auto with Geom.
basic_simpl.

set (xc := S O U C) in *.
set (xa := S O U A) in *.
set (xb := S O U B) in *.
set (xd := S O U D) in *.
set (yc := S O V C) in *.
set (ya := S O V A) in *.
set (yb := S O V B) in *.
set (yd := S O V D) in *.
set (X := S O U V) in *.
field.
repeat split;auto.
replace ((0 - - (X * X) - X * xd + X * yd) / X)
with (X -xd +yd) in H4 by (field;auto).
replace ((0 - - (X * X) - X * xc + X * yc) / X)
with (X - xc + yc) in H4 by (field;auto).
replace (-(xc * (X - xd + yd)) - - ((X - xc + yc) * xd))
  with (X * (xd - xc) - xc * yd + xd * yc) in H4 by ring.
auto.
replace (- (xc * ((0 - - (X * X) - X * xd + X * yd) / X)) -
     - ((0 - - (X * X) - X * xc + X * yc) / X * xd))
  with ((- (xc * (- - (X * X) - X * xd + X * yd)) -
- ((- - (X * X) - X * xc + X * yc) * xd)) / X) in H4
     by (field;auto).
intro Hx; rewrite Hx in *.
replace (0 / X) with 0 in * by (field;auto).
intuition.
Qed.

Lemma free_points_ratio_elimination_7_non_zero_denom : 
  forall O U V A B C D: Point,
  parallel A B C D ->
  C<>D ->
  ~ Col O U V ->
  ~ Col U A C ->
  Col A C D ->
  (S O U V * (S O U D - S O U C) - S O U C * S O V D + S O U D * S O V C) <> 0.
Proof.
intros.
assert (S U O C * S U V D - S U V C * S U O D <> 0)
by (apply (free_points_ratio_elimination_6_non_zero_denom U O V A B C D);auto with Geom).
rewrite (free_points_area_elimination O U V U V C) in * by assumption.
rewrite (free_points_area_elimination O U V U V D) in * by assumption.
unfold Det3 in *.
basic_simpl.
replace (S O V U) with (- S O U V) in * by auto with Geom.
replace (S U O A) with (- S O U A) in * by auto with Geom.
replace (S U O B) with (- S O U B) in * by auto with Geom.
replace (S U O C) with (- S O U C) in * by auto with Geom.
replace (S U O D) with (- S O U D) in * by auto with Geom.
basic_simpl.

set (xc := S O U C) in *.
set (xa := S O U A) in *.
set (xb := S O U B) in *.
set (xd := S O U D) in *.
set (yc := S O V C) in *.
set (ya := S O V A) in *.
set (yb := S O V B) in *.
set (yd := S O V D) in *.
set (X := S O U V) in *.
replace ((0 - - (X * X) - X * xd + X * yd) / X)
with (X -xd +yd) in H4 by (field;auto).
replace ((0 - - (X * X) - X * xc + X * yc) / X)
with (X - xc + yc) in H4 by (field;auto).
replace (-(xc * (X - xd + yd)) - - ((X - xc + yc) * xd))
  with (X * (xd - xc) - xc * yd + xd * yc) in H4 by ring.
auto.
Qed.

Lemma free_points_ratio_elimination_8 : forall O U V A B C D: Point,
  parallel A B C D ->
  C<>D ->
  ~ Col O U V ->
  ~ Col V A C ->
  Col A C D ->
  A**B / C**D = 
    ( S O U V * (S O V B - S O V A) + S O V A * S O U B - S O V B * S O U A) /
    ( S O U V * (S O V D - S O V C) + S O V C * S O U D - S O V D * S O U C).
Proof.
intros.
(*
set (X_C := S O U C).
set (X_A := S O U A).
set (X_B := S O U B).
set (X_D := S O U D).
set (Y_C := S O V C).
set (Y_A := S O V A).
set (Y_B := S O V B).
set (Y_D := S O V D).
*)
rewrite (free_points_ratio_elimination_7 O V U A B C D) by auto with Geom.
replace (S O V U) with (- S O U V) by auto with Geom.
field.
replace (- S O U V) with (S O V U) by auto with Geom.
split.
replace (S O U V) with (- S O V U) by auto with Geom.
replace (- S O V U * (S O V D - S O V C) + S O V C * S O U D - S O V D * S O U C)
with    (- (S O V U * (S O V D - S O V C) - S O V C * S O U D + S O V D * S O U C))
 by ring.
Lemma aux: forall x, x<>0 -> -x<>0.
Proof.
auto with field_hints.
Qed. 
apply aux.
apply (free_points_ratio_elimination_7_non_zero_denom O V U A B C D); auto with Geom.
apply (free_points_ratio_elimination_7_non_zero_denom O V U A B C D); auto with Geom.
Qed.

