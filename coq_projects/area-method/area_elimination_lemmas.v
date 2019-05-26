(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export advanced_parallel_lemmas.
Require Export geometry_tools.

(*********************************************************************)
(*  Elimination Theorems                                               *)
(*********************************************************************)

(* Area elimination *)

Theorem non_zero_denom_on_line_area : forall A B C : Point, on_line A B C -> B <> C.
unfold on_line in |- *.
Proof.
intuition.
Qed.

Theorem non_zero_denom_inter_ll_area :
 forall A B C D E : Point, inter_ll A B C D E -> S4 B D C E <> 0.
Proof.
unfold inter_ll in |- *.
unfold parallel in |- *.
intuition.
Qed.

Theorem non_zero_denom_on_parallel_d_area : forall A B C D : Point, on_parallel A B C D -> C <> D.
Proof.
unfold on_parallel in |- *.
intuition.
Qed.

Theorem non_zero_denom_on_inter_line_parallel_area :
 forall A B C D E G : Point, on_inter_line_parallel A B C D E G -> S4 E C G D <> 0.
Proof.
unfold on_inter_line_parallel in |- *.
unfold parallel in |- *.
intuition.
Qed.

Theorem non_zero_denom_on_inter_parallel_parallel_area :
 forall A B C D E G H : Point, on_inter_parallel_parallel A B C D E G H -> S4 C G D H <> 0.
Proof with Geometry.
unfold on_inter_parallel_parallel in |- *.
unfold parallel in |- *.
intros.
assert (S4 G C H D = - S4 C G D H)...
rewrite H1 in H0.
intuition.
Qed.


Theorem elim_area_on_line_d :
 forall (A B P Q Y : Point) (lambda : F),
 on_line_d Y P Q lambda -> S A B Y = lambda * S A B Q + (1 - lambda) * S A B P.
Proof with Geometry.
intros.
unfold on_line_d in *.
DecompAndAll.
RewriteVar lambda H3...
clear H3.
assert (1 - P ** Y / P ** Q = Y ** Q / P ** Q)...
assert (Y ** P + P ** Q = Y ** Q)...
rewrite <- H1...
assert (P ** Y = - Y ** P)...
rewrite H3; field...
rewrite H1...
replace (S A B Y) with (S Y A B)...
replace (S A B Q) with (S Q A B)...
replace (S A B P) with (S P A B)...
apply l2_9...
Qed.

Theorem elim_area_on_line :
 forall A B P Q Y : Point,
 on_line Y P Q ->
 S A B Y = P ** Y / P ** Q * S A B Q + (1 - P ** Y / P ** Q) * S A B P.
Proof with Geometry.
intros.
assert (on_line_d Y P Q (P ** Y / P ** Q)).
apply on_line_to_on_line_d...
apply elim_area_on_line_d...
Qed.

Theorem elim_area_inter_ll :
 forall A B P Q U V Y : Point,
 inter_ll Y P Q U V ->
 S A B Y = 1 / S4 P U Q V * (S P U V * S A B Q + S Q V U * S A B P). 
Proof with Geometry.
intros.
unfold inter_ll in *.
DecompAndAll.
assert (P <> Q);eauto with Geom.
assert (S Y A B = P ** Y / P ** Q * S Q A B + Y ** Q / P ** Q * S P A B)...
apply l2_9...
unfold parallel in H3.
assert (P ** Y / P ** Q = S P U V / S4 P U Q V)...
assert (Q ** Y / P ** Q = S Q U V / S4 P U Q V)...
replace (Q**Y) with (- Y**Q) in H5.
2:symmetry;Geometry.
uniformize_signed_areas.
IsoleVar (Y ** Q) H5...
rewrite H1.
rewrite H4.
rewrite H5.
field...
Qed.


Theorem elim_area_on_parallel_d :
 forall (A B P Q R Y : Point) (lambda : F),
 on_parallel_d Y R P Q lambda -> 
 S A B Y = S A B R + lambda * S4 A P B Q. 
Proof with Geometry.
intros.
unfold on_parallel_d in H.
DecompAndAll.

cases_equality R Y.
subst R;basic_simpl.
IsoleVar lambda H3...
assert (lambda = 0).
rewrite H3.
field...
rewrite H1.
ring.

assert (parallel R Y P Q)...

assert (Th := on_line_dex_spec_strong_f R Y P Q H1 H)...
DecompExAnd Th T.
assert (R <> T).
unfold not;intro;subst R;basic_simpl...

assert (S A B Y = lambda * S A B T + (1 - lambda) * S A B R).
apply elim_area_on_line_d.
rewrite <- H7 in H3.
unfold on_line_d in *...

assert (S R A B + S Q A B = S T A B + S P A B).
apply l2_11a_strong_strong_strong...
IsoleVar (S T A B) H9.
uniformize_signed_areas.
rewrite H9 in H6.
replace (S4 A P B Q) with (S Q A B - S P A B).
rewrite H6;ring.
unfold S4 in |- *;uniformize_signed_areas;ring.
Qed.

Theorem elim_area_on_parallel :
 forall A B P Q R Y : Point,
 on_parallel Y R P Q -> 
 S A B Y = S A B R + R ** Y / P ** Q * S4 A P B Q.
Proof with auto.
intros. 
assert (on_parallel_d Y R P Q (R ** Y / P ** Q)).
apply on_parallel_to_on_parallel_d...
apply elim_area_on_parallel_d...
Qed.


(** We prove parallel transitivity using the elimination lemmas *)

Lemma parallel_transitivity : forall A B C D E F, 
  C<> D -> 
  parallel A B C D -> 
  parallel C D E F -> 
  parallel A B E F.
Proof.
intros.

cases_equality A B.

subst;Geometry.

assert (on_parallel E F C D).
unfold on_parallel;intuition Geometry.
assert (on_parallel_d E F C D (F ** E / C ** D)).
apply on_parallel_to_on_parallel_d.
assumption.
set (F ** E / C ** D).
unfold parallel,S4.
replace (S A E B) with (S B A E) by Geometry.
assert (T: S B A E = S B A F + f * S4 B C A D). 
apply (elim_area_on_parallel_d B A C D F E).
auto.
rewrite T.
unfold S4.
replace (S B C A) with (S A B C) by Geometry.
assert (on_parallel_d C D A B ( D ** C / A ** B)). 
unfold on_parallel_d.
repeat split;Geometry.
field;Geometry.
set (D ** C / A ** B).
replace (S A B C) with (S A B D + f0 * S4 A A B B).
basic_simpl.
uniformize_signed_areas.
ring.
symmetry.
apply elim_area_on_parallel_d.
assumption.
Qed.

Lemma elim_area_on_inter_line_parallel :
    forall P Q R U V Y A B : Point,
    on_inter_line_parallel Y R U V P Q ->
    R <>Y ->
    S A B Y = (S4 P U Q R * S A B V - S4 P V Q R * S A B U) / S4 P U Q V.
Proof with Geometry.
intros.
unfold on_inter_line_parallel in H.
DecompAndAll.
assert (P<>Q);eauto with Geom.
assert (parallel R Y P Q)...

assert (~ Col R Y Q).
eapply diff_not_col_par_not_col.
2:apply H1.
auto.
Geometry.

assert (Th:= (on_line_dex_spec_strong R Y P Q H4 H H6)).
DecompExAnd Th T.
assert (R<>T).
unfold not;intro;subst T.
basic_simpl...

assert  (~ parallel U V T R).
unfold not;intro.
unfold parallelogram in *.
DecompAndAll.
assert (parallel T R P Q)...
assert (parallel U V P Q).
eapply parallel_transitivity.
apply H7.
Geometry.
Geometry.
intuition.

assert ((S A B Y) =  1 / (S4 U T V R) * ((S U T R)*(S A B V) + (S V R T)*(S A B U))). 
apply elim_area_inter_ll...
unfold inter_ll...

assert ((S4 U R V T) = (S4 U P V Q)).
apply l2_11b...
assert ((S U R T) = (S4 U P R Q)).
apply l2_12b...
assert ((S V R T) = (S4 V P R Q)).
apply l2_12b...

rewrite H12.

replace (S4 P U Q V) with (- S4 U P V Q)...
rewrite <- H13.
replace (S4 U R V T) with (- S4 U T V R)...
replace  (S U T R) with (- S U R T)...
rewrite H14.
rewrite H15.
replace (S4 V P R Q) with (- S4 P V Q R)...
replace (S4 U P R Q) with (- S4 P U Q R)...
field.
assert (S4 U T V R<>0)...
Qed.

