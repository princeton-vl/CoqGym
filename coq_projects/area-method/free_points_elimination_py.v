(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export pythagoras_difference_lemmas.
Require Export euclidean_constructions_2.
Require Export construction_lemmas_2.
Require Export ratios_elimination_lemmas.

Lemma grid_existence : 
  forall O U, O<>U ->
  exists V, 
  perp O U O V /\ O**U <> 0 /\ O**V <> 0.
Proof.
intros.
assert ( exists Y : Point, on_perp_d Y O U 1).
apply (on_perp_d_ex O U 1 H).
auto with field_hints.
elim H0;intros V HV.
exists V.
unfold on_perp_d in HV.
use HV.
repeat split;auto with Geom.
intro.
assert (O=V) by auto with Geom.
subst.
basic_simpl.
unfold Py in H2.
uniformize_dir_seg.
basic_simpl.
ring_simplify in H2.
assert (U=V).
cases_equality U V.
auto.
assert (U**V<>0).
auto with Geom.
assert (2 * U ** V * U ** V <> 0).
repeat (apply (nonzeromult));auto with Geom.
intuition.
intuition.
Qed.

Ltac construct_grid O U V H := 
 elim grid_existence;let H:= fresh in (
 intros O H; elim H; clear H;intros U H;elim H;clear H;intro V;intros H;decompose [and] H).

Lemma area_grid : forall O U V, perp O U O V -> 
O ** U <> 0 -> O ** V <> 0 ->
 2*2*(S O U V * S O U V) = O**U*O**U*O**V*O**V.
Proof.
intros.
assert ( 2 * 2 * S U O V * S U O V = U ** O * U ** O * O ** V * O ** V).
apply (per_area U O V).
assert (perp U O O V) by auto with Geom.
auto with Geom.
uniformize_signed_areas.
basic_simpl.
ring_simplify_eq.
rewrite H2.
uniformize_dir_seg.
ring.
Qed.

Lemma grid_not_col : forall O U V, perp O U O V -> 
O ** U <> 0 -> O ** V <> 0 -> ~ Col O U V.
Proof.
intros.
intro.
assert (parallel O U O V) by auto with Geom.
assert (~ parallel O U O V) by
(apply (perp_not_parallel);auto with Geom).
intuition.
Qed.

Lemma degen_py_elim : forall O U V, perp O U O V -> 
O ** U <> 0 -> O ** V <> 0 ->
forall A B,  (* ~ Col A O V -> ~ Col B O U -> *)
Py A B A = 2*2*2*(
   (S O V A-S O V B) * (S O V A-S O V B) / (O**V * O**V) +
   (S O U A-S O U B) * (S O U A-S O U B) / (O**U * O**U)).
Proof.
intros.

cases_col A O V.
assert (Col O V A) by auto with Geom.
rewrite H3.
replace ((0 - S O V B) * (0 - S O V B)) with (S O V B  * S O V B) by ring.

replace (S O V A) with 0.
2:auto with Geom.
admit.
cases_col B O U.
admit.

assert ({Y : Point | on_inter_parallel_parallel Y A O U B O V}).
apply (on_inter_parallel_parallel_ex O U A O V B).
apply perp_not_parallel;auto with Geom.
auto.
elim H4;intros M HM;clear H4.

cases_equality M A.
subst M.
unfold on_inter_parallel_parallel in *.
use HM.
assert (parallel O V A B) by auto with Geom.
unfold parallel, S4 in H7.
admit.

cases_equality M B.
admit.

assert (T:=HM).
unfold on_inter_parallel_parallel in HM.
use HM.
assert ( perp M A O V) 
by (apply (perp_para_perp O U O V M A);auto with Geom).
assert (perp M B M A)
by (apply (perp_para_perp O V M A M B);auto with Geom).
assert (per A M B).
assert (perp A M M B) by auto with Geom.
auto with Geom.
unfold per, Py in *.
uniformize_dir_seg.
basic_simpl.
IsoleVar (A ** B * A ** B) H12.
rewrite H12.
basic_simpl.
assert (A ** M / O ** U = S4 A O B V / S4 O O U V).
apply (elim_length_ratio_on_inter_parallel_parallel_2 A O U O U A O V B M);
auto with Geom.
assert (B ** M / O ** V = S4 B O A U / S4 O O V U).
apply (elim_length_ratio_on_inter_parallel_parallel_2 B O V O V B O U A M);
auto with Geom.
unfold on_inter_parallel_parallel in *.
use T;repeat split;auto with Geom.
basic_simpl.
replace (S4 B O A U) with (- S4 O B U A) in * by auto with Geom.
replace (S4 A O B V) with (- S4 O A V B) in * by auto with Geom.
unfold S4 in *.
IsoleVar (A**M) H13.
IsoleVar (B**M) H14.
assert (~ Col O U V).
apply grid_not_col;auto with Geom.
assert ( 2 * 2 * (S O U V * S O U V) = O ** U * O ** U * O ** V * O ** V).
apply area_grid;auto with Geom.
IsoleVar (S O U V * S O U V) H16.
assert (A ** M * A ** M = O ** U * O**U * ( (S O A V + S O V B) * (S O A V + S O V B) / (S O U V * S O U V))).
rewrite H13.
field;auto with Geom.
rewrite H16 in H18.
assert (B ** M * B ** M = O**V * O**V* ((S O B U + S O U A)* (S O B U + S O U A) / (S O V U * S O V U)
)).
rewrite H14.
field;auto with Geom.
uniformize_signed_areas.
basic_simpl.
rewrite H16 in H19.
rewrite H18.
rewrite H19.
field; auto with Geom.
apply nonzeromult;auto with Geom.
Qed.

Lemma py_to_pys : forall A B C,
 Py A B C = 1/2 * (Py A B A + Py B C B - Py A C A).
Proof.
intros.
unfold Py.
uniformize_dir_seg.
basic_simpl.
field;auto with Geom.
Qed.


Lemma py_elim :  forall O U V, perp O U O V -> 
O ** U <> 0 -> O ** V <> 0 ->
forall A B C, 
~ Col A O V -> ~ Col B O U ->
Py A B C = 
(- (2*2*2)* O ** U * O ** U * S O V A * S O V B +
    2*2*2 * O ** U * O ** U * S O V A * S O V C +
    2*2*2 * O ** U * O ** U * S O V B * S O V B -
    2*2*2 * O ** U * O ** U * S O V B * S O V C -
    2*2*2 * O ** V * O ** V * S O U A * S O U B +
    2*2*2 * O ** V * O ** V * S O U A * S O U C +
    2*2*2 * O ** V * O ** V * S O U B * S O U B -
    2*2*2 * O ** V * O ** V * S O U B * S O U C) /
(O ** V * O ** V * O ** U * O ** U).
Proof.
intros.
rewrite py_to_pys.
repeat (rewrite (degen_py_elim O U V H) by auto with Geom).
field;auto with Geom.
Qed.


Ltac elim_pys O U V H1 H2 H3 :=
repeat (rewrite (degen_py_elim O U V H1 H2 H3));
repeat (rewrite (py_elim O U V H1 H2 H3)).

