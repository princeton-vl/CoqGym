(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export pythagoras_difference.

Definition on_perp (A' B C : Point) : Prop := B <> C /\ perp A' B B C /\ S B C A' <> 0.

Definition on_perp_d (Y U V : Point)  (lambda : F) : Prop := 
     U <> V  /\ perp Y U U V /\ lambda * Py U V U = (2+2) * S U V Y /\ lambda <> 0.

Definition on_inter_line_perp (Y R U V P Q : Point) : Prop :=
  Col Y U V /\ perp Y R P Q /\ ~ perp P Q U V.

Lemma proj_ex : forall A P Q, P<>Q -> exists X, on_foot X A P Q.
Proof.
intros.
unfold on_foot.
assert (T:=on_line_dex P Q (Py A P Q/Py P Q P) H).
elim T;clear T.
intros Y HY.
use HY.
exists Y.
repeat split;auto.

unfold perp, Py4.
rewrite col_pyth by assumption.
rewrite H1.
unfold Py.
basic_simpl.
uniformize_dir_seg.
basic_simpl.
field.
replace (P ** Q * P ** Q + P ** Q * P ** Q) with (2*P ** Q * P ** Q) by ring.
repeat apply nonzeromult; auto with Geom.
Qed.




Lemma on_perp_to_on_perp_d : forall A B C : Point,
       on_perp A B C  -> on_perp_d A B C ((2 + 2) * S B C A / Py B C B).
Proof.
intros.
unfold on_perp, on_perp_d in *.
decompose [and] H; clear H.
repeat split; try assumption.
field.
auto with Geom.
replace (2+2) with (2*2) by ring.
repeat apply nonzeromult;auto with Geom.
intro.
assert ( Py B C B * / Py B C B = 0 * Py B C B).
rewrite H.
ring.
replace (Py B C B * / Py B C B) with 1 in H1.
2: field;auto with Geom.
basic_simpl.
intuition.
Qed.

Lemma on_line_d_iff_on_parallel_d : forall A B C r,
 on_line_d A B C r <-> on_parallel_d A B C B (0-r).
Proof.
intros.
unfold on_line_d, on_parallel_d.
unfold parallel, S4, Col.
split.
intros.
decompose [and] H; clear H.
repeat split.
auto.
basic_simpl.
uniformize_signed_areas.
rewrite H0.
ring.
auto.
rewrite H3.
uniformize_dir_seg.
ring.
intros.
decompose [and] H; clear H.
repeat split.
basic_simpl.
uniformize_signed_areas.
rewrite H2;ring.
auto.
uniformize_dir_seg.
rewrite H3;ring.
Qed.

Lemma on_line_iff_on_parallel : forall A B C,
 on_line A B C <-> on_parallel A B C B.
Proof.
intros.
unfold on_line, on_parallel.
unfold parallel, S4, Col.
split.
intros.
decompose [and] H; clear H.
split.
auto.
basic_simpl.
uniformize_signed_areas.
auto.
intros.
decompose [and] H; clear H.
split.
basic_simpl.
uniformize_signed_areas.
auto.
auto.
Qed.

Definition eq_distance A B C D := Py A B A = Py C D C.

Definition harmonic A B C D := A**C / C**B = D**A / D**B.

Definition eq_product A B C D P Q R S := Py A B A * Py C D C = Py P Q P * Py R S R.

Definition tangent O1 A O2 B :=
Py O1 O2 O1 * Py O1 O2 O1 / (2+2) + 
Py O1 A O1   * Py O1 A O1 / (2+2) +  
Py O1 B O1   * Py O1 B O1 / (2+2) -
Py O1 O2 O1 * Py O1 A O1 / 2 -
Py O1 O2 O1 * Py O1 B O1 / 2 -
 Py O1 A O1 * Py O1 B O1 / 2.

Definition m_ratio Y U V r := 1+r<>0 /\ on_parallel_d Y U U V (r/(1+r)).

Definition inversion P Q O A := Py O Q O <> 0 /\ on_line_d P O Q (Py O A O / Py O Q O).

Definition eq_angle A B C D E F := 
  S A B C * Py D E F = S D E F  * Py A B C.

Definition co_circle A B C D :=
  S C A D * Py C B D = S C B D * Py C A D.

Lemma check_co_circle : forall A B C D, 
 co_circle A B C D <-> eq_angle C A D C B D.
Proof.
intros.
unfold co_circle, eq_angle.
intuition.
Qed.

(* TODO remove auxiliary points *)


Definition inter_lc Y U V O N := on_foot N O U V /\ on_parallel_d Y N N U 1.

Definition on_circle Y O P Q' N' :=  inter_lc Y P Q' O N'.
