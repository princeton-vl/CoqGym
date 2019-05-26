(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export pythagoras_difference_lemmas.

Lemma on_perp_d_ex : forall U V r,
 U<>V -> r<> 0 ->
 exists Y, on_perp_d Y U V r.
Proof.
intros.
assert (exists M: Point, ~ Col U V M).
apply build_point_not_collinear_1;auto.

elim H1;intros M HM; clear H1.
elim (proj_ex M U V);[intros N Hn|auto].

cases_equality U N.
subst.
unfold on_foot in *.
use Hn.
clear H3 H4.
assert (N<> M)
 by (intro;subst;auto with Geom).

elim (on_line_dex N M (r * Py N V N / (2*2*S V M N)) H2).
intros Y HY.
exists Y.
unfold on_perp_d.
repeat split;auto.
use HY.
apply (perp_para_perp N M N V Y N);auto with Geom.
use HY.
assert (~ Col V N M) by auto with Geom.
assert (Col N Y M) by auto with Geom.
IsoleVar r H4.
rewrite (A6 N Y M V H2 H5 H6) in H4.
rewrite H4.
uniformize_signed_areas.
field.
split;auto with Geom.
cut (S V M N <> 0).
auto with field_hints.
intro.
rewrite H10 in H8.
basic_simpl.
intuition.
auto with Geom.
repeat apply nonzeromult;auto with Geom.
auto with Geom.

assert (U<>M) by (intro;subst;intuition).

assert (~ Col U M N).
unfold on_foot in *.
use Hn.
assert (N<>M).
intro;subst;intuition.
assert (T:=perp_not_parallel N M U V H3 H4 H6).
intro.
assert (Col N M V).
apply (col_trans_1 N U M V); auto with Geom.
unfold parallel, S4 in T.
rewrite H8 in T.
assert (Col N U M) by auto with Geom.
rewrite H9 in T.
basic_simpl;intuition.

assert (M<>N) by (intro; subst;intuition).

elim (on_parallel_d_ex M N U (-(1)) H4).
2:auto with Geom.
intros B HB.

assert (U<>B).
intro;subst.
unfold on_parallel_d in *.
use HB.
basic_simpl.
assert (M=N).
auto with Geom.
intuition.

elim (on_line_dex U B (r*Py U V U / (2*2*S U V B)) H5).
intros Y HY.
use HY.

exists Y.
unfold on_perp_d.
repeat split; auto.

unfold on_parallel_d in HB.
use HB.
unfold on_foot in *.
use Hn.

assert (perp B U U V).
apply (perp_para_perp M N U V B U H8);auto with Geom.

apply (perp_para_perp U B U V Y U H5); auto with Geom.

assert (~ Col U V B).
intro.
unfold on_parallel_d in HB.
use HB.
unfold on_foot in *.
use Hn.

assert (Col U Y V)
by (apply (col_trans_1 U B Y V);auto with Geom).

assert (Col U Y N)
by (apply (col_trans_1 U V Y N);auto with Geom).


unfold parallel, S4 in H11.
assert (Col U B N).
apply (col_trans_1 U V B N);auto with Geom.
assert (Col B U N) by auto with Geom.
rewrite H18 in H11.
basic_simpl.
assert (Col B M U) by auto with Geom.
assert (Col U M N).
apply (col_trans_1 U B M N);auto with Geom.
intuition.

IsoleVar (r * Py U V U) H7.
rewrite H7.
rewrite (A6 U Y B V H5).
uniformize_signed_areas.
field.
cut (S U V B <> 0).
auto with field_hints.
intuition.
auto with Geom.
auto with Geom.
repeat apply nonzeromult; auto with Geom.
auto with Geom.
Qed.
