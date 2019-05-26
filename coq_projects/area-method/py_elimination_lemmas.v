(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export pythagoras_difference_lemmas.
Require Export ratios_elimination_lemmas.

Theorem elim_py_on_parallel_d_middle :
 forall (A B W U V Y : Point) (r : F),
 on_parallel_d Y W U V r -> 
 Py A Y B = Py A W B + r* (Py A V B - Py A U B  + 2* Py W U V  )-r*(1-r)*(Py U V U).
Proof.
intros.
cases_equality W Y.

subst.
unfold on_parallel_d in H.
use H.
basic_simpl.
symmetry in H3.
assert (r= 0).
IsoleVar r H3.
rewrite H3.
field;auto with Geom.
auto with Geom.
rewrite H.
basic_simpl;auto.

assert (parallel W Y U V).
unfold on_parallel_d in H.
use H.
auto with Geom.
elim ( on_line_dex_spec_strong_f W Y U V H1 H0).
intros S HS.
use HS.

assert (Py A Y B =
       W ** Y / W ** S * Py A S B + Y ** S / W ** S * Py A W B -
       W ** Y / W ** S * (Y ** S / W ** S) * Py W S W).
apply  (l3_5_py A B W S Y).
unfold not;intro;subst.
basic_simpl.
assert (U=V) by auto with Geom.
unfold on_parallel_d in *.
use H;auto.
auto with Geom.

assert (W ** Y / W ** S = r).
unfold on_parallel_d in *.
use H.
rewrite H9.
rewrite H4.
field.
auto with Geom.
rewrite H6 in H3.
assert ( Y ** S / W ** S  = 1 - r).
unfold on_parallel_d in *.
use H.
replace (Y**S) with (Y**W + W**S) by auto with Geom.
uniformize_dir_seg.
rewrite H10.
rewrite H4.
field;auto with Geom.
rewrite H7 in H3.
assert (weak_3_parallelogram U V S W) by auto with Geom.

assert  (T:= l_27_c U V S W A B H8).

revert T.
revert H3.
uniformize_pys.
intros.
IsoleVar (Py A S B) T.
rewrite T in H3.
rewrite H3.
replace (Py W S W) with (Py U V U).
2:unfold Py;basic_simpl;uniformize_dir_seg;rewrite H4;ring.
ring.
Qed.

Theorem elim_py_on_parallel_d_right :
 forall (A B W U V Y : Point) (r : F),
 on_parallel_d Y W U V r -> 
 Py A B Y = Py A B W + r  * (Py A B V - Py A B U).
Proof.
intros.

cases_equality W Y.
subst.
unfold on_parallel_d in H.
use H.
basic_simpl.
symmetry in H3.
assert (r= 0).
IsoleVar r H3.
rewrite H3.
field;auto with Geom.
auto with Geom.
rewrite H.
basic_simpl;auto.

assert (parallel W Y U V).
unfold on_parallel_d in H.
use H.
auto with Geom.
elim ( on_line_dex_spec_strong_f W Y U V H1 H0).
intros S HS.
use HS.
assert (Py A B Y = W ** Y / W ** S * Py A B S + Y ** S / W ** S * Py A B W).
apply (l_28_b A B W S Y).
 intro;subst.
 basic_simpl.
 assert (U=V) by auto with Geom.
 subst. 
 unfold on_parallel_d in H.
 intuition.
 auto with Geom.
unfold on_parallel_d in H.
use H.
assert (W ** Y / W ** S = r).
rewrite H9.
rewrite H4.
field.
auto with Geom.
rewrite H in H3.
assert ( Y ** S / W ** S  = 1 - r).
replace (Y**S) with (Y**W + W**S) by auto with Geom.
uniformize_dir_seg.
rewrite H9.
rewrite H4.
field;auto with Geom.
rewrite H7 in H3.

assert (weak_3_parallelogram U V S W) by auto with Geom.

assert (T:= l_27_a U V S W B A H10).
revert T.
revert H3.
uniformize_pys.
intros.
IsoleVar (Py S B A) T.
rewrite T in H3.
rewrite H3.
ring.
Qed.

Theorem elim_py_on_parallel_d_left_right :
 forall (B W U V Y : Point) (r : F),
 on_parallel_d Y W U V r -> 
 Py Y B Y = Py W B W + r * r * Py V B V - 2 * r * r * Py V B U + r * r * Py U B U +
2 * r * Py V B W - 2 * r * Py U B W.
Proof.
intros.
rewrite (elim_py_on_parallel_d_right Y B W U V Y r H).
rewrite pyth_sym.
replace ( Py Y B V) with (Py V B Y) by (apply pyth_sym;auto).
replace ( Py Y B U) with (Py U B Y) by (apply pyth_sym;auto).
rewrite (elim_py_on_parallel_d_right W B W  U V Y r H).
rewrite (elim_py_on_parallel_d_right V B W  U V Y r H).
rewrite (elim_py_on_parallel_d_right U B W  U V Y r H).
replace (Py W B U) with (Py U B W) by auto with Geom.
replace (Py W B V) with (Py V B W) by auto with Geom.
replace (Py U B V) with (Py V B U) by auto with Geom.
ring.
Qed.

Theorem elim_py_on_line_d_right :
 forall (A B P Q Y : Point) (f : F),
 on_line_d Y P Q f ->
 Py A B Y = f * Py A B Q + (1 - f) * Py A B P.
Proof.
intros.
apply -> on_line_d_iff_on_parallel_d in H.
rewrite (elim_py_on_parallel_d_right A B P Q P Y (0-f) H).
ring.
Qed.

Theorem elim_py_on_line_d_left_right :
 forall (A P Q Y : Point) (f : F),
 on_line_d Y P Q f -> Py Y A Y = f* (f * Py Q A Q + (1 - f) * Py Q A P) +
(1 - f) * (f * Py P A Q + (1 - f) * Py P A P) .
Proof.
intros.
rewrite (elim_py_on_line_d_right Y A P Q Y f H).
rewrite pyth_sym.
replace ( Py Y A P) with (Py P A Y) by (apply pyth_sym;auto).
rewrite (elim_py_on_line_d_right Q A P Q Y f H).
rewrite (elim_py_on_line_d_right P A P Q Y f H).
auto.
Qed.

Lemma elim_py_midpoint_left_right : forall A B C M : Point, 
on_line_d M B C (1 / 2) ->
       Py M A M = - (1)/(2+2) * (Py B C B - 2* Py A C A - 2 *Py A B A).
Proof.
intros.
rewrite (elim_py_on_line_d_left_right A B C M (1/2)) by auto.
field_simplify.
unfold Py.
basic_simpl.
uniformize_dir_seg.
field_simplify_eq.
auto.
solve_conds.
solve_conds.
solve_conds.
Qed.

Theorem elim_py_on_line_right :
 forall A B P Q Y : Point,
 on_line Y P Q ->
 Py A B Y = P ** Y / P ** Q * Py A B Q + (1 - P ** Y / P ** Q) * Py A B P.
Proof with Geometry.
intros.
assert (on_line_d Y P Q (P ** Y / P ** Q)).
apply on_line_to_on_line_d...
apply elim_py_on_line_d_right...
Qed.

Theorem elim_py_on_line_d_middle :
 forall A B P Q Y r,
 on_line_d Y P Q r ->
 Py A Y B = - Py A P B * r + Py A P B + r * r * Py Q P Q + r * Py A Q B- r * Py Q P Q .
Proof.
intros.
apply -> on_line_d_iff_on_parallel_d in H.
rewrite (elim_py_on_parallel_d_middle A B P Q P Y (0-r) H).
replace (Py P Q P) with (Py Q P Q) by auto with Geom.
ring.
Qed.

(* shows that we need A<>B in elim_py_on_line_d_middle
Lemma essai : forall A P Q Y : Point, forall r:F,
 r<> 0 -> on_line_d Y P Q r -> False.
Proof.
intros.
assert (Py A Y A = Py A Y A).
reflexivity.
rewrite (elim_py_on_line_d_middle A A P Q Y r) in H1 at 1.
2:auto.
replace (Py A Y A) with (Py Y A Y) in H1 by auto with Geom.
rewrite (elim_py_on_line_d_left_right A P Q Y r) in H1 by auto.
unfold Py in *.
uniformize_dir_seg.
basic_simpl.
field_simplify_eq in H1.
set (
- (2) * A ** P * A ** P * r + 2 * A ** P * A ** P +
2 * r * r * P ** Q * P ** Q) in H1.
set (2 * r * A ** Q * A ** Q) in H1.
assert (f + f0 - (f  + f0) = f - 2 * r * P ** Q * P ** Q + f0 - (f  + f0)).
rewrite H1.
ring.
ring_simplify in H2.
assert (P**Q <> 0).
unfold on_line_d in H0.
use H0.
auto with Geom.
assert (P ** Q * P ** Q <> 0).
apply nonzeromult; auto.
cut (r<>0).
intro.
assert (- (2) * r * P ** Q * P ** Q <> 0).
repeat (apply nonzeromult);
auto with Geom.
rewrite <- H2 in H6.
intuition.
auto.
Qed.
*)

Theorem elim_py_on_line_middle :
 forall A B P Q Y : Point,
 on_line Y P Q ->
 Py A Y B = Py A P B + P ** Y / Q ** P * (Py A P B - Py A Q B + 2* Py Q P Q) -
P ** Y / Q ** P * (1 - P ** Y / Q ** P) * Py Q P Q.
Proof.
intros.
apply -> on_line_iff_on_parallel in H.
apply on_parallel_to_on_parallel_d in H.
rewrite (elim_py_on_parallel_d_middle A B P Q P Y (P ** Y / Q ** P) H).
replace (Py P Q P) with (Py Q P Q) by auto with Geom.
ring.
Qed.

Theorem elim_py_inter_ll_right :
 forall A B P Q U V Y : Point,
 inter_ll Y P Q U V ->
 Py A B Y = 1 / S4 P U Q V * (S P U V * Py A B Q + S Q V U * Py A B P).
Proof.
intros.
unfold inter_ll in H.
decompose [and] H; clear H.
assert (P<>Q).
eauto with Geom.
rewrite (l_28_b A B P Q Y).
3:auto with Geom.
replace (Y ** Q / P ** Q) with (- (Q ** Y/ P**Q )).
rewrite (co_side_bis U V P Q Y H3) by auto with Geom.
replace (P ** Y / P ** Q) with (- (P ** Y / Q ** P)).
rewrite (co_side_bis V U Q P Y).
replace (S4 Q V P U) with (S4 P U Q V) by (auto with Geom).
uniformize_signed_areas.
field.
auto with Geom.
unfold not;intro.
assert (parallel P Q U V).
auto with Geom.
intuition.
auto with Geom.
auto with Geom.
rewrite dirseg_4 at 1.
ring.
auto with Geom.
rewrite dirseg_3 at 1.
ring.
auto with Geom.
auto.
Qed.

Theorem elim_py_inter_ll_right_invariant :
 forall A B P Q U V Y : Point,
 inter_ll Y P Q U V -> S4 P U Q V <> 0.
Proof.
intros.
unfold inter_ll, parallel in H.
intuition.
Qed.

Theorem elim_py_inter_ll_left_right :
 forall B P Q U V Y : Point,
 inter_ll Y P Q U V ->
 Py Y B Y = 1 / S4 P U Q V *
(S P U V * (1 / S4 P U Q V * (S P U V * Py Q B Q + S Q V U * Py Q B P)) +
 S Q V U * (1 / S4 P U Q V * (S P U V * Py P B Q + S Q V U * Py P B P))).
Proof.
intros.
rewrite (elim_py_inter_ll_right Y B P Q U V Y H).
replace (Py Y B P) with (Py P B Y) by auto with Geom.
replace (Py Y B Q) with (Py Q B Y) by auto with Geom.
rewrite (elim_py_inter_ll_right Q B P Q U V Y H).
rewrite (elim_py_inter_ll_right P B P Q U V Y H).
auto.
Qed.

Theorem elim_py_inter_ll_left_right_invariant :
 forall B P Q U V Y : Point,
 inter_ll Y P Q U V -> S4 P U Q V <> 0.
Proof.
intros.
unfold inter_ll, parallel in H.
intuition.
Qed.

Theorem elim_py_inter_ll_middle :
 forall A B P Q U V Y : Point,
 inter_ll Y P Q U V ->
 Py A Y B = - (S P V U / S4 P U Q V) * Py A Q B + - (S Q U V / S4 P U Q V) * Py A P B -
- (S P V U / S4 P U Q V) * - (S Q U V / S4 P U Q V) * Py P Q P.
Proof.
intros.
unfold inter_ll in H.
decompose [and] H; clear H.
assert (P<>Q).
eauto with Geom.
rewrite (l3_5_py A B P Q Y) by auto.
replace (Y ** Q / P ** Q) with (- (Q ** Y/ P**Q )).
rewrite (co_side_bis U V P Q Y H3) by auto with Geom.
replace (P ** Y / P ** Q) with (- (P ** Y / Q ** P)).
rewrite (co_side_bis V U Q P Y).
replace (S4 Q V P U) with (S4  P U Q V) by auto with Geom.
auto.
intro.
assert (parallel P Q U V); auto with Geom.
auto with Geom.
auto with Geom.
rewrite dirseg_4 at 1.
ring.
auto with Geom.
rewrite dirseg_3 at 1.
ring.
auto with Geom.
Qed.

Theorem elim_py_inter_ll_middle_invariant :
 forall A B P Q U V Y : Point,
 inter_ll Y P Q U V -> S4  P U Q V <> 0.
Proof.
exact elim_py_inter_ll_right_invariant.
Qed.

Theorem elim_py_on_foot_right :
 forall A B P U V Y : Point,
 on_foot Y P U V ->
 Py A B Y = (Py P U V * Py A B V + Py P V U * Py A B U) / (Py U V U).
Proof.
intros.
unfold on_foot in *.
use H.
rewrite (l_28_b A B U V) by auto with Geom.
assert (U**Y/U**V = Py P U V / Py U V U).
apply l_24_c_on_foot.
unfold on_foot;auto.
assert (V**Y/V**U = Py P V U / Py V U V).
apply l_24_c_on_foot.
unfold on_foot;auto with Geom.
replace (Y ** V / U ** V) with (V**Y/V**U) by auto with Geom.
rewrite H.
rewrite H1.
replace (Py V U V) with (Py U V U) by auto with Geom.
field;auto with Geom.
Qed.

Theorem elim_py_on_foot_left_right :
 forall B P U V Y : Point,
 on_foot Y P U V ->
 Py Y B Y = 
 (Py P U V * Py P U V * Py V B V + Py P U V * Py P V U * Py V B U +
 Py P U V * Py P V U * Py U B V + Py P V U * Py P V U * Py U B U) / (Py U V U *  Py U V U).
Proof.
intros.
rewrite (elim_py_on_foot_right Y B P U V Y H).
replace (Py Y B V) with (Py V B Y) by auto with Geom.
replace (Py Y B U) with (Py U B Y) by auto with Geom.
rewrite (elim_py_on_foot_right V B P U V Y H).
rewrite (elim_py_on_foot_right U B P U V Y H).
field.
unfold on_foot in H.
use H.
unfold Py.
basic_simpl.
uniformize_dir_seg.
replace (U ** V * U ** V + - U ** V * - U ** V) with (2* U ** V * U ** V) by ring.
repeat (apply nonzeromult);auto with Geom.
Qed.

Theorem elim_py_on_foot_left_right_invariant :
forall B P U V Y : Point,
 on_foot Y P U V -> (Py U V U *  Py U V U) <> 0.
Proof.
intros.
unfold on_foot in H.
use H.
unfold Py.
basic_simpl.
uniformize_dir_seg.
replace (U ** V * U ** V + - U ** V * - U ** V) with (2* U ** V * U ** V) by ring.
repeat (apply nonzeromult);auto with Geom.
Qed.

Theorem elim_py_on_foot_right_invariant :
 forall A B P U V Y : Point,
 on_foot Y P U V -> Py U V U <> 0.
Proof.
intros.
unfold on_foot in *.
unfold Py.
uniformize_dir_seg.
basic_simpl.
 replace (U ** V * U ** V + U ** V * U ** V) with
(2 * U ** V * U ** V) by ring.
decompose [and] H; clear H.
repeat apply nonzeromult;auto with Geom.
Qed.

Theorem elim_py_on_foot_middle :
 forall A B P U V Y : Point,
 on_foot Y P U V ->
 Py A Y B = (Py P U V / Py U V U) * Py A V B + 
                  (Py P V U) / (Py  U V U) * Py A U B - 
                  (Py P U V * Py P V U) / Py U V U.
Proof.
intros.
rewrite (l3_5_py A B U V) by
 (unfold on_foot in  *;intuition).
assert (U**Y/U**V = Py P U V / Py U V U).
apply l_24_c_on_foot.
unfold on_foot;auto.
assert (V**Y/V**U = Py P V U / Py V U V).
apply l_24_c_on_foot.
unfold on_foot in *;intuition.
rewrite H0.
unfold on_foot in *;use H.
replace (Y ** V / U ** V) with (V**Y/V**U) by auto with Geom.
rewrite H1.
replace (Py V U V) with (Py U V U).
field.
auto with Geom.
auto with Geom.
Qed.

Theorem elim_py_on_foot_middle_invariant :
 forall A B P U V Y : Point,
 on_foot Y P U V -> Py U V U <> 0.
Proof.
exact elim_py_on_foot_right_invariant.
Qed.

Theorem elim_py_on_perp_d_right :
forall A B P Q Y : Point, forall r: F,
on_perp_d Y P Q r ->
Py A B Y = Py A B P - (2+2) * r * S4 P A Q B.
Proof.
intros.
unfold on_perp_d in H.
use H.
assert (P<>Y).
intro;subst;basic_simpl.
IsoleVar (Py Y Q Y) H1.
replace (0/r) with 0 in H1 by (field;auto with Geom).
intuition.

elim (proj_ex A P Y H).
intros A1 HA1.
elim (proj_ex B P Y H).
intros B1 HB1.

assert (Py4 B P A Y / Py Y P Y = S4 P A Q B / S P Q Y).

replace (Py4 B P A Y) with (Py4 B1 P A1 Y).

assert (parallel A1 B1 P Y).
   unfold on_foot in *.
   use HA1.
   use HB1.
   cut (parallel Y P A1 B1).
   auto with Geom.
   unfold parallel, S4.
   unfold Col in *.
   uniformize_signed_areas.
   rewrite H6, H9.
   ring.

replace (Py Y P Y) with (Py P Y P) by auto with Geom.
rewrite <- (l3_10b A1 B1 P Y) by assumption.

replace (A1 ** B1 / P ** Y) with ((S4 P A1 Q B1) / (S P Q Y)).
replace (S4 P A1 Q B1) with (S4 P A Q B).
auto.
unfold S4.
unfold on_foot in *.
use HA1.
use HB1.

assert (parallel P Q B B1).
apply (perp_perp_para P Q Y P B B1);auto with Geom.
assert (parallel P Q A A1).
apply (perp_perp_para P Q Y P A A1);auto with Geom.
unfold parallel, S4 in *.
uniformize_signed_areas.
IsoleVar (S P A Q) H12;rewrite H12.
IsoleVar (S P B Q) H9;rewrite H9.
ring.
unfold S4.
replace (A1**B1) with (A1**P + P**B1).
2:apply chasles.
assert (~ (Col P Q Y)).
intro.
rewrite H5 in H1.
basic_simpl.
IsoleVar r H1.
replace (0/ Py P Q P) with 0 in H1.
intuition.
field;auto with Geom.
auto with Geom.

replace ((A1 ** P + P ** B1) / P ** Y) with (- (P**A1 / P**Y) + P ** B1/ P**Y).
2:uniformize_dir_seg;field;auto with Geom.
rewrite (A6 P A1 Y Q H).
rewrite (A6 P B1 Y Q H).
uniformize_signed_areas.
field;solve_conds;auto with Geom.
auto with Geom.
unfold on_foot in *.
use HA1.
use HB1.
auto with Geom.
auto with Geom.
unfold on_foot in *.
use HA1.
use HB1.
auto with Geom.
unfold on_foot in *.
use HA1.
use HB1.
assert (Col P A1 B1).
apply (col_trans_1 P Y A1 B1 H11);auto with Geom.
auto with Geom.

unfold Py4.
unfold on_foot in *.
use HA1.
use HB1.
unfold perp, Py4 in *.
IsoleVar (Py A1 P Y) H3.
IsoleVar (Py B1 P Y) H5.
rewrite H3, H5.
ring.

(* ** *)
assert (T:=herron_qin P Q Y).
unfold perp, Py4 in H2.
basic_simpl.
replace (Py Q P Y) with 0 in T
 by (replace (Py Q P Y) with (Py Y P Q) by auto with Geom;auto).
basic_simpl.
assert (Py Y P Y = (2*2)*r* S P Q Y).
IsoleVar r H1.
rewrite H1.
field_simplify_eq.
2:auto with Geom.
2:auto with Geom.
replace (2 * (2 * (2 * 2)) * S P Q Y * S P Q Y) with 
        ((2 * (2 * (2 * 2))) * (S P Q Y * S P Q Y)) by ring.
rewrite T.
uniformize_pys.
field;solve_conds.
replace (Py A B Y) with (Py A B P - Py4 B P A Y).
IsoleVar (Py4 B P A Y) H3.
rewrite H3.
rewrite H5.
field.
2:auto with Geom.
intro.
assert (Col Y P Q) by auto with Geom.
rewrite col_pyth in H2 by assumption.
IsoleVar (P**Q) H2.
2:solve_conds;auto with Geom.
replace (0 / (2 * P ** Y)) with (0) in H2.
2:field;solve_conds;auto with Geom.
assert (P=Q) by auto with Geom.
intuition.

replace (Py4 B P A Y) with (- Py4 Y B P A) by auto with Geom.

unfold  Py4.
uniformize_pys.
ring.
Qed.

Theorem elim_py_on_perp_d_middle :
forall A B U V Y : Point, forall r: F,
on_perp_d Y U V r ->
Py A Y B = Py A U B + r * r * Py U V U - (2+2)*r*(S A U V + S B U V).
Proof.
intros.
rename U into P.
rename V into Q.
replace (Py A Y B) with (Py A P B - Py A P Y - Py B P Y + Py Y P Y)
       by (unfold Py; uniformize_dir_seg;basic_simpl;ring).
rewrite (elim_py_on_perp_d_right A P P Q Y r H).
rewrite (elim_py_on_perp_d_right B P P Q Y r H).
basic_simpl.
unfold on_perp_d in H.
use H.
assert (T:=herron_qin P Q Y).
unfold perp in H2.
unfold Py4 in H2.
basic_simpl.
replace (Py Q P Y) with (Py Y P Q) in * by auto with Geom.
rewrite H2 in T.
basic_simpl.
replace (Py P Y P) with (Py Y P Y) in  * by auto with Geom.
IsoleVar (Py Y P Y) T.
2:auto with Geom.
IsoleVar r H1.
rewrite H1.
rewrite T.
uniformize_signed_areas.
field;solve_conds.
auto with field_hints.
solve_conds.
auto with field_hints.
Qed.

(* elimination of area for euclidean constructions *)

Theorem elim_area_on_perp_d :
forall A B U V Y : Point, forall r: F,
on_perp_d Y U V r ->
S A B Y = S A B U - r / (2+2)  * Py4 U A V B.
Proof.
intros A B U V Y r.
intros.

assert (S A B Y = S A B U + S A U Y + S U B Y) by auto with Geom.
rewrite H0.

assert (Hyuv :~ Col Y U V).
unfold on_perp_d in H.
use H.

intro.
assert (Col U V Y) by auto with Geom.
rewrite H4 in H2.
basic_simpl.
IsoleVar r H2.
replace (0 / Py U V U) with 0 in H2.
2:field;auto.
2:auto with Geom.
intuition.

elim (proj_ex A U V).
intros A1 HA1.
2:unfold on_perp_d in H;intuition.

assert (S U A Y = Py A U V / Py U V U * S U V Y).

assert (S U A Y / S U  V Y = S U A1 Y / S U V Y).
replace (S U A Y) with (S U A1 Y).
auto.

unfold on_foot in *.
use HA1.
unfold on_perp_d in *.
use H.
assert (parallel A1 A Y U).
apply (perp_perp_para A1 A U V Y U);auto with Geom.
assert (parallel Y U A1 A) by auto with Geom.
unfold parallel, S4 in H7.
uniformize_signed_areas.
IsoleVar (S Y A1 U) H7.
rewrite H7.
ring.

assert ( S U A1 Y / S U V Y = U**A1 / U**V).

rewrite (A6 U A1 V Y).
uniformize_signed_areas.
auto with Geom.
unfold on_perp_d in H.
use H;auto.
unfold on_perp_d in H.
use H.
auto.
unfold on_foot in *.
use HA1.
auto with Geom.

assert (U**A1 / U**V = Py A1 U V / Py U V U).
rewrite col_pyth.
unfold Py.
uniformize_dir_seg.
basic_simpl.
replace (U ** V * U ** V + U ** V * U ** V) with (2*U**V*U**V) by ring.
field;solve_conds;unfold on_perp_d in *;auto with Geom.
unfold on_perp_d in *;use H;auto with Geom.
unfold on_foot in *;use HA1;auto with Geom.
assert (Py A1 U V = Py A U V).

unfold on_foot in *.
use HA1.
unfold perp, Py4 in H4.
IsoleVar (Py A1 U V) H4.
rewrite H4.
ring.

rewrite H2 in H1.
rewrite H3 in H1.
rewrite H4 in H1.
IsoleVar (S U A Y) H1.
rewrite H1.
field.
unfold on_perp_d in *.
intuition.

auto with Geom.

(* cases B *)
assert (S U B Y = Py B U V / Py U V U * S U V Y).

elim (proj_ex B U V).
intros B1 HB1.
2:unfold on_perp_d in H;intuition.

assert (S U B Y / S U  V Y = S U B1 Y / S U V Y).
replace (S U B Y) with (S U B1 Y).
auto.

unfold on_foot in *.
use HB1.
unfold on_perp_d in *.
use H.
assert (parallel B1 B Y U).
apply (perp_perp_para B1 B U V Y U);auto with Geom.
assert (parallel Y U B1 B) by auto with Geom.
unfold parallel, S4 in H8.
uniformize_signed_areas.
IsoleVar (S Y B1 U) H8.
rewrite H8.
ring.

assert ( S U B1 Y / S U V Y = U**B1 / U**V).

rewrite (A6 U B1 V Y).
uniformize_signed_areas.
auto with Geom.
unfold on_perp_d in H.
use H;auto.
unfold on_perp_d in H.
use H.
auto.
unfold on_foot in *.
use HB1.
auto with Geom.

assert (U**B1 / U**V = Py B1 U V / Py U V U).
rewrite col_pyth.
unfold Py.
uniformize_dir_seg.
basic_simpl.
replace (U ** V * U ** V + U ** V * U ** V) with (2*U**V*U**V) by ring.
field;solve_conds;unfold on_perp_d in *;auto with Geom.
unfold on_perp_d in *;use H;auto with Geom.
unfold on_foot in *;use HB1;auto with Geom.
assert (Py B1 U V = Py B U V).

unfold on_foot in *.
use HB1.
unfold perp, Py4 in H5.
IsoleVar (Py B1 U V) H5.
rewrite H5.
ring.

rewrite H3 in H2.
rewrite H4 in H2.
rewrite H5 in H2.
IsoleVar (S U B Y) H2.
rewrite H2.
field.
unfold on_perp_d in *.
intuition.

auto with Geom.

(* *** *)
assert (S U A Y = r / (2+2) * Py A U V).
rewrite H1.
unfold on_perp_d in H.
use H.
IsoleVar  (S U V Y) H4.
rewrite H4.
field;solve_conds.
auto with Geom.
replace (2+2) with (2*2) by ring.
solve_conds.
assert (S U B Y = r / (2+2) * Py B U V).
unfold on_perp_d in H.
use H.
rewrite H2.
IsoleVar  (S U V Y) H5.
rewrite H5.
field;solve_conds.
auto with Geom.
replace (2+2) with (2*2) by ring.
solve_conds.

replace (S A U Y) with (- S U A Y) by auto with Geom.
rewrite H3, H4.
replace (Py4 U A V B) with( Py A U V - Py B U V).
ring.
symmetry.
replace ( Py A U V - Py B U V) with  (Py4 A U B V) by auto.
auto with Geom.
Qed.

Theorem elim_py_on_perp_d_left_right :
forall B U V Y : Point, forall r: F,
on_perp_d Y U V r ->
Py Y B Y = Py U B U - (2 + 2) * r * S U V B -
(2 + 2) * r * (0 - r / (2 + 2) * Py U V U + S U V B).
Proof.
intros.
rewrite (elim_py_on_perp_d_right Y B U V Y r H).
replace (Py Y B U) with (Py U B Y) by auto with Geom.
rewrite (elim_py_on_perp_d_right U B U V Y r H).
unfold S4.
basic_simpl.
replace (S U Y V) with (S V U Y) by auto with Geom.
rewrite (elim_area_on_perp_d V U U V Y r H).
unfold Py4.
basic_simpl.
auto.
Qed.


Theorem elim_area_on_foot :
forall A B P U V Y : Point,
 on_foot Y P U V ->
 S A B Y = (Py P U V * S A B V + Py P V U * S A B U) / (Py U V U).
Proof.
intros.
unfold on_foot in *.
use H.
replace (S A B Y) with (S Y A B) by auto with Geom.
rewrite (l2_9 A B U V Y) by auto with Geom.
assert (U**Y/U**V = Py P U V / Py U V U).
apply l_24_c_on_foot.
unfold on_foot;auto.
assert (V**Y/V**U = Py P V U / Py V U V).
apply l_24_c_on_foot.
unfold on_foot;auto with Geom.
replace (Y ** V / U ** V) with (V**Y/V**U) by auto with Geom.
rewrite H.
rewrite H1.
replace (Py V U V) with (Py U V U) by auto with Geom.
uniformize_signed_areas.
field;auto with Geom.
Qed.

Theorem elim_area_on_foot_invariant :
forall A B P U V Y : Point,
 on_foot Y P U V ->
 Py U V U <> 0.
Proof.
exact elim_py_on_foot_right_invariant.
Qed.

(* elimination of ratios for euclidean constructions *)
(* the condition A<>Y is required *)

Theorem elim_ratio_on_foot_a :
forall Y P U V A C D : Point,
on_foot Y P U V ->
Col A U V ->
parallel A Y C D ->
C <> D ->
A <> Y ->
A**Y / C**D = Py4 P C A D / Py C D C.
Proof.
intros.

cases_equality A U.
subst U.
cases_equality A V.
subst V.
unfold on_foot in H.
use H;intuition.
clear H0.
unfold on_foot in H.
use H.

pose (d := C**D/A**V).
assert ({T : Point | Col T A V /\ A ** T = d * A**V}).
apply (on_line_dex A V);assumption.
elim H;intros T HT; clear H.
use HT.
unfold d in H5.

assert (A**T = C**D).
rewrite H5.
field;auto with Geom.
rewrite <- H8.
clear H5.
rewrite ( l_24_b A T P Y).
replace (2 * A ** T * A ** T) with (Py A T A)
 by (unfold Py;basic_simpl;uniformize_dir_seg;ring).
replace (Py A T A) with (Py C D C) by
(unfold Py;
uniformize_dir_seg;
rewrite H8;
ring).
replace (Py P A T) with (Py4 P C A D).
auto.
rewrite (l3_8_a A T D C P);auto.

apply parallel_side_eq_weak_weak_weak_para;auto with Geom.
assert (Col A Y T).
apply (col_trans_1 A V Y T H4); auto with Geom.

cut ( parallel C D A T).
auto with Geom.
apply (parallel_transitivity C D A Y A T);auto with Geom.
unfold parallel, S4;basic_simpl.
auto.

apply (col_trans_1 A V Y T H7);auto with Geom.

apply (perp_para_perp A V P Y A T); auto.
auto with Geom.
unfold parallel, S4;basic_simpl.
assert (Col A V T);auto with Geom;auto.

unfold not;intro.
subst.
basic_simpl.
assert (C=D).
auto with Geom.
intuition.

(* case A<>U *)

unfold on_foot in H.
use H.
pose (d := C**D/A**U).
assert ({T : Point | Col T A U /\ A ** T = d * A**U}).
apply (on_line_dex A U);assumption.
elim H;intros T HT; clear H.
use HT.
unfold d in H6.

assert (A**T = C**D).
rewrite H6.
field;auto with Geom.
rewrite <- H9.
clear H6.
rewrite ( l_24_b A T P Y).
replace (2 * A ** T * A ** T) with (Py A T A)
 by (unfold Py;basic_simpl;uniformize_dir_seg;ring).
replace (Py A T A) with (Py C D C) by
(unfold Py;
uniformize_dir_seg;
rewrite H9;
ring).
replace (Py P A T) with (Py4 P C A D).
auto.
rewrite (l3_8_a A T D C P);auto.

assert (Col U Y A).
apply (col_trans_1 U V Y A H8);auto with Geom.
assert (Col U Y T).
apply (col_trans_1 U A Y T);auto with Geom.
assert (Col A Y T).
apply (col_trans_1 A U Y T H4); auto with Geom.
assert (parallel C D T A).
apply (parallel_transitivity C D A Y T A);auto with Geom.
unfold parallel;basic_simpl.
assert (Col A T Y) by auto with Geom.
auto.

apply parallel_side_eq_weak_weak_weak_para;auto with Geom.

assert (Col U Y A).
apply (col_trans_1 U V Y A H8);auto with Geom.
assert (Col U Y T).
apply (col_trans_1 U A Y T);auto with Geom.
assert (Col A Y T).
apply (col_trans_1 A U Y T H4); auto with Geom.
auto.

assert (Col U Y A).
apply (col_trans_1 U V Y A H8);auto with Geom.
assert (Col U Y T).
apply (col_trans_1 U A Y T);auto with Geom.
assert (Col A Y T).
apply (col_trans_1 A U Y T H4); auto with Geom.
auto.
assert (Col U V T).
apply (col_trans_1 U A V T);auto with Geom.
assert (parallel U V A T).
unfold parallel, S4.
basic_simpl.
replace (S U A V) with 0.
rewrite H12.
ring.
assert (Col U A V) by auto with Geom.
symmetry;auto with Geom.

cut (perp A T Y P).
auto with Geom.
apply (perp_para_perp U V Y P A T);auto with Geom.

unfold not;intro.
subst.
basic_simpl.
assert (C=D).
auto with Geom.
intuition.
Qed.

Theorem elim_ratio_on_foot_a_invariant : forall C D,
C<>D -> Py C D C <> 0.
Proof.
auto with Geom.
Qed.

Theorem elim_ratio_on_foot_spec_a :
forall Y P U V A C D : Point,
on_foot Y P U V ->
Col A U V ->
parallel A Y C Y ->
C <> Y ->
A <> Y ->
A**Y / C**Y = (Py P U V * Py4 P C A V + Py P V U * Py4 P C A U) /
(Py P U V * Py C V C + Py P V U * Py C U C - Py P U V * Py P V U).
Proof.
intros.
rewrite (elim_ratio_on_foot_a Y P U V) by auto.
assert (T:= (elim_ratio_on_foot_a_invariant C Y H2)).

unfold Py4.
rewrite (elim_py_on_foot_right P C P U V) in * by auto.
rewrite (elim_py_on_foot_right A C P U V) in * by auto.
rewrite (pyth_simpl_4 C Y) in *.
rewrite (elim_py_on_foot_left_right C P U V Y) in * by auto.
replace (((Py P U V * Py P C V + Py P V U * Py P C U) / Py U V U -
 (Py P U V * Py A C V + Py P V U * Py A C U) / Py U V U) /
((Py P U V * Py P U V * Py V C V + Py P U V * Py P V U * Py V C U +
  Py P U V * Py P V U * Py U C V + Py P V U * Py P V U * Py U C U) /
 (Py U V U * Py U V U)))
with 
(((Py P U V * Py P C V + Py P V U * Py P C U) -
 (Py P U V * Py A C V + Py P V U * Py A C U) ) /
((Py P U V * Py P U V * Py V C V + Py P U V * Py P V U * Py V C U +
  Py P U V * Py P V U * Py U C V + Py P V U * Py P V U * Py U C U) /
 ( Py U V U))) in *.
replace (Py P U V * Py P C V + Py P V U * Py P C U -
 (Py P U V * Py A C V + Py P V U * Py A C U))
with (Py P U V * Py P C V + Py P V U * Py P C U -
Py P U V * Py A C V - Py P V U * Py A C U) in * by ring.
replace (Py P U V * Py P C V + Py P V U * Py P C U - Py P U V * Py A C V -
 Py P V U * Py A C U)
with
(Py P U V * Py4 P C A V + Py P V U * Py4 P C A U) in * by (unfold Py4;ring).
replace ((Py P U V * Py P U V * Py V C V + Py P U V * Py P V U * Py V C U +
  Py P U V * Py P V U * Py U C V + Py P V U * Py P V U * Py U C U) / 
 Py U V U)
with (
 Py P U V * Py C V C +
Py P V U * Py C U C - Py P U V * Py P V U) in *.

trivial.

unfold Py.
uniformize_dir_seg.
field.
basic_simpl.
replace(U ** V * U ** V + U ** V * U ** V)
with (2*U ** V * U ** V) by ring.
unfold on_foot in H;use H.
repeat (apply nonzeromult);auto with Geom.

field.
split.
unfold on_foot in H.
use H.
auto with Geom.
intro Ha.
rewrite Ha in *.
replace ( 0 / (Py U V U * Py U V U) ) with 0 in *.
intuition.
field.
unfold on_foot in H.
use H.
auto with Geom.
Qed.

Theorem elim_ratio_on_foot_b :
forall Y P U V A C D : Point,
on_foot Y P U V ->
~ Col A U V ->
parallel A Y C D ->
C <> D ->
A**Y / C**D = S A U V / S4 C U D V.
Proof.
intros.
cases_equality Y P.

subst Y.
unfold S4.
unfold on_foot in H.
use H.
clear H3.
eapply elim_length_ratio_inter_ll_1 with (P:=A) (Q:=P);auto with Geom.
unfold inter_ll.
repeat split;auto with Geom.
intro.
assert (parallel V U P A) by auto with Geom.
unfold parallel, S4 in H3.
replace (S V P U) with (S P U V) in H3 by auto with Geom.
rewrite H5 in H3.
basic_simpl.
assert (Col A U V).
auto with Geom.
intuition.

eapply elim_length_ratio_inter_ll_1 with (P:=P) (Q:=Y); auto with Geom.
unfold inter_ll, on_foot in *.
use H.
repeat split; auto with Geom.
cut (~ parallel Y P U V).
auto with Geom.
apply perp_not_parallel; auto with Geom.
Qed.

Theorem elim_ratio_on_foot_spec_b :
forall Y P U V A C : Point,
on_foot Y P U V ->
~ Col A U V ->
parallel A Y C Y ->
C <> Y ->
A**Y / C**Y = S A U V / S C U V.
Proof.
intros.
rewrite (elim_ratio_on_foot_b Y P U V A C) by assumption.
unfold S4.
replace (S C Y V) with (S V C Y) by auto with Geom.
rewrite (elim_area_on_foot C U P U V Y) by assumption.
rewrite (elim_area_on_foot V C P U V Y) by assumption.
basic_simpl.
uniformize_signed_areas.
replace (Py P U V * S C U V / Py U V U + Py P V U * S C U V / Py U V U)
with (S C U V).
trivial.
unfold Py.
uniformize_dir_seg.
basic_simpl.
field.
replace (U ** V * U ** V + U ** V * U ** V) with (2*U ** V * U ** V) by ring.
unfold on_foot in H;decompose [and] H.
repeat (apply nonzeromult);auto with Geom.
Qed.


Theorem elim_ratio_on_foot_b_invariant :
forall Y P U V A C D : Point,
on_foot Y P U V ->
~ Col A U V ->
parallel A Y C D ->
C<>D ->
S4 C U D V <> 0.
Proof.
intros.
intro.
assert (parallel C D U V) by auto with Geom.
unfold on_foot in *.
use H.
assert  (T:=parallel_transitivity A Y C D U V H2 H1 H4).
assert (parallel U V A Y) by auto with Geom.
unfold parallel, S4 in H.
replace (S U V Y) with (0) in H.
basic_simpl.
assert (Col A U V) by auto with Geom.
intuition.
assert (Col U V Y) by auto with Geom.
auto with Geom.
Qed.

Theorem elim_ratio_on_perp_d_a_invariant :
  forall Y P Q A C D : Point, forall r: F,
  on_perp_d Y P Q r->
  Col A P Y  ->
  parallel A Y C D ->
  A<>Y ->
  C<>D ->
  S4 C P D Q <> 0.
Proof.
intros.
unfold on_perp_d in H.
use H.
intro.
assert (parallel C D P Q) by auto with Geom.
clear H.
assert (T:=parallel_transitivity A Y C D P Q H3 H1 H7).

assert (parallel Y P P Q).
apply (parallel_transitivity Y P A Y P Q H2);
auto with Geom.
unfold parallel.
basic_simpl.
assert (Col Y A P) by auto with Geom.
auto with Geom.
assert (~ perp Y P P Q).
apply (parallel_not_perp Y P P Q H).
2:auto.
2:intuition.
intro;subst.
basic_simpl.
IsoleVar (Py P Q P) H5.
replace (0/r) with (0) in H5.
2:field.
2:auto.
assert (P=Q).
auto with Geom.
intuition.
Qed.

Theorem elim_ratio_on_perp_d_a_aux :
 forall Y P Q A C D : Point, forall r: F,
on_perp_d Y P Q r->
Col A P Y  ->
parallel A Y C D ->
C<>D ->
A<>Y ->
A<>P ->
A**Y / C**D = (S A P Q -r/(2+2) * Py P Q P)/(S4 C P D Q).
Proof.
intros.




rename H4 into Hap.
assert (T:= (elim_ratio_on_perp_d_a_invariant Y P Q A C D r H H0 H1 H3 H2)).

assert (Hr: r<> 0).
unfold on_perp_d in *;use H;auto.

replace  (A**Y) with (A**P + P**Y) by
  (auto with Geom).
replace ((A ** P + P ** Y) / C ** D) with (A**P/C**D + P**Y/C**D) by (field;auto with Geom).
replace (A**P / C**D) with (S A P Q / S4 C P D Q).
replace (P**Y / C**D) with (- r / (2+2) * Py P Q P / S4 C P D Q).
field;solve_conds.

(* deux exprs *)



assert (P**Y / C**D = S P Y Q / S4 C P D Q).
assert (Y ** P / C ** D = S Y P Q / S4 C P D Q).
apply (elim_length_ratio_inter_ll_2 Y C D P A P Q P).
unfold inter_ll.
repeat split;auto with Geom.

intro.
unfold on_perp_d in H.
use H.

assert (parallel P Q P Y).
apply (parallel_transitivity P Q P A P Y).

auto.

auto.
unfold parallel, S4.
basic_simpl.
unfold Col in H0.
uniformize_signed_areas.
rewrite H0.
ring.
assert (parallel Y P P Q) by auto with Geom.
apply (perp_not_parallel Y P P Q H7).
intro.
subst Y.
basic_simpl.
IsoleVar r H6.
replace (0 / Py P Q P) with 0 in H6.
auto.
field.
auto with Geom.
auto with Geom.
auto.
auto.
unfold Col in *.
uniformize_signed_areas.
rewrite H0;ring.
auto.

assert (parallel C D P Y).
apply (parallel_transitivity C D A Y P Y); auto with Geom.
auto with Geom.

intro.
subst.
unfold on_perp_d in H.
use H.
basic_simpl.
IsoleVar r H5.
replace (0 / Py P Q P) with 0 in H5.
auto.
field;solve_conds.
auto with Geom.

assert (parallel C D Y P).
apply (parallel_transitivity C D A Y Y P H3).
auto with Geom.
auto with Geom.

replace (P ** Y / C ** D) with (- ( Y**P / C**D)).
rewrite H4.
uniformize_signed_areas.
field.
auto.
uniformize_dir_seg.
field.
auto with Geom.

rewrite H4.
unfold on_perp_d in H.
use H.
IsoleVar r H6.
rewrite H6.
uniformize_signed_areas.
field.
repeat split;auto with Geom.
solve_conds.
auto with Geom.

cases_equality A P.
subst P.
basic_simpl.
field;solve_conds.
auto with Geom.

rewrite (elim_length_ratio_inter_ll_2 A C D P Y P Q P).
auto.
unfold inter_ll.
repeat split;auto with Geom.
apply perp_not_parallel.
unfold on_perp_d in H.
use H.
auto with Geom.
unfold on_perp_d in H.
use H.
auto.
unfold on_perp_d in H.
use H.
intro.
subst P.
basic_simpl.
IsoleVar (Py Y Q Y) H6.
replace (0/r) with 0 in H6 by (field;solve_conds).

assert (Py Y Q Y <> 0).
auto with Geom.
intuition.

auto with Geom.
auto.
assert (parallel C D P A).
apply (parallel_transitivity C D A Y P A H3).
auto with Geom.
unfold parallel, S4.
basic_simpl.
auto with Geom.
auto with Geom.
auto.
Qed.

Theorem elim_ratio_on_perp_d_a :
 forall Y P Q A C D : Point, forall r: F,
on_perp_d Y P Q r->
Col A P Y  ->
parallel A Y C D ->
C<>D ->
A<>Y ->
A**Y / C**D = (S A P Q -r/(2+2) * Py P Q P)/(S4 C P D Q).
Proof.
intros.
cases_equality A P.
subst A.
clear H0.
basic_simpl.
unfold on_perp_d in H.
use H.
replace (0 - r / (2 + 2) * Py P Q P) with (S Q P Y).
replace (P ** Y / C ** D) with (- (Y**P / C**D)).
rewrite (elim_length_ratio_inter_ll_1 Y C D  P Q P Y P).
uniformize_signed_areas.
field.
cut (~ parallel C D P Q).
auto with Geom.
assert (perp C D P Q).
apply (perp_para_perp P Y P Q C D);auto with Geom.
intro.
assert  (T:=parallel_not_perp C D P Q H6 H2 H0).
intuition.

unfold inter_ll.
repeat split;auto with Geom.
intro.
assert (T:=parallel_not_perp P Y P Q H H3 H0).
assert (perp P Y P Q) by auto with Geom.
intuition.
intro.
uniformize_signed_areas.
rewrite H in H4.
basic_simpl.
assert (r * Py P Q P <> 0) by (apply nonzeromult;auto with Geom).
intuition.
auto.
auto with Geom.
uniformize_dir_seg.
field.
auto with Geom.
uniformize_signed_areas.
IsoleVar (S P Q Y) H4.
rewrite H4.
field.
apply nonzeromult;auto with Geom.
replace (2+2) with (2*2) by ring.
apply nonzeromult;auto with Geom.

apply elim_ratio_on_perp_d_a_aux;auto.
Qed.

Theorem elim_ratio_on_perp_d_spec_a :
 forall Y P Q A C : Point, forall r: F,
on_perp_d Y P Q r->
Col A P Y  ->
parallel A Y C Y ->
C<>Y ->
A<>Y ->
A**Y / C**Y = (S A P Q - r / (2 + 2) * Py P Q P) /
(S Q C P -r/(2+2) * Py P Q P).
Proof.
intros.
rewrite (elim_ratio_on_perp_d_a Y P Q A C Y r); try assumption.
unfold S4.
replace (S C Y Q) with (S Q C Y) by auto with Geom.
rewrite (elim_area_on_perp_d C P P Q Y r) by assumption.
rewrite (elim_area_on_perp_d Q C P Q Y r) by assumption.
basic_simpl.
unfold Py4.
basic_simpl.
uniformize_signed_areas.
replace (0 - r / (2 + 2) * (Py P C P - Py Q C P) + (S Q C P - r / (2 + 2) * Py P Q C))
with (S Q C P - r / (2 + 2) * (Py P C P - Py Q C P) - r / (2 + 2) * Py P Q C) by ring.
replace (Py P C P - Py Q C P) with (Py C P Q) by 
(unfold Py;uniformize_dir_seg;basic_simpl;ring).
replace (S Q C P - r / (2 + 2) * Py C P Q - r / (2 + 2) * Py P Q C) with 
(S Q C P -r/(2+2) * Py P Q P).
2:unfold Py.
2:uniformize_dir_seg.
2:basic_simpl.
2:field.
2:apply nonzeromult; auto with Geom.
trivial.
Qed.

Lemma elim_ratio_on_perp_d_b_auxi : 
  forall A Y C D P Q : Point, 
  on_parallel_d Y A C D 1 ->
  Py C P Q - Py D P Q = Py A P Q - Py Y P Q.
Proof.
intros.
replace (Py Y P Q) with (Py Q P Y) by apply pyth_sym.
rewrite (elim_py_on_parallel_d_right Q P A C D Y 1) by assumption.
replace (Py A P Q) with (Py Q P A) by apply pyth_sym.
replace (Py Q P D) with (Py D P Q) by apply pyth_sym.
replace (Py Q P C) with (Py C P Q) by apply pyth_sym.
ring.
Qed.

Theorem elim_ratio_on_perp_d_b_aux :
 forall Y P Q A C D : Point, forall r: F,
 on_perp_d Y P Q r->
 ~ Col A P Y  ->
 parallel A Y C D ->
 C<>D -> C**D <>A**Y ->
 A**Y / C**D = Py A P Q / Py4 C P D Q.
Proof.
intros.
unfold on_perp_d in H.
assert (A<>Y).
unfold not;intro.
subst.
intuition.

assert (T:=on_line_dex_spec_strong_f A Y C D H1 H4).

elim T;intros D' HD'.
clear T.
decompose [and] HD'; clear HD'.
rewrite <- H7.

assert (A<>D').
unfold not;intro.
subst.
basic_simpl.
assert (C=D).
auto with Geom.
subst.
intuition.

assert (D'<>Y).
unfold not;intro;subst.
subst.
rewrite H7 in H3.
intuition.

rewrite (l_25_b P Q A D' Y H6 H9).
assert (Py4 A P D' Q = Py4 C P D Q).
apply l_27_b; auto.

rewrite H10.
reflexivity.
unfold not;intro.
assert (parallel Y P D' P).
decompose [and] H;clear H.
apply (perp_perp_para Y P P Q D' P); auto with Geom.
assert (Col Y P D').
unfold parallel,S4 in H11.
basic_simpl.
auto with Geom.
assert (Col Y A P).
apply (col_trans_1 Y D' A P);
auto with Geom.
intuition.

unfold on_inter_line_perp.
decompose [and] H.
repeat split.
auto with Geom.
auto with Geom.

intro.
assert (parallel A D' Y P).
apply (perp_perp_para A D' P Q Y P);auto with Geom.
assert (Col A P Y).
assert (Col P A D').
apply (par_col_col_3 Y P A D');auto with Geom.

assert (parallel Y P A P).
apply (col_par_par Y P A D' P);
auto with Geom.
unfold parallel, S4 in H17.
basic_simpl.
auto with Geom.

intuition.
Qed.

Theorem elim_ratio_on_perp_d_b_invariant :
 forall Y P Q A C D : Point, forall r: F,
 on_perp_d Y P Q r ->
 ~ Col A P Y ->
 parallel A Y C D ->
 C<>D ->
 Py4 C P D Q <> 0.
Proof.
intros.
unfold on_perp_d in H.
use H.
intro.
assert (perp C D P Q) by auto with Geom.
clear H.
assert (parallel Y P C D)
 by (eapply perp_perp_para;eauto).
assert (parallel Y P A Y)
 by (apply (parallel_transitivity Y P C D A Y); auto with Geom).
assert (Col A P Y).
unfold parallel in *.
basic_simpl.
auto with Geom.
intuition.
Qed.


Theorem elim_ratio_on_perp_d_b :
 forall Y P Q A C D : Point, forall r: F,
 on_perp_d Y P Q r->
 ~ Col A P Y  ->
 parallel A Y C D ->
 C<>D ->
 A**Y / C**D = Py A P Q / Py4 C P D Q.
Proof.
intros.
elim (classic (A**Y=C**D)).
intro.
assert (on_parallel_d Y A C D 1).
unfold on_parallel_d;repeat split;auto with Geom.
ring_simplify;auto.
rewrite H3.
replace (C ** D / C ** D) with 1 by (field;auto with Geom).
assert (T:=elim_ratio_on_perp_d_b_auxi A Y C D P Q H4).
assert (Py A P Q = Py4 C P D Q).
unfold Py4.
assert (Py Y P Q = 0).
unfold on_perp_d in H;use H; unfold perp, Py4 in *.
basic_simpl;assumption.
rewrite H5 in T.
ring_simplify in T.
rewrite <- T.
ring.
rewrite H5.
field.
eapply elim_ratio_on_perp_d_b_invariant;eauto.
intros.
eapply elim_ratio_on_perp_d_b_aux;eauto.
Qed.




Theorem elim_ratio_on_perp_d_spec_b :
 forall Y P Q A C : Point, forall r: F,
 on_perp_d Y P Q r->
 ~ Col A P Y  ->
 parallel A Y C Y ->
 C<>Y ->
 A**Y / C**Y = Py A P Q / Py C P Q.
Proof.
intros.
rewrite (elim_ratio_on_perp_d_b Y P Q A C Y r) by assumption.
unfold Py4.
replace (Py Y P Q) with (Py Q P Y) by auto with Geom.
rewrite (elim_py_on_perp_d_right Q P P Q Y r) by assumption.
basic_simpl.
trivial.
Qed.








