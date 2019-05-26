(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export area_method.

(* A small lemma to check that centroid is really at the 
intersection of medians. *)

Lemma centroid_check : forall A B C G A',
 is_centroid G A B C ->
 is_midpoint A' B C ->
 Col A G A'.
Proof.
area_method.
Qed.

Lemma euler_line : forall A B C H O G,
  is_circumcenter O A B C ->
  is_orthocenter H A B C ->
  is_centroid G A B C ->
  Col O G H.
Proof.
area_method.
Qed.

Lemma centroid_midpoint_centroid : forall A B C G A' B' C' G' X,
 is_centroid G A B C ->
 is_midpoint A' B C ->
 is_midpoint B' A C ->
 is_midpoint C' A B ->
 is_centroid G' A' B' C' ->
 1+2<>0 ->
 Col G G' X.
Proof.
area_method.
Qed.

Lemma centroid_midpoint_centroid_2 : forall A B C G A' B' C' G',
 is_centroid G A B C ->
 is_midpoint A' B C ->
 is_midpoint B' A C ->
 is_midpoint C' A B ->
 is_centroid G' A' B' C' ->
 1+2<>0 ->
 Py G G' G = 0.
Proof.
geoInit.
eliminate G'.
eliminate A'.
eliminate B'.
eliminate C'.
eliminate G.
unfold_Py.
uniformize_dir_seg.
field_and_conclude.
Qed.

Lemma l6_44 : forall A B C G P Q,
 is_centroid G A B C ->
 on_inter_line_parallel P G A B B C  ->
 on_inter_line_parallel Q G A C B C  ->
 G<>Q -> G<>P -> 1+2 <> 0 ->
 2*2*S4 P Q C B = (2+2+1)* S A Q P.
Proof.
area_method.
Qed.

Lemma l6_47 : forall A B C G M N,
 is_centroid G A B C ->
 on_line M A B ->
 inter_ll N G M A C ->
 parallel M B A M -> A<>M -> A<>N ->
 parallel N C A N -> B<>M ->
 1+2<> 0 -> 2+1 <> 0 ->
 M**B/A**M + N**C/A**N = 1.
Proof.
geoInit.
am_before_field.
field;solve_conds.
intro.
replace (- (f * (/ (2 + 1) * S C A B))) with (- (f * S C A B) / (2+1)) in H7 by (field;solve_conds).
rewrite H13 in H7.
replace (0 / (2 + 1)) with (0) in H7 by (field;solve_conds).
intuition.
intuition.
intuition.
Qed.
