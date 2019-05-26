(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require  Import area_method.

(** Area elimination *)

(** on_line *)

Lemma test_area_on_line_1 : forall I B C, 
  on_line I B C -> S I B C = 0.
Proof.
geoInit.
eliminate I.
basic_simpl.
auto.
Qed.

Lemma test_area_on_line_2 : forall I B C, 
  on_line I B C -> S B C I = 0.
Proof.
geoInit.
eliminate I.
basic_simpl.
auto.
Qed.

Lemma test_area_on_line_3 : forall I B C, 
  on_line I B C -> S B I C = 0.
Proof.
geoInit.
eliminate I.
basic_simpl.
auto.
Qed.

(** on_line_d *)

Lemma test_area_on_line_d_1 : forall I B C, forall x:F, 
  on_line_d I B C x -> S B I C = 0.
Proof.
geoInit.
eliminate I.
basic_simpl.
auto.
Qed.

Lemma test_area_on_line_d_2 : forall I B C, forall x:F, 
  on_line_d I B C x -> S I B C = 0.
Proof.
geoInit.
eliminate I.
basic_simpl.
auto.
Qed.

Lemma test_area_on_line_d_3 : forall I B C, forall x:F, 
  on_line_d I B C x -> S B C I = 0.
Proof.
geoInit.
eliminate I.
basic_simpl.
auto.
Qed.

(* inter_ll *)

Lemma test_area_inter_ll_1 : forall I A B C D X Y,
 inter_ll I A B C D -> S X Y I = 1 / S4 A C B D * (S A C D * S X Y B + S B D C * S X Y A) .
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_inter_ll_2  : forall I A B C D X Y,
 inter_ll I A B C D -> S I X Y = 1 / S4 A C B D * (S A C D * S X Y B + S B D C * S X Y A) .
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_inter_ll_3  : forall I A B C D X Y,
 inter_ll I A B C D -> S Y I X = 1 / S4 A C B D * (S A C D * S X Y B + S B D C * S X Y A) .
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_parallel_1  : forall I B C D X Y,
 on_parallel I B C D -> S X Y I = S X Y B + B ** I / C ** D * S4 X C Y D.
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_parallel_2  : forall I B C D X Y,
 on_parallel I B C D -> S Y I X = S X Y B + B ** I / C ** D * S4 X C Y D.
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_parallel_3  : forall I B C D X Y,
 on_parallel I B C D -> S I X Y = S X Y B + B ** I / C ** D * S4 X C Y D.
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_parallel_d_1  : forall I B C D X Y r,
 on_parallel_d I B C D r -> S I X Y = S X Y B + r * S4 X C Y D.
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_parallel_d_2  : forall I B C D X Y r,
 on_parallel_d I B C D r -> S X Y I = S X Y B + r * S4 X C Y D.
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_parallel_d_3  : forall I B C D X Y r,
 on_parallel_d I B C D r -> S Y I X = S X Y B + r * S4 X C Y D.
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_inter_line_parallel_1 : forall I A B C D E X Y,
  on_inter_line_parallel I A B C D E -> False -> 
  S X Y I = (S4 D B E A * S X Y C - S4 D C E A * S X Y B) / S4 D B E C .
Proof.
geoInit.
eliminate I.
2:reflexivity.
intuition.
Qed.

Lemma test_area_on_inter_parallel_parallel_1 : forall I A B C D E F X Y,
  on_inter_parallel_parallel I A B C D E F ->
  False -> 
  S X Y I = S4 B D C A / S4 B E C F * S4 X E Y F + S X Y D.
Proof.
geoInit.
eliminate I.
2:reflexivity. 
intuition.
Qed.

(* on_foot *)

Lemma test_area_on_foot_1  : forall I X Y Z A B,
 on_foot I X Y Z -> S A B I = (Py X Y Z * S A B Z + Py X Z Y * S A B Y) / (Py Y Z Y).
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_foot_2  : forall I X Y Z A B,
 on_foot I X Y Z -> S I A B = (Py X Y Z * S A B Z + Py X Z Y * S A B Y) / (Py Y Z Y).
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

(* on_perp_d *)

Lemma test_area_on_perp_d_1  : forall I X Y A B r,
 on_perp_d I X Y  r -> S A B I = S A B X - r / (2 + 2) * (Py X A B - Py Y A B).
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_perp_d_2  : forall I X Y A B r,
 on_perp_d I X Y  r -> S I A B = S A B X - r / (2 + 2) * (Py X A B - Py Y A B).
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

(* on_perp *)

Lemma test_area_on_perp_1  : forall I X Y A B,
 on_perp I X Y -> S I A B = S I A B.
Proof.
intros.
prepare_half_free_construction.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_perp_2  : forall I X Y A B,
 on_perp I X Y -> S A B I = S I A B.
Proof.
intros.
prepare_half_free_construction.
eliminate I.
reflexivity.
Qed.








