(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require  Import area_method.

Lemma essai : forall A B C,
let x := S A B C + 2 in
let y := S B C A + 2 in
x = y.
Proof.
intros.
unfold x,y.
uniformize_signed_areas.
auto.
Qed.


(* on_line *)

Lemma test_py_on_line_1 : forall I B C D E, 
  on_line I B C -> Py I D E = Py E D I.
Proof.
intros.
prepare_half_free_construction.
eliminate I.
auto.
Qed.

Lemma test_py_on_line_2 : forall I B C D E, 
  on_line I B C -> Py D E I = Py D E I.
Proof.
intros.
prepare_half_free_construction.
eliminate I.
auto.
Qed.

Lemma test_py_on_line_3 : forall I B C D, 
  on_line I B C -> Py I D I = Py I D I.
Proof.
intros.
prepare_half_free_construction.
eliminate I.
auto.
Qed.

Lemma test_py_on_line_4 : forall I B C, 
  on_line I B C -> Py B I C = Py B I C.
Proof.
intros.
prepare_half_free_construction.
eliminate I;auto.
Qed.

Lemma test_py_on_line_4_b : forall I B C, 
  B<>C -> on_line I B C -> Py B I C = Py B I C.
Proof.
intros.
prepare_half_free_construction.
eliminate I.
auto.
Qed.

Lemma test_py_on_line_4_c : forall I B C, 
  B=C -> on_line I B C -> Py B I C = Py B I C.
Proof.
intros.
prepare_half_free_construction.
eliminate I.
auto.
Qed.


Lemma test_py_on_line_5 : forall I P Q B, 
  on_line I P Q -> Py B I B = Py B I B.
Proof.
intros.
prepare_half_free_construction.
eliminate I.
auto.
Qed.

(* on_line_d *)

Lemma test_py_on_line_d_1 : forall I B C r, 
  on_line_d I B C r -> Py I C B = Py B C I.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma test_py_on_line_d_2 : forall I B C r, 
  on_line_d I B C r -> Py B C I = Py B C I.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma test_py_on_line_d_3 : forall I B C r, 
  on_line_d I B C r -> Py B I C = Py B I C.
Proof.
intros.
eliminate I;
auto.
Qed.

Lemma test_py_on_line_d_4 : forall I B C r, 
  on_line_d I B C r -> Py B I B = Py B I B.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma test_py_on_line_d_5 : forall A B C D Q r,
  on_line_d Q B C r -> Py A Q D = Py A Q D.
Proof.
intros.
eliminate Q;auto.
Qed.

Lemma test_py_on_line_d_6 : forall A B C D Q r,
  on_line_d Q B C r ->
  Py A Q A + Py A Q D = Py Q A Q + Py A Q D.
Proof.
geoInit.
eliminate Q;auto.
Qed. 


(* inter_ll *)

Lemma  test_inter_ll_1 : forall I A B C D X Y, 
  inter_ll I A B C D -> Py I X Y = Py Y X I.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma  test_inter_ll_2 : forall I A B C D X Y, 
  inter_ll I A B C D -> Py Y X I = Py Y X I.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma  test_inter_ll_3 : forall I A B C D X Y, 
  inter_ll I A B C D -> Py Y I X = Py Y I X.
Proof.
intros.
eliminate I.
auto.
Qed.


Lemma  test_inter_ll_4 : forall I A B C D X, 
  inter_ll I A B C D -> Py X I X = Py X I X.
Proof.
intros.
eliminate I.
auto.
Qed.


(* on_parallel_d *)

Lemma test_py_on_parallel_d_1  : forall I B C D X Y r, 
 on_parallel_d I B C D r -> Py X Y I = Py X Y I.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma test_py_on_parallel_d_2  : forall I B C D X Y r,
 on_parallel_d I B C D r -> Py I Y X = Py I Y X.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma test_py_on_parallel_d_3  : forall I B C D X Y r,
 on_parallel_d I B C D r -> Py X I Y = Py X I Y.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma test_py_on_parallel_d_4  : forall I B C D X r,
 on_parallel_d I B C D r -> Py X I X = Py X I X.
Proof.
intros.
eliminate I.
auto.
Qed.

(* on_perp *)

Lemma test_py_on_perp_1  : forall I A B X Y, 
 on_perp I A B -> Py X Y I = Py X Y I.
Proof.
intros.
prepare_half_free_construction.
eliminate I.
auto.
Qed.

Lemma test_py_on_perp_2  : forall I A B X Y, 
 on_perp I A B -> Py I Y X = Py X Y I.
Proof.
intros.
prepare_half_free_construction.
eliminate I.
auto.
Qed.

Lemma test_py_on_perp_3  : forall I A B X Y, 
 on_perp I A B -> Py X I Y = Py X I Y.
Proof.
intros.
prepare_half_free_construction.
eliminate I.
auto.
Qed.

Lemma test_py_on_perp_4  : forall I A B X, 
 on_perp I A B -> Py X I X = Py X I X.
Proof.
intros.
prepare_half_free_construction.
eliminate I.
auto.
Qed.


(* on_perp_d *)

Lemma test_py_on_perp_d_1  : forall I A B r X Y, 
 on_perp_d I A B r -> Py X Y I = Py X Y I.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma test_py_on_perp_d_2  : forall I A B r X Y, 
 on_perp_d I A B r -> Py I Y X = Py X Y I.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma test_py_on_perp_d_3  : forall I A B r X Y, 
 on_perp_d I A B r -> Py X I Y = Py X I Y.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma test_py_on_perp_d_4  : forall I A B r Y, 
 on_perp_d I A B r -> Py Y I Y = Py Y I Y.
Proof.
intros.
eliminate I.
auto.
Qed.


(* on_foot *)

Lemma test_py_on_foot_1  : forall I A B C X Y, 
 on_foot I A B C -> Py X Y I = Py X Y I.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma test_py_on_foot_2  : forall I A B C X Y, 
 on_foot I A B C -> Py I Y X = Py X Y I.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma test_py_on_foot_3  : forall I A B C X Y, 
 on_foot I A B C -> Py X I Y = Py X I Y.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma test_py_on_foot_4  : forall I A B C X, 
 on_foot I A B C -> Py X I X = Py X I X.
Proof.
intros.
eliminate I.
auto.
Qed.

Lemma test_py_on_foot_5 : forall A B C E,
on_foot E B A C ->
Py B E B + Py E A C = Py B E B + Py E A C.
Proof.
intros.
eliminate E.
auto.
Qed.

