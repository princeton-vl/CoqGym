(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export advanced_parallel_lemmas.

Definition Py A B C := A**B * A**B + B**C * B**C - A**C * A**C.
Definition Py4 A B C D := Py A B D - Py C B D.
Definition per A B C := Py A B C = 0.
Definition perp A B C D := Py4 A C B D = 0.
Definition on_foot (Y P U V : Point) := perp Y P U V /\ Col Y U V /\ U<>V.

(* We introduce three additionnal axioms *)

Axiom perp_perp_para : forall A B C D E F,
 C<>D ->
 perp A B C D -> perp E F C D -> parallel A B E F.

Axiom perp_para_perp : forall A B C D E F, 
  A<>B ->
  perp A B C D -> parallel A B E F -> perp E F C D.

(* We use the square to get rid of sign issues *)

Axiom on_foot_area : forall A B C F, 
  on_foot F A B C ->
  2 * 2 * S A B C * S A B C = A**F * A**F * B**C * B**C.

Lemma on_foot_area_paper : forall A B C F, 
  perp F A B C -> Col F B C ->
  2 * 2 * S A B C * S A B C = A**F * A**F * B**C * B**C.
Proof.
intros.
cases_equality B C.
subst.
basic_simpl.
trivial.
apply on_foot_area.
unfold on_foot;auto.
Qed.


Lemma pyth_simpl_1 : forall A B, Py A A B = 0.
Proof.
intros.
unfold Py.
basic_simpl.
reflexivity.
Qed.

Lemma pyth_simpl_2 : forall A B, Py A B B = 0.
Proof.
intros.
unfold Py.
basic_simpl.
reflexivity.
Qed.

Hint Rewrite pyth_simpl_1  pyth_simpl_2 : seg_simplifications.
Hint Resolve pyth_simpl_1 pyth_simpl_2 : Geom.

Lemma test_basic_simpl : forall A B, Py A A B = 0.
Proof.
intros.
basic_simpl.
reflexivity.
Qed.

Lemma pyth_sym : forall A B C, Py A B C = Py C B A.
Proof.
intros.
unfold Py.
uniformize_dir_seg.
ring.
Qed.

Hint Resolve pyth_sym : Geom.

Lemma pyth_simpl_3 : forall A B, Py A B A = 2 * A**B * A**B.
Proof.
intros.
unfold Py.
uniformize_dir_seg.
basic_simpl.
ring.
Qed.

Lemma pyth_simpl_4 : forall A B, Py A B A = Py B A B.
Proof.
intros.
unfold Py.
uniformize_dir_seg.
basic_simpl.
ring.
Qed.

Hint Immediate pyth_simpl_4 : Geom.

Ltac uniformize_pys :=
  repeat (rewrite pyth_simpl_1);
  repeat (rewrite pyth_simpl_2);
  repeat
   match goal with
   |  |- context [(Py ?A ?B ?C)] =>
    (match goal with
       |  |- context [(Py C B A)] => rewrite (pyth_sym A B C) in *   
       end)
   |  |- context [(Py ?A ?B ?A)] =>
    (match goal with
       |  |- context [(Py B A B)] => rewrite (pyth_simpl_4 A B) in *   
       end)
   end.

Lemma test_uniformize_pys : forall A B C, 
 Py A B C - Py C B A + Py A A C + Py A C C + Py A B A - Py B A B = 0.
Proof.
intros.
uniformize_pys.
ring.
Qed.

Lemma square_to_py : forall A B, A**B * A**B = Py A B A / 2.
Proof.
intros.
rewrite pyth_simpl_3.
field.
auto with Geom.
Qed.

Lemma col_pyth : forall A B C, Col A B C -> Py A B C = 2 * B**A * B**C.
Proof.
intros.
unfold Py.
replace (A**C) with (A**B + B**C) by (apply chasles;auto).
uniformize_dir_seg.
ring.
Qed.


Lemma py4_1 : forall A B C D, Py4 A B C D = - Py4 A D C B.
Proof.
intros.
unfold Py4, Py.
uniformize_dir_seg.
ring.
Qed.

Lemma py4_2 : forall A B C D, Py4 A B C D = Py4 B A D C.
Proof.
intros.
unfold Py4, Py.
uniformize_dir_seg.
ring.
Qed.

Lemma py4_3 : forall A B C D, Py4 A B C D = - Py4 B C D A.
Proof.
intros.
unfold Py4, Py.
uniformize_dir_seg.
ring.
Qed.

Lemma py4_4 : forall A B C D, Py4 A B C D = Py4 C D A B.
Proof.
intros.
unfold Py4, Py.
uniformize_dir_seg.
ring.
Qed.

Lemma py4_5 : forall A B C D, Py4 A B C D = - Py4 C B A D.
Proof.
intros.
unfold Py4, Py.
uniformize_dir_seg.
ring.
Qed.

Lemma py4_6 : forall A B C D, Py4 A B C D = Py4 D C B A.
Proof.
intros.
unfold Py4, Py.
uniformize_dir_seg.
ring.
Qed.

Lemma py4_7 : forall A B C D, Py4 A B C D = - Py4 D A B C.
Proof.
intros.
unfold Py4, Py.
uniformize_dir_seg.
ring.
Qed.

Hint Resolve py4_1 py4_2 py4_3 py4_4 py4_5 py4_6 py4_7 : Geom.

Lemma py4_simpl_1 : forall A B C, Py4 A A B C = - Py B A C.
Proof.
intros.
unfold Py4.
rewrite pyth_simpl_1.
ring.
Qed.

Lemma py4_simpl_2 : forall A B C, Py4 B A A C = Py B A C.
Proof.
intros.
unfold Py4.
rewrite pyth_simpl_1.
ring.
Qed.

Lemma py4_simpl_3 : forall A B C, Py4 A B A C = 0.
Proof.
intros.
unfold Py4.
ring.
Qed.

Lemma py4_simpl_4 : forall A B C, Py4 B A C A = 0.
Proof.
intros.
unfold Py4.
repeat (rewrite pyth_simpl_2).
ring.
Qed.

Lemma py4_simpl_5 : forall A B C, Py4 B C A A = - Py B A C.
Proof.
intros.
rewrite py4_6.
rewrite py4_simpl_1.
rewrite pyth_sym.
ring.
Qed.

Lemma py4_simpl_6 : forall A B C, Py4 A B C A = Py B A C.
Proof.
intros.
rewrite py4_5.
rewrite py4_simpl_5.
rewrite pyth_sym.
ring.
Qed.

Hint Resolve 
py4_simpl_1 
py4_simpl_2 
py4_simpl_3 
py4_simpl_4 
py4_simpl_5 
py4_simpl_6 : Geom.

Hint Rewrite
pyth_simpl_1
pyth_simpl_2
py4_simpl_1 
py4_simpl_2 
py4_simpl_3 
py4_simpl_4 
py4_simpl_5 
py4_simpl_6 : py_simplifications.

Ltac py_simpl := autorewrite with py_simplifications in *.

Lemma test_py_simpl : forall A B C, Py A A B = 0 -> Py A A B + Py B A A + Py4 B A C A = 0.
intros.
py_simpl.
ring.
Qed.

Lemma perp_1 : forall A B C D,
perp A B C D -> perp A B D C.
Proof.
unfold perp.
intros.
replace (Py4 A D B C) with (- Py4 A C B D) by auto with Geom.
rewrite H.
ring.
Qed.

Lemma perp_2 : forall A B C D,
perp A B C D -> perp B A C D.
Proof.
unfold perp.
intros.
replace (Py4 B C A D) with (- Py4 A C B D) by auto with Geom.
rewrite H.
ring.
Qed.

Lemma perp_3 : forall A B C D,
perp A B C D -> perp B A D C.
Proof.
unfold perp.
intros.
replace (Py4 B D A C) with (Py4 A C B D) by auto with Geom.
rewrite H.
ring.
Qed.

Lemma perp_4 : forall A B C D,
perp A B C D -> perp C D A B.
Proof.
unfold perp.
intros.
replace (Py4 C A D B) with (Py4 A C B D) by auto with Geom.
rewrite H.
ring.
Qed.

Lemma perp_5 : forall A B C D,
perp A B C D -> perp C D B A.
Proof.
unfold perp.
intros.
replace (Py4 C B D A) with (- Py4 A C B D) by auto with Geom.
rewrite H.
ring.
Qed.

Lemma perp_6 : forall A B C D,
perp A B C D -> perp D C A B.
Proof.
unfold perp.
intros.
replace (Py4 D A C B) with (- Py4 A C B D) by auto with Geom.
rewrite H.
ring.
Qed.

Lemma perp_7 : forall A B C D,
perp A B C D -> perp D C B A.
Proof.
unfold perp.
intros.
replace (Py4 D B C A) with ( Py4 A C B D) by auto with Geom.
rewrite H.
ring.
Qed.

Lemma perp_8 : forall A B C,
perp A B B C -> per A B C.
Proof.
intros.
unfold perp, Py4 in *.
basic_simpl.
auto.
Qed.

Lemma perp_9 : forall A B C,
per A B C -> perp A B B C.
Proof.
intros.
unfold perp, Py4 in *.
basic_simpl.
auto.
Qed.


Hint Resolve 
perp_1
perp_2
perp_3
perp_4
perp_5
perp_6
perp_7 : Geom.

Hint Immediate perp_8 perp_9 : Geom.

Lemma not_eq_py_not_zero : forall A B, A<>B -> Py A B A <> 0.
Proof with auto with Geom.
intros.
unfold Py.
uniformize_dir_seg.
basic_simpl.
unfold not;intro.
apply H.
replace (A ** B * A ** B + A ** B * A ** B) with (2* A ** B * A ** B) in H0 by ring.
IsoleVar (A ** B ) H0...
replace (0 / A ** B / 2) with 0 in H0 ...
field...
Qed.

Hint Resolve not_eq_py_not_zero : Geom.

Lemma py_zero_eq : forall A B, Py A B A = 0 -> A = B.
Proof.
intros.
cases_equality A B.
auto.
unfold Py in H.
uniformize_dir_seg.
basic_simpl.
ring_simplify in H.
assert (A**B<>0) by auto with Geom.
assert (2 * A ** B * A ** B <>0).
repeat apply nonzeromult;auto with Geom.
intuition.
Qed.

Hint Resolve py_zero_eq : Geom.
