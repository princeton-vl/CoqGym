(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export field_general_properties.
Require Export chou_gao_zhang_axioms.

(* This file contains the lemmas needed by the tactics used as tools for
both the development and the decision procedure. *)

(********************************************************)
(* Signed areas                                         *)
(********************************************************)

Lemma S_0 : forall A B C : Point, S A B C = S C A B.
auto with Geom.
Qed.

Lemma S_1 : forall A B C : Point, S A B C = S B C A.
auto with Geom.
Qed.
Hint Resolve S_1: Geom. 

Lemma S_2 : forall A B C : Point, S A B C = - S C B A.
Proof with try solve [ Geometry | congruence ].
intros...
assert (S A B C = - S B A C)...
assert (S B A C = S C B A)...
Qed.
Hint Resolve S_2: Geom.

Lemma S_3 : forall A B C : Point, S A B C = - S A C B.
Proof with try solve [ Geometry | congruence ].
intros...
assert (S A B C = - S B A C)...
assert (S B A C = S A C B)...
Qed.
Hint Resolve S_3: Geom.

Lemma S_4 : forall A B C : Point, S A B C = - S B A C.
intros.
Geometry.
Qed. 

(********************************************************)
(* Signed areas (4)                                     *)
(********************************************************)

Lemma S4_1 : forall A B C D : Point, S4 A B C D = S A B D - S C B D.
Proof with try solve [ Geometry | ring ].
intros...
unfold S4 in |- *...
assert (S A B C = S A B D + S A D C + S D B C)...
assert (S D B C = - S C B D)...
rewrite H0 in H...
assert (S A D C = - S A C D)...
rewrite H1 in H...
clear H0 H1...
rewrite H...
Qed.
Hint Resolve S4_1: Geom.

Lemma S4_2 : forall A B C D : Point, S4 A B C D = S4 B C D A. 
Proof with try solve [ Geometry | ring ].
unfold S4 in |- *...
intros...
assert (S B D A = S A B D)...
assert (S B C D = - S C B D)...
assert (S4 A B C D = S A B D - S C B D)...
rewrite <- H in H1.
rewrite H0.
unfold S4 in H1.
rewrite H1 in |- *.
ring.
Qed.
Hint Resolve S4_2: Geom.

Lemma S4_3 : forall A B C D : Point, S4 A B C D = S4 C D A B. 
Proof with try solve [ Geometry | congruence ].
intros...
assert (S4 A B C D = S4 B C D A)...
rewrite H...
Qed.
Hint Resolve S4_3: Geom.

Lemma S4_4 : forall A B C D : Point, S4 A B C D = S4 D A B C. 
Proof with Geometry.
intros...
Qed.
Hint Resolve S4_4: Geom.

Lemma S4_5 : forall A B C D : Point, S4 A B C D = - S4 A D C B. 
Proof with Geometry.
intros...
unfold S4 in |- *...
assert (S A C D = - S A D C)...
rewrite H.
assert (S A B C = - S A C B)...
rewrite H0.
ring.
Qed.
Hint Resolve S4_5: Geom.

Lemma S4_6 : forall A B C D : Point, S4 A B C D = - S4 D C B A. 
Proof with try solve [ Geometry | congruence ].
intros...
assert (S4 D C B A = S4 A D C B)...
rewrite H...
Qed.
Hint Resolve S4_6: Geom.

Lemma S4_7 : forall A B C D : Point, S4 A B C D = - S4 C B A D. 
Proof with try solve [ Geometry | congruence ].
intros...
assert (S4 A D C B = S4 C B A D)...
rewrite <- H...
Qed.
Hint Resolve S4_7: Geom.

Lemma S4_8 : forall A B C D : Point, S4 A B C D = - S4 B A D C. 
Proof with Geometry.
intros...
assert (S4 A D C B = S4 B A D C)...
rewrite <- H...
Qed.
Hint Resolve S4_8: Geom.


Lemma lpar1 : forall A B C D : Point, parallel A B C D -> parallel A B D C.
Proof.
intros.
unfold parallel in *.
rewrite S4_5.
rewrite H.
ring.
Qed.

Lemma lpar2 : forall A B C D : Point, parallel A B C D -> parallel B A C D.
Proof.
intros.
unfold parallel in *.
rewrite S4_7.
rewrite H.
ring.
Qed. 

Lemma lpar3 : forall A B C D : Point, parallel A B C D -> parallel B A D C.
Proof.
intros.
unfold parallel in *.
rewrite S4_3.
assumption.
Qed.
 
Lemma ldiff : forall A B : Point, A <> B -> B <> A.
Proof.
intros.
Geometry.
Qed.

(***************************************************)
(* Simplification lemmas                           *)
(***************************************************)

Lemma simplring1 : forall x : F, x = - - x. 
Proof.
intro.
ring.
Qed.

Lemma zeroegal : forall A B : Point, A = B -> A ** B = 0.
Proof.
intros.
assert (P := A1b A B).
intuition.
Qed.

Lemma egalzero : forall A B : Point, A ** B = 0 -> A = B.
Proof.
intros.
assert (P := A1b A B).
intuition.
Qed.

Hint Resolve zeroegal egalzero: Geom.

Lemma nuldirseg : forall A : Point, 0 = A ** A.
Proof.
intros.
symmetry  in |- *.
Geometry.
Qed.

Lemma neq_not_zero : forall A B:Point, 
  A<>B -> A**B<>0.
Proof.
intros.
Geometry.
Qed.

(* This lemma depends on the fact the 2<>0 *)

Lemma field_prop_2 : forall a : F, a = - a -> a = 0.
Proof with try solve [ ring | congruence ].
intros...
assert (a + a = - a + a)...
assert (- a + a = 0)...
rewrite H1 in H0...
assert (a + a = 2 * a)...
rewrite H2 in H0...
assert (2 * a / 2 = a)...
field...
auto with Geom...
assert (2 * a / 2 = 0 / 2)...
rewrite H3 in H4...
assert (0 / 2 = 0)...
field...
auto with Geom...
Qed.

Hint Resolve field_prop_2: Geom.

Lemma trivial_col1 : forall A B : Point, 0 = S A A B.
intros.
symmetry  in |- *.
Geometry.
Qed.

Lemma trivial_col2 : forall A B : Point, 0 = S A B B.
intros.
symmetry  in |- *.
Geometry.
Qed.

Lemma trivial_col3 : forall A B : Point, 0 = S A B A.
intros.
symmetry  in |- *.
Geometry.
Qed.


Lemma A1a : forall A B : Point, A ** B = - B ** A.
Proof.
intros.
assert (Col A B A).
Geometry.
assert (T:=chasles A B A H).
replace (A**A) with 0 in T.
2:symmetry;Geometry.
IsoleVar (A**B) T.
rewrite T.
ring.
Qed.


Lemma degenerated_ratio : forall A B C D, 
  A=B -> C<>D -> A**B/C**D=0.
Proof.
intros.
field_simplify_eq; Geometry.
Qed.

Hint Immediate A1a: Geom.
