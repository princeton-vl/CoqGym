(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export field.
Require Import Classical.

Ltac Geometry := auto with Geom field_hints.

(*******************************************************)
(** Axioms                                                             *)
(*******************************************************)

(** The set of Points *)
Parameter Point : Set.
(** The signed area *)
Parameter S : Point -> Point -> Point -> F.
(** The signed distance *)
Parameter DSeg : Point -> Point -> F.

Infix "**" := DSeg (left associativity, at level 20) : F_scope.

Definition Col (A B C : Point) : Prop := S A B C = 0.
Definition S4 (A B C D : Point) : F := S A B C + S A C D. 
Definition parallel (A B C D : Point) : Prop := S4 A C B D = 0.

Axiom A1b : forall A B : Point, A ** B = 0 <-> A = B.

Axiom A2a : forall (A B : Point) (r : F),
    {P : Point | Col A B P /\ A ** P = r * A ** B}.
Axiom  A2b : forall (A B P P' : Point) (r : F),
    A <> B ->
    Col A B P ->
    A ** P = r * A ** B -> Col A B P' -> A ** P' = r * A ** B -> P = P'.

Axiom chasles : forall A B C : Point, Col A B C -> A ** B + B ** C = A ** C.

Axiom A3a : forall A B C : Point, S A B C = S C A B.
Axiom A3b : forall A B C : Point, S A B C = - S B A C.

Axiom A4 : {A : Point &  {B : Point &  {C : Point | ~ Col A B C}}}.

Axiom A5 : forall A B C D : Point, S A B C = S A B D + S A D C + S D B C.

Axiom A6 : forall A B C P : Point,
    A <> C -> ~ Col P A C -> Col A B C -> A ** B / A ** C = S P A B / S P A C.

(* Parallelogram axiom *)

Axiom parallel_side_eq_parallel : forall P Q C D,
  parallel P Q C D -> P**Q=C**D -> C<>D -> parallel D Q P C. 

(** We assume that the field is not of characteristic two *)
Axiom chara_not_2 : 2 <> 0.

Hint Unfold S4 parallel Col: Geom.
Hint Resolve chara_not_2 chasles A2a A2b A3a A3b A5 A6: Geom.

(** Decidability lemmmas *)

Lemma eq_dec_points : forall A B:Point, A=B \/ A<>B.
Proof.
intros.
apply classic.
Qed.

Lemma col_dec : forall A B C:Point, Col A B C \/ ~ Col A B C.
Proof.
intros.
apply classic.
Qed.

Lemma parallel_dec : forall A B C D, parallel A B C D \/ ~ parallel A B C D.
Proof.
intros.
apply classic.
Qed.

Lemma number_dec : forall r: F, r=0 \/ r<>0.
Proof.
intros.
apply classic.
Qed.

Ltac cases_equality A B := elim (eq_dec_points A B);intros.
Ltac cases_col A B C := elim (col_dec A B C);intros.
Ltac cases_parallel A B C D := elim (parallel_dec A B C D);intros.
Ltac cases_equality_f r := elim (number_dec r);intros.

Ltac named_cases_equality A B H := elim (eq_dec_points A B);intro H.
Ltac named_cases_col A B C H := elim (col_dec A B C);intro H.
Ltac named_cases_parallel A B C D H := elim (parallel_dec A B C D);intro H.

