(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir *)

Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.SetoidList.
Require Import Coq.omega.Omega.

Require Import Metalib.CoqUniquenessTac.


(* *********************************************************************** *)
(** * Examples *)

(** The examples go through more smoothly if we declare [eq_nat_dec]
    as a hint. *)

Hint Resolve eq_nat_dec : eq_dec.


(* *********************************************************************** *)
(** ** Predicates on natural numbers *)

Scheme le_ind' := Induction for le Sort Prop.

Lemma le_unique : forall (x y : nat) (p q: x <= y), p = q.
Proof.
  induction p using le_ind';
  uniqueness 1;
  assert False by omega; intuition.

Qed.


(* ********************************************************************** *)
(** ** Predicates on lists *)

(** Uniqueness of proofs for predicates on lists often comes up when
    discussing extensional equality on finite sets, as implemented by
    the FSets library. *)

Section Uniqueness_Of_SetoidList_Proofs.

  Variable A : Type.
  Variable R : A -> A -> Prop.

  Hypothesis R_unique : forall (x y : A) (p q : R x y), p = q.
  Hypothesis list_eq_dec : forall (xs ys : list A), {xs = ys} + {xs <> ys}.

  Scheme lelistA_ind' := Induction for lelistA Sort Prop.
  Scheme sort_ind'    := Induction for sort Sort Prop.
  Scheme eqlistA_ind' := Induction for eqlistA Sort Prop.

  Theorem lelistA_unique :
    forall (x : A) (xs : list A) (p q : lelistA R x xs), p = q.
  Proof. induction p using lelistA_ind'; uniqueness 1. Qed.

  Theorem sort_unique :
    forall (xs : list A) (p q : sort R xs), p = q.
  Proof. induction p using sort_ind'; uniqueness 1. apply lelistA_unique. Qed.

  Theorem eqlistA_unique :
    forall (xs ys : list A) (p q : eqlistA R xs ys), p = q.
  Proof. induction p using eqlistA_ind'; uniqueness 2. Qed.

End Uniqueness_Of_SetoidList_Proofs.


(* *********************************************************************** *)
(** ** Vectors *)

(** [uniqueness] can show that the only vector of length zero is the
    empty vector.  This shows that the tactic is not restricted to
    working only on [Prop]s. *)

Inductive vector (A : Type) : nat -> Type :=
  | vnil : vector A 0
  | vcons : forall (n : nat) (a : A), vector A n -> vector A (S n).

Theorem vector_O_eq : forall (A : Type) (v : vector A 0),
  v = vnil _.
Proof. intros. uniqueness 1. Qed.
