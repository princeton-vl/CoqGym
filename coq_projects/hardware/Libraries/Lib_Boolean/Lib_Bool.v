(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                   Solange Coupet-Grimal & Line Jakubiec                  *)
(*                                                                          *)
(*                                                                          *)
(*              Laboratoire d'Informatique de Marseille                     *)
(*               CMI-Technopole de Chateau-Gombert                          *)
(*                   39, Rue F. Joliot Curie                                *)
(*                   13453 MARSEILLE Cedex 13                               *)
(*           e-mail:{Solange.Coupet,Line.Jakubiec}@lim.univ-mrs.fr          *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              May 30th 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                                Lib_Bool.v                                *)
(****************************************************************************)

Require Export Bool.
Require Export IfProp.
(*Require Export Orb.*)
Require Export Zerob.

Lemma bool_dec : forall b : bool, {b = true} + {b = false}.
simple induction b; auto with bool.
Qed.
Hint Resolve bool_dec.

(************************************************************************)

Lemma orb_sym : forall a b : bool, a || b = b || a.
simple induction a; simple induction b; auto with bool.
Qed.
Hint Immediate orb_sym.


Lemma orb_false : forall a b : bool, a || b = false -> a = false /\ b = false.
simple induction a; simple induction b; auto with bool.
Qed.
Hint Resolve orb_false.


Lemma orb_false_l : forall a b : bool, a || b = false -> a = false.
intros; elim (orb_false a b); auto with bool.
Qed.


Lemma orb_false_r : forall a b : bool, a || b = false -> b = false.
intros; elim (orb_false a b); auto with bool.
Qed.


Lemma true_orb_intro :
 forall b1 b2 : bool, b1 || b2 = true -> b1 = true \/ b2 = true.
simple induction b1; auto with bool.
Qed.

(************************************************************************)

Lemma and_sym : forall a b : bool, a && b = b && a.
simple induction a; simple induction b; auto with bool.
Qed.
Hint Immediate and_sym.


Lemma andb_false :
 forall a b : bool,
 a && b = false ->
 a = false /\ b = false \/ a = false /\ b = true \/ a = true /\ b = false.
simple induction a; simple induction b; auto with bool.
Qed.


Lemma andb_true : forall a b : bool, a && b = true -> a = true /\ b = true.
simple induction a; simple induction b; auto with bool.
Qed.


Lemma andb_true_l : forall a b : bool, a && b = true -> a = true.
intros; elim (andb_true a b); auto with bool.
Qed.


Lemma andb_true_r : forall a b : bool, a && b = true -> b = true.
intros; elim (andb_true a b); auto with bool.
Qed.


Lemma andb_negb_true_r : forall a b : bool, a && negb b = true -> b = false.
simple induction b; auto with bool.
elim and_sym; auto with bool.
Qed.


Lemma andb_negb_true_l : forall a b : bool, negb a && b = true -> a = false.
intros a b.
elim and_sym; intros H.
apply andb_negb_true_r with b; auto with bool.
Qed.


(************************************************************************)

Lemma no_true_false : forall b : bool, b = false -> b <> true.
simple induction b; auto with bool.
Qed.
Hint Resolve no_true_false.

(************************************************************************)

Definition if_bool (C : Set) (b : bool) (x y : C) : C :=
  match b return C with
  | true => x
  | false => y
  end.
Notation If := (if_bool _) (only parsing).

(************************************************************************)
