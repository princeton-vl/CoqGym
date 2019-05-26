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
(*                              Lib_Zerob.v                                 *)
(****************************************************************************)

Require Export Lib_Bool.
Require Export Lib_Prop.
Require Export Lib_Set_Products.
Require Export Lt.

Lemma zerob_If :
 forall (b : bool) (x y : nat),
 zerob (if_bool _ b x y) = true -> x <> 0 -> b = false.
simple induction b; simpl in |- *; intros; auto.
absurd (x <> 0).
apply no_no_A; apply zerob_true_elim; auto.
trivial.
Qed.



Lemma lt_no_zerob : forall n : nat, 0 < n -> zerob n <> true.
simple induction n; [ intros; inversion H | auto ]. 
Qed.
Hint Resolve lt_no_zerob.


Lemma zerob_pred_no : forall n : nat, zerob (pred n) = false -> n <> 0.
simple induction n; auto with bool.
Qed.
Hint Resolve zerob_pred_no.



Lemma zerob_lt : forall n : nat, zerob n = false -> 0 < n.
simple induction n.
simpl in |- *; intro.
absurd (true = false); auto with bool.
intros.
auto with arith.
Qed.
Hint Resolve zerob_lt.



Lemma no_zerob_true : forall n : nat, n <> 0 -> zerob n <> true.
simple induction n; auto.
Qed.
Hint Resolve no_zerob_true.



Lemma x_1_or_y_0 :
 forall x y : nat,
 zerob (pred x) || zerob y = true -> x <> 0 -> x = 1 \/ y = 0.
simple induction x; simple induction y.
intros; right; try trivial.
intros.
absurd (0 <> 0); auto with arith.
right; auto.
simpl in |- *.
elim orb_sym; simpl in |- *; intros.
left; replace n with 0.
try trivial.
apply sym_equal; apply zerob_true_elim; try trivial.
Qed.



Lemma zerob_pred_false :
 forall n : nat, zerob (pred n) = false -> zerob n = false.
simple induction n; auto.
Qed.
Hint Resolve zerob_pred_false.

(************************************************************************)
