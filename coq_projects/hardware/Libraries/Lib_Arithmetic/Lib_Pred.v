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
(*                                 Lib_Pred.v                               *)
(****************************************************************************)


Require Export Lib_Eq_Le_Lt.
Require Export Lib_Prop.


Lemma pred_diff_O : forall n : nat, n <> 0 -> n <> 1 -> pred n <> 0.
simple induction n; auto with arith.
Qed.
Hint Resolve pred_diff_O.



Lemma S_pred_n : forall n : nat, 1 <= n -> S (pred n) = n.
simple induction n; auto with arith.
Qed.
Hint Resolve S_pred_n.



Lemma eq_pred : forall n m : nat, n = m -> pred n = pred m.
intros n m H.
rewrite H; auto with arith.
Qed.
Hint Resolve eq_pred.



Lemma pred_diff_lt : forall n : nat, n <> 0 -> n <> 1 -> 0 < pred n.
intros; apply neq_O_lt.
apply sym_not_equal; auto with arith.
Qed.
Hint Resolve pred_diff_lt.



Lemma pred_n_O : forall n : nat, pred n = 0 -> n = 0 \/ n = 1.
simple induction n; auto with arith.
Qed. 
Hint Resolve pred_n_O.



Lemma pred_O : forall n : nat, n = 0 -> pred n = 0.
intros.
rewrite H; auto with arith.
Qed.
Hint Resolve pred_O.


Lemma pred_no_O : forall n : nat, pred n <> 0 -> n <> 0.
simple induction n; auto with arith.
Qed.
Hint Resolve pred_no_O.



Lemma lt_pred : forall n : nat, 0 < n -> pred n < n.
simple induction n; auto with arith.
Qed.
Hint Resolve lt_pred.



Lemma dif_0_pred_eq_0_eq_1 : forall n : nat, n <> 0 -> pred n = 0 -> n = 1.
intros n H0 H1.
cut (n = 0 \/ n = 1).
intros H_Cut.
apply no_or_r with (n = 0); try trivial with arith.
apply pred_n_O; try trivial with arith.
Qed.



Lemma lt_le_pred : forall n m : nat, n < m -> n <= pred m.
simple induction n; simple induction m; auto with arith.
Qed.
Hint Resolve lt_le_pred.



(************************************************************************)
