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
(*                               Lib_Minus.v                                *)
(****************************************************************************)


Require Export Lib_Pred.


Lemma minus_SS_n : forall n : nat, S (S n) - n = 2.
intros n.
elim minus_Sn_m.
apply eq_S.
elim minus_Sn_m.
apply eq_S.
elim minus_n_n; auto with arith.
auto with arith.
auto with arith.
Qed.
Hint Resolve minus_SS_n.



Lemma minus_S : forall n m : nat, n - m = S n - S m.
intros; simpl in |- *; auto with arith.
Qed.
Hint Resolve minus_S.



Lemma pred_minus_minus : forall n m : nat, pred (n - m) = n - S m.
simple induction n; simple induction m; auto with arith.
intros; elim minus_S.
elim minus_S; auto with arith.
Qed.
Hint Resolve pred_minus_minus.



Lemma minus_pred_S : forall n m p : nat, n = m - p -> pred n = m - S p.
intros n m p H.
rewrite H; auto with arith.
Qed.
Hint Resolve minus_pred_S.



Lemma pred_minus : forall n : nat, pred n = n - 1.
simple induction n; auto with arith.
Qed.
Hint Resolve pred_minus.



Lemma O_minus_S : forall n m : nat, 0 = n - m -> 0 = n - S m.
intros n m H.
elim pred_minus_minus.
elim H; auto with arith.
Qed.
Hint Resolve O_minus_S.



Lemma minus_minus_plus : forall n m p : nat, n - m - p = n - (m + p).
simple induction n; simple induction m; auto with arith.
intros; elim minus_S.
change (n0 - n1 - p = S n0 - S (n1 + p)) in |- *.
elim minus_S; apply H.
Qed.
Hint Resolve minus_minus_plus.



Lemma lt_O_minus : forall n m : nat, n < m -> 0 < m - n.
simple induction n; simple induction m; simpl in |- *; auto with arith.
intro.
apply lt_trans with (S n0); auto with arith.
Qed.
Hint Resolve lt_O_minus.



Lemma le_minus : forall n m : nat, n - m <= n.
simple induction n; auto with arith.
  intros. 	 
  case m; simpl in |- *; auto with arith.
Qed.
Hint Resolve le_minus.



Lemma le_minus_n_Sn : forall n m : nat, n - m <= S n - m.
simple induction n; simple induction m; auto with arith.
intros.
elim minus_S.
elim minus_S; apply H. 
Qed.
Hint Resolve le_minus_n_Sn.



Lemma le_reg_minus : forall n m p : nat, n <= m -> n - p <= m - p.
intros.
elim H; auto with arith.
intros.
apply le_trans with (m0 - p).
assumption.
apply le_minus_n_Sn.
Qed.
Hint Resolve le_reg_minus.



Lemma lt_transp_r : forall n m p : nat, 0 < n -> p < n + m -> p - m < n.
simple induction m; simple induction p.
elim plus_n_O; auto with arith.
elim plus_n_O; auto with arith.
auto with arith.
intros.
simpl in |- *.
apply H.
auto with arith.
apply lt_S_n.
replace (S (n + n0)) with (n + S n0).
auto with arith.
elim plus_comm; simpl in |- *; auto with arith.
Qed.



Lemma lt_neq_O_pred : forall n m : nat, S n < m -> pred (m - n) <> 0.
intros.
elim H.
rewrite minus_SS_n; auto with arith.
intros.
elim minus_Sn_m.
simpl in |- *.
auto with arith.
apply le_trans with (S (S n)); auto with arith.
Qed.
Hint Resolve lt_neq_O_pred.



Lemma minus_Sn_n : forall n : nat, S n - n = 1.
simple induction n; auto with arith.
Qed.
Hint Resolve minus_Sn_n.



Lemma eq_minus_plus : forall n m : nat, m <= n -> n - m + m = n.
intros n m.
generalize n.
elim m.
clear n.
intro n.
intro lenO.
elim plus_n_O. 
auto with arith.
clear n m.
intros m H_rec n leSmn.
elim plus_n_Sm.
replace (S (n - S m + m)) with (S (n - S m) + m); auto with arith.
rewrite minus_Sn_m; auto with arith.
apply (H_rec n).
auto with arith.
Qed.
Hint Immediate eq_minus_plus.


(************************************************************************)

