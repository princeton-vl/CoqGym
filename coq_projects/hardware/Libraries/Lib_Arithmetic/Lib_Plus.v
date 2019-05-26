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
(*                               Lib_Plus.v                                 *)
(****************************************************************************)

Require Export Lib_Minus.


Lemma plus_opp : forall n m : nat, n + m - m = n.
intros n m; elim (plus_comm m n); apply minus_plus.
Qed.
Hint Resolve plus_opp.



Lemma S_plus : forall n : nat, S n = n + 1.
intro; elim plus_comm; auto with arith.
Qed.
Hint Resolve S_plus.



Lemma lt_plus : forall n m : nat, 0 < n -> m < n + m.
simple induction n; simple induction m; auto with arith.
intros.
simpl in |- *; apply lt_n_S.
auto with arith.
Qed.
Hint Resolve lt_plus.



Lemma le_minus_plus : forall n m : nat, n - m <= n + m.
simple induction n; auto with arith.
Qed.
Hint Resolve le_minus_plus.



Lemma le_le_assoc_plus_minus :
 forall n m p : nat, n <= m -> n <= p -> m - n + p = m + (p - n).
intros.
elim H.
elim minus_n_n; simpl in |- *; elim le_plus_minus; auto with arith.
intros.
elim minus_Sn_m; simpl in |- *.
apply eq_S; auto with arith.
assumption.
Qed.
Hint Resolve le_le_assoc_plus_minus.



Lemma le_lt_plus : forall n m p q : nat, n <= p -> m < q -> n + m < p + q.
intros.
apply lt_le_trans with (n + q).
apply plus_lt_compat_l; try trivial with arith.
apply plus_le_compat_r; try trivial with arith.
Qed.



Lemma plus_eq_zero : forall a b : nat, a + b = 0 -> a = 0 /\ b = 0.
intros a b H.
split; apply sym_equal; apply le_n_O_eq; elim H; auto with arith.
Qed.
Hint Resolve plus_eq_zero.



Lemma le_transp_l : forall n m p : nat, n + m <= p -> m <= p - n.
simple induction n; intros.
simpl in H; elim minus_n_O; assumption.
elim H0.
elim plus_comm; rewrite plus_opp; auto with arith.
intros.
simpl in |- *; apply H; auto with arith.
Qed.
Hint Resolve le_transp_l.



Lemma le_transp_r : forall n m p : nat, n + m <= p -> n <= p - m.
intros.
apply le_transp_l.
elim plus_comm; assumption.
Qed.
Hint Resolve le_transp_r.


(************************************************************************)
