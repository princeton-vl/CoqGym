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
(*                               Lib_Square.v                               *)
(****************************************************************************)
Require Export Lib_Exp.

Definition Square (n : nat) := n * n.

Lemma Square_exp_2 : forall n : nat, Square (exp_2 n) = exp_2 (2 * n).
intro.
unfold Square in |- *.
elim exp_2_n_plus_m.
rewrite plus_mult; reflexivity.
Qed.
Hint Resolve Square_exp_2.



Lemma eq_Square_exp_n : forall n : nat, Square n = exp_n n 2.
unfold Square in |- *.
simpl in |- *.
intro; elim (mult_comm 1 n); simpl in |- *; auto with arith.
Qed.
Hint Resolve eq_Square_exp_n.

Lemma Square_inc : forall n m : nat, n <= m -> Square n <= Square m.
intros.
unfold Square in |- *.
apply le_mult_csts; assumption.
Qed.
Hint Resolve Square_inc.

Lemma Square_strict_inc : forall n m : nat, n < m -> Square n < Square m.
intros.
unfold Square in |- *.
apply lt_mult_csts; assumption.
Qed.
Hint Resolve Square_strict_inc.



Lemma le_n_Square : forall n : nat, n <= Square n.
simple induction n; auto with arith.
intros.
unfold Square in |- *.
simpl in |- *.
apply le_n_S.
elim mult_comm; simpl in |- *.
change (n0 <= n0 + (n0 + Square n0)) in |- *.
apply le_plus_l.
Qed.
Hint Resolve le_n_Square.
