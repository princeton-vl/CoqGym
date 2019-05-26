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
(*                                Lib_Exp.v                                 *)
(****************************************************************************)


Require Export Lib_Mult.


Fixpoint exp_2 (n : nat) : nat :=
  match n return nat with
  | O =>
      (*O*)  1 
      (*S p*) 
  | S p => 2 * exp_2 p
  end.



Fixpoint exp_n (n m : nat) {struct m} : nat :=
  match m return nat with
  | O =>
      (*O*)  1 
      (*S p*) 
  | S p => n * exp_n n p
  end.




(************************************************************************)
(********************************* Base 2 *******************************)
(************************************************************************)

Lemma eq_exp_2_exp_n : forall n : nat, exp_2 n = exp_n 2 n.
simple induction n; auto with arith.
intros.
change (exp_2 (S n0) = 2 * exp_n 2 n0) in |- *.
elim H; auto with arith.
Qed.
Hint Resolve eq_exp_2_exp_n.



Lemma exp_2_n_plus_n : forall n : nat, exp_2 n + exp_2 n = exp_2 (S n).
intro.
rewrite plus_mult.
change (2 * exp_2 n = 2 * exp_2 n) in |- *.
reflexivity.
Qed.
Hint Resolve exp_2_n_plus_n.



Lemma exp_2_plus_pn_pn :
 forall n : nat, 0 < n -> exp_2 (pred n) + exp_2 (pred n) = exp_2 n.
intros.
rewrite exp_2_n_plus_n.
rewrite S_pred_n; auto with arith.
Qed.
Hint Resolve exp_2_plus_pn_pn.



Lemma exp_2_le_pn_n : forall n : nat, exp_2 (pred n) <= exp_2 n.
simple induction n; auto with arith.
intros.
simpl in |- *.
elim plus_n_O; auto with arith.
Qed.
Hint Resolve exp_2_le_pn_n.



Lemma exp_2_pos : forall n : nat, 0 < exp_2 n.
simple induction n; auto with arith.
intros.
simpl in |- *.
elim plus_n_O; auto with arith.
Qed.
Hint Resolve exp_2_pos.



Lemma exp_2_incr : forall n m : nat, n <= m -> exp_2 n <= exp_2 m.
intros.
elim H; auto with arith.
intros.
simpl in |- *.
elim plus_n_O.
elim H1; auto with arith.
Qed.
Hint Resolve exp_2_incr.



Lemma exp_2_n_plus_m : forall n m : nat, exp_2 (n + m) = exp_2 n * exp_2 m.
simple induction n.
intro.
simpl in |- *.
elim plus_n_O; reflexivity.
intros.
simpl in |- *.
elim plus_n_O.
apply sym_equal.
elim plus_n_O.
rewrite H.
elim mult_plus_distr_r; reflexivity.
Qed.
Hint Resolve exp_2_n_plus_m.


(************************************************************************)
(********************************** Base n ******************************)
(************************************************************************)

Lemma exp_n_incr : forall n m p : nat, n <= m -> exp_n n p <= exp_n m p.
simple induction p; auto with arith.
intros.
simpl in |- *.
apply le_mult_csts; auto with arith.
Qed.
Hint Resolve exp_n_incr.



Lemma exp_n_neutre : forall n : nat, exp_n 1 n = 1.
simple induction n; auto with arith.
intros.
simpl in |- *.
rewrite H; auto with arith.
Qed.
Hint Resolve exp_n_neutre.



Lemma exp_n_plus_mult :
 forall n m p : nat, exp_n n (m + p) = exp_n n m * exp_n n p.
simple induction p.
simpl in |- *.
elim plus_n_O.
elim mult_n_Sm.
auto with arith.
elim mult_n_O; auto with arith.

clear p; intros p H_rec.
elim plus_n_Sm.
simpl in |- *.
rewrite H_rec.
elim mult_assoc_reverse.
rewrite (mult_comm n (exp_n n m)).
auto with arith.
Qed.
Hint Resolve exp_n_plus_mult.



Lemma exp_n_permut :
 forall n m p : nat, exp_n n (m * p) = exp_n (exp_n n p) m.
simple induction m; auto with arith.
intros.
simpl in |- *.
elim H.
elim exp_n_plus_mult; auto with arith.
Qed.
Hint Resolve exp_n_permut.



Lemma exp_n_plus_p1 : forall n p : nat, exp_n n (p + 1) = n * exp_n n p.
simple induction p; simpl in |- *.
auto with arith.
intros no H; rewrite H; auto with arith.
Qed.
Hint Resolve exp_n_plus_p1.


Lemma exp_n_pos : forall n p : nat, 0 < n -> 0 < exp_n n p.
simple induction p.
simpl in |- *; auto with arith.
intros.
simpl in |- *.
apply lt_nm_mult; auto with arith.
Qed.
Hint Resolve exp_n_pos.



Lemma le_exp_n_mult : forall n p : nat, 0 < n -> exp_n n p <= n * exp_n n p.
auto with arith.
Qed.
Hint Resolve le_exp_n_mult.


(************************************************************************)
