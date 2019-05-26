(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                            Nat_complements.v                             *)
(****************************************************************************)
Require Import Arith.
Require Import Compare_dec.

(****************)
Lemma eq_gt_O_dec : forall n : nat, {n = 0} + {n > 0}.

simple destruct n; auto with arith.
Qed.

(********************)
Lemma technical_lemma :
 forall y m : nat, S (y * m + (y + m) + m) = S y * m + (S y + m).

intros; simpl in |- *; elim (plus_comm m (y * m + (y + m))).
rewrite (plus_assoc m (y * m) (y + m)); auto with arith.
Qed.

(**************)
Lemma lt_minus2 : forall n m : nat, n < m -> 0 < m - n.
simple induction 1; intros; elim minus_Sn_m; auto with arith.
Qed.

(***************)
Lemma minus_n_Sm : forall n m : nat, m < n -> pred (n - m) = n - S m.

simple induction 1; intros; elim minus_Sn_m; auto with arith.
Qed.

(************)
Lemma lt_succ : forall n m : nat, n <= S m -> {n <= m} + {n = S m}.

intros; elim (le_lt_eq_dec n (S m) H); auto with arith.
Qed.
