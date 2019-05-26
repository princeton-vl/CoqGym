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
(*                               comparith.v                                *)
(****************************************************************************)

(*****************************************************************************)
(*          Projet Coq  - Calculus of Inductive Constructions V5.8           *)
(*****************************************************************************)
(*                                                                           *)
(*      Meta-theory of the explicit substitution calculus lambda-env         *)
(*      Amokrane Saibi                                                       *)
(*                                                                           *)
(*      September 1993                                                       *)
(*                                                                           *)
(*****************************************************************************)



              (*         complements d arithmetique            *)


Require Import Le.
Require Import Lt.
Require Import Plus.
Require Import Gt.
Require Import Minus.
Require Import Mult.

Hint Resolve mult_n_O mult_n_Sm plus_le_compat. 

(* gt *)

Goal forall n m : nat, n > m -> S n > m.
auto with arith.
Save gt_S_l.
Hint Resolve gt_S_l.

Goal forall n m : nat, n > S m -> n > m.
auto with arith.
Save gt_S_r.
Hint Resolve gt_S_r.
 
(* plus *)

Goal forall n m p : nat, n = m -> p + n = p + m.
intros; elim p; elim H; auto with arith.
Save eq_plus_reg_r.
Hint Resolve eq_plus_reg_r.

Goal forall n m p : nat, n = m -> n + p = m + p.
intros; elim p; elim H; auto with arith.
Save eq_plus_reg_l.
Hint Resolve eq_plus_reg_l.

Goal forall n m p : nat, n > m -> n + p > m + p.
intros; elim (plus_comm p m); elim (plus_comm p n); auto with arith.
Save gt_reg_r.
Hint Resolve gt_reg_r.

Goal forall n m p q : nat, n > m -> p > q -> n + p > m + q.
simple induction 1; intros; simpl in |- *; auto with arith.
Save gt_plus_plus.
Hint Resolve gt_plus_plus.

Goal forall p : nat, p > 0 -> forall n : nat, p + n > n.
simple induction 1; intros.
auto with arith.
simpl in |- *; auto with arith.
Save gt_plus_l.
Hint Resolve gt_plus_l.

Goal forall p : nat, p > 0 -> forall n : nat, n + p > n.
intros; elim (plus_comm p n); auto with arith.
Save gt_plus_r.
Hint Resolve gt_plus_r.

Goal forall n m p : nat, n > m -> n + p > m.
auto with arith.
Save gt_plus_trans_r.
Hint Resolve gt_plus_trans_r.

Goal forall n m p : nat, n > m -> p + n > m.
intros; elim (plus_comm n p); auto with arith.
Save gt_plus_trans_l.
Hint Resolve gt_plus_trans_l.

Goal forall n : nat, S n = n + 1.
simple induction n.
auto with arith.
simpl in |- *; auto with arith.
Save S_plus.
Hint Resolve S_plus.
 
(* mult *)

Goal forall n m : nat, n * m = m * n.
simple induction n; intros.
auto with arith.
simpl in |- *; elim mult_n_Sm; elim H; auto with arith.
Save mult_sym.
Hint Resolve mult_sym.

Goal forall n m p : nat, n * (m * p) = n * m * p.
intros n m p; elim n; simpl in |- *.
auto with arith.
intros y H; rewrite mult_plus_distr_r; elim H; auto with arith.
Save mult_assoc_l.
Hint Resolve mult_assoc_l.

Goal forall n m p : nat, n * (m * p) = m * (n * p).
intros; rewrite (mult_assoc_l m n p); rewrite (mult_sym m n); auto with arith.
Save mult_permut.
Hint Resolve mult_permut. 

Goal forall n m p : nat, p * (n + m) = p * n + p * m.
intros n m p; elim p.
auto with arith.
simpl in |- *; intros y H; rewrite H; elim plus_assoc; elim plus_assoc.
pattern (y * n + (m + y * m)) in |- *; elim plus_permute; trivial with arith.
Save mult_plus_distr_r.
Hint Resolve comparith.mult_plus_distr_r.

Goal forall n : nat, n * 2 = n + n.
simple induction n.
auto with arith.
intros; simpl in |- *; rewrite H; auto with arith.
Save mult_n_2. 
Hint Resolve mult_n_2.
 
Goal forall n : nat, n = n * 1.  
simple induction n.
auto with arith.
simpl in |- *; auto with arith.
Save mult_n_1. 
Hint Resolve mult_n_1.

Goal forall n m p : nat, n = m -> p * n = p * m.
intros; elim p; elim H; auto with arith.
Save eq_mult_reg_r.
Hint Resolve eq_mult_reg_r.

Goal forall n m p : nat, n = m -> n * p = m * p.
intros; elim p; elim H; auto with arith.
Save eq_mult_reg_l.
Hint Resolve eq_mult_reg_l.

Goal forall p : nat, p > 0 -> forall n m : nat, n > m -> p * n > p * m.
simple induction p.
intros H n m H0; absurd (0 > 0); auto with arith.
intros y H H0 n m H1; elim (gt_O_eq y); intros.
simpl in |- *; auto with arith.
elim H2; simpl in |- *; elim (plus_n_O n); elim (plus_n_O m);
 trivial with arith.
Save gt_mult_reg_l.
Hint Resolve gt_mult_reg_l.

Goal forall p : nat, p > 0 -> forall n m : nat, n > m -> n * p > m * p.
intros; elim (mult_sym p n); elim (mult_sym p m); auto with arith.
Save gt_mult_reg_r.
Hint Resolve gt_mult_reg_r.

Goal forall p : nat, p > 1 -> forall n : nat, n > 0 -> p * n > n.
simple induction p.
intros H n H0; absurd (0 > 1); auto with arith.
intros y H H0 n H1; simpl in |- *; apply gt_plus_r; replace 0 with (y * 0);
 auto with arith.
Save gt_mult_l.
Hint Resolve gt_mult_l.

Goal forall p : nat, p > 1 -> forall n : nat, n > 0 -> n * p > n.
intros; elim (mult_sym p n); auto with arith.
Save gt_mult_r.
Hint Resolve gt_mult_r.

Goal forall p : nat, p > 0 -> forall n m : nat, n > m -> p * n > m.
simple induction p.
intros H n m H0; simpl in |- *; absurd (0 > 0); auto with arith.
intros y H H0 n m H1; simpl in |- *; elim (gt_O_eq y); intro H2.
auto with arith.
elim H2; simpl in |- *; elim plus_n_O; assumption.
Save gt_mult_trans_r.
Hint Resolve gt_mult_trans_r.

Goal forall p : nat, p > 0 -> forall n m : nat, n > m -> n * p > m.
intros; elim (mult_sym p n); auto with arith.
Save gt_mult_trans_l.
Hint Resolve gt_mult_trans_l.

(* power2: (power2 n)=2^n *)

Fixpoint power2 (n : nat) : nat :=
  match n with
  | O => 1
  | S p => 2 * power2 p
  end.

Goal forall n : nat, power2 n > 0.
simple induction n; simpl in |- *; intros.
auto with arith.
elim plus_n_O; auto with arith.
Save gt_power2_O.
Hint Resolve gt_power2_O.

 
