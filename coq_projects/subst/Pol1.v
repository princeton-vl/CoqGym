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
(*                                  Pol1.v                                  *)
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


       (* Preuve de terminaison: Polynome P1 *)

Require Import Le.
Require Import Lt.
Require Import Plus.
Require Import Gt.
Require Import Minus.
Require Import Mult.
Require Import TS. 
Require Import sigma_lift.  
Require Import comparith.

Definition e_P1 (b : wsort) (U : TS b) : nat :=
  (fix F (w : wsort) (t : TS w) {struct t} : nat :=
     match t with
     | var n => power2 (S n)
     | app t0 t1 => F wt t0 + F wt t1
     | lambda t0 => F wt t0 + 2
     | env t0 t1 => F wt t0 * F ws t1
     | id => 2
     | shift => 2
     | cons t0 t1 => F wt t0 + F ws t1
     | comp t0 t1 => F ws t0 * F ws t1
     | lift t0 => F ws t0
     | meta_X _ => 2
     | meta_x _ => 2
     end) b U.
(* var *) 
(* app *) 
(* lam *) 
(* env *) 
(*  id *)  
(*  |  *) 
(*  .  *) 
(*  o  *) 
(*  || *) 
(*  X  *) 
(*  x  *)  

Notation P1 := (e_P1 _) (only parsing).
(* <Warning> : Syntax is discontinued *)


Theorem gt_P1_1 : forall (b : wsort) (M : TS b), e_P1 _ M > 1.
Proof.
simple induction M; intros; simpl in |- *; auto with arith.
(* var *)
elim plus_n_O; elim n; simpl in |- *.
auto with arith.
intros; elim plus_n_O; auto with arith.
Qed.
Hint Resolve gt_P1_1.

Theorem P1_app : forall M N : terms, reg_app M N -> e_P1 _ M = e_P1 _ N.
Proof. 
simple induction 1; intros; simpl in |- *; auto with arith.
Qed.
Hint Resolve P1_app.

Theorem P1_lambda : forall M N : terms, reg_lambda M N -> e_P1 _ M > e_P1 _ N.
Proof. 
simple induction 1; intros; simpl in |- *; rewrite Mult.mult_plus_distr_r;
 auto with arith.
Qed.
Hint Resolve P1_lambda.

Theorem P1_clos : forall M N : terms, reg_clos M N -> e_P1 _ M = e_P1 _ N.
Proof. 
simple induction 1; intros; simpl in |- *; auto with arith.
Qed.
Hint Resolve P1_clos.
 
Theorem P1_varshift1 :
 forall M N : terms, reg_varshift1 M N -> e_P1 _ M = e_P1 _ N.
Proof. 
simple induction 1; intros.
change (power2 (S n) * 2 = 2 * power2 (S n)) in |- *.
auto with arith.
Qed.
Hint Resolve P1_varshift1.

Theorem P1_varshift2 :
 forall M N : terms, reg_varshift2 M N -> e_P1 _ M = e_P1 _ N.
Proof. 
simple induction 1; intros.
change (power2 (S n) * (2 * e_P1 _ s) = 2 * power2 (S n) * e_P1 _ s) in |- *.
elim mult_permut; auto with arith.
Qed.
Hint Resolve P1_varshift2.

Theorem P1_fvarcons :
 forall M N : terms, reg_fvarcons M N -> e_P1 _ M > e_P1 _ N.
Proof.
simple induction 1; intros; simpl in |- *; elim plus_n_O; auto with arith.
Qed.
Hint Resolve P1_fvarcons.

Theorem P1_fvarlift1 :
 forall M N : terms, reg_fvarlift1 M N -> e_P1 _ M > e_P1 _ N.
Proof.
simple induction 1; intros.
change (2 * e_P1 _ s > 2) in |- *.
auto with arith.
Qed.
Hint Resolve P1_fvarlift1.

Theorem P1_fvarlift2 :
 forall M N : terms, reg_fvarlift2 M N -> e_P1 _ M > e_P1 _ N.
Proof.
simple induction 1; intros.
change (2 * (e_P1 _ s * e_P1 _ t) > 2 * e_P1 _ t) in |- *.
auto with arith.
Qed.
Hint Resolve P1_fvarlift2.

Theorem P1_rvarcons :
 forall M N : terms, reg_rvarcons M N -> e_P1 _ M > e_P1 _ N.
Proof.
simple induction 1; intros.
change (2 * power2 (S n) * (e_P1 _ a + e_P1 _ s) > power2 (S n) * e_P1 _ s)
 in |- *.
rewrite comparith.mult_plus_distr_r; auto with arith.
Qed.
Hint Resolve P1_rvarcons.

Theorem P1_rvarlift1 :
 forall M N : terms, reg_rvarlift1 M N -> e_P1 _ M = e_P1 _ N.
Proof.
simple induction 1; intros.
change (2 * power2 (S n) * e_P1 _ s = power2 (S n) * (e_P1 _ s * 2)) in |- *.
elim mult_assoc_l; elim (mult_permut (power2 (S n)) 2 (e_P1 _ s)).
auto with arith.
Qed.
Hint Resolve P1_rvarlift1.

Theorem P1_rvarlift2 :
 forall M N : terms, reg_rvarlift2 M N -> e_P1 _ M = e_P1 _ N.
Proof.
simple induction 1; intros.
change
  (2 * power2 (S n) * (e_P1 _ s * e_P1 _ t) =
   power2 (S n) * (e_P1 _ s * (2 * e_P1 _ t))) in |- *.
elim (mult_sym (power2 (S n)) 2); elim mult_assoc_l; auto with arith.
Qed.
Hint Resolve P1_rvarlift2.

Theorem P1_assenv :
 forall M N : sub_explicits, reg_assenv M N -> e_P1 _ M = e_P1 _ N.
Proof.
simple induction 1; intros; simpl in |- *; auto with arith.
Qed.
Hint Resolve P1_assenv.

Theorem P1_mapenv :
 forall M N : sub_explicits, reg_mapenv M N -> e_P1 _ M = e_P1 _ N.
Proof.
simple induction 1; intros; simpl in |- *; auto with arith.
Qed.
Hint Resolve P1_mapenv.

Theorem P1_shiftcons :
 forall M N : sub_explicits, reg_shiftcons M N -> e_P1 _ M > e_P1 _ N.
Proof.
simple induction 1; intros; simpl in |- *; elim plus_n_O; auto with arith.
Qed.
Hint Resolve P1_shiftcons.

Theorem P1_shiftlift1 :
 forall M N : sub_explicits, reg_shiftlift1 M N -> e_P1 _ M = e_P1 _ N.
Proof.
simple induction 1; intros; simpl in |- *; elim plus_n_O; auto with arith.
Qed.
Hint Resolve P1_shiftlift1.

Theorem P1_shiftlift2 :
 forall M N : sub_explicits, reg_shiftlift2 M N -> e_P1 _ M = e_P1 _ N.
Proof.
simple induction 1; intros; simpl in |- *; do 2 elim plus_n_O;
 auto with arith.
Qed.
Hint Resolve P1_shiftlift2.

Theorem P1_lift1 :
 forall M N : sub_explicits, reg_lift1 M N -> e_P1 _ M = e_P1 _ N.
Proof.
simple induction 1; intros; simpl in |- *; auto with arith.
Qed.
Hint Resolve P1_lift1.

Theorem P1_lift2 :
 forall M N : sub_explicits, reg_lift2 M N -> e_P1 _ M = e_P1 _ N.
Proof.
simple induction 1; intros; simpl in |- *; auto with arith.
Qed.
Hint Resolve P1_lift2.

Theorem P1_liftenv :
 forall M N : sub_explicits, reg_liftenv M N -> e_P1 _ M > e_P1 _ N.
Proof.
simple induction 1; intros; simpl in |- *;
 rewrite comparith.mult_plus_distr_r; auto with arith.
Qed.
Hint Resolve P1_liftenv.

Theorem P1_idl :
 forall M N : sub_explicits, reg_idl M N -> e_P1 _ M > e_P1 _ N.
Proof.
simple induction 1; intros; simpl in |- *; elim plus_n_O; auto with arith.
Qed.
Hint Resolve P1_idl.

Theorem P1_idr :
 forall M N : sub_explicits, reg_idr M N -> e_P1 _ M > e_P1 _ N.
Proof.
simple induction 1; intros; simpl in |- *; auto with arith.
Qed.
Hint Resolve P1_idr.

Theorem P1_liftid :
 forall M N : sub_explicits, reg_liftid M N -> e_P1 _ M = e_P1 _ N.
Proof.
simple induction 1; intros; simpl in |- *; auto with arith.
Qed.
Hint Resolve P1_liftid.

Theorem P1_id : forall M N : terms, reg_id M N -> e_P1 _ M > e_P1 _ N.
Proof.
simple induction 1; intros; simpl in |- *; auto with arith.
Qed.
Hint Resolve P1_id.
