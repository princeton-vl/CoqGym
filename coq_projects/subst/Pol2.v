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
(*                                  Pol2.v                                  *)
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


           (* Preuve de terminaison: polynome P2 *)

Require Import Le.
Require Import Lt.
Require Import Plus.
Require Import Gt.
Require Import Minus.
Require Import Mult.
Require Import TS.  
Require Import sigma_lift.
Require Import comparith.

Definition e_P2 (b : wsort) (U : TS b) : nat :=
  (fix F (w : wsort) (t : TS w) {struct t} : nat :=
     match t with
     | var _ => 1
     | app t0 t1 => S (F wt t0 + F wt t1)
     | lambda t0 => 2 * F wt t0
     | env t0 t1 => F wt t0 * S (F ws t1)
     | id => 1
     | shift => 1
     | cons t0 t1 => S (F wt t0 + F ws t1)
     | comp t0 t1 => F ws t0 * S (F ws t1)
     | lift t0 => 4 * F ws t0
     | meta_X _ => 1
     | meta_x _ => 1
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


Notation P2 := (e_P2 _) (only parsing).
(* <Warning> : Syntax is discontinued *)

Theorem P2_pos : forall (b : wsort) (M : TS b), e_P2 _ M > 0.
Proof.
simple induction M; simpl in |- *; intros; auto with arith.
Qed.
Hint Resolve P2_pos.

Theorem P2_app : forall M N : terms, reg_app M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros; simpl in |- *; elim Mult.mult_plus_distr_r;
 auto with arith.
Qed.
Hint Resolve P2_app.

Theorem P2_lambda : forall M N : terms, reg_lambda M N -> e_P2 _ M < e_P2 _ N.
Proof.
simple induction 1; intros.
change (2 * (e_P2 _ a * S (4 * e_P2 _ s)) > 2 * e_P2 _ a * S (e_P2 _ s))
 in |- *.
elim mult_assoc_reverse; auto with arith.
Qed.
Hint Resolve P2_lambda.

Theorem P2_clos : forall M N : terms, reg_clos M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros; simpl in |- *.
elim mult_assoc_l; apply gt_mult_reg_l.
auto with arith.
simpl in |- *; auto with arith.
Qed.
Hint Resolve P2_clos.

Theorem P2_varshift1 :
 forall M N : terms, reg_varshift1 M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; simpl in |- *; auto with arith.
Qed.
Hint Resolve P2_varshift1.

Theorem P2_varshift2 :
 forall M N : terms, reg_varshift2 M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros; simpl in |- *; repeat elim plus_n_O;
 auto with arith.
Qed.
Hint Resolve P2_varshift2.

Theorem P2_fvarcons :
 forall M N : terms, reg_fvarcons M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros; simpl in |- *; elim plus_n_O; auto with arith.
Qed.
Hint Resolve P2_fvarcons.

Theorem P2_fvarlift1 :
 forall M N : terms, reg_fvarlift1 M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros.
change (1 * S (4 * e_P2 _ s) > 1) in |- *.
auto with arith.
Qed.
Hint Resolve P2_fvarlift1.

Theorem P2_fvarlift2 :
 forall M N : terms, reg_fvarlift2 M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros; simpl in |- *; repeat elim plus_n_O;
 auto with arith.
Qed.
Hint Resolve P2_fvarlift2.

Theorem P2_rvarcons :
 forall M N : terms, reg_rvarcons M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros; simpl in |- *; repeat elim plus_n_O;
 auto with arith.
Qed.
Hint Resolve P2_rvarcons.

Theorem P2_rvarlift1 :
 forall M N : terms, reg_rvarlift1 M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros; simpl in |- *; repeat elim plus_n_O.
elim mult_n_2; auto with arith.
Qed.
Hint Resolve P2_rvarlift1.

Theorem P2_rvarlift2 :
 forall M N : terms, reg_rvarlift2 M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros.
change
  (1 * S (4 * e_P2 _ s * S (e_P2 _ t)) >
   1 * S (e_P2 _ s * S (1 * S (e_P2 _ t)))) in |- *.
unfold mult at 1 in |- *; unfold mult at 3 in |- *; unfold mult at 4 in |- *;
 repeat elim plus_n_O.
apply gt_n_S; repeat elim mult_n_Sm; elim plus_assoc.
apply gt_plus_plus.
elim mult_assoc_l; auto with arith.
elim mult_n_2; elim mult_sym; auto with arith.
Qed.
Hint Resolve P2_rvarlift2.

Theorem P2_assenv :
 forall M N : sub_explicits, reg_assenv M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros; simpl in |- *.
rewrite mult_assoc_reverse; simpl in |- *; auto with arith.
Qed.
Hint Resolve P2_assenv.

Theorem P2_mapenv :
 forall M N : sub_explicits, reg_mapenv M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros; simpl in |- *; elim Mult.mult_plus_distr_r;
 auto with arith.
Qed.
Hint Resolve P2_mapenv.

Theorem P2_shiftcons :
 forall M N : sub_explicits, reg_shiftcons M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros; simpl in |- *; elim plus_n_O; auto with arith.
Qed.
Hint Resolve P2_shiftcons.

Theorem P2_shiftlift1 :
 forall M N : sub_explicits, reg_shiftlift1 M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros.
change (1 * S (4 * e_P2 _ s) > e_P2 _ s * 2) in |- *.
unfold mult at 1 in |- *; elim plus_n_O.
apply gt_S_l; elim mult_sym; auto with arith.
Qed.
Hint Resolve P2_shiftlift1.

Theorem P2_shiftlift2 :
 forall M N : sub_explicits, reg_shiftlift2 M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros.
change
  (1 * S (4 * e_P2 _ s * S (e_P2 _ t)) > e_P2 _ s * S (1 * S (e_P2 _ t)))
 in |- *.
unfold mult at 1 in |- *; elim plus_n_O; unfold mult at 4 in |- *;
 elim plus_n_O.
apply gt_S_l; repeat elim mult_n_Sm; elim plus_assoc.
apply gt_plus_plus.
elim mult_assoc_l; auto with arith.
elim mult_n_2; elim mult_sym; auto with arith.
Qed.
Hint Resolve P2_shiftlift2.

Theorem P2_lift1 :
 forall M N : sub_explicits, reg_lift1 M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros.
change (4 * e_P2 _ s * S (4 * e_P2 _ t) > 4 * (e_P2 _ s * S (e_P2 _ t)))
 in |- *.
elim mult_assoc_reverse; auto with arith.
Qed.
Hint Resolve P2_lift1.

Theorem P2_lift2 :
 forall M N : sub_explicits, reg_lift2 M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros.
change
  (4 * e_P2 _ s * S (4 * e_P2 _ t * S (e_P2 _ u)) >
   4 * (e_P2 _ s * S (e_P2 _ t)) * S (e_P2 _ u)) in |- *.
elim mult_assoc_reverse;
 elim (mult_assoc_l (4 * e_P2 _ s) (S (e_P2 _ t)) (S (e_P2 _ u)));
 apply gt_mult_reg_l.
auto with arith.
apply gt_S_l; apply gt_mult_reg_r.
auto with arith.
apply gt_trans with (3 * e_P2 _ t).
auto with arith.
simpl in |- *; elim plus_n_O; rewrite S_plus; apply plus_gt_compat_l.
elim mult_n_2; auto with arith.
Qed.
Hint Resolve P2_lift2.

Theorem P2_liftenv :
 forall M N : sub_explicits, reg_liftenv M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros.
change
  (4 * e_P2 _ s * S (S (e_P2 _ a + e_P2 _ t)) >
   S (e_P2 _ a + e_P2 _ s * S (e_P2 _ t))) in |- *.
cut (S (S (e_P2 _ a + e_P2 _ t)) = e_P2 _ a + (e_P2 _ t + 2)).
intro H1; rewrite H1. 
rewrite (S_plus (e_P2 _ a + e_P2 _ s * S (e_P2 _ t)));
 rewrite comparith.mult_plus_distr_r.
elim plus_assoc; apply gt_plus_plus.
apply gt_mult_l.
auto with arith.
auto with arith.
replace (e_P2 _ t + 2) with (e_P2 _ t + 1 + 1).
rewrite comparith.mult_plus_distr_r; apply gt_plus_plus.
elim S_plus; elim mult_assoc_l.
apply gt_mult_l; auto with arith.
apply gt_mult_l; auto with arith.
elim (plus_n_Sm (e_P2 _ t) 1); auto with arith.
rewrite plus_assoc; elim plus_n_Sm; elim plus_n_Sm; elim plus_n_O;
 auto with arith.
Qed.
Hint Resolve P2_liftenv.

Theorem P2_idl :
 forall M N : sub_explicits, reg_idl M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; simpl in |- *; intros; elim plus_n_O; auto with arith.
Qed.
Hint Resolve P2_idl.

Theorem P2_idr :
 forall M N : sub_explicits, reg_idr M N -> e_P2 _ M > e_P2 _ N.
Proof. 
simple induction 1; intros; simpl in |- *; auto with arith.
Qed.
Hint Resolve P2_idr.

Theorem P2_liftid :
 forall M N : sub_explicits, reg_liftid M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros; simpl in |- *; auto with arith.
Qed.
Hint Resolve P2_liftid.

Theorem P2_id : forall M N : terms, reg_id M N -> e_P2 _ M > e_P2 _ N.
Proof.
simple induction 1; intros; simpl in |- *; auto with arith.
Qed.
Hint Resolve P2_id.





