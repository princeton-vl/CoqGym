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
(*                             terminaison_SL.v                             *)
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


              (* Preuve de terminaison *)  


Require Import Le.
Require Import Lt.
Require Import Plus.
Require Import Gt.
Require Import Minus.
Require Import Mult.
Require Import sur_les_relations.
Require Import TS. 
Require Import sigma_lift.  
Require Import comparith.
Require Import Pol1.
Require Import Pol2.

Section ordre.

Variable A : Set.
Variable f g : A -> nat.

Definition e_lexfg (a b : A) := f a > f b \/ f a = f b /\ g a > g b.

Lemma lexfg_notherian : explicit_noetherian _ e_lexfg. 
Proof.
unfold explicit_noetherian in |- *; unfold universal in |- *;
 unfold hereditary in |- *; unfold adjoint in |- *; 
 unfold sub in |- *; unfold a_set in |- *.
intros P H.
cut (forall (n m : nat) (a : A), n > f a \/ n = f a /\ m > g a -> P a).
intros H0 x; apply (H0 (S (f x)) 0).
auto with arith.
simple induction n; simple induction m.
(* m=n=0 *)
simple induction 1; intro H1.
absurd (0 > f a); auto with arith.
elim H1; intros.
absurd (0 > g a); auto with arith.
(* n=0, m=(S y) *)
intros y H' a H0.
apply H; intros b lexfgab. 
apply H'; right.
elim H0; intro H1.
absurd (0 > f a); auto with arith.
elim H1; intros H2 H3; elim lexfgab; intro H4.
absurd (0 > f b).
auto with arith.
rewrite H2; assumption.
elim H4; intros.
split.
rewrite H2; assumption.
apply le_gt_trans with (g a); auto with arith.
(* n=(S y), m=0 *)
intros a H0'; apply H; intros b lexfgab.
apply (H0 (g a) b); elim H0'; intro H1.
elim lexfgab; intro H2.
left; apply le_gt_trans with (f a); auto with arith.
elim H2; intros H3 H4; elim (gt_S n0 (f a) H1); intro H5.
left; elim H3; assumption.
right; split.
elim H3; auto with arith.
assumption.
elim H1; intros H2 H3.
absurd (0 > g a); auto with arith.
(* n=(S y), m=(S y0) *)
intros y0 H0' a H1; apply H; intros b lexfgab.
apply H0'; elim H1; elim lexfgab; intros H2 H3.
left; apply le_gt_trans with (f a); auto with arith.
elim H2; intros H4 H5; left; elim H4; assumption.
elim H3; intros H4 H5; left; rewrite H4; assumption.
elim H2; intros H4 H5; elim H3; intros H6 H7.
right; split.
apply trans_equal with (f a); assumption.
apply le_gt_trans with (g a); auto with arith.
Qed.

End ordre.

Notation lexfg := (e_lexfg _) (only parsing).
(* <Warning> : Syntax is discontinued *)

Theorem lexfg_systemSL :
 forall (b : wsort) (M N : TS b),
 e_systemSL _ M N -> e_lexfg _ (e_P1 b) (e_P2 b) M N.
Proof.
red in |- *; simple induction 1; auto with arith.
Qed.
Hint Resolve lexfg_systemSL.
 
Theorem lexfg_app_l :
 forall a a' b : terms,
 e_lexfg _ (e_P1 wt) (e_P2 wt) a a' ->
 e_lexfg _ (e_P1 wt) (e_P2 wt) (app a b) (app a' b).
Proof.
unfold e_lexfg in |- *; simple induction 1; simpl in |- *; auto with arith.
intros; elim H0; auto with arith.
Qed.
Hint Resolve lexfg_app_l.

Theorem lexfg_app_r :
 forall a b b' : terms,
 e_lexfg _ (e_P1 wt) (e_P2 wt) b b' ->
 e_lexfg _ (e_P1 wt) (e_P2 wt) (app a b) (app a b').
Proof.
unfold e_lexfg in |- *; simple induction 1; simpl in |- *; auto with arith.
intros; elim H0; auto with arith.
Qed.
Hint Resolve lexfg_app_r.

Theorem lexfg_lambda :
 forall a a' : terms,
 e_lexfg _ (e_P1 wt) (e_P2 wt) a a' ->
 e_lexfg _ (e_P1 wt) (e_P2 wt) (lambda a) (lambda a').
Proof.
unfold e_lexfg in |- *; simple induction 1; simpl in |- *; auto with arith.
intros; elim H0; auto with arith.
Qed.
Hint Resolve lexfg_lambda.

Theorem lexfg_env_t :
 forall (a a' : terms) (s : sub_explicits),
 e_lexfg _ (e_P1 wt) (e_P2 wt) a a' ->
 e_lexfg _ (e_P1 wt) (e_P2 wt) (env a s) (env a' s).
Proof.
unfold e_lexfg in |- *; simple induction 1; simpl in |- *; auto with arith.
intros; elim H0; auto with arith.
Qed.
Hint Resolve lexfg_env_t.

Theorem lexfg_env_s :
 forall (a : terms) (s s' : sub_explicits),
 e_lexfg _ (e_P1 ws) (e_P2 ws) s s' ->
 e_lexfg _ (e_P1 wt) (e_P2 wt) (env a s) (env a s').
Proof.
unfold e_lexfg in |- *; simple induction 1; simpl in |- *; auto with arith.
intros; elim H0; auto with arith.
Qed.
Hint Resolve lexfg_env_s.

Theorem lexfg_cons_t :
 forall (a a' : terms) (s : sub_explicits),
 e_lexfg _ (e_P1 wt) (e_P2 wt) a a' ->
 e_lexfg _ (e_P1 ws) (e_P2 ws) (cons a s) (cons a' s).
Proof.
unfold e_lexfg in |- *; simple induction 1; simpl in |- *; auto with arith.
intros; elim H0; auto with arith.
Qed.
Hint Resolve lexfg_cons_t.

Theorem lexfg_cons_s :
 forall (a : terms) (s s' : sub_explicits),
 e_lexfg _ (e_P1 ws) (e_P2 ws) s s' ->
 e_lexfg _ (e_P1 ws) (e_P2 ws) (cons a s) (cons a s').
Proof.
unfold e_lexfg in |- *; simple induction 1; simpl in |- *; auto with arith.
intros; elim H0; auto with arith.
Qed.
Hint Resolve lexfg_cons_s.

Theorem lexfg_comp_l :
 forall s s' t : sub_explicits,
 e_lexfg _ (e_P1 ws) (e_P2 ws) s s' ->
 e_lexfg _ (e_P1 ws) (e_P2 ws) (comp s t) (comp s' t).
Proof.
unfold e_lexfg in |- *; simple induction 1; simpl in |- *; auto with arith.
intros; elim H0; auto with arith.
Qed.
Hint Resolve lexfg_comp_l.

Theorem lexfg_comp_r :
 forall s t t' : sub_explicits,
 e_lexfg _ (e_P1 ws) (e_P2 ws) t t' ->
 e_lexfg _ (e_P1 ws) (e_P2 ws) (comp s t) (comp s t').
Proof.
unfold e_lexfg in |- *; simple induction 1; simpl in |- *; auto with arith.
intros; elim H0; auto with arith.
Qed.
Hint Resolve lexfg_comp_r.

Theorem lexfg_lift :
 forall s s' : sub_explicits,
 e_lexfg _ (e_P1 ws) (e_P2 ws) s s' ->
 e_lexfg _ (e_P1 ws) (e_P2 ws) (lift s) (lift s').
Proof.
unfold e_lexfg in |- *; simple induction 1; simpl in |- *; intros.
auto with arith.
elim H0; intros; right; split.
assumption.
change (4 * e_P2 _ s > 4 * e_P2 _ s') in |- *.
auto with arith.
Qed.
Hint Resolve lexfg_lift.

Theorem lexfg_relSL :
 forall (b : wsort) (M N : TS b),
 e_relSL _ M N -> e_lexfg _ (e_P1 b) (e_P2 b) M N.
Proof.
simple induction 1; auto with arith.
Qed.


(***************************************************)
(*   la relation sigma-lift (SL) est noetherienne  *)
(***************************************************)

Theorem relSL_noetherian :
 forall b : wsort, explicit_noetherian _ (e_relSL b).
Proof.
intro b; apply noether_inclus with (e_lexfg _ (e_P1 b) (e_P2 b)).
apply lexfg_notherian.
exact (lexfg_relSL b).
Qed.

