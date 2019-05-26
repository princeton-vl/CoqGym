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
(*                              resoudPC_SL.v                               *)
(****************************************************************************)


      (* confluence locale de sigma_lift: resolution des paires critiques *)

Require Import TS.
Require Import sur_les_relations.
Require Import sigma_lift.
Require Import determinePC_SL.

(*** app ***)

Goal
forall a b : terms,
exists u : terms,
  e_relSLstar _ (app (env a id) (env b id)) u /\ e_relSLstar _ (app a b) u.
intros; exists (app a b); split; red in |- *.
apply star_trans1 with (app a (env b id)); auto.
auto.
Save PC_app_id.
Hint Resolve PC_app_id.

Goal
forall (a a' b : terms) (s : sub_explicits),
e_relSL _ a a' ->
exists u : terms,
  e_relSLstar _ (app (env a s) (env b s)) u /\
  e_relSLstar _ (env (app a' b) s) u.
intros; exists (app (env a' s) (env b s)); auto 6.
Save PC1_app_ctxt_l.
Hint Resolve PC1_app_ctxt_l.

Goal
forall (a b b' : terms) (s : sub_explicits),
e_relSL _ b b' ->
exists u : terms,
  e_relSLstar _ (app (env a s) (env b s)) u /\
  e_relSLstar _ (env (app a b') s) u.
intros; exists (app (env a s) (env b' s)); auto 6.
Save PC2_app_ctxt_l.
Hint Resolve PC2_app_ctxt_l.

Goal
forall (a b : terms) (s s' : sub_explicits),
e_relSL _ s s' ->
exists u : terms,
  e_relSLstar _ (app (env a s) (env b s)) u /\
  e_relSLstar _ (env (app a b) s') u.
intros; exists (app (env a s') (env b s')); split; red in |- *.
apply star_trans1 with (app (env a s') (env b s)); auto.
auto.
Save PC_app_ctxt_r.
Hint Resolve PC_app_ctxt_r.

Goal
forall (a b x' : terms) (s : sub_explicits),
e_relSL _ (app a b) x' ->
exists u : terms,
  e_relSLstar _ (app (env a s) (env b s)) u /\ e_relSLstar _ (env x' s) u.
intros a b x' s H; pattern x' in |- *; apply case_SLapp with a b; auto.
Save PC_app_ctxt_l.
Hint Resolve PC_app_ctxt_l.

(*** lambda ***)

Goal
forall a : terms,
exists u : terms,
  e_relSLstar _ (lambda (env a (lift id))) u /\ e_relSLstar _ (lambda a) u.
intro; exists (lambda a); split; red in |- *.
apply star_trans1 with (lambda (env a id)); auto.
auto.
Save PC_lambda_id.
Hint Resolve PC_lambda_id.

Goal
forall (a x' : terms) (s : sub_explicits),
e_relSL _ (lambda a) x' ->
exists u : terms,
  e_relSLstar _ (lambda (env a (lift s))) u /\ e_relSLstar _ (env x' s) u.
intros a x' s H; pattern x' in |- *; apply case_SLlambda with a; intros.
2: assumption.
exists (lambda (env a' (lift s))); auto 6.
Save PC_lambda_ctxt_l.
Hint Resolve PC_lambda_ctxt_l.

Goal
forall (a : terms) (s s' : sub_explicits),
e_relSL _ s s' ->
exists u : terms,
  e_relSLstar _ (lambda (env a (lift s))) u /\
  e_relSLstar _ (env (lambda a) s') u.
intros; exists (lambda (env a (lift s'))); auto 8.
Save PC_lambda_ctxt_r.
Hint Resolve PC_lambda_ctxt_r.

(*** Clos ***)

Goal
forall (a : terms) (s : sub_explicits),
exists u : terms,
  e_relSLstar _ (env a (comp s id)) u /\ e_relSLstar _ (env a s) u.
intros; exists (env a s); split; red in |- *; auto.
Save PC1_clos_id.
Hint Resolve PC1_clos_id.

Goal
forall (a b : terms) (s t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (app a b) (comp s t)) u /\
  e_relSLstar _ (env (app (env a s) (env b s)) t) u.
intros; exists (app (env a (comp s t)) (env b (comp s t))); split;
 red in |- *.
auto.
apply star_trans1 with (app (env (env a s) t) (env (env b s) t)).
auto.
apply star_trans1 with (app (env a (comp s t)) (env (env b s) t)); auto.
Save PC_clos_app.
Hint Resolve PC_clos_app.

Goal
forall (a : terms) (s t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (lambda a) (comp s t)) u /\
  e_relSLstar _ (env (lambda (env a (lift s))) t) u.
intros; exists (lambda (env a (lift (comp s t)))); split; red in |- *.
auto.
apply star_trans1 with (lambda (env (env a (lift s)) (lift t))).
auto.
apply star_trans1 with (lambda (env a (comp (lift s) (lift t)))); auto 6.
Save PC_clos_lambda.
Hint Resolve PC_clos_lambda.

Goal
forall (a : terms) (s s1 t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (env a s1) (comp s t)) u /\
  e_relSLstar _ (env (env a (comp s1 s)) t) u.
intros; exists (env a (comp s1 (comp s t))); split; red in |- *.
auto.
apply star_trans1 with (env a (comp (comp s1 s) t)); auto.
Save PC_clos_clos.
Hint Resolve PC_clos_clos.

Goal
forall (n : nat) (t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var n) (comp shift t)) u /\
  e_relSLstar _ (env (var (S n)) t) u.
intros; exists (env (var (S n)) t); auto 6.
Save PC_clos_varshift1.
Hint Resolve PC_clos_varshift1.

Goal
forall (n : nat) (s t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var n) (comp (comp shift s) t)) u /\
  e_relSLstar _ (env (env (var (S n)) s) t) u.
intros; exists (env (var (S n)) (comp s t)); split; red in |- *.
apply star_trans1 with (env (var n) (comp shift (comp s t))); auto.
auto.
Save PC_clos_varshift2.
Hint Resolve PC_clos_varshift2.

Goal
forall (a : terms) (s t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var 0) (comp (cons a s) t)) u /\
  e_relSLstar _ (env a t) u.
intros; exists (env a t); split; red in |- *.
apply star_trans1 with (env (var 0) (cons (env a t) (comp s t))); auto.
auto.
Save PC_clos_fvarcons.
Hint Resolve PC_clos_fvarcons.

Goal
forall s t : sub_explicits,
exists u : terms,
  e_relSLstar _ (env (var 0) (comp (lift s) t)) u /\
  e_relSLstar _ (env (var 0) t) u.
intros; exists (env (var 0) t); auto 6.
Save PC_clos_fvarlift1.
Hint Resolve PC_clos_fvarlift1.

Goal
forall s1 s2 t : sub_explicits,
exists u : terms,
  e_relSLstar _ (env (var 0) (comp (comp (lift s1) s2) t)) u /\
  e_relSLstar _ (env (env (var 0) s2) t) u.
intros; exists (env (var 0) (comp s2 t)); split; red in |- *.
apply star_trans1 with (env (var 0) (comp (lift s1) (comp s2 t))); auto.
auto.
Save PC_clos_fvarlift2.
Hint Resolve PC_clos_fvarlift2.

Goal
forall (n : nat) (a : terms) (s t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var (S n)) (comp (cons a s) t)) u /\
  e_relSLstar _ (env (env (var n) s) t) u.
intros; exists (env (var n) (comp s t)); split; red in |- *.
apply star_trans1 with (env (var (S n)) (cons (env a t) (comp s t))); auto.
auto.
Save PC_clos_rvarcons.
Hint Resolve PC_clos_rvarcons.

Goal
forall (n : nat) (s t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var (S n)) (comp (lift s) t)) u /\
  e_relSLstar _ (env (env (var n) (comp s shift)) t) u.
intros; exists (env (var n) (comp s (comp shift t))); split; red in |- *.
auto.
apply star_trans1 with (env (var n) (comp (comp s shift) t)); auto.
Save PC_clos_rvarlift1.
Hint Resolve PC_clos_rvarlift1.

Goal
forall (n : nat) (s1 s2 t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var (S n)) (comp (comp (lift s1) s2) t)) u /\
  e_relSLstar _ (env (env (var n) (comp s1 (comp shift s2))) t) u.
intros; exists (env (var n) (comp s1 (comp shift (comp s2 t)))); split;
 red in |- *.
apply star_trans1 with (env (var (S n)) (comp (lift s1) (comp s2 t))); auto.
apply star_trans1 with (env (var n) (comp (comp s1 (comp shift s2)) t)).
auto.
apply star_trans1 with (env (var n) (comp s1 (comp (comp shift s2) t)));
 auto 6.
Save PC_clos_rvarlift2.
Hint Resolve PC_clos_rvarlift2.

Goal
forall (a : terms) (t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env a (comp id t)) u /\ e_relSLstar _ (env a t) u.
intros; exists (env a t); auto 8.
Save PC2_clos_id.
Hint Resolve PC2_clos_id.

Goal
forall (a a' : terms) (s t : sub_explicits),
e_relSL _ a a' ->
exists u : terms,
  e_relSLstar _ (env a (comp s t)) u /\ e_relSLstar _ (env (env a' s) t) u.
intros; exists (env a' (comp s t)); auto 8.
Save PC1_clos_ctxt_l.
Hint Resolve PC1_clos_ctxt_l.

Goal
forall (a : terms) (s s' t : sub_explicits),
e_relSL _ s s' ->
exists u : terms,
  e_relSLstar _ (env a (comp s t)) u /\ e_relSLstar _ (env (env a s') t) u.
intros; exists (env a (comp s' t)); auto 6.
Save PC2_clos_ctxt_l.
Hint Resolve PC2_clos_ctxt_l.

Goal
forall (a : terms) (s t t' : sub_explicits),
e_relSL _ t t' ->
exists u : terms,
  e_relSLstar _ (env a (comp s t)) u /\ e_relSLstar _ (env (env a s) t') u.
intros; exists (env a (comp s t')); auto 6.
Save PC_clos_ctxt_r.
Hint Resolve PC_clos_ctxt_r.

Goal
forall (a x' : terms) (s t : sub_explicits),
e_relSL _ (env a s) x' ->
exists u : terms,
  e_relSLstar _ (env a (comp s t)) u /\ e_relSLstar _ (env x' t) u.
intros a x' s t H; pattern a, s, x' in |- *; apply case_SLenv; auto.
Save PC_clos_ctxt_l.
Hint Resolve PC_clos_ctxt_l.

(*** varshift1 ***)

 (* aucune PC *)

(*** varshift2 ***)

Goal
forall (n : nat) (a : terms) (s : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var (S n)) (cons a s)) u /\
  e_relSLstar _ (env (var n) s) u.
intros; exists (env (var n) s); auto 6.
Save PC_varshift2_shiftcons.
Hint Resolve PC_varshift2_shiftcons.

Goal
forall (n : nat) (s : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var (S n)) (lift s)) u /\
  e_relSLstar _ (env (var n) (comp s shift)) u.
intros; exists (env (var n) (comp s shift)); auto 6.
Save PC_varshift2_shiftlift1.
Hint Resolve PC_varshift2_shiftlift1.

Goal
forall (n : nat) (s t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var (S n)) (comp (lift s) t)) u /\
  e_relSLstar _ (env (var n) (comp s (comp shift t))) u.
intros; exists (env (var n) (comp s (comp shift t))); auto 6.
Save PC_varshift2_shiftlift2.
Hint Resolve PC_varshift2_shiftlift2.

Goal
forall n : nat,
exists u : terms,
  e_relSLstar _ (env (var (S n)) id) u /\ e_relSLstar _ (env (var n) shift) u.
intros; exists (var (S n)); auto 6.
Save PC_varshift2_idr.
Hint Resolve PC_varshift2_idr.

Goal
forall (n : nat) (s s' : sub_explicits),
e_relSL _ s s' ->
exists u : terms,
  e_relSLstar _ (env (var (S n)) s) u /\
  e_relSLstar _ (env (var n) (comp shift s')) u.
intros; exists (env (var (S n)) s'); auto 6.
Save PC_varshift2_ctxt_r.
Hint Resolve PC_varshift2_ctxt_r.

Goal
forall (n : nat) (s x' : sub_explicits),
e_relSL _ (comp shift s) x' ->
exists u : terms,
  e_relSLstar _ (env (var (S n)) s) u /\ e_relSLstar _ (env (var n) x') u.
intros n s x' H; pattern s, x' in |- *; apply case_SLcomp1; auto.
Save PC_varshift2_ctxt_r'.
Hint Resolve PC_varshift2_ctxt_r'.

(*** fvarcons ***)

Goal
forall (a a' : terms) (s : sub_explicits),
e_relSL _ a a' ->
exists u : terms,
  e_relSLstar _ a u /\ e_relSLstar _ (env (var 0) (cons a' s)) u.
intros; exists a'; auto 6.
Save PC1_fvarcons_ctxt_r.
Hint Resolve PC1_fvarcons_ctxt_r.

Goal
forall (a : terms) (s' : sub_explicits),
exists u : terms,
  e_relSLstar _ a u /\ e_relSLstar _ (env (var 0) (cons a s')) u.
intros; exists a; auto 6.
Save PC2_fvarcons_ctxt_r.
Hint Resolve PC2_fvarcons_ctxt_r.

Goal
forall (a : terms) (s x' : sub_explicits),
e_relSL _ (cons a s) x' ->
exists u : terms, e_relSLstar _ a u /\ e_relSLstar _ (env (var 0) x') u.
intros a s x' H; pattern x' in |- *; apply case_SLcons with a s; auto.
Save PC_fvarcons_ctxt_r. 

(*** fvarlift1 ***)

Goal
exists u : terms, e_relSLstar _ (var 0) u /\ e_relSLstar _ (env (var 0) id) u.
intros; exists (var 0); auto 6.
Save PC_fvarlift1_liftid.
Hint Resolve PC_fvarlift1_liftid.

Goal
forall s' : sub_explicits,
exists u : terms,
  e_relSLstar _ (var 0) u /\ e_relSLstar _ (env (var 0) (lift s')) u.
intros; exists (var 0); auto 6.
Save PC_fvarlift1_ctxt_r.
Hint Resolve PC_fvarlift1_ctxt_r.

Goal
forall s x' : sub_explicits,
e_relSL _ (lift s) x' ->
exists u : terms, e_relSLstar _ (var 0) u /\ e_relSLstar _ (env (var 0) x') u.
intros s x' H; pattern s, x' in |- *; apply case_SLlift; auto.
Save PC_fvarlift1_ctxt_r'.

(*** fvarlift2 ***)

Goal
forall s t : sub_explicits,
exists u : terms,
  e_relSLstar _ (env (var 0) (lift t)) u /\
  e_relSLstar _ (env (var 0) (lift (comp s t))) u.
intros; exists (var 0); auto 6.
Save PC_fvarlift2_lift1.
Hint Resolve PC_fvarlift2_lift1.

Goal
forall s t v : sub_explicits,
exists u : terms,
  e_relSLstar _ (env (var 0) (comp (lift t) v)) u /\
  e_relSLstar _ (env (var 0) (comp (lift (comp s t)) v)) u.
intros; exists (env (var 0) v); auto 6.
Save PC_fvarlift2_lift2.
Hint Resolve PC_fvarlift2_lift2.

Goal
forall (a : terms) (s t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var 0) (cons a t)) u /\
  e_relSLstar _ (env (var 0) (cons a (comp s t))) u.
intros; exists a; auto 6.
Save PC_fvarlift2_liftenv.
Hint Resolve PC_fvarlift2_liftenv.

Goal
forall s : sub_explicits,
exists u : terms,
  e_relSLstar _ (env (var 0) id) u /\ e_relSLstar _ (env (var 0) (lift s)) u.
exists (var 0); auto 6.
Save PC_fvarlift2_idr.
Hint Resolve PC_fvarlift2_idr.

Goal
forall t : sub_explicits,
exists u : terms,
  e_relSLstar _ (env (var 0) t) u /\
  e_relSLstar _ (env (var 0) (comp id t)) u.
intros; exists (env (var 0) t); auto 7.
Save PC_fvarlift2_liftid.
Hint Resolve PC_fvarlift2_liftid.

Goal
forall s' t : sub_explicits,
exists u : terms,
  e_relSLstar _ (env (var 0) t) u /\
  e_relSLstar _ (env (var 0) (comp (lift s') t)) u.
intros; exists (env (var 0) t); auto 6.
Save PC1_fvarlift2_ctxt_r.
Hint Resolve PC1_fvarlift2_ctxt_r.

Goal
forall s t t' : sub_explicits,
e_relSL _ t t' ->
exists u : terms,
  e_relSLstar _ (env (var 0) t) u /\
  e_relSLstar _ (env (var 0) (comp (lift s) t')) u.
intros; exists (env (var 0) t'); auto 6.
Save PC2_fvarlift2_ctxt_r.
Hint Resolve PC2_fvarlift2_ctxt_r.

Goal
forall s t x' : sub_explicits,
e_relSL _ (comp (lift s) t) x' ->
exists u : terms,
  e_relSLstar _ (env (var 0) t) u /\ e_relSLstar _ (env (var 0) x') u.
intros s t x' H; pattern t, x' in |- *; apply case_SLcomp2 with s; auto.
intros; pattern s, x'0 in |- *; apply case_SLlift; auto.
Save PC_fvarlift2_ctxt_r.

(*** rvarcons ***)

Goal
forall (n : nat) (a' : terms) (s : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var n) s) u /\
  e_relSLstar _ (env (var (S n)) (cons a' s)) u.
intros; exists (env (var n) s); auto 6.
Save PC1_rvarcons_ctxt_r.
Hint Resolve PC1_rvarcons_ctxt_r.

Goal
forall (n : nat) (a : terms) (s s' : sub_explicits),
e_relSL _ s s' ->
exists u : terms,
  e_relSLstar _ (env (var n) s) u /\
  e_relSLstar _ (env (var (S n)) (cons a s')) u.
intros; exists (env (var n) s'); auto 6.
Save PC2_rvarcons_ctxt_r.
Hint Resolve PC2_rvarcons_ctxt_r.

Goal
forall (n : nat) (a : terms) (s x' : sub_explicits),
e_relSL _ (cons a s) x' ->
exists u : terms,
  e_relSLstar _ (env (var n) s) u /\ e_relSLstar _ (env (var (S n)) x') u.
intros n a s x' H; pattern x' in |- *; apply case_SLcons with a s; auto.
Save PC_rvarcons_ctxt_r.

(*** rvarlift1 ***)

Goal
forall n : nat,
exists u : terms,
  e_relSLstar _ (env (var n) (comp id shift)) u /\
  e_relSLstar _ (env (var (S n)) id) u.
intros; exists (var (S n)); split; red in |- *.
apply star_trans1 with (env (var n) shift); auto.
auto.
Save PC_rvarlift1_id.
Hint Resolve PC_rvarlift1_id.

Goal
forall (n : nat) (s s' : sub_explicits),
e_relSL _ s s' ->
exists u : terms,
  e_relSLstar _ (env (var n) (comp s shift)) u /\
  e_relSLstar _ (env (var (S n)) (lift s')) u.
intros; exists (env (var n) (comp s' shift)); auto 6.
Save PC_rvarlift1_ctxt_r.
Hint Resolve PC_rvarlift1_ctxt_r.

Goal
forall (n : nat) (s x' : sub_explicits),
e_relSL _ (lift s) x' ->
exists u : terms,
  e_relSLstar _ (env (var n) (comp s shift)) u /\
  e_relSLstar _ (env (var (S n)) x') u.
intros n s x' H; pattern s, x' in |- *; apply case_SLlift; auto.
Save PC_rvarlift1_ctxt_r'.
Hint Resolve PC_rvarlift1_ctxt_r'.

(*** rvarlift2 ***)

Goal
forall (n : nat) (s t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var n) (comp s (comp shift (lift t)))) u /\
  e_relSLstar _ (env (var (S n)) (lift (comp s t))) u.
intros; exists (env (var n) (comp s (comp t shift))); split; red in |- *.
auto 6.
apply star_trans1 with (env (var n) (comp (comp s t) shift)); auto.
Save PC_rvarlift2_lift1.
Hint Resolve PC_rvarlift2_lift1.

Goal
forall (n : nat) (s t v : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var n) (comp s (comp shift (comp (lift t) v)))) u /\
  e_relSLstar _ (env (var (S n)) (comp (lift (comp s t)) v)) u.
intros; exists (env (var n) (comp s (comp t (comp shift v)))); split;
 red in |- *.
auto 6.
apply star_trans1 with (env (var n) (comp (comp s t) (comp shift v))); auto.
Save PC_rvarlift2_lift2.
Hint Resolve PC_rvarlift2_lift2.

Goal
forall (n : nat) (a : terms) (s t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var n) (comp s (comp shift (cons a t)))) u /\
  e_relSLstar _ (env (var (S n)) (cons a (comp s t))) u.
intros; exists (env (var n) (comp s t)); auto 8.
Save PC_rvarlift2_liftenv.
Hint Resolve PC_rvarlift2_liftenv.

Goal
forall (n : nat) (s : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var n) (comp s (comp shift id))) u /\
  e_relSLstar _ (env (var (S n)) (lift s)) u.
intros; exists (env (var n) (comp s shift)); auto 8.
Save PC_rvarlift2_idr.
Hint Resolve PC_rvarlift2_idr.

Goal
forall (n : nat) (t : sub_explicits),
exists u : terms,
  e_relSLstar _ (env (var n) (comp id (comp shift t))) u /\
  e_relSLstar _ (env (var (S n)) (comp id t)) u.
intros; exists (env (var (S n)) t); split; red in |- *.
apply star_trans1 with (env (var n) (comp shift t)); auto.
auto.
Save PC_rvarlift2_liftid.
Hint Resolve PC_rvarlift2_liftid.

Goal
forall (n : nat) (s s' t : sub_explicits),
e_relSL _ s s' ->
exists u : terms,
  e_relSLstar _ (env (var n) (comp s (comp shift t))) u /\
  e_relSLstar _ (env (var (S n)) (comp (lift s') t)) u.
intros; exists (env (var n) (comp s' (comp shift t))); auto 6.
Save PC1_rvarlift2_ctxt_r.
Hint Resolve PC1_rvarlift2_ctxt_r.

Goal
forall (n : nat) (s t t' : sub_explicits),
e_relSL _ t t' ->
exists u : terms,
  e_relSLstar _ (env (var n) (comp s (comp shift t))) u /\
  e_relSLstar _ (env (var (S n)) (comp (lift s) t')) u.
intros; exists (env (var n) (comp s (comp shift t'))); auto 7.
Save PC2_rvarlift2_ctxt_r.
Hint Resolve PC2_rvarlift2_ctxt_r.

Goal
forall (n : nat) (s t x' : sub_explicits),
e_relSL _ (comp (lift s) t) x' ->
exists u : terms,
  e_relSLstar _ (env (var n) (comp s (comp shift t))) u /\
  e_relSLstar _ (env (var (S n)) x') u.
intros n s t x' H; pattern t, x' in |- *; apply case_SLcomp2 with s; auto.
intros; pattern s, x'0 in |- *; apply case_SLlift; auto.
Save PC_rvarlift2_ctxt_r.
Hint Resolve PC_rvarlift2_ctxt_r.

(*** assenv ***) 

Goal
forall s1 s2 t v : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp (comp s1 s2) (comp t v)) u /\
  e_relSLstar _ (comp (comp s1 (comp s2 t)) v) u.
intros; exists (comp s1 (comp s2 (comp t v))); split; red in |- *.
auto.
apply star_trans1 with (comp s1 (comp (comp s2 t) v)); auto.
Save PC_assenv_assenv.
Hint Resolve PC_assenv_assenv.

Goal
forall (a : terms) (s t v : sub_explicits),
exists u : sub_explicits,
  e_relSLstar _ (comp (cons a s) (comp t v)) u /\
  e_relSLstar _ (comp (cons (env a t) (comp s t)) v) u.
intros; exists (cons (env a (comp t v)) (comp s (comp t v))); split;
 red in |- *.
auto.
apply star_trans1 with (cons (env (env a t) v) (comp (comp s t) v)).
auto.
apply star_trans1 with (cons (env a (comp t v)) (comp (comp s t) v)); auto.
Save PC_assenv_mapenv.
Hint Resolve PC_assenv_mapenv.

Goal
forall (a : terms) (s v : sub_explicits),
exists u : sub_explicits,
  e_relSLstar _ (comp shift (comp (cons a s) v)) u /\
  e_relSLstar _ (comp s v) u.
intros; exists (comp s v); split; red in |- *.
apply star_trans1 with (comp shift (cons (env a v) (comp s v))); auto.
auto.
Save PC_assenv_shiftcons.
Hint Resolve PC_assenv_shiftcons.

Goal
forall s v : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp shift (comp (lift s) v)) u /\
  e_relSLstar _ (comp (comp s shift) v) u.
intros; exists (comp s (comp shift v)); auto 6.
Save PC_assenv_shiftlift1.
Hint Resolve PC_assenv_shiftlift1.

Goal
forall s t v : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp shift (comp (comp (lift s) t) v)) u /\
  e_relSLstar _ (comp (comp s (comp shift t)) v) u.
intros; exists (comp s (comp shift (comp t v))); split; red in |- *.
apply star_trans1 with (comp shift (comp (lift s) (comp t v))); auto.
apply star_trans1 with (comp s (comp (comp shift t) v)); auto.
Save PC_assenv_shiftlift2.
Hint Resolve PC_assenv_shiftlift2.

Goal
forall s t v : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp (lift s) (comp (lift t) v)) u /\
  e_relSLstar _ (comp (lift (comp s t)) v) u.
intros; exists (comp (lift (comp s t)) v); auto 6.
Save PC_assenv_lift1.
Hint Resolve PC_assenv_lift1.

Goal
forall s t1 t2 v : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp (lift s) (comp (comp (lift t1) t2) v)) u /\
  e_relSLstar _ (comp (comp (lift (comp s t1)) t2) v) u.
intros; exists (comp (lift (comp s t1)) (comp t2 v)); split; red in |- *.
apply star_trans1 with (comp (lift s) (comp (lift t1) (comp t2 v))); auto.
auto.
Save PC_assenv_lift2.
Hint Resolve PC_assenv_lift2.

Goal
forall (a : terms) (s t v : sub_explicits),
exists u : sub_explicits,
  e_relSLstar _ (comp (lift s) (comp (cons a t) v)) u /\
  e_relSLstar _ (comp (cons a (comp s t)) v) u.
intros; exists (cons (env a v) (comp s (comp t v))); split; red in |- *.
apply star_trans1 with (comp (lift s) (cons (env a v) (comp t v))); auto.
apply star_trans1 with (cons (env a v) (comp (comp s t) v)); auto.
Save PC_assenv_liftenv.
Hint Resolve PC_assenv_liftenv.

Goal
forall t v : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp id (comp t v)) u /\ e_relSLstar _ (comp t v) u.
intros; exists (comp t v); auto 6.
Save PC_assenv_idl.
Hint Resolve PC_assenv_idl.

Goal
forall s v : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp s (comp id v)) u /\ e_relSLstar _ (comp s v) u.
intros; exists (comp s v); auto 7.
Save PC1_assenv_idr.
Hint Resolve PC1_assenv_idr.

Goal
forall s t : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp s (comp t id)) u /\ e_relSLstar _ (comp s t) u.
intros; exists (comp s t); auto 7.
Save PC2_assenv_idr.
Hint Resolve PC2_assenv_idr.

Goal
forall s s' t v : sub_explicits,
e_relSL _ s s' ->
exists u : sub_explicits,
  e_relSLstar _ (comp s (comp t v)) u /\ e_relSLstar _ (comp (comp s' t) v) u.
intros; exists (comp s' (comp t v)); auto 6.
Save PC_assenv_ctxt_l.
Hint Resolve PC_assenv_ctxt_l.

Goal
forall s t t' v : sub_explicits,
e_relSL _ t t' ->
exists u : sub_explicits,
  e_relSLstar _ (comp s (comp t v)) u /\ e_relSLstar _ (comp (comp s t') v) u. 
intros; exists (comp s (comp t' v)); auto 6.
Save PC1_assenv_ctxt_r.
Hint Resolve PC1_assenv_ctxt_r.

Goal
forall s t v v' : sub_explicits,
e_relSL _ v v' ->
exists u : sub_explicits,
  e_relSLstar _ (comp s (comp t v)) u /\ e_relSLstar _ (comp (comp s t) v') u. 
intros; exists (comp s (comp t v')); auto 6.
Save PC2_assenv_ctxt_r.
Hint Resolve PC2_assenv_ctxt_r.

Goal
forall s t v x' : sub_explicits,
e_relSL _ (comp s t) x' ->
exists u : sub_explicits,
  e_relSLstar _ (comp s (comp t v)) u /\ e_relSLstar _ (comp x' v) u.
intros s t v x' H; pattern s, t, x' in |- *; apply case_SLcomp; auto.
Save PC_assenv_ctxt_r.
Hint Resolve PC_assenv_ctxt_r.

(*** mapenv ***)

Goal
forall (a : terms) (s : sub_explicits),
exists u : sub_explicits,
  e_relSLstar _ (cons (env a id) (comp s id)) u /\ e_relSLstar _ (cons a s) u. 
intros; exists (cons a s); split; red in |- *.
apply star_trans1 with (cons a (comp s id)); auto.
auto.
Save PC_mapenv_idr.
Hint Resolve PC_mapenv_idr.

Goal
forall (a a' : terms) (s t : sub_explicits),
e_relSL _ a a' ->
exists u : sub_explicits,
  e_relSLstar _ (cons (env a t) (comp s t)) u /\
  e_relSLstar _ (comp (cons a' s) t) u. 
intros; exists (cons (env a' t) (comp s t)); auto 6.
Save PC1_mapenv_ctxt_l.
Hint Resolve PC1_mapenv_ctxt_l.

Goal
forall (a : terms) (s s' t : sub_explicits),
e_relSL _ s s' ->
exists u : sub_explicits,
  e_relSLstar _ (cons (env a t) (comp s t)) u /\
  e_relSLstar _ (comp (cons a s') t) u. 
intros; exists (cons (env a t) (comp s' t)); auto 6.
Save PC2_mapenv_ctxt_l.
Hint Resolve PC2_mapenv_ctxt_l.

Goal
forall (a : terms) (s t t' : sub_explicits),
e_relSL _ t t' ->
exists u : sub_explicits,
  e_relSLstar _ (cons (env a t) (comp s t)) u /\
  e_relSLstar _ (comp (cons a s) t') u. 
intros; exists (cons (env a t') (comp s t')); split; red in |- *.
apply star_trans1 with (cons (env a t') (comp s t)); auto.
auto.
Save PC_mapenv_ctxt_r.
Hint Resolve PC_mapenv_ctxt_r.

Goal
forall (a : terms) (s t x' : sub_explicits),
e_relSL _ (cons a s) x' ->
exists u : sub_explicits,
  e_relSLstar _ (cons (env a t) (comp s t)) u /\ e_relSLstar _ (comp x' t) u. 
intros a s t x' H; pattern x' in |- *; apply case_SLcons with a s; auto.
Save PC_mapenv_ctxt_l.
Hint Resolve PC_mapenv_ctxt_l.

(*** shiftcons ***)

Goal
forall (a' : terms) (s : sub_explicits),
exists u : sub_explicits,
  e_relSLstar _ s u /\ e_relSLstar _ (comp shift (cons a' s)) u. 
intros; exists s; auto 6.
Save PC1_shiftcons_ctxt_r.
Hint Resolve PC1_shiftcons_ctxt_r.

Goal
forall (a : terms) (s s' : sub_explicits),
e_relSL _ s s' ->
exists u : sub_explicits,
  e_relSLstar _ s u /\ e_relSLstar _ (comp shift (cons a s')) u.
intros; exists s'; auto 6.
Save PC2_shiftcons_ctxt_r.
Hint Resolve PC2_shiftcons_ctxt_r.

Goal
forall (a : terms) (s x' : sub_explicits),
e_relSL _ (cons a s) x' ->
exists u : sub_explicits,
  e_relSLstar _ s u /\ e_relSLstar _ (comp shift x') u.
intros a s x' H; pattern x' in |- *; apply case_SLcons with a s; auto.
Save PC_shiftcons_ctxt_r.

(*** shiftlift1 ***)

Goal
exists u : sub_explicits,
  e_relSLstar _ (comp id shift) u /\ e_relSLstar _ (comp shift id) u.
intros; exists shift; auto 6.
Save PC_shiftlift1_liftid.
Hint Resolve PC_shiftlift1_liftid.

Goal
forall s s' : sub_explicits,
e_relSL _ s s' ->
exists u : sub_explicits,
  e_relSLstar _ (comp s shift) u /\ e_relSLstar _ (comp shift (lift s')) u.
intros; exists (comp s' shift); auto 6.
Save PC_shiftlift1_ctxt_r.
Hint Resolve PC_shiftlift1_ctxt_r.

Goal
forall s x' : sub_explicits,
e_relSL _ (lift s) x' ->
exists u : sub_explicits,
  e_relSLstar _ (comp s shift) u /\ e_relSLstar _ (comp shift x') u.
intros s x' H; pattern s, x' in |- *; apply case_SLlift; auto.
Save PC_shiftlift1_ctxt_r'.
Hint Resolve PC_shiftlift1_ctxt_r'.

(*** shiftlift2 ***)

Goal
forall s t : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp s (comp shift (lift t))) u /\
  e_relSLstar _ (comp shift (lift (comp s t))) u.
intros; exists (comp s (comp t shift)); split; red in |- *.
auto.
apply star_trans1 with (comp (comp s t) shift); auto.
Save PC_shiftlift2_lift1.
Hint Resolve PC_shiftlift2_lift1.

Goal
forall s t v : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp s (comp shift (comp (lift t) v))) u /\
  e_relSLstar _ (comp shift (comp (lift (comp s t)) v)) u.
intros; exists (comp s (comp t (comp shift v))); split; red in |- *.
auto.
apply star_trans1 with (comp (comp s t) (comp shift v)); auto.
Save PC_shiftlift2_lift2.
Hint Resolve PC_shiftlift2_lift2.

Goal
forall (a : terms) (s t : sub_explicits),
exists u : sub_explicits,
  e_relSLstar _ (comp s (comp shift (cons a t))) u /\
  e_relSLstar _ (comp shift (cons a (comp s t))) u.
intros; exists (comp s t); auto 7.
Save PC_shiftlift2_liftenv.
Hint Resolve PC_shiftlift2_liftenv.

Goal
forall t : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp id (comp shift t)) u /\
  e_relSLstar _ (comp shift (comp id t)) u.
intros; exists (comp shift t); auto 7.
Save PC_shiftlift2_liftid.
Hint Resolve PC_shiftlift2_liftid.

Goal
forall s : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp s (comp shift id)) u /\
  e_relSLstar _ (comp shift (lift s)) u.
intros; exists (comp s shift); auto 7.
Save PC_shiftlift2_idr.
Hint Resolve PC_shiftlift2_idr.

Goal
forall s s' t : sub_explicits,
e_relSL _ s s' ->
exists u : sub_explicits,
  e_relSLstar _ (comp s (comp shift t)) u /\
  e_relSLstar _ (comp shift (comp (lift s') t)) u.
intros; exists (comp s' (comp shift t)); auto 6.
Save PC1_shiftlift2_ctxt_r.
Hint Resolve PC1_shiftlift2_ctxt_r.

Goal
forall s t t' : sub_explicits,
e_relSL _ t t' ->
exists u : sub_explicits,
  e_relSLstar _ (comp s (comp shift t)) u /\
  e_relSLstar _ (comp shift (comp (lift s) t')) u.
intros; exists (comp s (comp shift t')); auto 6.
Save PC2_shiftlift2_ctxt_r.
Hint Resolve PC2_shiftlift2_ctxt_r.

Goal
forall s t x' : sub_explicits,
e_relSL _ (comp (lift s) t) x' ->
exists u : sub_explicits,
  e_relSLstar _ (comp s (comp shift t)) u /\ e_relSLstar _ (comp shift x') u.
intros s t x' H; pattern t, x' in |- *; apply case_SLcomp2 with s; auto.
intros; pattern s, x'0 in |- *; apply case_SLlift; auto.
Save PC_shiftlift2_ctxt_r.
Hint Resolve PC_shiftlift2_ctxt_r.
  
(*** lift1 ***)

Goal
forall t : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (lift (comp id t)) u /\ e_relSLstar _ (comp id (lift t)) u.
intros; exists (lift t); auto 7.
Save PC1_lift1_liftid.
Hint Resolve PC1_lift1_liftid.

Goal
forall s : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (lift (comp s id)) u /\ e_relSLstar _ (comp (lift s) id) u.
intros; exists (lift s); auto 7.
Save PC2_lift1_liftid.
Hint Resolve PC2_lift1_liftid.

Goal
forall s s' t : sub_explicits,
e_relSL _ s s' ->
exists u : sub_explicits,
  e_relSLstar _ (lift (comp s t)) u /\
  e_relSLstar _ (comp (lift s') (lift t)) u.
intros; exists (lift (comp s' t)); auto 6.
Save PC_lift1_ctxt_l.
Hint Resolve PC_lift1_ctxt_l.

Goal
forall s t t' : sub_explicits,
e_relSL _ t t' ->
exists u : sub_explicits,
  e_relSLstar _ (lift (comp s t)) u /\
  e_relSLstar _ (comp (lift s) (lift t')) u.
intros; exists (lift (comp s t')); auto 6.
Save PC_lift1_ctxt_r.
Hint Resolve PC_lift1_ctxt_r.

Goal
forall s t x' : sub_explicits,
e_relSL _ (lift s) x' ->
exists u : sub_explicits,
  e_relSLstar _ (lift (comp s t)) u /\ e_relSLstar _ (comp x' (lift t)) u.
intros s t x' H; pattern s, x' in |- *; apply case_SLlift; auto.
Save PC_lift1_ctxt_l'.
Hint Resolve PC_lift1_ctxt_l'.

Goal
forall s t x' : sub_explicits,
e_relSL _ (lift t) x' ->
exists u : sub_explicits,
  e_relSLstar _ (lift (comp s t)) u /\ e_relSLstar _ (comp (lift s) x') u.
intros a t x' H; pattern t, x' in |- *; apply case_SLlift; auto.
Save PC_lift1_ctxt_r'.
Hint Resolve PC_lift1_ctxt_r'.

(*** lift2 ***)

Goal
forall s t v : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp (lift (comp s t)) (lift v)) u /\
  e_relSLstar _ (comp (lift s) (lift (comp t v))) u.
intros; exists (lift (comp s (comp t v))); split; red in |- *.
apply star_trans1 with (lift (comp (comp s t) v)); auto.
auto.
Save PC_lift2_lift1.
Hint Resolve PC_lift2_lift1.

Goal
forall s t1 t2 v : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp (lift (comp s t1)) (comp (lift t2) v)) u /\
  e_relSLstar _ (comp (lift s) (comp (lift (comp t1 t2)) v)) u.
intros; exists (comp (lift (comp s (comp t1 t2))) v); split; red in |- *.
apply star_trans1 with (comp (lift (comp (comp s t1) t2)) v); auto 6.
auto.
Save PC_lift2_lift2.
Hint Resolve PC_lift2_lift2.

Goal
forall (a : terms) (s t v : sub_explicits),
exists u : sub_explicits,
  e_relSLstar _ (comp (lift (comp s t)) (cons a v)) u /\
  e_relSLstar _ (comp (lift s) (cons a (comp t v))) u.
intros; exists (cons a (comp s (comp t v))); split; red in |- *.
apply star_trans1 with (cons a (comp (comp s t) v)); auto.
auto.
Save PC_lift2_liftenv.
Hint Resolve PC_lift2_liftenv.

Goal
forall t v : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp (lift (comp id t)) v) u /\
  e_relSLstar _ (comp id (comp (lift t) v)) u.
intros; exists (comp (lift t) v); auto 8.
Save PC1_lift2_liftid.
Hint Resolve PC1_lift2_liftid.

Goal
forall s v : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp (lift (comp s id)) v) u /\
  e_relSLstar _ (comp (lift s) (comp id v)) u.
intros; exists (comp (lift s) v); auto 8.
Save PC2_lift2_liftid.
Hint Resolve PC2_lift2_liftid.

Goal
forall s t : sub_explicits,
exists u : sub_explicits,
  e_relSLstar _ (comp (lift (comp s t)) id) u /\
  e_relSLstar _ (comp (lift s) (lift t)) u.
intros; exists (lift (comp s t)); auto 6.
Save PC_lift2_idr.
Hint Resolve PC_lift2_idr.

Goal
forall s s' t v : sub_explicits,
e_relSL _ s s' ->
exists u : sub_explicits,
  e_relSLstar _ (comp (lift (comp s t)) v) u /\
  e_relSLstar _ (comp (lift s') (comp (lift t) v)) u.
intros; exists (comp (lift (comp s' t)) v); auto 7.
Save PC_lift2_ctxt_l.
Hint Resolve PC_lift2_ctxt_l.

Goal
forall s t t' v : sub_explicits,
e_relSL _ t t' ->
exists u : sub_explicits,
  e_relSLstar _ (comp (lift (comp s t)) v) u /\
  e_relSLstar _ (comp (lift s) (comp (lift t') v)) u.
intros; exists (comp (lift (comp s t')) v); auto 7.
Save PC1_lift2_ctxt_r.
Hint Resolve PC1_lift2_ctxt_r.

Goal
forall s t v v' : sub_explicits,
e_relSL _ v v' ->
exists u : sub_explicits,
  e_relSLstar _ (comp (lift (comp s t)) v) u /\
  e_relSLstar _ (comp (lift s) (comp (lift t) v')) u.
intros; exists (comp (lift (comp s t)) v'); auto 6.
Save PC2_lift2_ctxt_r.
Hint Resolve PC2_lift2_ctxt_r.

Goal
forall s t v x' : sub_explicits,
e_relSL _ (lift s) x' ->
exists u : sub_explicits,
  e_relSLstar _ (comp (lift (comp s t)) v) u /\
  e_relSLstar _ (comp x' (comp (lift t) v)) u.
intros s t v x' H; pattern s, x' in |- *; apply case_SLlift; auto.
Save PC_lift2_ctxt_l'. 
Hint Resolve PC_lift2_ctxt_l'. 

Goal
forall s t v x' : sub_explicits,
e_relSL _ (comp (lift t) v) x' ->
exists u : sub_explicits,
  e_relSLstar _ (comp (lift (comp s t)) v) u /\
  e_relSLstar _ (comp (lift s) x') u.
intros s t v x' H; pattern v, x' in |- *; apply case_SLcomp2 with t; auto.
intros; pattern t, x'0 in |- *; apply case_SLlift; auto.
Save PC_lift2_ctxt_r.
Hint Resolve PC_lift2_ctxt_r.

(*** liftenv ***)

Goal
forall (a : terms) (t : sub_explicits),
exists u : sub_explicits,
  e_relSLstar _ (cons a (comp id t)) u /\
  e_relSLstar _ (comp id (cons a t)) u.
intros; exists (cons a t); auto 7.
Save PC_liftenv_liftid.
Hint Resolve PC_liftenv_liftid.

Goal
forall (a : terms) (s s' t : sub_explicits),
e_relSL _ s s' ->
exists u : sub_explicits,
  e_relSLstar _ (cons a (comp s t)) u /\
  e_relSLstar _ (comp (lift s') (cons a t)) u.
intros; exists (cons a (comp s' t)); auto 6.
Save PC_liftenv_ctxt_l.
Hint Resolve PC_liftenv_ctxt_l.

Goal
forall (a a' : terms) (s t : sub_explicits),
e_relSL _ a a' ->
exists u : sub_explicits,
  e_relSLstar _ (cons a (comp s t)) u /\
  e_relSLstar _ (comp (lift s) (cons a' t)) u.
intros; exists (cons a' (comp s t)); auto 6.
Save PC1_liftenv_ctxt_r.
Hint Resolve PC1_liftenv_ctxt_r.

Goal
forall (a : terms) (s t t' : sub_explicits),
e_relSL _ t t' ->
exists u : sub_explicits,
  e_relSLstar _ (cons a (comp s t)) u /\
  e_relSLstar _ (comp (lift s) (cons a t')) u.
intros; exists (cons a (comp s t')); auto 6.
Save PC2_liftenv_ctxt_r.
Hint Resolve PC2_liftenv_ctxt_r.

Goal
forall (a : terms) (s t x' : sub_explicits),
e_relSL _ (lift s) x' ->
exists u : sub_explicits,
  e_relSLstar _ (cons a (comp s t)) u /\ e_relSLstar _ (comp x' (cons a t)) u.
intros a s t x' H; pattern s, x' in |- *; apply case_SLlift; auto.
Save PC_liftenv_ctxt_l'.
Hint Resolve PC_liftenv_ctxt_l'.

Goal
forall (a : terms) (s t x' : sub_explicits),
e_relSL _ (cons a t) x' ->
exists u : sub_explicits,
  e_relSLstar _ (cons a (comp s t)) u /\ e_relSLstar _ (comp (lift s) x') u.
intros a s t x' H; pattern x' in |- *; apply case_SLcons with a t; auto.
Save PC_liftenv_ctxt_r.
Hint Resolve PC_liftenv_ctxt_r.

(*** idl ***)

Goal exists u : sub_explicits, e_relSLstar _ id u /\ e_relSLstar _ id u.
intros; exists id; auto.
Save PC_idl_idr.
Hint Resolve PC_idl_idr.

Goal
forall s s' : sub_explicits,
e_relSL _ s s' ->
exists u : sub_explicits, e_relSLstar _ s u /\ e_relSLstar _ (comp id s') u.
intros; exists s'; auto 6.
Save PC_idl_ctxt_r.
Hint Resolve PC_idl_ctxt_r.

(*** idr ***)

Goal
forall s s' : sub_explicits,
e_relSL _ s s' ->
exists u : sub_explicits, e_relSLstar _ s u /\ e_relSLstar _ (comp s' id) u.
intros; exists s'; auto 6.
Save PC_idr_ctxt_l.
Hint Resolve PC_idr_ctxt_l.

(*** liftid ***)

 (* aucune PC *)

(*** id ***)

Goal
forall a a' : terms,
e_relSL _ a a' ->
exists u : terms, e_relSLstar _ a u /\ e_relSLstar _ (env a' id) u.
intros; exists a'; auto 6.
Save PC_id_ctxt_l.
Hint Resolve PC_id_ctxt_l.


