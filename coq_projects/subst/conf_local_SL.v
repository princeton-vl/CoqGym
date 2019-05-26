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
(*                             conf_local_SL.v                              *)
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



                             (* Confluence locale de sigma-lift *)

Require Import TS.
Require Import sur_les_relations.
Require Import sigma_lift.
Require Import determinePC_SL.
Require Import resoudPC_SL.


Definition e_local1 (b : wsort) (x y : TS b) :=
  forall z : TS b,
  e_relSL _ x z -> exists u : TS b, e_relSLstar _ y u /\ e_relSLstar _ z u.

Notation local1 := (e_local1 _) (only parsing).
(* <Warning> : Syntax is discontinued *)

(* app *)

Goal forall x y : terms, reg_app x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros a b0 s z H0.
pattern s, z in |- *; apply case_SL_reg_app with a b0; auto.
exists (app (env a s) (env b0 s)); auto.
Save local_app.
Hint Resolve local_app.

(* lambda *)

Goal forall x y : terms, reg_lambda x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros a s z H0.
pattern s, z in |- *; apply case_SL_reg_lambda with a; auto.
exists (lambda (env a (lift s))); auto.
Save local_lambda.
Hint Resolve local_lambda.

(* clos *)

Goal forall x y : terms, reg_clos x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros a s t z H0.
pattern t, z in |- *; apply case_SL_clos with a s; auto.
exists (env a (comp s t)); auto.
Save local_clos.
Hint Resolve local_clos.

(* varshift1 *)

Goal forall x y : terms, reg_varshift1 x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros n z H0.
pattern z in |- *; apply case_SL_varshift1 with n; auto.
exists (var (S n)); auto.
Save local_varshift1.
Hint Resolve local_varshift1.

(* varshift2 *)

Goal forall x y : terms, reg_varshift2 x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros n s z H0.
pattern z in |- *; apply case_SL_varshift2 with n s; auto.
exists (env (var (S n)) s); auto.
Save local_varshift2.
Hint Resolve local_varshift2.

(* fvarcons *)

Goal forall x y : terms, reg_fvarcons x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros a s z H0.
pattern z in |- *; apply case_SL_fvarcons with a s; intros.
3: assumption.
exists a; auto.
apply PC_fvarcons_ctxt_r with s; assumption.
Save local_fvarcons.
Hint Resolve local_fvarcons.

(* fvarlift1 *)

Goal forall x y : terms, reg_fvarlift1 x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros s z H0.
pattern z in |- *; apply case_SL_fvarlift1 with s; intros.
3: assumption.
exists (var 0); auto.
apply PC_fvarlift1_ctxt_r' with s; assumption.
Save local_fvarlift1.
Hint Resolve local_fvarlift1.

(* fvarlift2 *)

Goal forall x y : terms, reg_fvarlift2 x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros s t z H0.
pattern z in |- *; apply case_SL_fvarlift2 with s t; intros.
3: assumption.
exists (env (var 0) t); auto.
apply PC_fvarlift2_ctxt_r with s; assumption.
Save local_fvarlift2.
Hint Resolve local_fvarlift2.

(* rvarcons *)

Goal forall x y : terms, reg_rvarcons x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros n a s z H0.
pattern z in |- *; apply case_SL_rvarcons with n a s; intros.
3: assumption.
exists (env (var n) s); auto.
apply PC_rvarcons_ctxt_r with a; assumption.
Save local_rvarcons.
Hint Resolve local_rvarcons.

(* rvarlift1 *)

Goal forall x y : terms, reg_rvarlift1 x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros n s z H0.
pattern z in |- *; apply case_SL_rvarlift1 with n s; auto.
exists (env (var n) (comp s shift)); auto.
Save local_rvarlift1.
Hint Resolve local_rvarlift1.

(* rvarlift2 *)

Goal forall x y : terms, reg_rvarlift2 x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros n s t z H0.
pattern z in |- *; apply case_SL_rvarlift2 with n s t; auto.
exists (env (var n) (comp s (comp shift t))); auto.
Save local_rvarlift2.
Hint Resolve local_rvarlift2.

(* assenv *)

Goal forall x y : sub_explicits, reg_assenv x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros s t u z H0.
pattern u, z in |- *; apply case_SL_assenv with s t; auto.
exists (comp s (comp t u)); auto.
Save local_assenv.
Hint Resolve local_assenv.

(* mapenv *)

Goal forall x y : sub_explicits, reg_mapenv x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros a s t z H0.
pattern t, z in |- *; apply case_SL_mapenv with a s; auto.
exists (cons (env a t) (comp s t)); auto.
Save local_mapenv.
Hint Resolve local_mapenv.

(* shiftcons *)

Goal forall x y : sub_explicits, reg_shiftcons x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros a s z H0.
pattern z in |- *; apply case_SL_shiftcons with a s; intros.
3: assumption.
exists s; auto.
apply PC_shiftcons_ctxt_r with a; assumption.
Save local_shiftcons.
Hint Resolve local_shiftcons.

(* shiftlift1 *)

Goal forall x y : sub_explicits, reg_shiftlift1 x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros s z H0.
pattern z in |- *; apply case_SL_shiflift1 with s; auto.
exists (comp s shift); auto.
Save local_shiftlift1.
Hint Resolve local_shiftlift1.

(* shiftlift2 *)

Goal forall x y : sub_explicits, reg_shiftlift2 x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros s t z H0.
pattern z in |- *; apply case_SL_shiflift2 with s t; auto.
exists (comp s (comp shift t)); auto.
Save local_shiftlift2.
Hint Resolve local_shiftlift2.

(* lift1 *)

Goal forall x y : sub_explicits, reg_lift1 x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros s t z H0.
pattern z in |- *; apply case_SL_lift1 with s t; auto.
exists (lift (comp s t)); auto.
Save local_lift1.
Hint Resolve local_lift1.

(* lift2 *)

Goal forall x y : sub_explicits, reg_lift2 x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros s t u z H0.
pattern z in |- *; apply case_SL_lift2 with s t u; auto.
exists (comp (lift (comp s t)) u); auto.
Save local_lift2.
Hint Resolve local_lift2.

(* liftenv *)

Goal forall x y : sub_explicits, reg_liftenv x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros a s t z H0.
pattern z in |- *; apply case_SL_liftenv with a s t; auto.
exists (cons a (comp s t)); auto.
Save local_liftenv.
Hint Resolve local_liftenv.

(* idl *)

Goal forall x y : sub_explicits, reg_idl x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros s z H0.
pattern s, z in |- *; apply case_SL_idl; auto.
exists s; auto.
Save local_idl.
Hint Resolve local_idl.

(* idr *)

Goal forall x y : sub_explicits, reg_idr x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros s z H0.
apply Ex_PQ; pattern s, z in |- *; apply case_SL_idr; auto.
exists s; auto.
Save local_idr.
Hint Resolve local_idr.

(* liftid *)

Goal forall x y : sub_explicits, reg_liftid x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros z H0.
pattern z in |- *; apply case_SL_liftid; auto.
Save local_liftid.
Hint Resolve local_liftid.

(* id *)

Goal forall x y : terms, reg_id x y -> e_local1 _ x y.
simple induction 1; red in |- *; intros a z H0.
apply Ex_PQ; pattern a, z in |- *; apply case_SL_reg_id; auto.
exists a; auto 6.
Save local_id.
Hint Resolve local_id.

(* systeme SL *)

Goal forall (b : wsort) (x y : TS b), e_systemSL _ x y -> e_local1 _ x y.
simple induction 1; auto.
Save local_systemSL.

Goal forall (b : wsort) (x y : TS b), e_relSL _ x y -> e_local1 _ x y.
simple induction 1.
(* systemSL *)
intros; apply local_systemSL; assumption.
(* contexte app gauche *)
red in |- *; intros a a' b0 H0 H1 z H2.
pattern z in |- *; apply case_SLapp with a b0.
3: assumption.
intros a'' H3; elim (H1 a'' H3); intros a_ H4.
elim H4; intros H5 H6.
exists (app a_ b0); auto.
intros b0' H3; exists (app a' b0'); auto.
(* contexte app droit *)
red in |- *; intros a b0 b0' H0 H1 z H2.
pattern z in |- *; apply case_SLapp with a b0.
3: assumption.
intros a' H3; exists (app a' b0'); auto.
intros b0'' H3; elim (H1 b0'' H3); intros b0_ H4.
elim H4; intros H5 H6.
exists (app a b0_); auto.
(* contexte lambda *)
red in |- *; intros a a' H0 H1 z H2.
pattern z in |- *; apply case_SLlambda with a.
2: assumption.
intros a'' H3; elim (H1 a'' H3); intros a_ H4; elim H4; intros H5 H6.
exists (lambda a_); auto.
(* contexte env gauche *)
red in |- *; intros a a' s H0 H1 z H2.
apply Ex_PQ; generalize H0; pattern a, s, z in |- *; apply case_SLenv; auto.
intros n H3; elim (case_SLvar n a' H3).
intros n s1 H3; elim (case_SLvar n a' H3).
intros a1 s1 H3; elim (case_SLvar 0 a' H3).
intros s1 H3; elim (case_SLvar 0 a' H3).
intros s1 s2 H3; elim (case_SLvar 0 a' H3).
intros n a1 s1 H3; elim (case_SLvar (S n) a' H3).
intros n s1 H3; elim (case_SLvar (S n) a' H3).
intros n s1 s2 H3; elim (case_SLvar (S n) a' H3).
intros a'' H3 H4; elim (H1 a'' H3); intros a_ H5; elim H5; intros H6 H7.
exists (env a_ s); auto.
intros s' H3 H4; exists (env a' s'); auto.
(* contexte env droit *)
red in |- *; intros a s s' H0 H1 z H2.
apply Ex_PQ; generalize H0; pattern a, s, z in |- *; apply case_SLenv; auto.
intros n H3; elim (case_SLshift s' H3).
intros; apply PC_fvarcons_ctxt_r with s1; assumption.
intros; apply PC_fvarlift1_ctxt_r' with s1; assumption.
intros; apply PC_fvarlift2_ctxt_r with s1; assumption.
intros; apply PC_rvarcons_ctxt_r with a1; assumption.
intro H3; elim (case_SLid s' H3).
intros a' H3 H4; exists (env a' s'); auto.
intros s'' H3 H4; elim (H1 s'' H3); intros s_ H5; elim H5; intros H6 H7.
exists (env a s_); auto.
(* contexte cons gauche *)
red in |- *; intros a a' s H0 H1 z H2.
pattern z in |- *; apply case_SLcons with a s; auto.
intros a'' H3; elim (H1 a'' H3); intros a_ H4; elim H4; intros H5 H6.
exists (cons a_ s); auto.
intros s' H3; exists (cons a' s'); auto.
(* contexte cons droit *)
red in |- *; intros a s s' H0 H1 z H2.
pattern z in |- *; apply case_SLcons with a s; auto.
intros a' H3; exists (cons a' s'); auto.
intros s'' H3; elim (H1 s'' H3); intros s_ H4; elim H4; intros H5 H6.
exists (cons a s_); auto.
(* contexte comp gauche *)
red in |- *; intros s s' t H0 H1 z H2.
apply Ex_PQ; generalize H0; pattern s, t, z in |- *; apply case_SLcomp; auto.
intros a t1 H3; elim (case_SLshift s' H3).
intros t1 H3; elim (case_SLshift s' H3).
intros t1 t2 H3; elim (case_SLshift s' H3).
intro H3; elim (case_SLid s' H3).
intros s'' H3; elim (H1 s'' H3); intros s_ H4; elim H4; intros H5 H6.
exists (comp s_ t); auto.
intros t' H3; exists (comp s' t'); auto.
(* contexte comp droit *)
red in |- *; intros s t t' H0 H1 z H2.
apply Ex_PQ; generalize H0; pattern s, t, z in |- *; apply case_SLcomp; auto.
intros; apply PC_shiftcons_ctxt_r with a; assumption.
intro H3; elim (case_SLid t' H3).
intros s' H3; exists (comp s' t'); auto.
intros t'' H3; elim (H1 t'' H3); intros t_ H4; elim H4; intros H5 H6.
exists (comp s t_); auto.
(* contexte lift *)
red in |- *; intros s s' H0 H1 z H2.
generalize H0; pattern s, z in |- *; apply case_SLlift.
3: assumption.
intro H3; elim (case_SLid s' H3).
intros s'' H3; elim (H1 s'' H3); intros s_ H4; elim H4; intros H5 H6.
exists (lift s_); auto.
Save local_relSL.


(*************************************************************)
(*           sigma-lift est localement confluente            *)
(*************************************************************)


Theorem conf_local_SL :
 forall b : wsort, explicit_local_confluence _ (e_relSL b).
red in |- *; red in |- *; intros b x y z H H0.
generalize z H0.
change (e_local1 _ x y) in |- *; apply local_relSL; assumption.
Qed.

