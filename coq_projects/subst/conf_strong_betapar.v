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
(*                          conf_strong_betapar.v                           *)
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

       
        (*  confluence du LSL-calcul:  beta_par est fortement confluente *)

Require Import TS.
Require Import sur_les_relations.
Require Import betapar.
Require Import egaliteTS.


Definition sconf (b : wsort) (N N' : TS b) :=
  forall z : TS b,
  e_beta_par _ N z -> exists u : TS b, e_beta_par _ N' u /\ e_beta_par _ z u.

Goal forall M M' : terms, sconf wt (lambda M) (lambda M') -> sconf wt M M'.
unfold sconf in |- *; intros M M' H z H0.
elim (H (lambda z)).
2: auto.
intros M_ H1; elim H1; intros H2 H3.
cut (M_ = M_).
2: trivial.
pattern M_ at 1 in |- *; apply case_blambda with M'.
2: assumption.
intros u1 H4.
pattern M_ in |- *; apply case_blambda with z.
2: assumption.
intros u2 H5 H6.
exists u1; split.
assumption.
rewrite (proj_lambda u1 u2 H6); assumption.
Save sconf_lambda_bpar.

(**********************************************)
(*  beta_par est fortement confluente         *)
(**********************************************)

Theorem sconf_betapar :
 forall b : wsort, explicit_strong_confluence _ (e_beta_par b).
red in |- *; red in |- *; intros b x y z H; generalize z; elim H.
(* regle var *)
intros n z0 H1; pattern z0 in |- *; apply case_bvar with n.
2: assumption.
exists (var n); auto.
(* regle id  *)
intros z0 H1; pattern z0 in |- *; apply case_bid.
2: assumption.
exists id; auto.
(*  regle |  *)
intros z0 H1; pattern z0 in |- *; apply case_bshift.
2: assumption.
exists shift; auto.
(* regle app *)
intros M N M' N' H0 H1 H2 H3 z0 H4.
generalize H0 H1; pattern z0 in |- *; apply case_bapp with M N.
3: assumption.
(* 1-regle app *)
intros M'' N'' H5 H6 H7 H8.
elim (H3 N'' H6); intros N_ H9; elim H9; intros H10 H11.
elim (H1 M'' H5); intros M_ H12; elim H12; intros H13 H14.
exists (app M_ N_); auto.
(* 2-regle beta *)
intros M1 M1'' N'' H5 H6 H7; rewrite H5; intros H8.
pattern M' in |- *; apply case_blambda with M1.
2: assumption.
intros M1' H9 H10.
elim (sconf_lambda_bpar M1 M1' H10 M1'' H6); intros M1_ H11.
elim H11; intros H12 H13.
elim (H3 N'' H7); intros N_ H14; elim H14; intros H15 H16.
exists (env M1_ (cons N_ id)); auto.
(* regle lam *)
intros M M' H0 H1 z0 H2; pattern z0 in |- *; apply case_blambda with M.
2: assumption.
intros M'' H3; elim (H1 M'' H3); intros M_ H4; elim H4; intros H5 H6.
exists (lambda M_); auto.
(* regle env *)
intros M M' s s' H0 H1 H2 H3 z0 H4.
pattern z0 in |- *; apply case_benv with M s.
2: assumption.
intros M'' s'' H5 H6.
elim (H1 M'' H5); intros M_ H7; elim H7; intros H8 H9.
elim (H3 s'' H6); intros s_ H10; elim H10; intros H11 H12.
exists (env M_ s_); auto.
(* regle beta *)
intros M N M' N' H0 H1 H2 H3 z0 H4.
pattern z0 in |- *; apply case_bapp with (lambda M) N.
3: assumption.
(* 1-regle app *)
intros M1'' N'' H5 H6.
pattern M1'' in |- *; apply case_blambda with M.
2: assumption.
intros M'' H7.
elim (H1 M'' H7); intros M_ H8; elim H8; intros H9 H10.
elim (H3 N'' H6); intros N_ H11; elim H11; intros H12 H13.
exists (env M_ (cons N_ id)); auto.
(* 2-regle beta *)
intros M1 M1'' N'' H5 H6 H7; generalize H6; elim (proj_lambda M M1 H5);
 intro H8.
elim (H1 M1'' H8); intros M_ H9; elim H9; intros H10 H11.
elim (H3 N'' H7); intros N_ H12; elim H12; intros H13 H14.
exists (env M_ (cons N_ id)); auto.
(* regle . *)
intros M M' s s' H0 H1 H2 H3 z0 H4.
pattern z0 in |- *; apply case_bcons with M s.
2: assumption.
intros M'' s'' H5 H6.
elim (H1 M'' H5); intros M_ H7; elim H7; intros H8 H9.
elim (H3 s'' H6); intros s_ H10; elim H10; intros H11 H12.
exists (cons M_ s_); auto.
(* regle || *)
intros s s' H0 H1 z0 H2.
pattern z0 in |- *; apply case_blift with s.
2: assumption.
intros s'' H3.
elim (H1 s'' H3); intros s_ H4; elim H4; intros H5 H6.
exists (lift s_); auto.
(* regle comp *)
intros s s' t t' H0 H1 H2 H3 z0 H4.
pattern z0 in |- *; apply case_bcomp with s t.
2: assumption.
intros s'' t'' H5 H6.
elim (H1 s'' H5); intros s_ H7; elim H7; intros H8 H9.
elim (H3 t'' H6); intros t_ H10; elim H10; intros H11 H12.
exists (comp s_ t_); auto.
(* regle X *)
intros n z0 H1; pattern z0 in |- *; apply case_bmetaX with n.
2: assumption.
exists (meta_X n); auto.
(* regle x *)
intros n z0 H1; pattern z0 in |- *; apply case_bmetax with n.
2: assumption.
exists (meta_x n); auto.
Qed.
