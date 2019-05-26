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
(*                           SLstar_bpar_SLstar.v                           *)
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

         
                   (* relation SL* o B|| o SL* *)

Require Import TS.
Require Import sur_les_relations.
Require Import sigma_lift.
Require Import lambda_sigma_lift.
Require Import betapar.

Definition e_slstar_bp_slstar (b : wsort) :=
  explicit_comp_rel _ (e_relSLstar b)
    (explicit_comp_rel _ (e_beta_par b) (e_relSLstar b)).

Notation slstar_bp_slstar := (e_slstar_bp_slstar _) (only parsing).
(* <Warning> : Syntax is discontinued *)

Hint Unfold e_slstar_bp_slstar.

Goal
forall a a' b b' : terms,
e_beta_par _ b b' ->
e_slstar_bp_slstar _ a a' -> e_slstar_bp_slstar _ (app a b) (app a' b').
simple induction 2; intros.
red in |- *; apply comp_2rel with (app y b).
auto.
elim H2; intros.
apply comp_2rel with (app y0 b'); auto.
Save slbpsl_context_app_l.
Hint Resolve slbpsl_context_app_l.

Goal
forall a a' b b' : terms,
e_beta_par _ a a' ->
e_slstar_bp_slstar _ b b' -> e_slstar_bp_slstar _ (app a b) (app a' b').
simple induction 2; intros.
red in |- *; apply comp_2rel with (app a y).
auto.
elim H2; intros.
apply comp_2rel with (app a' y0); auto.
Save slbpsl_context_app_r.
Hint Resolve slbpsl_context_app_r.

Goal
forall a b a' b' : terms,
e_beta_par _ b b' ->
e_slstar_bp_slstar _ a a' ->
e_slstar_bp_slstar _ (app (lambda a) b) (env a' (cons b' id)).
simple induction 2; intros.
red in |- *; apply comp_2rel with (app (lambda y) b).
auto.
elim H2; intros.
apply comp_2rel with (env y0 (cons b' id)); auto.
Save slbpsl_context_beta_l.
Hint Resolve slbpsl_context_beta_l.

Goal
forall a b a' b' : terms,
e_beta_par _ a a' ->
e_slstar_bp_slstar _ b b' ->
e_slstar_bp_slstar _ (app (lambda a) b) (env a' (cons b' id)).
simple induction 2; intros.
red in |- *; apply comp_2rel with (app (lambda a) y).
auto.
elim H2; intros.
apply comp_2rel with (env a' (cons y0 id)); auto.
Save slbpsl_context_beta_r.
Hint Resolve slbpsl_context_beta_r.

Goal
forall a a' : terms,
e_slstar_bp_slstar _ a a' -> e_slstar_bp_slstar _ (lambda a) (lambda a').
simple induction 1; intros.
red in |- *; apply comp_2rel with (lambda y).
auto.
elim H1; intros.
apply comp_2rel with (lambda y0); auto.
Save slbpsl_context_lambda.
Hint Resolve slbpsl_context_lambda.

Goal
forall (a a' : terms) (s s' : sub_explicits),
e_beta_par _ s s' ->
e_slstar_bp_slstar _ a a' -> e_slstar_bp_slstar _ (env a s) (env a' s').
simple induction 2; intros.
red in |- *; apply comp_2rel with (env y s).
auto.
elim H2; intros.
apply comp_2rel with (env y0 s'); auto.
Save slbpsl_context_env_t.
Hint Resolve slbpsl_context_env_t.

Goal
forall (a a' : terms) (s s' : sub_explicits),
e_beta_par _ a a' ->
e_slstar_bp_slstar _ s s' -> e_slstar_bp_slstar _ (env a s) (env a' s').
simple induction 2; intros.
red in |- *; apply comp_2rel with (env a y).
auto.
elim H2; intros.
apply comp_2rel with (env a' y0); auto.
Save slbpsl_context_env_s.
Hint Resolve slbpsl_context_env_s.

Goal
forall (a a' : terms) (s s' : sub_explicits),
e_beta_par _ s s' ->
e_slstar_bp_slstar _ a a' -> e_slstar_bp_slstar _ (cons a s) (cons a' s').
simple induction 2; intros.
red in |- *; apply comp_2rel with (cons y s).
auto.
elim H2; intros.
apply comp_2rel with (cons y0 s'); auto.
Save slbpsl_context_cons_t.
Hint Resolve slbpsl_context_cons_t.

Goal
forall (a a' : terms) (s s' : sub_explicits),
e_beta_par _ a a' ->
e_slstar_bp_slstar _ s s' -> e_slstar_bp_slstar _ (cons a s) (cons a' s').
simple induction 2; intros.
red in |- *; apply comp_2rel with (cons a y).
auto.
elim H2; intros.
apply comp_2rel with (cons a' y0); auto.
Save slbpsl_context_cons_s.
Hint Resolve slbpsl_context_cons_s.

Goal
forall s s' t t' : sub_explicits,
e_beta_par _ t t' ->
e_slstar_bp_slstar _ s s' -> e_slstar_bp_slstar _ (comp s t) (comp s' t').
simple induction 2; intros.
red in |- *; apply comp_2rel with (comp y t).
auto.
elim H2; intros.
apply comp_2rel with (comp y0 t'); auto.
Save slbpsl_context_comp_l.
Hint Resolve slbpsl_context_comp_l.

Goal
forall s s' t t' : sub_explicits,
e_beta_par _ s s' ->
e_slstar_bp_slstar _ t t' -> e_slstar_bp_slstar _ (comp s t) (comp s' t').
simple induction 2; intros.
red in |- *; apply comp_2rel with (comp s y).
auto.
elim H2; intros.
apply comp_2rel with (comp s' y0); auto.
Save slbpsl_context_comp_r.
Hint Resolve slbpsl_context_comp_r.

Goal
forall s s' : sub_explicits,
e_slstar_bp_slstar _ s s' -> e_slstar_bp_slstar _ (lift s) (lift s').
simple induction 1; intros.
red in |- *; apply comp_2rel with (lift y).
auto.
elim H1; intros.
apply comp_2rel with (lift y0); auto.
Save slbpsl_context_lift.
Hint Resolve slbpsl_context_lift.

Goal
forall (b : wsort) (M N : TS b), e_beta_par _ M N -> e_slstar_bp_slstar _ M N.
intros; red in |- *; apply comp_2rel with M.
red in |- *; auto.
apply comp_2rel with N; auto.
Save betapar_slbpsl.
Hint Resolve betapar_slbpsl.

Goal forall (b : wsort) (M : TS b), e_slstar_bp_slstar _ M M.
auto.
Save refl_slbpsl.
Hint Resolve refl_slbpsl.

(* LSL inclus dans SL*B||SL* *)

Goal forall b : wsort, explicit_inclus _ (e_relLSL b) (e_slstar_bp_slstar b).
red in |- *; simple induction 1; auto.
simple induction 1; auto.
 (* regle beta *)
simple induction 1; auto.
intros b1 M0 N0 H1; red in |- *; apply comp_2rel with N0.
auto. 
apply comp_2rel with N0; auto.
Save relLSL_inclus_slbpsl.
Hint Resolve relLSL_inclus_slbpsl.

(* SL*B||SL* inclus dans LSL* *)

Goal forall b : wsort, explicit_inclus _ (e_beta_par b) (e_relLSLstar b).
red in |- *; simple induction 1; intros; auto.
(* beta_bpar *)
red in |- *; apply star_trans1 with (env M (cons N id)).
auto.
change (e_relLSLstar _ (env M (cons N id)) (env M' (cons N' id))) in |- *;
 auto.
Save betapar_inclus_relSLstar.
Hint Resolve betapar_inclus_relSLstar.

Goal forall b : wsort, explicit_inclus _ (e_relSL b) (e_relLSL b).
red in |- *; simple induction 1; auto.
Save relSL_inclus_relLSL.
Hint Resolve relSL_inclus_relLSL.

Goal
forall b : wsort, explicit_inclus _ (e_slstar_bp_slstar b) (e_relLSLstar b).

unfold e_slstar_bp_slstar in |- *; intro b.
apply inclus_comp.
(* SL* incl LSL* *)
change
  (explicit_inclus _ (explicit_star _ (e_relSL b))
     (explicit_star _ (e_relLSL b))) in |- *; auto.
apply inclus_comp.
(* B|| incl LSL* *)
auto.
(* SL* incl LSL* *)
change
  (explicit_inclus _ (explicit_star _ (e_relSL b))
     (explicit_star _ (e_relLSL b))) in |- *; auto.
intros; red in |- *; apply star_trans with y; assumption.
intros; red in |- *; apply star_trans with y; assumption.
Save slbpsl_inclus_relLSLstar.
Hint Resolve slbpsl_inclus_relLSLstar.


