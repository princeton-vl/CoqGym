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
(*                           lambda_sigma_lift.v                            *)
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


               (* theorie lambda-sigma-lift-calcul *) 

Require Import TS.
Require Import sur_les_relations.
Require Import sigma_lift.


(* regle beta *)

Inductive reg_beta : terms -> terms -> Prop :=
    reg1_beta :
      forall a b : terms, reg_beta (app (lambda a) b) (env a (cons b id)).
Hint Resolve reg1_beta.

(* systeme lambda-sigma-lift *)

Inductive e_systemLSL : forall b : wsort, TS b -> TS b -> Prop :=
  | beta1 : forall M N : terms, reg_beta M N -> e_systemLSL wt M N
  | SL1 :
      forall (b : wsort) (M N : TS b), e_systemSL _ M N -> e_systemLSL b M N. 
Hint Resolve beta1 SL1.

Notation systemLSL := (e_systemLSL _) (only parsing).
(* <Warning> : Syntax is discontinued *)

(* relation engendree par le systeme lambda-sigma-lift *)

Inductive e_relLSL : forall b : wsort, TS b -> TS b -> Prop :=
  | LSL_one_regle :
      forall (b : wsort) (M N : TS b), e_systemLSL _ M N -> e_relLSL b M N
  | LSL_context_app_l :
      forall a a' b : terms,
      e_relLSL wt a a' -> e_relLSL wt (app a b) (app a' b)
  | LSL_context_app_r :
      forall a b b' : terms,
      e_relLSL wt b b' -> e_relLSL wt (app a b) (app a b')
  | LSL_context_lambda :
      forall a a' : terms,
      e_relLSL wt a a' -> e_relLSL wt (lambda a) (lambda a')
  | LSL_context_env_t :
      forall (a a' : terms) (s : sub_explicits),
      e_relLSL wt a a' -> e_relLSL wt (env a s) (env a' s)
  | LSL_context_env_s :
      forall (a : terms) (s s' : sub_explicits),
      e_relLSL ws s s' -> e_relLSL wt (env a s) (env a s')
  | LSL_context_cons_t :
      forall (a a' : terms) (s : sub_explicits),
      e_relLSL wt a a' -> e_relLSL ws (cons a s) (cons a' s)
  | LSL_context_cons_s :
      forall (a : terms) (s s' : sub_explicits),
      e_relLSL ws s s' -> e_relLSL ws (cons a s) (cons a s')
  | LSL_context_comp_l :
      forall s s' t : sub_explicits,
      e_relLSL ws s s' -> e_relLSL ws (comp s t) (comp s' t)
  | LSL_context_comp_r :
      forall s t t' : sub_explicits,
      e_relLSL ws t t' -> e_relLSL ws (comp s t) (comp s t')
  | LSL_context_lift :
      forall s s' : sub_explicits,
      e_relLSL ws s s' -> e_relLSL ws (lift s) (lift s').

Notation relLSL := (e_relLSL _) (only parsing).
(* <Warning> : Syntax is discontinued *)

Hint Resolve LSL_one_regle LSL_context_app_l LSL_context_app_r
  LSL_context_lambda LSL_context_env_t LSL_context_env_s LSL_context_cons_t
  LSL_context_cons_s LSL_context_comp_l LSL_context_comp_r LSL_context_lift.

(* fermeture reflexive-transitive de la relation lambda-sigma-lift *)

Definition e_relLSLstar (b : wsort) := explicit_star _ (e_relLSL b).

Notation relLSLstar := (e_relLSLstar _) (only parsing).
(* <Warning> : Syntax is discontinued *)

Hint Unfold e_relLSLstar.

(* un exemple *)

Goal
e_relLSLstar _
  (lambda (app (lambda (app (var 0) (var 0))) (lambda (app (var 0) (var 1)))))
  (lambda (app (var 0) (var 0))).
red in |- *;
 apply
  star_trans1
   with
     (lambda
        (env (app (var 0) (var 0)) (cons (lambda (app (var 0) (var 1))) id))).
auto.
apply
 star_trans1
  with
    (lambda
       (app (env (var 0) (cons (lambda (app (var 0) (var 1))) id))
          (env (var 0) (cons (lambda (app (var 0) (var 1))) id)))).
auto.
apply
 star_trans1
  with
    (lambda
       (app (lambda (app (var 0) (var 1)))
          (env (var 0) (cons (lambda (app (var 0) (var 1))) id)))).
auto 6.
apply
 star_trans1
  with
    (lambda
       (app (lambda (app (var 0) (var 1))) (lambda (app (var 0) (var 1))))).
auto 6.
apply
 star_trans1
  with
    (lambda
       (env (app (var 0) (var 1)) (cons (lambda (app (var 0) (var 1))) id))).
auto.
apply
 star_trans1
  with
    (lambda
       (app (env (var 0) (cons (lambda (app (var 0) (var 1))) id))
          (env (var 1) (cons (lambda (app (var 0) (var 1))) id)))).
auto.
apply
 star_trans1
  with
    (lambda
       (app (lambda (app (var 0) (var 1)))
          (env (var 1) (cons (lambda (app (var 0) (var 1))) id)))).
auto 6.


apply
 star_trans1
  with (lambda (app (lambda (app (var 0) (var 1))) (env (var 0) id))).
auto 6.
apply
 star_trans1
  with (lambda (env (app (var 0) (var 1)) (cons (env (var 0) id) id))). 
auto.
apply
 star_trans1
  with
    (lambda
       (app (env (var 0) (cons (env (var 0) id) id))
          (env (var 1) (cons (env (var 0) id) id)))).
auto 6.
apply
 star_trans1
  with
    (lambda (app (env (var 0) id) (env (var 1) (cons (env (var 0) id) id)))). 
auto 6.
apply star_trans1 with (lambda (app (env (var 0) id) (env (var 0) id))).
auto 6.
apply star_trans1 with (lambda (app (var 0) (env (var 0) id))).
auto 6.
apply star_trans1 with (lambda (app (var 0) (var 0))); auto 6.
Save exemple.

(* *)

Goal
forall a a' b : terms,
e_relLSLstar _ a a' -> e_relLSLstar _ (app a b) (app a' b).
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (app y b); auto.
Save LSLstar_context_app_l.
Hint Resolve LSLstar_context_app_l.

Goal
forall a b b' : terms,
e_relLSLstar _ b b' -> e_relLSLstar _ (app a b) (app a b').
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (app a y); auto.
Save LSLstar_context_app_r.
Hint Resolve LSLstar_context_app_r.

Goal
forall a a' b b' : terms,
e_relLSLstar _ a a' ->
e_relLSLstar _ b b' -> e_relLSLstar _ (app a b) (app a' b').
intros; red in |- *.
apply star_trans with (app a' b).
change (e_relLSLstar _ (app a b) (app a' b)) in |- *; auto.
change (e_relLSLstar _ (app a' b) (app a' b')) in |- *; auto.
Save LSLstar_context_app.
Hint Resolve LSLstar_context_app.

Goal
forall a a' : terms,
e_relLSLstar _ a a' -> e_relLSLstar _ (lambda a) (lambda a').
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (lambda y); auto.
Save LSLstar_context_lambda.
Hint Resolve LSLstar_context_lambda.

Goal
forall (a a' : terms) (s : sub_explicits),
e_relLSLstar _ a a' -> e_relLSLstar _ (env a s) (env a' s).
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (env y s); auto.
Save LSLstar_context_env_t.
Hint Resolve LSLstar_context_env_t.

Goal
forall (a : terms) (s s' : sub_explicits),
e_relLSLstar _ s s' -> e_relLSLstar _ (env a s) (env a s').
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (env a y); auto.
Save LSLstar_context_env_s.
Hint Resolve LSLstar_context_env_s.

Goal
forall (a a' : terms) (s s' : sub_explicits),
e_relLSLstar _ a a' ->
e_relLSLstar _ s s' -> e_relLSLstar _ (env a s) (env a' s').
intros; red in |- *.
apply star_trans with (env a' s).
change (e_relLSLstar _ (env a s) (env a' s)) in |- *; auto.
change (e_relLSLstar _ (env a' s) (env a' s')) in |- *; auto.
Save LSLstar_context_env.
Hint Resolve LSLstar_context_env.

Goal
forall (a a' : terms) (s : sub_explicits),
e_relLSLstar _ a a' -> e_relLSLstar _ (cons a s) (cons a' s). 
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (cons y s); auto.
Save LSLstar_context_cons_t.
Hint Resolve LSLstar_context_cons_t.

Goal
forall (a : terms) (s s' : sub_explicits),
e_relLSLstar _ s s' -> e_relLSLstar _ (cons a s) (cons a s'). 
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (cons a y); auto.
Save LSLstar_context_cons_s.
Hint Resolve LSLstar_context_cons_s.

Goal
forall (a a' : terms) (s s' : sub_explicits),
e_relLSLstar _ a a' ->
e_relLSLstar _ s s' -> e_relLSLstar _ (cons a s) (cons a' s').
intros; red in |- *.
apply star_trans with (cons a' s).
change (e_relLSLstar _ (cons a s) (cons a' s)) in |- *; auto.
change (e_relLSLstar _ (cons a' s) (cons a' s')) in |- *; auto.
Save LSLstar_context_cons.
Hint Resolve LSLstar_context_cons.

Goal
forall s s' t : sub_explicits,
e_relLSLstar _ s s' -> e_relLSLstar _ (comp s t) (comp s' t).
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (comp y t); auto.
Save LSLstar_context_comp_l.
Hint Resolve LSLstar_context_comp_l.

Goal
forall s t t' : sub_explicits,
e_relLSLstar _ t t' -> e_relLSLstar _ (comp s t) (comp s t').
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (comp s y); auto.
Save LSLstar_context_comp_r.
Hint Resolve LSLstar_context_comp_r.

Goal
forall s s' t t' : sub_explicits,
e_relLSLstar _ t t' ->
e_relLSLstar _ s s' -> e_relLSLstar _ (comp s t) (comp s' t').
intros; red in |- *.
apply star_trans with (comp s' t).
change (e_relLSLstar _ (comp s t) (comp s' t)) in |- *; auto.
change (e_relLSLstar _ (comp s' t) (comp s' t')) in |- *; auto.
Save LSLstar_context_comp.
Hint Resolve LSLstar_context_comp.

Goal
forall s s' : sub_explicits,
e_relLSLstar _ s s' -> e_relLSLstar _ (lift s) (lift s').
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (lift y); auto.
Save LSLstar_context_lift.
Hint Resolve LSLstar_context_lift.

