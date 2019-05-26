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
(*                               sigma_lift.v                               *)
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


                    (* Systeme sigma-lift *)

Require Import TS.
Require Import sur_les_relations.

(* regles de reecriture *)

Inductive reg_app : terms -> terms -> Prop :=
    reg1_app :
      forall (a b : terms) (s : sub_explicits),
      reg_app (env (app a b) s) (app (env a s) (env b s)). 
Hint Resolve reg1_app.

Inductive reg_lambda : terms -> terms -> Prop :=
    reg1_lambda :
      forall (a : terms) (s : sub_explicits),
      reg_lambda (env (lambda a) s) (lambda (env a (lift s))). 
Hint Resolve reg1_lambda.

Inductive reg_clos : terms -> terms -> Prop :=
    reg1_clos :
      forall (a : terms) (s t : sub_explicits),
      reg_clos (env (env a s) t) (env a (comp s t)). 
Hint Resolve reg1_clos.

Inductive reg_varshift1 : terms -> terms -> Prop :=
    reg1_varshift1 :
      forall n : nat, reg_varshift1 (env (var n) shift) (var (S n)). 
Hint Resolve reg1_varshift1.

Inductive reg_varshift2 : terms -> terms -> Prop :=
    reg1_varshift2 :
      forall (n : nat) (s : sub_explicits),
      reg_varshift2 (env (var n) (comp shift s)) (env (var (S n)) s). 
Hint Resolve reg1_varshift2.

Inductive reg_fvarcons : terms -> terms -> Prop :=
    reg1_fvarcons :
      forall (a : terms) (s : sub_explicits),
      reg_fvarcons (env (var 0) (cons a s)) a. 
Hint Resolve reg1_fvarcons.

Inductive reg_fvarlift1 : terms -> terms -> Prop :=
    reg1_fvarlift1 :
      forall s : sub_explicits, reg_fvarlift1 (env (var 0) (lift s)) (var 0). 
Hint Resolve reg1_fvarlift1.

Inductive reg_fvarlift2 : terms -> terms -> Prop :=
    reg1_fvarlift2 :
      forall s t : sub_explicits,
      reg_fvarlift2 (env (var 0) (comp (lift s) t)) (env (var 0) t). 
Hint Resolve reg1_fvarlift2.

Inductive reg_rvarcons : terms -> terms -> Prop :=
    reg1_rvarcons :
      forall (n : nat) (a : terms) (s : sub_explicits),
      reg_rvarcons (env (var (S n)) (cons a s)) (env (var n) s). 
Hint Resolve reg1_rvarcons.

Inductive reg_rvarlift1 : terms -> terms -> Prop :=
    reg1_rvarlift1 :
      forall (n : nat) (s : sub_explicits),
      reg_rvarlift1 (env (var (S n)) (lift s)) (env (var n) (comp s shift)). 
Hint Resolve reg1_rvarlift1.

Inductive reg_rvarlift2 : terms -> terms -> Prop :=
    reg1_rvarlift2 :
      forall (n : nat) (s t : sub_explicits),
      reg_rvarlift2 (env (var (S n)) (comp (lift s) t))
        (env (var n) (comp s (comp shift t))). 
Hint Resolve reg1_rvarlift2.

Inductive reg_assenv : sub_explicits -> sub_explicits -> Prop :=
    reg1_assenv :
      forall s t u : sub_explicits,
      reg_assenv (comp (comp s t) u) (comp s (comp t u)). 
Hint Resolve reg1_assenv.

Inductive reg_mapenv : sub_explicits -> sub_explicits -> Prop :=
    reg1_mapenv :
      forall (a : terms) (s t : sub_explicits),
      reg_mapenv (comp (cons a s) t) (cons (env a t) (comp s t)). 
Hint Resolve reg1_mapenv.

Inductive reg_shiftcons : sub_explicits -> sub_explicits -> Prop :=
    reg1_shiftcons :
      forall (a : terms) (s : sub_explicits),
      reg_shiftcons (comp shift (cons a s)) s. 
Hint Resolve reg1_shiftcons.

Inductive reg_shiftlift1 : sub_explicits -> sub_explicits -> Prop :=
    reg1_shiftlift1 :
      forall s : sub_explicits,
      reg_shiftlift1 (comp shift (lift s)) (comp s shift). 
Hint Resolve reg1_shiftlift1.

Inductive reg_shiftlift2 : sub_explicits -> sub_explicits -> Prop :=
    reg1_shiftlift2 :
      forall s t : sub_explicits,
      reg_shiftlift2 (comp shift (comp (lift s) t)) (comp s (comp shift t)). 
Hint Resolve reg1_shiftlift2. 

Inductive reg_lift1 : sub_explicits -> sub_explicits -> Prop :=
    reg1_lift1 :
      forall s t : sub_explicits,
      reg_lift1 (comp (lift s) (lift t)) (lift (comp s t)). 
Hint Resolve reg1_lift1.

Inductive reg_lift2 : sub_explicits -> sub_explicits -> Prop :=
    reg1_lift2 :
      forall s t u : sub_explicits,
      reg_lift2 (comp (lift s) (comp (lift t) u)) (comp (lift (comp s t)) u). 
Hint Resolve reg1_lift2.

Inductive reg_liftenv : sub_explicits -> sub_explicits -> Prop :=
    reg1_liftenv :
      forall (a : terms) (s t : sub_explicits),
      reg_liftenv (comp (lift s) (cons a t)) (cons a (comp s t)). 
Hint Resolve reg1_liftenv.

Inductive reg_idl : sub_explicits -> sub_explicits -> Prop :=
    reg1_idl : forall s : sub_explicits, reg_idl (comp id s) s. 
Hint Resolve reg1_idl.

Inductive reg_idr : sub_explicits -> sub_explicits -> Prop :=
    reg1_idr : forall s : sub_explicits, reg_idr (comp s id) s. 
Hint Resolve reg1_idr.

Inductive reg_liftid : sub_explicits -> sub_explicits -> Prop :=
    reg1_liftid : reg_liftid (lift id) id. 
Hint Resolve reg1_liftid.

Inductive reg_id : terms -> terms -> Prop :=
    reg1_id : forall a : terms, reg_id (env a id) a. 
Hint Resolve reg1_id.

(* systeme sigma-lift *)

Inductive e_systemSL : forall b : wsort, TS b -> TS b -> Prop :=
  | regle_app : forall a b : terms, reg_app a b -> e_systemSL wt a b
  | regle_lambda : forall a b : terms, reg_lambda a b -> e_systemSL wt a b
  | regle_clos : forall a b : terms, reg_clos a b -> e_systemSL wt a b
  | regle_varshift1 :
      forall a b : terms, reg_varshift1 a b -> e_systemSL wt a b
  | regle_varshift2 :
      forall a b : terms, reg_varshift2 a b -> e_systemSL wt a b
  | regle_fvarcons :
      forall a b : terms, reg_fvarcons a b -> e_systemSL wt a b
  | regle_fvarlift1 :
      forall a b : terms, reg_fvarlift1 a b -> e_systemSL wt a b
  | regle_fvarlift2 :
      forall a b : terms, reg_fvarlift2 a b -> e_systemSL wt a b
  | regle_rvarcons :
      forall a b : terms, reg_rvarcons a b -> e_systemSL wt a b
  | regle_rvarlift1 :
      forall a b : terms, reg_rvarlift1 a b -> e_systemSL wt a b
  | regle_rvarlift2 :
      forall a b : terms, reg_rvarlift2 a b -> e_systemSL wt a b
  | regle_assenv :
      forall s t : sub_explicits, reg_assenv s t -> e_systemSL ws s t
  | regle_mapenv :
      forall s t : sub_explicits, reg_mapenv s t -> e_systemSL ws s t
  | regle_shiftcons :
      forall s t : sub_explicits, reg_shiftcons s t -> e_systemSL ws s t
  | regle_shiftlift1 :
      forall s t : sub_explicits, reg_shiftlift1 s t -> e_systemSL ws s t
  | regle_shiftlift2 :
      forall s t : sub_explicits, reg_shiftlift2 s t -> e_systemSL ws s t
  | regle_lift1 :
      forall s t : sub_explicits, reg_lift1 s t -> e_systemSL ws s t
  | regle_lift2 :
      forall s t : sub_explicits, reg_lift2 s t -> e_systemSL ws s t
  | regle_liftenv :
      forall s t : sub_explicits, reg_liftenv s t -> e_systemSL ws s t
  | regle_idl : forall s t : sub_explicits, reg_idl s t -> e_systemSL ws s t
  | regle_idr : forall s t : sub_explicits, reg_idr s t -> e_systemSL ws s t
  | regle_liftid :
      forall s t : sub_explicits, reg_liftid s t -> e_systemSL ws s t
  | regle_id : forall a b : terms, reg_id a b -> e_systemSL wt a b.

Notation systemSL := (e_systemSL _) (only parsing).
(* <Warning> : Syntax is discontinued *)

Hint Resolve regle_app regle_lambda regle_clos regle_varshift1
  regle_varshift2 regle_fvarcons regle_fvarlift1 regle_fvarlift2
  regle_rvarcons regle_rvarlift1 regle_rvarlift2 regle_assenv regle_mapenv
  regle_shiftcons regle_shiftlift1 regle_shiftlift2 regle_lift1 regle_lift2
  regle_liftenv regle_idl regle_idr regle_liftid regle_id.

(* relation engendree par le systeme sigma-lift *)

Inductive e_relSL : forall b : wsort, TS b -> TS b -> Prop :=
  | SL_one_regle :
      forall (b : wsort) (M N : TS b), e_systemSL _ M N -> e_relSL b M N
  | SL_context_app_l :
      forall a a' b : terms,
      e_relSL wt a a' -> e_relSL wt (app a b) (app a' b)
  | SL_context_app_r :
      forall a b b' : terms,
      e_relSL wt b b' -> e_relSL wt (app a b) (app a b')
  | SL_context_lambda :
      forall a a' : terms,
      e_relSL wt a a' -> e_relSL wt (lambda a) (lambda a')
  | SL_context_env_t :
      forall (a a' : terms) (s : sub_explicits),
      e_relSL wt a a' -> e_relSL wt (env a s) (env a' s)
  | SL_context_env_s :
      forall (a : terms) (s s' : sub_explicits),
      e_relSL ws s s' -> e_relSL wt (env a s) (env a s')
  | SL_context_cons_t :
      forall (a a' : terms) (s : sub_explicits),
      e_relSL wt a a' -> e_relSL ws (cons a s) (cons a' s)
  | SL_context_cons_s :
      forall (a : terms) (s s' : sub_explicits),
      e_relSL ws s s' -> e_relSL ws (cons a s) (cons a s')
  | SL_context_comp_l :
      forall s s' t : sub_explicits,
      e_relSL ws s s' -> e_relSL ws (comp s t) (comp s' t)
  | SL_context_comp_r :
      forall s t t' : sub_explicits,
      e_relSL ws t t' -> e_relSL ws (comp s t) (comp s t')
  | SL_context_lift :
      forall s s' : sub_explicits,
      e_relSL ws s s' -> e_relSL ws (lift s) (lift s').

Notation relSL := (e_relSL _) (only parsing).
(* <Warning> : Syntax is discontinued *)

Hint Resolve SL_one_regle SL_context_app_l SL_context_app_r SL_context_lambda
  SL_context_env_t SL_context_env_s SL_context_cons_t SL_context_cons_s
  SL_context_comp_l SL_context_comp_r SL_context_lift.

(* fermeture reflexive-transitive de la relation sigma-lift *)

Definition e_relSLstar (b : wsort) := explicit_star _ (e_relSL b).

Notation relSLstar := (e_relSLstar _) (only parsing).
(* <Warning> : Syntax is discontinued *)

Hint Unfold e_relSLstar.

(* *)

Goal
forall a a' b : terms,
e_relSLstar _ a a' -> e_relSLstar _ (app a b) (app a' b).
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (app y b); auto.
Save SLstar_context_app_l.
Hint Resolve SLstar_context_app_l.

Goal
forall a b b' : terms,
e_relSLstar _ b b' -> e_relSLstar _ (app a b) (app a b').
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (app a y); auto.
Save SLstar_context_app_r.
Hint Resolve SLstar_context_app_r.

Goal
forall a a' : terms,
e_relSLstar _ a a' -> e_relSLstar _ (lambda a) (lambda a').
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (lambda y); auto.
Save SLstar_context_lambda.
Hint Resolve SLstar_context_lambda.

Goal
forall (a a' : terms) (s : sub_explicits),
e_relSLstar _ a a' -> e_relSLstar _ (env a s) (env a' s).
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (env y s); auto.
Save SLstar_context_env_t.
Hint Resolve SLstar_context_env_t.

Goal
forall (a : terms) (s s' : sub_explicits),
e_relSLstar _ s s' -> e_relSLstar _ (env a s) (env a s').
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (env a y); auto.
Save SLstar_context_env_s.
Hint Resolve SLstar_context_env_s.

Goal
forall (a a' : terms) (s : sub_explicits),
e_relSLstar _ a a' -> e_relSLstar _ (cons a s) (cons a' s). 
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (cons y s); auto.
Save SLstar_context_cons_t.
Hint Resolve SLstar_context_cons_t.

Goal
forall (a : terms) (s s' : sub_explicits),
e_relSLstar _ s s' -> e_relSLstar _ (cons a s) (cons a s'). 
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (cons a y); auto.
Save SLstar_context_cons_s.
Hint Resolve SLstar_context_cons_s.

Goal
forall s s' t : sub_explicits,
e_relSLstar _ s s' -> e_relSLstar _ (comp s t) (comp s' t).
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (comp y t); auto.
Save SLstar_context_comp_l.
Hint Resolve SLstar_context_comp_l.

Goal
forall s t t' : sub_explicits,
e_relSLstar _ t t' -> e_relSLstar _ (comp s t) (comp s t').
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (comp s y); auto.
Save SLstar_context_comp_r.
Hint Resolve SLstar_context_comp_r.

Goal
forall s s' : sub_explicits,
e_relSLstar _ s s' -> e_relSLstar _ (lift s) (lift s').
red in |- *; simple induction 1; intros.
auto.
apply star_trans1 with (lift y); auto.
Save SLstar_context_lift.
Hint Resolve SLstar_context_lift.


