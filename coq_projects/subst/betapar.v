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
(*                                betapar.v                                 *)
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


         (* relation bata_par: Beta|| *)

Require Import TS.
Require Import sur_les_relations.

Inductive e_beta_par : forall b : wsort, TS b -> TS b -> Prop :=
  | var_bpar : forall n : nat, e_beta_par wt (var n) (var n)
  | id_bpar : e_beta_par ws id id
  | shift_bpar : e_beta_par ws shift shift
  | app_bpar :
      forall M N M' N' : terms,
      e_beta_par wt M M' ->
      e_beta_par wt N N' -> e_beta_par wt (app M N) (app M' N')
  | lambda_bpar :
      forall M M' : terms,
      e_beta_par wt M M' -> e_beta_par wt (lambda M) (lambda M')
  | env_bpar :
      forall (M M' : terms) (s s' : sub_explicits),
      e_beta_par wt M M' ->
      e_beta_par ws s s' -> e_beta_par wt (env M s) (env M' s')
  | beta_bpar :
      forall M N M' N' : terms,
      e_beta_par wt M M' ->
      e_beta_par wt N N' ->
      e_beta_par wt (app (lambda M) N) (env M' (cons N' id))
  | cons_bpar :
      forall (M M' : terms) (s s' : sub_explicits),
      e_beta_par wt M M' ->
      e_beta_par ws s s' -> e_beta_par ws (cons M s) (cons M' s')
  | lift_bpar :
      forall s s' : sub_explicits,
      e_beta_par ws s s' -> e_beta_par ws (lift s) (lift s')
  | comp_bpar :
      forall s s' t t' : sub_explicits,
      e_beta_par ws s s' ->
      e_beta_par ws t t' -> e_beta_par ws (comp s t) (comp s' t')
  | metaX_bpar : forall n : nat, e_beta_par wt (meta_X n) (meta_X n)
  | metax_bpar : forall n : nat, e_beta_par ws (meta_x n) (meta_x n).

Hint Resolve var_bpar id_bpar shift_bpar app_bpar lambda_bpar env_bpar
  beta_bpar cons_bpar lift_bpar comp_bpar metaX_bpar metax_bpar.


Notation beta_par := (e_beta_par _) (only parsing).
(* <Warning> : Syntax is discontinued *)


Goal forall (b : wsort) (M : TS b), e_beta_par _ M M.
simple induction M; auto.
Save refl_betapar.
Hint Resolve refl_betapar.

Definition e_betapar_inv (b : wsort) (M N : TS b) :=
  match M in (TS b) return Prop with
  | var n =>
      (* var *) 
      match N in (TS b) return Prop with
      | var m =>
          (* var *)  n = m
          (* app *) 
      | app N1 N2 => False 
          (* lam *) 
      | lambda N1 => False
          (* env *) 
      | env N1 N2 => False
          (* id  *) 
      | id => False
          (*  |  *) 
      | shift => False
          (*  .  *) 
      | cons N1 N2 => False 
          (*  o  *) 
      | comp N1 N2 => False
          (*  || *) 
      | lift N1 => False
          (*  X  *) 
      | meta_X n => False
          (*  x  *) 
      | meta_x n => False
      end
      (* app *) 
  | app M1 M2 =>
      match N in (TS b) return Prop with
      | var n =>
          (* var *)  False
          (* app *) 
      | app N1 N2 => e_beta_par _ M1 N1 /\ e_beta_par _ M2 N2
          (* lam *) 
      | lambda N1 => False 
          (* env *) 
      | env N1 N2 =>
          exists M3 : terms,
            (exists N3 : terms,
               M1 = lambda M3 /\
               e_beta_par _ M3 N1 /\ N2 = cons N3 id /\ e_beta_par _ M2 N3)
          (* id  *) 
      | id => False
          (*  |  *) 
      | shift => False
          (*  .  *) 
      | cons N1 N2 => False
          (*  o  *) 
      | comp N1 N2 => False
          (* ||  *) 
      | lift N1 => False
          (*  X  *) 
      | meta_X n => False
          (*  x  *) 
      | meta_x n => False
      end
      (* lam *) 
  | lambda M1 =>
      match N in (TS b) return Prop with
      | var n =>
          (* var *)  False
          (* app *) 
      | app N1 N2 => False 
          (* lam *) 
      | lambda N1 => e_beta_par _ M1 N1
          (* env *) 
      | env N1 N2 => False
          (* id  *) 
      | id => False
          (*  |  *) 
      | shift => False
          (*  .  *) 
      | cons N1 N2 => False
          (*  o  *) 
      | comp N1 N2 => False
          (* ||  *) 
      | lift N1 => False
          (*  X  *) 
      | meta_X n => False
          (*  x  *) 
      | meta_x n => False
      end
      (* env *) 
  | env M1 M2 =>
      match N in (TS b) return Prop with
      | var n =>
          (* var *)  False
          (* app *) 
      | app N1 N2 => False 
          (* lam *) 
      | lambda N1 => False 
          (* env *) 
      | env N1 N2 => e_beta_par _ M1 N1 /\ e_beta_par _ M2 N2
          (* id  *) 
      | id => False
          (*  |  *) 
      | shift => False
          (*  .  *) 
      | cons N1 N2 => False
          (*  o  *) 
      | comp N1 N2 => False
          (* ||  *) 
      | lift N1 => False
          (*  X  *) 
      | meta_X n => False
          (*  x  *) 
      | meta_x n => False
      end
      (* id  *) 
  | id =>
      match N in (TS b) return Prop with
      | var n =>
          (* var *)  False
          (* app *) 
      | app N1 N2 => False 
          (* lam *) 
      | lambda N1 => False
          (* env *) 
      | env N1 N2 => False
          (* id  *) 
      | id => True
          (*  |  *) 
      | shift => False
          (*  .  *) 
      | cons N1 N2 => False
          (*  o  *) 
      | comp N1 N2 => False
          (*  || *) 
      | lift N1 => False
          (*  X  *) 
      | meta_X n => False
          (*  x  *) 
      | meta_x n => False
      end
      (*  |  *) 
  | shift =>
      match N in (TS b) return Prop with
      | var n =>
          (* var *)  False
          (* app *) 
      | app N1 N2 => False 
          (* lam *) 
      | lambda N1 => False
          (* env *) 
      | env N1 N2 => False
          (* id  *) 
      | id => False
          (*  |  *) 
      | shift => True 
          (*  .  *) 
      | cons N1 N2 => False
          (*  o  *) 
      | comp N1 N2 => False
          (*  || *) 
      | lift N1 => False
          (*  X  *) 
      | meta_X n => False
          (*  x  *) 
      | meta_x n => False
      end 
      (*  .  *) 
  | cons M1 M2 =>
      match N in (TS b) return Prop with
      | var n =>
          (* var *)  False
          (* app *) 
      | app N1 N2 => False 
          (* lam *) 
      | lambda N1 => False 
          (* env *) 
      | env N1 N2 => False
          (* id  *) 
      | id => False
          (*  |  *) 
      | shift => False
          (*  .  *) 
      | cons N1 N2 => e_beta_par _ M1 N1 /\ e_beta_par _ M2 N2
          (*  o  *) 
      | comp N1 N2 => False
          (* ||  *) 
      | lift N1 => False
          (*  X  *) 
      | meta_X n => False
          (*  x  *) 
      | meta_x n => False
      end
      (*  o  *) 
  | comp M1 M2 =>
      match N in (TS b) return Prop with
      | var n =>
          (* var *)  False
          (* app *) 
      | app N1 N2 => False 
          (* lam *) 
      | lambda N1 => False
          (* env *) 
      | env N1 N2 => False
          (* id  *) 
      | id => False
          (*  |  *) 
      | shift => False
          (*  .  *) 
      | cons N1 N2 => False
          (*  o  *) 
      | comp N1 N2 => e_beta_par _ M1 N1 /\ e_beta_par _ M2 N2
          (* ||  *) 
      | lift N1 => False
          (*  X  *) 
      | meta_X n => False
          (*  x  *) 
      | meta_x n => False
      end 
      (* ||  *) 
  | lift M1 =>
      match N in (TS b) return Prop with
      | var n =>
          (* var *)  False
          (* app *) 
      | app N1 N2 => False 
          (* lam *) 
      | lambda N1 => False
          (* env *) 
      | env N1 N2 => False
          (* id  *) 
      | id => False
          (*  |  *) 
      | shift => False
          (*  .  *) 
      | cons N1 N2 => False
          (*  o  *) 
      | comp N1 N2 => False
          (* ||  *) 
      | lift N1 => e_beta_par _ M1 N1
          (*  X  *) 
      | meta_X n => False
          (*  x  *) 
      | meta_x n => False
      end
      (*  X  *) 
  | meta_X n =>
      match N in (TS b) return Prop with
      | var n =>
          (* var *)  False
          (* app *) 
      | app N1 N2 => False 
          (* lam *) 
      | lambda N1 => False
          (* env *) 
      | env N1 N2 => False
          (* id  *) 
      | id => False
          (*  |  *) 
      | shift => False
          (*  .  *) 
      | cons N1 N2 => False
          (*  o  *) 
      | comp N1 N2 => False
          (*  || *) 
      | lift N1 => False
          (*  X  *) 
      | meta_X m => n = m
          (*  x  *) 
      | meta_x m => False
      end
      (*  x  *) 
  | meta_x n =>
      match N in (TS b) return Prop with
      | var n =>
          (* var *)  False
          (* app *) 
      | app N1 N2 => False 
          (* lam *) 
      | lambda N1 => False
          (* env *) 
      | env N1 N2 => False
          (* id  *) 
      | id => False
          (*  |  *) 
      | shift => False
          (*  .  *) 
      | cons N1 N2 => False
          (*  o  *) 
      | comp N1 N2 => False
          (*  || *) 
      | lift N1 => False
          (*  X  *) 
      | meta_X m => False
          (*  x  *) 
      | meta_x m => n = m
      end
  end.


Notation betapar_inv := (e_betapar_inv _) (only parsing).
(* <Warning> : Syntax is discontinued *)


Goal
forall (b : wsort) (M N : TS b), e_beta_par _ M N -> e_betapar_inv _ M N.
simple induction 1; intros; simpl in |- *; auto.
(* beta *)exists M0; exists N'; auto.
Save lemma1_inv_betapar.
Hint Resolve lemma1_inv_betapar.

Goal
forall (P : terms -> Prop) (n : nat),
P (var n) -> forall M : terms, e_beta_par _ (var n) M -> P M.
intros P n H M H0; cut (e_betapar_inv _ (var n) M).
2: auto.
pattern M in |- *; apply terms_ind.
(* var *)
simple induction 1; assumption.
(* app *)
simple induction 3.
(* lam *)
simple induction 2.
(* env *)
simple induction 2.
(* X *)simple induction 1.
Save case_bvar.

Goal
forall (P : terms -> Prop) (a b : terms),
(forall a' b' : terms,
 e_beta_par _ a a' -> e_beta_par _ b b' -> P (app a' b')) ->
(forall a1 a1' b' : terms,
 a = lambda a1 ->
 e_beta_par _ a1 a1' -> e_beta_par _ b b' -> P (env a1' (cons b' id))) ->
forall M : terms, e_beta_par _ (app a b) M -> P M.
intros P a b H H0 M H1; cut (e_betapar_inv _ (app a b) M).
2: auto.
pattern M in |- *; apply terms_ind.
(* var *)
simple induction 1.
(* app *)
unfold e_betapar_inv at 3 in |- *; intros a' b' H2 H3 H4.
elim H4; intros H5 H6.
apply H; assumption.
(* lam *)
simple induction 2.
(* env *)
unfold e_betapar_inv at 2 in |- *; intros a1' H2 s H3.
elim H3; intros a1 H4; elim H4; intros b' H5.
elim H5; intros H6 H7; elim H7; intros H8 H9; elim H9; intros H10 H11.
try rewrite H6; try rewrite H10; apply (H0 a1); assumption.
(* X *)simple induction 1.
Save case_bapp.

Goal
forall (P : terms -> Prop) (a : terms),
(forall a' : terms, e_beta_par _ a a' -> P (lambda a')) ->
forall M : terms, e_beta_par _ (lambda a) M -> P M.
intros P a H M H0; cut (e_betapar_inv _ (lambda a) M).
2: auto.
pattern M in |- *; apply terms_ind.
(* var *)
simple induction 1.
(* app *)
simple induction 3.
(* lam *)
unfold e_betapar_inv at 2 in |- *; intros a' H1 H2.
apply H; assumption.
(* env *)
simple induction 2.
(* X *)simple induction 1.
Save case_blambda.

Goal
forall (P : terms -> Prop) (a : terms) (s : sub_explicits),
(forall (a' : terms) (s' : sub_explicits),
 e_beta_par _ a a' -> e_beta_par _ s s' -> P (env a' s')) ->
forall M : terms, e_beta_par _ (env a s) M -> P M.
intros P a s H M H0; cut (e_betapar_inv _ (env a s) M).
2: auto.
pattern M in |- *; apply terms_ind.
(* var *)
simple induction 1.
(* app *)
simple induction 3.
(* lam *)
simple induction 2.
(* env *)
unfold e_betapar_inv at 2 in |- *; intros a' H1 s' H2.
elim H2; intros; apply H; assumption.
(* X *)simple induction 1.
Save case_benv.

Goal
forall P : sub_explicits -> Prop,
P id -> forall M : sub_explicits, e_beta_par _ id M -> P M.
intros P H M H0; cut (e_betapar_inv _ id M).
2: auto.
pattern M in |- *; apply sub_explicits_ind.
(* id *)
intro; assumption.
(* |  *)
simple induction 1.
(* .  *)
simple induction 2.
(*  o *)
simple induction 3.
(* || *)
simple induction 2.
(* x *)simple induction 1.
Save case_bid.

Goal
forall P : sub_explicits -> Prop,
P shift -> forall M : sub_explicits, e_beta_par _ shift M -> P M.
intros P H M H0; cut (e_betapar_inv _ shift M).
2: auto.
pattern M in |- *; apply sub_explicits_ind.
(* id *)
simple induction 1.
(* |  *)
intro; assumption.
(* .  *)
simple induction 2.
(*  o *)
simple induction 3.
(* || *)
simple induction 2.
(* x *)simple induction 1.
Save case_bshift.

Goal
forall (P : sub_explicits -> Prop) (a : terms) (s : sub_explicits),
(forall (a' : terms) (s' : sub_explicits),
 e_beta_par _ a a' -> e_beta_par _ s s' -> P (cons a' s')) ->
forall M : sub_explicits, e_beta_par _ (cons a s) M -> P M.
intros P a s H M H0; cut (e_betapar_inv _ (cons a s) M).
2: auto.
pattern M in |- *; apply sub_explicits_ind.
(* id  *)
simple induction 1.
(*  |  *)
simple induction 1.
(*  .  *)
unfold e_betapar_inv at 2 in |- *; intros s' H1 a' H2.
elim H2; intros.
apply H; assumption.
(*  o  *)
simple induction 3.
(*  || *)
simple induction 2.
(* x *)simple induction 1.
Save case_bcons.

Goal
forall (P : sub_explicits -> Prop) (s t : sub_explicits),
(forall s' t' : sub_explicits,
 e_beta_par _ s s' -> e_beta_par _ t t' -> P (comp s' t')) ->
forall M : sub_explicits, e_beta_par _ (comp s t) M -> P M.
intros P s t H M H0; cut (e_betapar_inv _ (comp s t) M).
2: auto.
pattern M in |- *; apply sub_explicits_ind.
(* id  *)
simple induction 1.
(*  |  *)
simple induction 1.
(*  .  *)
simple induction 2.
(*  o  *)
unfold e_betapar_inv at 3 in |- *.
intros s' t' H1 H2 H3; elim H3; intros; apply H; assumption.
(*  || *)
simple induction 2.
(* x *)simple induction 1.
Save case_bcomp.

Goal
forall (P : sub_explicits -> Prop) (s : sub_explicits),
(forall s' : sub_explicits, e_beta_par _ s s' -> P (lift s')) ->
forall M : sub_explicits, e_beta_par _ (lift s) M -> P M.
intros P s H M H0; cut (e_betapar_inv _ (lift s) M).
2: auto.
pattern M in |- *; apply sub_explicits_ind.
(* id  *)
simple induction 1.
(*  |  *)
simple induction 1.
(*  .  *)
simple induction 2.
(*  o  *)
simple induction 3.
(*  || *)
unfold e_betapar_inv at 2 in |- *.
intros s' H1 H2; apply H; assumption.
(* x *)simple induction 1.
Save case_blift.

Goal
forall (P : terms -> Prop) (n : nat),
P (meta_X n) -> forall M : terms, e_beta_par _ (meta_X n) M -> P M.
intros P n H M H0; cut (e_betapar_inv _ (meta_X n) M).
2: auto.
pattern M in |- *; apply terms_ind.
(* var *)
simple induction 1.
(* app *)
simple induction 3.
(* lam *)
simple induction 2.
(* env *)
simple induction 2.
(* X *)simple induction 1; assumption.
Save case_bmetaX.

Goal
forall (P : sub_explicits -> Prop) (n : nat),
P (meta_x n) -> forall M : sub_explicits, e_beta_par _ (meta_x n) M -> P M.
intros P n H M H0; cut (e_betapar_inv _ (meta_x n) M).
2: auto.
pattern M in |- *; apply sub_explicits_ind.
(* id *)
simple induction 1.
(* |  *)
simple induction 1.
(* .  *)
simple induction 2.
(*  o *)
simple induction 3.
(* || *)
simple induction 2.
(* x *)simple induction 1; assumption.
Save case_bmetax.




