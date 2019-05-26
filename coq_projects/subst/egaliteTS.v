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
(*                               egaliteTS.v                                *)
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

      
                      (* egalite dans les termes-sub_explicits (TS) *)

Require Import TS.

(***********************************************)
(*            Inegalites dans TS               *)
(***********************************************)

Goal forall (n : nat) (a b : terms), var n <> app a b.
intros; discriminate.
Save diff_var_app.

Goal forall (n : nat) (a : terms), var n <> lambda a.
intros; discriminate.
Save diff_var_lambda.

Goal forall (n : nat) (a : terms) (s : sub_explicits), var n <> env a s.
intros; discriminate.
Save diff_var_env.

Goal forall a b c : terms, app a b <> lambda c.
intros; discriminate.
Save diff_app_lambda.

Goal forall (a b c : terms) (s : sub_explicits), app a b <> env c s.
intros; discriminate.
Save diff_app_env.

Goal forall (a b : terms) (s : sub_explicits), lambda a <> env b s.
intros; discriminate.
Save diff_lambda_env.

Goal id <> shift.
intros; discriminate.
Save diff_id_shift.

Goal forall (a : terms) (s : sub_explicits), id <> cons a s.
intros; discriminate.
Save diff_id_cons.

Goal forall s t : sub_explicits, id <> comp s t.
intros; discriminate.
Save diff_id_comp.

Goal forall s : sub_explicits, id <> lift s.
intros; discriminate.
Save diff_id_lift.

Goal forall (a : terms) (s : sub_explicits), shift <> cons a s.
intros; discriminate.
Save diff_shift_cons.

Goal forall s t : sub_explicits, shift <> comp s t.
intros; discriminate.
Save diff_shift_comp.

Goal forall s : sub_explicits, shift <> lift s.
intros; discriminate.
Save diff_shift_lift.

Goal forall (a : terms) (s t u : sub_explicits), cons a s <> comp t u.
intros; discriminate.
Save diff_cons_comp.

Goal forall (a : terms) (s t : sub_explicits), cons a s <> lift t.
intros; discriminate.
Save diff_cons_lift.

Goal forall s t u : sub_explicits, comp s t <> lift u.
intros; discriminate.
Save diff_comp_lift.

(***********************************************)
(*             Egalite dans TS                 *)
(***********************************************)

Goal forall n1 n2 : nat, var n1 = var n2 -> n1 = n2. 
intros n1 n2 H; injection H; trivial. 
Save proj_var.

Goal forall a1 b1 a2 b2 : terms, app a1 b1 = app a2 b2 -> a1 = a2.
intros a1 b1 a2 b2 H; injection H; trivial. 
Save proj_app1.

Goal forall a1 b1 a2 b2 : terms, app a1 b1 = app a2 b2 -> b1 = b2.
intros a1 b1 a2 b2 H; injection H; trivial. 
Save proj_app2.

Goal forall a b : terms, lambda a = lambda b -> a = b.
intros a b H; injection H; trivial. 
Save proj_lambda.

Goal forall (a b : terms) (s t : sub_explicits), env a s = env b t -> a = b.
intros a b s t H; injection H; trivial. 
Save proj_env1.

Goal forall (a b : terms) (s t : sub_explicits), env a s = env b t -> s = t.
intros a b s t H; injection H; trivial. 
Save proj_env2.

Goal
forall (a b : terms) (s t : sub_explicits), cons a s = cons b t -> a = b.
intros a b s t H; injection H; trivial. 
Save proj_cons1.

Goal
forall (a b : terms) (s t : sub_explicits), cons a s = cons b t -> s = t.
intros a b s t H; injection H; trivial. 
Save proj_cons2.

Goal forall s1 s2 t1 t2 : sub_explicits, comp s1 t1 = comp s2 t2 -> s1 = s2.
intros s1 s2 t1 t2 H; injection H; trivial. 
Save proj_comp1.

Goal forall s1 s2 t1 t2 : sub_explicits, comp s1 t1 = comp s2 t2 -> t1 = t2.
intros s1 s2 t1 t2 H; injection H; trivial. 
Save proj_comp2.

Goal forall s t : sub_explicits, lift s = lift t -> s = t.
intros s t H; injection H; trivial. 
Save proj_lift.




