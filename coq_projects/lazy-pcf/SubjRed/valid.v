(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  valid.v                                                                 *)
(*                                                                          *)
(*  This file contains definitions of valid environments and                *)
(*  configurations, and also a related property.                            *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November 1993                                                           *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                 valid.v                                  *)
(****************************************************************************)

Require Import syntax.
Require Import List.
Require Import utils.
Require Import environments.

Require Import typecheck.

(****************************************************************)
(*							      	*)
(*  Validity functions for OS environments and configurations 	*)
(*							      	*)
(*                   Domt(A)|- e:t  VAL(A) 			*) 
(*  valid_env     : -----------------------			*)
(*                     VAL ([v:t->e]*A)				*)
(*							      	*)
(*                   Domt(A)|- e:t  VAL(A)			*)
(* valid_config   : -----------------------			*)
(*                       VAL<<e,A>> 				*)
(*							      	*)
(****************************************************************)

Inductive valid_env : OS_env -> Prop :=
  | valid_nil : valid_env nil
  | valid_cons :
      forall (v : vari) (t : ty) (e : tm) (A : OS_env),
      TC (OS_Dom_ty A) e t -> valid_env A -> valid_env ((v, t, e) :: A).


Inductive valid_config (c : config) : Prop :=
    valid_cfg :
      valid_env (cfgenv c) ->
      forall t : ty, TC (OS_Dom_ty (cfgenv c)) (cfgexp c) t -> valid_config c.


(****************************************)
(*  inv_valid_cons		 	*)
(*	Val([v:t->e]A) --->		*)
(*         Val(A) /\ Domt(A)|-e:t	*)
(****************************************)
Definition valid_c (A : OS_env) :=
  match A return Prop with
  | nil =>
      (* nil *)  True
      (* cons *) 
  | vtt :: A' => valid_env A' /\ TC (OS_Dom_ty A') (snd vtt) (snd (fst vtt))
  end.

Goal
forall (v : vari) (t : ty) (e : tm) (A : OS_env),
valid_env ((v, t, e) :: A) -> valid_env A /\ TC (OS_Dom_ty A) e t.

intros v t e A H.
change (valid_c ((v, t, e) :: A)) in |- *.
elim H; simpl in |- *; exact I || intros; split; assumption.
Save inv_valid_cons.
