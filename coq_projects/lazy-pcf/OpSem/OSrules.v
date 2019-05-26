(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  OSrules.v                                                               *)
(*                                                                          *)
(*  This file contains the definition of the operational                    *)
(*  semantics rules for lazy PCF, as well as a definition                   *)
(*  of the Ap function and some related properties.                         *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November  1993                                                          *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                OSrules.v                                 *)
(****************************************************************************)

Require Import List.
Require Import syntax.
Require Import environments.

Require Import typecheck.

Require Import rename.

(************************************************)
(*  OScons  (abbrev.)				*)
(*    (OScons v t e A) == 			*)
(*     (cons VTT <VT,tm>(<vari,ty>(v,t),e) A)	*)
(************************************************)

Definition OScons (v : vari) (t : ty) (e : tm) (A : OS_env) := (v, t, e) :: A.


(********************************************************)
(* Ap:							*)
(*    Inductively defines the relation characterized by *)
(*    the Ap function.					*)
(*							*)
(*    (Ap a F A F' n t) <--> Ap(F,a)=<F',[n:t->a]>	*)
(*        New variables may not come from 		*)
(*        the Domain of OS env A.			*)
(*							*)
(********************************************************)

                        
Inductive Ap (a : tm) : tm -> OS_env -> tm -> vari -> ty -> Prop :=
  | Ap_abs :
      forall (nv v : vari) (t : ty) (e ne : tm) (A : OS_env),
      ~ member vari nv (OS_Dom A) ->
      rename nv v e ne -> Ap a (abs v t e) A ne nv t
  | Ap_clos :
      forall (n v : vari) (s t : ty) (e ne e1 : tm) (A : OS_env),
      Ap a e (OScons v s e1 A) ne n t ->
      Ap a (clos e v s e1) A (clos ne v s e1) n t.


(********************************)
(*   ApNewVar  			*)
(*     Ap(a,fun,A) = 		*)
(*       <b,[n:t->a]> --->	*)
(*     n not in Dom(A)		*)
(********************************)

Goal
forall (a fun_ b : tm) (A : OS_env) (n : vari) (t : ty),
Ap a fun_ A b n t -> ~ member vari n (OS_Dom A).

   simple induction 1; intros.
   assumption.
   red in |- *; intro; apply H1; simpl in |- *.
   right; assumption.
Save ApNewVar.



(****************************************)
(*  OSrules				*)
(*					*)
(*  Definition of Operational Semantics	*)
(*					*)
(*  <<e,A>> -> <<e',A'>>		*)
(*					*)
(****************************************)

Inductive OSred : config -> config -> Prop :=
  | OS_C0 : forall A : OS_env, OSred (cfg o A) (cfg o A)
  | OS_CT : forall A : OS_env, OSred (cfg ttt A) (cfg ttt A)
  | OS_CF : forall A : OS_env, OSred (cfg fff A) (cfg fff A)
  | OS_L :
      forall (A : OS_env) (e : tm) (t : ty) (x : vari),
      OSred (cfg (abs x t e) A) (cfg (abs x t e) A)
  | OS_P0 :
      forall (A A' : OS_env) (e : tm),
      OSred (cfg e A) (cfg o A') -> OSred (cfg (prd e) A) (cfg o A')
  | OS_P :
      forall (A A' : OS_env) (e e1 : tm),
      OSred (cfg e A) (cfg (succ e1) A') -> OSred (cfg (prd e) A) (cfg e1 A')
  | OS_ZT :
      forall (A A' : OS_env) (e : tm),
      OSred (cfg e A) (cfg o A') -> OSred (cfg (is_o e) A) (cfg ttt A')
  | OS_ZF :
      forall (A A' : OS_env) (e e1 : tm),
      OSred (cfg e A) (cfg (succ e1) A') ->
      OSred (cfg (is_o e) A) (cfg fff A')
  | OS_S :
      forall (A A' : OS_env) (e e1 : tm),
      OSred (cfg e A) (cfg e1 A') ->
      OSred (cfg (succ e) A) (cfg (succ e1) A')
  | OS_Var1 :
      forall (A A' : OS_env) (e en : tm) (t : ty) (x : vari),
      ~ member vari x (OS_Dom A) ->
      OSred (cfg e A) (cfg en A') ->
      OSred (cfg (var x) (OScons x t e A)) (cfg en (OScons x t en A'))
  | OS_Var2 :
      forall (A A' : OS_env) (e en : tm) (t : ty) (x y : vari),
      x <> y ->
      ~ member vari x (OS_Dom A) ->
      OSred (cfg (var y) A) (cfg en A') ->
      OSred (cfg (var y) (OScons x t e A)) (cfg en (OScons x t e A'))
  | OS_Appl :
      forall (A A' A'' : OS_env) (e1 e2 en en' enf : tm) (n : vari) (t : ty),
      OSred (cfg e1 A) (cfg en A') ->
      Ap e2 en A en' n t ->
      OSred (cfg (clos en' n t e2) A') (cfg enf A'') ->
      OSred (cfg (appl e1 e2) A) (cfg enf A'')
  | OS_IfTrue :
      forall (A A' A'' : OS_env) (e1 e2 e3 en : tm),
      OSred (cfg e1 A) (cfg ttt A') ->
      OSred (cfg e2 A') (cfg en A'') ->
      OSred (cfg (cond e1 e2 e3) A) (cfg en A'')
  | OS_IfFalse :
      forall (A A' A'' : OS_env) (e1 e2 e3 en : tm),
      OSred (cfg e1 A) (cfg fff A') ->
      OSred (cfg e3 A') (cfg en A'') ->
      OSred (cfg (cond e1 e2 e3) A) (cfg en A'')
  | OS_Fix :
      forall (A A' : OS_env) (e e' en : tm) (x nx : vari) (t : ty),
      ~ member vari nx (OS_Dom A) ->
      rename nx x e e' ->
      OSred (cfg (clos e' nx t (Fix x t e)) A) (cfg en A') ->
      OSred (cfg (Fix x t e) A) (cfg en A')
  | OS_CL :
      forall (A A' : OS_env) (e e1 en e1' : tm) (x : vari) (t : ty),
      OSred (cfg e (OScons x t e1 A)) (cfg en (OScons x t e1' A')) ->
      forall s : ty,
      TC (OS_Dom_ty (OScons x t e1 A)) en s ->
      ~ (s = nat_ty \/ s = bool_ty) ->
      OSred (cfg (clos e x t e1) A) (cfg (clos en x t e1') A')
  | OS_CL' :
      forall (A A' : OS_env) (e e1 en e1' : tm) (x : vari) (t : ty),
      OSred (cfg e (OScons x t e1 A)) (cfg en (OScons x t e1' A')) ->
      forall s : ty,
      TC (OS_Dom_ty (OScons x t e1 A)) en s ->
      s = nat_ty \/ s = bool_ty -> OSred (cfg (clos e x t e1) A) (cfg en A').
	
