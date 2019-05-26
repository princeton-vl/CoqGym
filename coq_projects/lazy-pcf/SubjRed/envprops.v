(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  envprops.v                                                              *)
(*                                                                          *)
(*  This file contains properties of domains of environments                *)
(*  and their relation to type judgments and evaluations.                   *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November 1993                                                           *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                envprops.v                                *)
(****************************************************************************)

Require Import syntax.
Require Import List.
Require Import utils.
Require Import freevars.
Require Import typecheck.

Require Import environments.

Require Import OSrules.


(********************************)
(*  TEDomDomty_OSDom		*)
(*    Dom(Domt (A)) = Dom(A)	*)
(********************************)

Goal forall A : OS_env, TE_Dom (OS_Dom_ty A) = OS_Dom A.
   simple induction A; intros.
   simpl in |- *; reflexivity.
   simpl in |- *; elim H; reflexivity.
Save TEDomDomty_OSDom.



(**********************************)
(* vtinH_vinDomH		  *)
(*  (v,t) in H  -->  v in Dom(H)  *)
(**********************************)

Goal
forall (v : vari) (t : ty) (H : ty_env),
mapsto v t H -> member vari v (TE_Dom H).

simple induction H; simpl in |- *.
intro; assumption.
intros; elim H1; intro.
left; elim H2; intros; assumption.
right; elim H2; intro; exact H0.
Save vtinH_vinDomH.


(****************************************)
(* TCHet_FVeinDomH 			*)
(*					*)
(*   H |- e : t  -->  FV(e) in Dom(H)   *)
(*					*)
(****************************************)

Goal
forall (H : ty_env) (e : tm) (t : ty),
TC H e t -> forall v : vari, FV v e -> member vari v (TE_Dom H).

simple induction 1; simpl in |- *; intros.
absurd (FV v o).    apply inv_FV_o.    assumption.
absurd (FV v ttt).  apply inv_FV_ttt.  assumption.
absurd (FV v fff).  apply inv_FV_fff.  assumption.
apply H3.  apply inv_FV_succ; assumption.
apply H3.  apply inv_FV_prd; assumption.
apply H3.  apply inv_FV_is_o; assumption.
specialize inv_FV_var with (1 := H3); intro Q.
rewrite Q; apply vtinH_vinDomH with t0; assumption.
specialize inv_FV_appl with (1 := H6).
simple induction 1; intro F.
apply H3; assumption.
apply H5; assumption.
specialize inv_FV_abs with (1 := H4); simple induction 1; intros.
elim (H3 v0).
intro; absurd (v0 = v); assumption || symmetry  in |- *; assumption.
intro; assumption.
assumption.
specialize inv_FV_cond with (1 := H8); simple induction 1.
intro; apply H3; assumption.
simple induction 1; intro.
apply H5; assumption.
apply H7; assumption.
specialize inv_FV_fix with (1 := H4); simple induction 1; intros.
elim (H3 v0).
intro; absurd (v0 = v); assumption || symmetry  in |- *; assumption.
intro; assumption.
assumption.
specialize inv_FV_clos with (1 := H6); simple induction 1; intros.
apply H3; assumption.
elim H8; intros.
elim (H5 v0).
intro; absurd (v0 = v); assumption || symmetry  in |- *; assumption.
intro; assumption.
assumption.
Save TCHet_FVeinDomH.



(********************************)
(*  dom_pres			*)
(*    <<e,A>> -> <<n,A'>>  ---> *)
(*	 Domt(A) = Domt(A')	*)
(********************************)

Goal
forall c c' : config,
OSred c c' -> OS_Dom_ty (cfgenv c) = OS_Dom_ty (cfgenv c').

   simple induction 1; simpl in |- *; intros.
   reflexivity.  reflexivity.  reflexivity.  reflexivity.
   assumption.  assumption.  assumption.  assumption.  assumption.
   elim H2; reflexivity.
   elim H3; reflexivity.
   transitivity (OS_Dom_ty A'); assumption.
   transitivity (OS_Dom_ty A'); assumption.
   transitivity (OS_Dom_ty A'); assumption.
   assumption.
   replace (OS_Dom_ty A) with (tail ((x, t) :: OS_Dom_ty A)).
   replace (OS_Dom_ty A') with (tail ((x, t) :: OS_Dom_ty A')).
   apply (f_equal (tail (A:=VT))); assumption.
   simpl in |- *; reflexivity.
   simpl in |- *; reflexivity.
   replace (OS_Dom_ty A) with (tail ((x, t) :: OS_Dom_ty A)).
   replace (OS_Dom_ty A') with (tail ((x, t) :: OS_Dom_ty A')).
   apply (f_equal (tail (A:=VT))); assumption.
   simpl in |- *; reflexivity.
   simpl in |- *; reflexivity.
Save dom_pres.

