(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  subjrfn.v                                                               *)
(*                                                                          *)
(*  This file contains the main theorem, subjr_NF,                          *)
(*  which combines the subject reduction and normal                         *)
(*  form characterization theorems (the combination is                      *)
(*  necessary in order for the induction to go through).                    *)
(*  This proof is followed by individual proofs of the                      *)
(*  subject reduction theorem and normal form character-                    *)
(*  ization theorem as corollaries of the main proof.                       *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November 1993                                                           *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                subjrnf.v                                 *)
(****************************************************************************)

Require Import utils.
Require Import syntax.
Require Import environments.
Require Import typecheck.
Require Import freevars.
Require Import List.
Require Import ApTypes.
Require Import NF.
Require Import valid.
Require Import OSrules.
Require Import envprops.
Require Import rename.
Require Import NFprops.
Require Import TypeThms.


(********************************************************)
(*   							*)
(*   Subject Reduction + NF 				*)
(*	<<e,A>> -> <<e',A'>>  --->			*)
(*         Valid(A)           --->			*)
(*	   Domt(A)|- e:t      --->			*)
(*         Valid(A') /\  Domt(A')|- e':t /\ (NF e') 	*)
(*   							*)
(********************************************************)

Goal
forall c c' : config,
OSred c c' ->
valid_env (cfgenv c) ->
forall t : ty,
TC (OS_Dom_ty (cfgenv c)) (cfgexp c) t ->
valid_env (cfgenv c') /\
TC (OS_Dom_ty (cfgenv c')) (cfgexp c') t /\ NF (cfgexp c'). 

simple induction 1; simpl in |- *; intros.
(* CO CT CF CL *)
split. assumption.  split. assumption.  apply NF_Sno; apply Sno_o.
split. assumption.  split. assumption.  apply NF_ttt.
split. assumption.  split. assumption.  apply NF_fff.
split. assumption.  split. assumption.  apply NF_F; apply F_abs.
(* PO *)
specialize inv_TC_prd with (1 := H3); simple induction 1; intros Q T.
apply H1. assumption.
rewrite Q; assumption.
(* P *)
specialize inv_TC_prd with (1 := H3); simple induction 1; intros Q T.
elim H1 with t. intro V; simple induction 1; intros Ts Nf.
split. assumption.
split.
specialize inv_TC_succ with (1 := Ts); simple induction 1; intros.
rewrite Q; assumption.
apply NF_Sno; apply inv_Sno_s; apply inv_NF_Sno; assumption.
assumption.
rewrite Q; assumption.
(* ZT *)
specialize inv_TC_is_o with (1 := H3); simple induction 1; intros Q T.
elim H1 with nat_ty. intro V; simple induction 1; intros Tc Nf.
split. assumption.
split. rewrite Q; apply TC_ttt.
apply NF_ttt.
assumption.
assumption.
(* ZF *)
specialize inv_TC_is_o with (1 := H3); simple induction 1; intros Q T.
elim H1 with nat_ty. intro V; simple induction 1; intros Tc Nf.
split. assumption.
split. rewrite Q; apply TC_fff.
apply NF_fff.
assumption.
assumption.
(* S *)
specialize inv_TC_succ with (1 := H3); simple induction 1; intros Q T.
elim H1 with nat_ty. intro V; simple induction 1; intros Te1 Nf.
split. assumption.
split. rewrite Q; apply TC_succ; assumption.
apply NF_Sno; apply Sno_s; apply NFenat_Snoe with (OS_Dom_ty A'); assumption.
assumption.
assumption.
(* Var1 *)
specialize inv_TC_var with (1 := H4); simpl in |- *; intro M.
specialize  If_T with (1 := M); intro T.
cut (x = x). intro R; specialize T with (1 := R); rename T into Q.
unfold OScons in H3.
specialize inv_valid_cons with (1 := H3); simple induction 1; intros V Te.
elim H2 with t. intro V'; simple induction 1; intros Ten NFen.
split. unfold OScons in |- *; apply valid_cons; assumption.
split. change (TC (nil ++ (x, t) :: OS_Dom_ty A') en t0) in |- *.
apply TEp_nfvExt with (OS_Dom_ty A').
elim Q; assumption.
red in |- *; intro F; apply H0.
elim (TEDomDomty_OSDom A).
apply TCHet_FVeinDomH with en t.
replace (OS_Dom_ty A) with (OS_Dom_ty A').  assumption.
symmetry  in |- *; apply (dom_pres (cfg e A) (cfg en A')).
assumption.
assumption.
reflexivity.
assumption.
assumption.
assumption.
reflexivity.
(* Var2 *)
specialize inv_TC_var with (1 := H5); simpl in |- *; intro M.
specialize If_F with (1 := M) (2 := H0); intro M1.
unfold OScons in H4.
specialize inv_valid_cons with (1 := H4); simple induction 1; intros V Te.
elim H3 with t0. intro V'; simple induction 1; intros Ten NFen.
specialize dom_pres with (1 := H2); simpl in |- *; intro QA.
split. unfold OScons in |- *; apply valid_cons.
elim QA; assumption.
assumption.
split. change (TC (nil ++ (x, t) :: OS_Dom_ty A') en t0) in |- *.
apply TEp_nfvExt with (OS_Dom_ty A').
assumption.
red in |- *; intro F.
apply H1.
elim (TEDomDomty_OSDom A).
apply TCHet_FVeinDomH with en t0.
rewrite QA; assumption.
assumption.
reflexivity.
assumption.
assumption.
apply TC_var; assumption.
(* Appl *)
specialize inv_TC_appl with (1 := H6); simple induction 1; simple induction 1;
 intros T1 T2.
specialize dom_pres with (1 := H0); simpl in |- *; intro Q1.
specialize dom_pres with (1 := H3); simpl in |- *; intro Q2.
specialize 
 TEp_Ap
   with (a := e2) (e := en) (ne := en') (A := A) (n := n) (t := t) (1 := H2).
intro Ap.
elim H1 with (arr x t0). intro V'; simple induction 1; intros Ten NFen.
elim Ap with (OS_Dom_ty A') x t0. intros Ten' XT.
apply H4.
assumption.
apply TC_clos.
elim XT; elim Q1; assumption.
assumption.
specialize
 ApNewVar
  with (a := e2) (fun_ := en) (b := en') (A := A) (n := n) (t := t) (1 := H2);
 intros M x0 F.
elim (TEDomDomty_OSDom A).
apply TCHet_FVeinDomH with en (arr x t0).
rewrite Q1; assumption.
assumption.
assumption.
assumption.
assumption.
(* IfTrue *)
specialize inv_TC_cond with (1 := H5).
simple induction 1; intro T1; simple induction 1; intros T2 T3.
elim H1 with bool_ty. intro V'; simple induction 1; intros Tt NFt.
apply H3.  assumption.
specialize dom_pres with (1 := H0); simpl in |- *; intro Q1.
elim Q1; assumption.
assumption.
assumption.
(* IfFalse *)
specialize inv_TC_cond with (1 := H5).
simple induction 1; intro T1; simple induction 1; intros T2 T3.
elim H1 with bool_ty. intro V'; simple induction 1; intros Tf NFf.
apply H3.  assumption.
specialize dom_pres with (1 := H0); simpl in |- *; intro Q1.
elim Q1; assumption.
assumption.
assumption.
(* fix *)
specialize inv_TC_fix with (1 := H5).
simple induction 1; intros Q Te.
apply H3.  assumption.
apply TC_clos.
pattern t at 2 in |- *; rewrite Q; assumption.
apply TEp_RenExp with x e.  assumption.
specialize (Xmidvar nx x); simple induction 1; intro N.
left; assumption.
right; red in |- *; intro F; apply H0.
elim (TEDomDomty_OSDom A).
specialize TCHet_FVeinDomH with (1 := Te) (2 := F).
simpl in |- *; simple induction 1; intro R.
absurd (nx = x); assumption || symmetry  in |- *; assumption.
assumption.
assumption.
(* CL *)
specialize inv_TC_clos with (1 := H5); simple induction 1; intros T1 Te.
elim H1 with t0. intro VxA'; simple induction 1; intros Ten Fen.
unfold OScons in VxA'; specialize inv_valid_cons with (1 := VxA').
simple induction 1; intros V' T'.
split.  assumption.
split. apply TC_clos.
assumption.
assumption.
apply NF_F; apply F_clos; apply NFe_Fe with ((x, t) :: OS_Dom_ty A) s;
 assumption.
unfold OScons in |- *; apply valid_cons.
assumption.
assumption.
assumption.
(* CL' *)
specialize inv_TC_clos with (1 := H5); simple induction 1; intros T1 Te.
elim H1 with t0. intro VxA'; simple induction 1; intros Ten NFen.
unfold OScons in VxA'; specialize inv_valid_cons with (1 := VxA').
simple induction 1; intros V' T'.
split.  assumption.
split.  change (TC (nil ++ OS_Dom_ty A') en t0) in |- *.
apply TEp_inv_nfvExt with (nil ++ (x, t) :: OS_Dom_ty A') x t.
simpl in |- *; assumption.
reflexivity.
elim H3; intro Q.
apply Snoe_notFVe.
apply NFenat_Snoe with ((x, t) :: OS_Dom_ty A).
assumption.
elim Q; assumption.
specialize 
 NFebool_TF with (e := en) (1 := NFen) (H := (x, t) :: OS_Dom_ty A).
simple induction 1.
intro T; rewrite T; apply inv_FV_ttt.
intro F; rewrite F; apply inv_FV_fff.
elim Q; assumption.
assumption.
unfold OScons in |- *; apply valid_cons; assumption.
assumption.
Save subjr_NF.


(****************************************)
(*   					*)
(*   Subject Reduction  		*)
(*	<<e,A>> -> <<e',A'>>  --->	*)
(*         Valid(A)           --->	*)
(*	   Domt(A)|- e:t      --->	*)
(*         Domt(A')|- e':t 		*)
(*   					*)
(****************************************)

Goal
forall (e e' : tm) (A A' : OS_env),
OSred (cfg e A) (cfg e' A') ->
valid_env A -> forall t : ty, TC (OS_Dom_ty A) e t -> TC (OS_Dom_ty A') e' t.

intros.
specialize (subjr_NF (cfg e A) (cfg e' A')) with (1 := H) (2 := H0) (3 := H1).
simpl in |- *; simple induction 1; intro; simple induction 1; intros;
 assumption.
Save subjr_red.


(****************************************)
(*   					*)
(*   Normal Forms			*)
(*	<<e,A>> -> <<e',A'>>  --->	*)
(*         Valid<<e,A>>       --->	*)
(*         e in NF			*)
(*   					*)
(****************************************)

Goal
forall (e e' : tm) (A A' : OS_env),
OSred (cfg e A) (cfg e' A') -> valid_config (cfg e A) -> NF e'. 

intros e e' A A' R VC.
elim VC; simpl in |- *; intros V t T.
specialize (subjr_NF (cfg e A) (cfg e' A')) with (1 := R) (2 := V) (3 := T).
simpl in |- *; simple induction 1; intro; simple induction 1; intros;
 assumption.
Save NormalForms.
