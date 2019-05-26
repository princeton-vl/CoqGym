(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  TypeThms.v                                                              *)
(*                                                                          *)
(*  This file contains theorems which state some                            *)
(*  conditions under which types are preserved.                             *)
(*  These theorems directly depend on the mapsto                            *)
(*  preservation theorems (mapsto.v).                                       *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November 1993                                                           *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                TypeThms.v                                *)
(****************************************************************************)

Require Import List.
Require Import syntax.
Require Import environments.
Require Import freevars.
Require Import utils.

Require Import typecheck.

Require Import mapsto.


(********************************)
(* TEp_eqExt			*)
(* (HeqExt)  	                *)
(*   v=x --->			*)
(*   H1 |- e:t --->		*)
(*   H1 = HF[v:r]HM+H  --->    	*)
(*   HF[v:r]HM[x:s]H |- e:t 	*)
(********************************)

Goal
forall (v x : vari) (r s t : ty) (H H1 : ty_env) (e : tm),
v = x ->
TC H1 e t ->
forall HF HM : ty_env,
H1 = HF ++ (v, r) :: HM ++ H -> TC (HF ++ (v, r) :: HM ++ (x, s) :: H) e t. 

   simple induction 2; simpl in |- *; intros.
   apply TC_o.
   apply TC_ttt.
   apply TC_fff.
   apply TC_succ.
   apply H5; assumption.
   apply TC_prd.
   apply H5; assumption.
   apply TC_is_o.
   apply H5; assumption.
   apply TC_var.
   elim H0; apply Mp_eqExt.
   elim H5; assumption.
   apply TC_appl with s0.
   apply H5; assumption.
   apply H7; assumption.
   apply TC_abs.
   change (TC (((v0, s0) :: HF) ++ (v, r) :: HM ++ (x, s) :: H) e0 t0)
    in |- *.
   apply H5; rewrite H6; simpl in |- *; reflexivity.
   apply TC_cond.
   apply H5; assumption.
   apply H7; assumption.
   apply H9; assumption.
   apply TC_fix.
   change (TC (((v0, t0) :: HF) ++ (v, r) :: HM ++ (x, s) :: H) e0 t0)
    in |- *.
   apply H5; rewrite H6; simpl in |- *; reflexivity.
   apply TC_clos.
   apply H5; assumption.
   change (TC (((v0, s0) :: HF) ++ (v, r) :: HM ++ (x, s) :: H) e0 t0)
    in |- *.
   apply H7; rewrite H8; simpl in |- *; reflexivity.
Save TEp_eqExt.



(********************************)
(* TEp_inv_eqExt		*)
(* (HeqinvExt) 			*)
(*   v=x --->			*)
(*   H1 |- e:t --->		*)
(*   H1 = HF[v:r]HM[x:s]H --->	*)
(*   HF[v:r]HM*H |- e:t		*)
(********************************)

Goal
forall (v x : vari) (r s t : ty) (H H1 : ty_env) (e : tm),
v = x ->
TC H1 e t ->
forall HF HM : ty_env,
H1 = HF ++ (v, r) :: HM ++ (x, s) :: H -> TC (HF ++ (v, r) :: HM ++ H) e t.

   simple induction 2; intros.
   apply TC_o.
   apply TC_ttt.
   apply TC_fff.
   apply TC_succ; apply H5; assumption.
   apply TC_prd; apply H5; assumption.
   apply TC_is_o; apply H5; assumption.
   apply TC_var.
   apply Mp_inv_eqExt with x s; assumption || elim H5; assumption.
   apply TC_appl with s0.
   apply H5; assumption.
   apply H7; assumption.
   apply TC_abs.
   change (TC (((v0, s0) :: HF) ++ (v, r) :: HM ++ H) e0 t0) in |- *.
   apply H5.
   simpl in |- *; elim H6; reflexivity.
   apply TC_cond.
   apply H5; assumption.
   apply H7; assumption.
   apply H9; assumption.
   apply TC_fix.
   change (TC (((v0, t0) :: HF) ++ (v, r) :: HM ++ H) e0 t0) in |- *.
   apply H5.
   simpl in |- *; elim H6; reflexivity.
   apply TC_clos.
   apply H5; assumption.
   change (TC (((v0, s0) :: HF) ++ (v, r) :: HM ++ H) e0 t0) in |- *.
   apply H7.
   simpl in |- *; elim H8; reflexivity.
Save TEp_inv_eqExt.
   
   

(********************************)
(*   TEp_nfvExt			*)
(*   (TyExt)			*)
(*  	H1*H2|-e:t  --->	*)
(*      x not in FV(e) --->	*)
(*	H1[x:s]H2|-e:t		*)
(********************************)

Goal
forall (H : ty_env) (e : tm) (t : ty) (x : vari) (s : ty),
TC H e t ->
~ FV x e ->
forall H1 H2 : ty_env, H = H1 ++ H2 -> TC (H1 ++ (x, s) :: H2) e t.

simple induction 1; simpl in |- *; intros.
apply TC_o.
apply TC_ttt.
apply TC_fff.
apply TC_succ.
apply H3; assumption || apply notFV_succ; assumption.
apply TC_prd.
apply H3; assumption || apply notFV_prd; assumption.
apply TC_is_o.
apply H3; assumption || apply notFV_is_o; assumption.
apply TC_var.
simpl in |- *; specialize notFV_var with (1 := H3); intro NQ.
apply Mp_nfvExt.
red in |- *; intro; apply NQ; symmetry  in |- *; assumption.
elim H6; assumption.
apply TC_appl with s0.
apply H3; assumption || specialize notFV_appl with (1 := H6);
 simple induction 1; intros; assumption.
apply H5; assumption || specialize notFV_appl with (1 := H6);
 simple induction 1; intros; assumption.
apply TC_abs.
specialize (Xmidvar x v); simple induction 1.
intro xv; rewrite xv.
change (TC (nil ++ (v, s0) :: H5 ++ (v, s) :: H6) e0 t0) in |- *.
apply TEp_eqExt with (nil ++ (v, s0) :: H5 ++ H6). 
reflexivity.
simpl in |- *; elim H7; assumption.
reflexivity.
intro nxv. 
change (TC (((v, s0) :: H5) ++ (x, s) :: H6) e0 t0) in |- *.
apply H3.
specialize notFV_abs with (1 := H4).
simple induction 1; intro P.
absurd (x = v); assumption.
assumption.
rewrite H7; simpl in |- *; reflexivity.
apply TC_cond.
apply H3; assumption || red in |- *; intro; apply H8; apply FV_cond1;
 assumption.
apply H5; assumption || red in |- *; intro; apply H8; apply FV_cond2;
 assumption.
apply H7; assumption || red in |- *; intro; apply H8; apply FV_cond3;
 assumption.
apply TC_fix.
specialize (Xmidvar x v); simple induction 1.
intro xv; rewrite xv.
change (TC (nil ++ (v, t0) :: H5 ++ (v, s) :: H6) e0 t0) in |- *.
apply TEp_eqExt with (nil ++ (v, t0) :: H5 ++ H6). 
reflexivity.
simpl in |- *; elim H7; assumption.
reflexivity.
intro nxv. 
change (TC (((v, t0) :: H5) ++ (x, s) :: H6) e0 t0) in |- *.
apply H3.
specialize notFV_fix with (1 := H4).
simple induction 1; intro P.
absurd (x = v); assumption.
assumption.
rewrite H7; simpl in |- *; reflexivity.

apply TC_clos.
apply H3; assumption || red in |- *; intro; apply H6; apply FV_closa;
 assumption.
specialize (Xmidvar x v); simple induction 1.
intro xv; rewrite xv.
change (TC (nil ++ (v, s0) :: H7 ++ (v, s) :: H8) e0 t0) in |- *.
apply TEp_eqExt with (nil ++ (v, s0) :: H7 ++ H8). 
reflexivity.
simpl in |- *; elim H9; assumption.
reflexivity.
intro nxv. 
change (TC (((v, s0) :: H7) ++ (x, s) :: H8) e0 t0) in |- *.
apply H5.
specialize notFV_clos with (1 := H6).
simple induction 1; intro; simple induction 1; intro P.
absurd (x = v); assumption.
assumption.
rewrite H9; simpl in |- *; reflexivity.
Save TEp_nfvExt.



   (*****************************)
   (* TEp_inv_nfvExt		*)
   (* (Gen_inv_TyExt) 		*)
   (*   H1 |- e:t --->		*)
   (*   H1 = HF[x:s]H --->	*)
   (*   x not in FV(e) --->	*)
   (*   HF*H |- e:t		*)
   (*****************************)

   Goal
forall (H1 H : ty_env) (e : tm) (t : ty) (x : vari) (s : ty),
TC H1 e t ->
forall HF : ty_env, H1 = HF ++ (x, s) :: H -> ~ FV x e -> TC (HF ++ H) e t.

   simple induction 1; intros.
   apply TC_o.
   apply TC_ttt.
   apply TC_fff.
   apply TC_succ; apply H4; assumption || red in |- *; intro; apply H6;
    apply FV_succ; assumption.
   apply TC_prd; apply H4; assumption || red in |- *; intro; apply H6;
    apply FV_prd; assumption.
   apply TC_is_o; apply H4; assumption || red in |- *; intro; apply H6;
    apply FV_is_o; assumption.
   apply TC_var.
   apply Mp_inv_nfvExt with x s.
   red in |- *; intro; apply H5; apply FV_var; symmetry  in |- *; assumption.
   elim H4; assumption.
   apply TC_appl with s0.
   apply H4; assumption || red in |- *; intro; apply H8; apply FV_appl1;
    assumption.
   apply H6; assumption || red in |- *; intro; apply H8; apply FV_appl2;
    assumption.
   apply TC_abs.
   change (TC (((v, s0) :: HF) ++ H) e0 t0) in |- *.
   specialize (Xmidvar v x); simple induction 1; intros.
   simpl in |- *; change (TC (nil ++ (v, s0) :: HF ++ H) e0 t0) in |- *.
   apply TEp_inv_eqExt with x s (nil ++ (v, s0) :: HF ++ (x, s) :: H).
   assumption.
   elim H5; assumption.
   reflexivity.
   apply H4.  
   simpl in |- *; elim H5; reflexivity.
   red in |- *; intro; apply H6; apply FV_abs; assumption || red in |- *;
    intro; apply H8; symmetry  in |- *; assumption.
   apply TC_cond.
   apply H4; assumption || red in |- *; intro; apply H10; apply FV_cond1;
    assumption.
   apply H6; assumption || red in |- *; intro; apply H10; apply FV_cond2;
    assumption.
   apply H8; assumption || red in |- *; intro; apply H10; apply FV_cond3;
    assumption.
   apply TC_fix.
   specialize (Xmidvar v x); simple induction 1; intros.
   change (TC (nil ++ (v, t0) :: HF ++ H) e0 t0) in |- *.
   apply TEp_inv_eqExt with x s (nil ++ (v, t0) :: HF ++ (x, s) :: H).
   assumption.
   elim H5; assumption.
   reflexivity.
   change (TC (((v, t0) :: HF) ++ H) e0 t0) in |- *.
   apply H4.  
   simpl in |- *; elim H5; reflexivity.
   red in |- *; intro; apply H6; apply FV_fix; assumption || red in |- *;
    intro; apply H8; symmetry  in |- *; assumption.
   apply TC_clos.
   apply H4; assumption || red in |- *; intro; apply H8; apply FV_closa;
    assumption. 
   specialize (Xmidvar x v); simple induction 1; intros.
   change (TC (nil ++ (v, s0) :: HF ++ H) e0 t0) in |- *.
   apply TEp_inv_eqExt with x s (nil ++ (v, s0) :: HF ++ (x, s) :: H).
   symmetry  in |- *; assumption.
   elim H7; assumption.
   reflexivity.
   change (TC (((v, s0) :: HF) ++ H) e0 t0) in |- *.
   apply H6.
   simpl in |- *; elim H7; reflexivity.
   red in |- *; intro; apply H8; apply FV_closb; assumption.
Save TEp_inv_nfvExt.
   

(********************************)
(* TEp_swap			*)
(* (GenHswap)			*)
(*    ~v=x --->       		*)
(*    H1|-e:r --->	    	*)
(*    H1=HF[x:s,v:t]HB --->	*)
(*    HF[v:t,x:s]HB|-e:r 	*)
(********************************)

Goal
forall v x : vari,
v <> x ->
forall (r s t : ty) (e : tm) (H1 HB : ty_env),
TC H1 e r ->
forall HF : ty_env,
H1 = HF ++ (x, s) :: (v, t) :: HB -> TC (HF ++ (v, t) :: (x, s) :: HB) e r.

   simple induction 2; simpl in |- *; intros.
   apply TC_o.
   apply TC_ttt.
   apply TC_fff.
   apply TC_succ; apply (H4 HF); assumption.
   apply TC_prd; apply (H4 HF); assumption.
   apply TC_is_o; apply (H4 HF); assumption.
   apply TC_var; apply Mp_swap.
   red in |- *; intro; apply H; symmetry  in |- *; assumption.
   elim H4; assumption.
   apply TC_appl with s0.
   apply (H4 HF); assumption.
   apply H6; assumption.
   apply TC_abs.
   change (TC (((v0, s0) :: HF) ++ (v, t) :: (x, s) :: HB) e0 t0) in |- *.
   apply (H4 ((v0, s0) :: HF)); simpl in |- *.
   elim H5; reflexivity.
   apply TC_cond.
   apply (H4 HF); assumption.
   apply (H6 HF); assumption.
   apply (H8 HF); assumption.
   apply TC_fix.
   change (TC (((v0, t0) :: HF) ++ (v, t) :: (x, s) :: HB) e0 t0) in |- *.
   apply (H4 ((v0, t0) :: HF)); simpl in |- *.
   elim H5; reflexivity.
   apply TC_clos.
   apply (H4 HF); assumption.
   change (TC (((v0, s0) :: HF) ++ (v, t) :: (x, s) :: HB) e0 t0) in |- *.
   apply (H6 ((v0, s0) :: HF)); simpl in |- *.
   elim H7; reflexivity.
Save TEp_swap.