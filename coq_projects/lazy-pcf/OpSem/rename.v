(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  rename.v                                                                *)
(*                                                                          *)
(*  This file contains the definition of renaming a                         *)
(*  variable in an expression, along with a related                         *)
(*  property.                                                               *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November  1993                                                          *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                 rename.v                                 *)
(****************************************************************************)

Require Import syntax.
Require Import freevars.


(********************************************************)
(* 							*)
(*  rename                                              *)
(* 							*)
(*  Inductively defines a relation between terms where  *)
(*  one variable is renamed by another. 		*)
(*							*)
(*   (rename nv v e1 e2)  <-->  e2 = e1[nv/v]		*)
(*							*)
(*							*)
(********************************************************)


Inductive rename : vari -> vari -> tm -> tm -> Prop :=
  | ren_o : forall nv v : vari, rename nv v o o
  | ren_ttt : forall nv v : vari, rename nv v ttt ttt
  | ren_fff : forall nv v : vari, rename nv v fff fff
  | ren_abs1 :
      forall (nv v : vari) (t : ty) (e : tm),
      rename nv v (abs v t e) (abs v t e)
  | ren_abs2 :
      forall (nv v x nx : vari) (t : ty) (e1 e2 e3 : tm),
      nv = x ->
      ~ FV nx e1 ->
      nx <> v ->
      nx <> nv ->
      rename nx x e1 e2 ->
      rename nv v e2 e3 -> rename nv v (abs x t e1) (abs nx t e3)
  | ren_abs3 :
      forall (nv v x : vari) (t : ty) (e ne : tm),
      v <> x ->
      nv <> x -> rename nv v e ne -> rename nv v (abs x t e) (abs x t ne)
  | ren_appl :
      forall (nv v : vari) (e1 e2 ne1 ne2 : tm),
      rename nv v e1 ne1 ->
      rename nv v e2 ne2 -> rename nv v (appl e1 e2) (appl ne1 ne2)
  | ren_cond :
      forall (nv v : vari) (e1 ne1 e2 ne2 e3 ne3 : tm),
      rename nv v e1 ne1 ->
      rename nv v e2 ne2 ->
      rename nv v e3 ne3 -> rename nv v (cond e1 e2 e3) (cond ne1 ne2 ne3)
  | ren_var_eq : forall nv v : vari, rename nv v (var v) (var nv)
  | ren_var_not_eq :
      forall nv v x : vari, v <> x -> rename nv v (var x) (var x)
  | ren_succ :
      forall (nv v : vari) (e ne : tm),
      rename nv v e ne -> rename nv v (succ e) (succ ne)
  | ren_prd :
      forall (nv v : vari) (e ne : tm),
      rename nv v e ne -> rename nv v (prd e) (prd ne)
  | ren_is_o :
      forall (nv v : vari) (e ne : tm),
      rename nv v e ne -> rename nv v (is_o e) (is_o ne)
  | ren_fix1 :
      forall (nv v : vari) (t : ty) (e : tm),
      rename nv v (Fix v t e) (Fix v t e)
  | ren_fix2 :
      forall (nv v x nx : vari) (t : ty) (e1 e2 e3 : tm),
      nv = x ->
      ~ FV nx e1 ->
      nx <> v ->
      nx <> nv ->
      rename nx x e1 e2 ->
      rename nv v e2 e3 -> rename nv v (Fix x t e1) (Fix nx t e3)
  | ren_fix3 :
      forall (nv v x : vari) (t : ty) (e ne : tm),
      v <> x ->
      nv <> x -> rename nv v e ne -> rename nv v (Fix x t e) (Fix x t ne)
  | ren_clos1 :
      forall (nv v : vari) (t : ty) (e a na : tm),
      rename nv v a na -> rename nv v (clos e v t a) (clos e v t na)
  | ren_clos2 :
      forall (nv v x nx : vari) (t : ty) (e e' ne a na : tm),
      nv = x ->
      ~ FV nx e ->
      nx <> v ->
      nx <> nv ->
      rename nx x e e' ->
      rename nv v e' ne ->
      rename nv v a na -> rename nv v (clos e x t a) (clos ne nx t na)
  | ren_clos3 :
      forall (nv v x : vari) (t : ty) (e ne a na : tm),
      v <> x ->
      nv <> x ->
      rename nv v e ne ->
      rename nv v a na -> rename nv v (clos e x t a) (clos ne x t na).


(************************)
(*  RenNotFree		*)
(*    [nx/x]e=ne --->	*) 
(*    ~nx=x	--->	*)
(*    x not in FV(ne)	*)
(************************)

Goal
forall (nx x : vari) (e ne : tm), rename nx x e ne -> nx <> x -> ~ FV x ne.

   simple induction 1; simpl in |- *; intros.
   apply inv_FV_o.
   apply inv_FV_ttt.
   apply inv_FV_fff.
   red in |- *; intro F; specialize inv_FV_abs with (1 := F);
    simple induction 1; intros Fe N.
   apply N; reflexivity.
   red in |- *; intro F; specialize inv_FV_abs with (1 := F).
   simple induction 1; intros Fe3 N.
   red in H7; apply H7; assumption.
   red in |- *; intro F; specialize inv_FV_abs with (1 := F).
   simple induction 1; intros Fe N.
   red in H3; apply H3; assumption.
   red in |- *; intro F; specialize inv_FV_appl with (1 := F);
    simple induction 1.
   apply H1; assumption.
   apply H3; assumption.
   red in |- *; intro F; specialize inv_FV_cond with (1 := F);
    simple induction 1. apply H1; assumption.
   simple induction 1.
   apply H3; assumption.
   apply H5; assumption.
   red in |- *; intro F; specialize inv_FV_var with (1 := F).
   intro; apply H0; symmetry  in |- *; assumption.
   red in |- *; intro F; specialize inv_FV_var with (1 := F).  assumption.
   red in |- *; intro F; specialize inv_FV_succ with (1 := F).
   apply H1; assumption.
   red in |- *; intro F; specialize inv_FV_prd with (1 := F); apply H1;
    assumption.
   red in |- *; intro F; specialize inv_FV_is_o with (1 := F); apply H1;
    assumption.
   red in |- *; intro F; specialize inv_FV_fix with (1 := F);
    simple induction 1; intros Fe N.
   apply N; reflexivity.
   red in |- *; intro F; specialize inv_FV_fix with (1 := F).
   simple induction 1; intros Fe3 N.
   red in H7; apply H7; assumption.
   red in |- *; intro F; specialize inv_FV_fix with (1 := F).
   simple induction 1; intros Fe N.
   red in H3; apply H3; assumption.
   red in |- *; intro F; specialize inv_FV_clos with (1 := F).
   simple induction 1. apply H1; assumption.
   simple induction 1; intros Fe N.
   apply N; reflexivity.
   red in |- *; intro F; specialize inv_FV_clos with (1 := F).
   simple induction 1.  apply H9; assumption.
   simple induction 1; intros Fe3 N.
   red in H7; apply H7; assumption.
   red in |- *; intro F; specialize inv_FV_clos with (1 := F).
   simple induction 1.  apply H5; assumption.
   simple induction 1; intros Fe N.
   red in H3; apply H3; assumption.
Save RenNotFree.
   