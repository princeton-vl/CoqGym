(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  mapsto.v                                                                *)
(*                                                                          *)
(*  This file contains theorems which describe how                          *)
(*  a type environment may be altered without changing                      *)
(*  the mapsto function.                                                    *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November 1993                                                           *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                 mapsto.v                                 *)
(****************************************************************************)

Require Import List.
Require Import syntax.
Require Import environments.

Require Import utils.


(************************)
(* Mp_nfvExt 		*)
(*   ~v=x --->		*)
(*   HF*H(v) = t  --->	*)
(*   HF[x:s]H(v) = t 	*)
(************************)

Goal
forall (v x : vari) (t s : ty) (HF H : ty_env),
v <> x -> mapsto v t (HF ++ H) -> mapsto v t (HF ++ (x, s) :: H). 

   simple induction HF; simpl in |- *.
   intros H neq M.
   apply F_If.
   red in |- *; intro; apply neq; symmetry  in |- *; assumption.
   assumption.
   simple induction a; simpl in |- *; intros a0 b y IH H0 neq If.
   specialize (Xmidvar a0 v); simple induction 1. intro T.
   specialize If_T with (1 := If) (2 := T); intro B.
   apply T_If; assumption.
   intro F.
   specialize If_F with (1 := If) (2 := F); intro M.
   apply F_If. assumption.
   apply IH; assumption.
Save Mp_nfvExt.


(********************************)
(* Mp_inv_nfvExt 		*)
(*   ~v=x --->			*)
(*   HF[x:s]H(v) = t --->	*)
(*   HF*H(v) = t		*)
(********************************)

Goal
forall (v x : vari) (t s : ty) (HF H : ty_env),
v <> x -> mapsto v t (HF ++ (x, s) :: H) -> mapsto v t (HF ++ H).

   simple induction HF; simpl in |- *.
   intros H neq If.
   apply If_F with (x = v) (s = t).
   assumption.
   red in |- *; intro; apply neq; symmetry  in |- *; assumption.
   simple induction a; simpl in |- *; intros a0 b y IH H0 neq If.
   specialize (Xmidvar a0 v); simple induction 1. intro T.
   specialize If_T with (1 := If) (2 := T); intro B.
   apply T_If; assumption.
   intro F.
   specialize If_F with (1 := If) (2 := F); intro M.
   apply F_If. assumption.
   apply IH; assumption.
Save Mp_inv_nfvExt.



(********************************)
(* Mp_eqExt			*)
(*    H[v:s]HM+H'(x)=t --->  	*)
(*    H[v:s]HM[v:r]H'(x)=t   	*)
(********************************)

Goal
forall (x v : vari) (r s t : ty) (H HM H' : ty_env),
mapsto x t (H ++ (v, s) :: HM ++ H') ->
mapsto x t (H ++ (v, s) :: HM ++ (v, r) :: H').

   simple induction H; simpl in |- *.
   simple induction HM; simpl in |- *.  intros.
   apply IfA_IfAIfA.  assumption.
   simple induction a; simpl in |- *; intros.
   specialize (Xmidvar v x); simple induction 1.
   intro T.
   specialize If_T with (1 := H1) (2 := T); intro.
   apply T_If; assumption.
   intro F.
   specialize If_F with (1 := H1) (2 := F); intro I.
   apply F_If.
   assumption. 
   specialize (Xmidvar a0 x); simple induction 1.
   intro Q. 
   specialize If_T with (1 := I) (2 := Q); intro.
   apply T_If; assumption.
   intro nQ.
   specialize If_F with (1 := I) (2 := nQ); intro.
   apply F_If.  assumption.
   apply If_F with (v = x) (s = t).
   apply H0.
   specialize If_F with (1 := H1) (2 := F); intro I2.
   specialize If_F with (1 := I2) (2 := nQ); intro.
   apply F_If; assumption.
   assumption. 
   simple induction a; simpl in |- *; intros.
   specialize (Xmidvar a0 x); simple induction 1.
   intro T.
   specialize If_T with (1 := H1) (2 := T); intro.
   apply T_If; assumption.
   intro F.
   specialize If_F with (1 := H1) (2 := F); intro.
   apply F_If.  assumption.
   apply H0; assumption.
Save Mp_eqExt.


(********************************)
(* Mp_inv_eqExt 		*)
(*   v=x --->			*)
(*   HF[v:s]HM[x:t]H(y) = r -->	*)
(*   HF[v:s]HM*H(y) = r		*)
(********************************)

Goal
forall (v x y : vari) (r s t : ty) (HF HM H : ty_env),
v = x ->
mapsto y r (HF ++ (v, s) :: HM ++ (x, t) :: H) ->
mapsto y r (HF ++ (v, s) :: HM ++ H).

   simple induction HF; simpl in |- *. intros HM H Q A.
   specialize (Xmidvar v y); simple induction 1. intro T.
   specialize If_T with (1 := A) (2 := T); intro sr.
   apply T_If; assumption.
   intro F.
   specialize If_F with (1 := A) (2 := F); intro M.
   apply F_If. assumption.
   apply Mp_inv_nfvExt with x t. 
   elim Q; red in |- *; intro; apply F; symmetry  in |- *; assumption.
   assumption.
   simple induction a; simpl in |- *; intros a0 b y0 IH HM H0 Q If.
   specialize (Xmidvar a0 y); simple induction 1. intro T.
   specialize If_T with (1 := If) (2 := T); intro br.
   apply T_If; assumption.
   intro F.
   specialize If_F with (1 := If) (2 := F); intro M.
   apply F_If. assumption.
   apply IH; assumption.
Save Mp_inv_eqExt.




(***************************)
(* Mp_swap		   *)
(*    ~x=y --->       	   *)
(*    H[x:s,y:t]H'(v)=r -->*)
(*    H[y:t,x:s]H'(v)=r    *)
(***************************)

Goal
forall (v x y : vari) (r s t : ty) (H H' : ty_env),
x <> y ->
mapsto v r (H ++ (x, s) :: (y, t) :: H') ->
mapsto v r (H ++ (y, t) :: (x, s) :: H').

	simple induction H.
	simpl in |- *; intros H' neq If.
        specialize (Xmidvar y v); simple induction 1.
        intro T.
        apply T_If. assumption.
        apply If_T with (y = v) (mapsto v r H').
        apply If_F with (x = v) (s = r).
        assumption.
        elim T; assumption.
        assumption.
        intro F.
        apply F_If. assumption.
        specialize (Xmidvar x v); simple induction 1.
        intro TT.
	specialize If_T with (1 := If) (2 := TT); intro sr.
        apply T_If; assumption.
        intro FF.
        specialize If_F with (1 := If) (2 := FF); intro If2.
        specialize If_F with (1 := If2) (2 := F); intro M.
        apply F_If; assumption.
	simple induction a.
	simpl in |- *; intros a0 b y0 IH H' N A.
        specialize (Xmidvar a0 v); simple induction 1.
        intro T.
        specialize If_T with (1 := A) (2 := T); intro br.
        apply T_If; assumption.
        intro F.
        specialize If_F with (1 := A) (2 := F); intro M.
        apply F_If; assumption || apply IH; assumption.
Save Mp_swap.
