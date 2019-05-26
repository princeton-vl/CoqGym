(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  ApTypes.v                                                               *)
(*                                                                          *)
(*  This file contains proofs that the Ap function and                      *)
(*  the renaming definition preserve types.  The proof                      *)
(*  that renaming preserves types is quite long and is                      *)
(*  broken down into certain subcases.  Also, the proof                     *)
(*  is first made for a more general case than necessary                    *)
(*  and then the corollary is proved.  The proof that Ap                    *)
(*  preserves types is simple once the theorem about                        *)
(*  renaming is complete.                                                   *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November 1993                                                           *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                ApTypes.v                                 *)
(****************************************************************************)

Require Import TypeThms.

Require Import List.
Require Import syntax.
Require Import environments.
Require Import utils.
Require Import freevars.
Require Import typecheck.
Require Import rename.
Require Import OSrules.


(****************************************)
(* TEp_RenExp                           *)
(*   This theorem states that renaming  *)
(*   preserves types.			*)
(*                                      *)
(* The proof proceeds as follows:       *)
(*   Special Cases                      *)
(*   General theorem                    *)
(*   TEp_RenExp (Corollary)             *)
(****************************************)



(****************************************)
(*  ren_case1                           *)
(*    Tool used in first case of abs,   *)
(*    fix, and clos.                    *)
(****************************************)

Goal
forall (nv v : vari) (HF H0 : ty_env) (e : tm) (t s r : ty),
nv = v \/
~ FV nv e /\ ~ member vari v (TE_Dom HF) /\ ~ member vari nv (TE_Dom HF) ->
TC ((v, t) :: HF ++ (v, s) :: H0) e r ->
TC ((v, t) :: HF ++ (nv, s) :: H0) e r. 
intros.
elim H; intro B.
rewrite B; assumption.
change (TC (((v, t) :: HF) ++ (nv, s) :: H0) e r) in |- *.
apply TEp_nfvExt with (((v, t) :: HF) ++ H0).
change (TC (nil ++ (v, t) :: HF ++ H0) e r) in |- *.
apply TEp_inv_eqExt with v s (nil ++ (v, t) :: HF ++ (v, s) :: H0).
reflexivity.
simpl in |- *; assumption.
reflexivity.
elim B; intros; assumption.
reflexivity.
Save ren_case1.


(****************************************)
(*  ren_case2                           *)
(*    Tool used in second case of abs,  *)
(*    fix, and clos.                    *)
(****************************************)

Goal
forall (nv v nx x : vari) (HF H0 : ty_env) (e1 e2 e3 : tm) (t s r : ty),
v <> nx ->
nx <> nv ->
~ FV nx e1 ->
~ FV nv e2 ->
nv = v \/
(nv = x \/ ~ FV nv e1) /\
~ member vari v (TE_Dom HF) /\ ~ member vari nv (TE_Dom HF) ->
(forall (HF H : ty_env) (s t : ty),
 nx = x \/
 ~ FV nx e1 /\ ~ member vari x (TE_Dom HF) /\ ~ member vari nx (TE_Dom HF) ->
 TC (HF ++ (x, s) :: H) e1 t -> TC (HF ++ (nx, s) :: H) e2 t) ->
(forall (HF H : ty_env) (s t : ty),
 nv = v \/
 ~ FV nv e2 /\ ~ member vari v (TE_Dom HF) /\ ~ member vari nv (TE_Dom HF) ->
 TC (HF ++ (v, s) :: H) e2 t -> TC (HF ++ (nv, s) :: H) e3 t) ->
TC ((x, t) :: HF ++ (v, s) :: H0) e1 r ->
TC ((nx, t) :: HF ++ (nv, s) :: H0) e3 r. 
intros.
change (TC (((nx, t) :: HF) ++ (nv, s) :: H0) e3 r) in |- *.
apply H6.
elim H4; intro A.
left; assumption.
right; split.
assumption.
elim A; intros F M.
elim M; intros Mv Mnv.
split; simpl in |- *; unfold IF_then_else in |- *; red in |- *;
 simple induction 1; intro N.
apply H; symmetry  in |- *; assumption.
apply Mv; assumption.
apply H1; assumption.
apply Mnv; assumption.
change (TC (nil ++ (nx, t) :: HF ++ (v, s) :: H0) e2 r) in |- *.
apply H5.
right; split; assumption || split; simpl in |- *; red in |- *; intro;
 assumption.
simpl in |- *; assumption.
Save ren_case2.



(****************************************)
(*  ren_var1                            *)
(*    Tool used in var_eq case          *)
(****************************************)

Goal
forall (nv v : vari) (H HF : ty_env) (s t : ty),
nv = v \/
nv <> v /\ ~ member vari v (TE_Dom HF) /\ ~ member vari nv (TE_Dom HF) ->
mapsto v t (HF ++ (v, s) :: H) -> mapsto nv t (HF ++ (nv, s) :: H).
simple induction 1; intro N.
intro; rewrite N; assumption.
generalize N; elim HF; simpl in |- *.
intros A If.
apply T_If.
reflexivity.
apply If_T with (v = v) (mapsto v t H).
assumption.
reflexivity.
simple induction a; simpl in |- *.
intros a0 b y IH A If.
elim A; intro nvv; simple induction 1; intros a0v a0nv.
apply F_If.
red in |- *; intro; apply a0nv; left; assumption.
apply IH.
split.  assumption.
split.
red in |- *; intro; apply a0v; right; assumption.
red in |- *; intro; apply a0nv; right; assumption.
apply If_F with (a0 = v) (b = t).
assumption.
red in |- *; intro; apply a0v; left; assumption.
Save ren_var1.


(****************************************)
(*  ren_var2                            *)
(*    Tool used in var_not_eq case      *)
(****************************************)

Goal
forall (nv v x : vari) (H HF : ty_env) (s t : ty),
v <> x ->
nv = v \/
nv <> x /\ ~ member vari v (TE_Dom HF) /\ ~ member vari nv (TE_Dom HF) ->
mapsto x t (HF ++ (v, s) :: H) -> mapsto x t (HF ++ (nv, s) :: H).
intros nv v x H HF s t nvx.
simple induction 1; intro A.
intro; rewrite A; assumption.
generalize A; elim HF; simpl in |- *.
intros B If.
apply F_If.
elim B; intros; assumption.
apply If_F with (v = x) (s = t); assumption.
simple induction a; simpl in |- *.
intros a0 b y IH B If.
specialize (Xmidvar a0 x); simple induction 1; intro ax.
apply T_If.
assumption.
apply If_T with (a0 = x) (mapsto x t (y ++ (v, s) :: H)); assumption.
apply F_If.  assumption.
apply IH.
elim B; intro nx; simple induction 1; intros a0v a0nv.
split. assumption.
split.
red in |- *; intro; apply a0v; right; assumption.
red in |- *; intro; apply a0nv; right; assumption.
apply If_F with (a0 = x) (b = t); assumption.
Save ren_var2.


(************************************************)
(* TEp_RenExpGen                            	*)
(*   [nx/x]e=ne --->                            *)
(*   nx=x \/                                    *)
(*   (nx not in FV(e) /\  x not in dom(HF)      *) 
(*                    /\ nx not in dom(HF)) --> *)
(*   HF[x:s]H  |- e:t  --->                     *)
(*   HF[nx:s]H |- ne:t                          *)
(************************************************)

Goal
forall (nx x : vari) (e ne : tm),
rename nx x e ne ->
forall (HF H : ty_env) (s t : ty),
nx = x \/
~ FV nx e /\ ~ member vari x (TE_Dom HF) /\ ~ member vari nx (TE_Dom HF) ->
TC (HF ++ (x, s) :: H) e t -> TC (HF ++ (nx, s) :: H) ne t.

simple induction 1; intros.
(* ren_o *)
specialize inv_TC_o with (1 := H2).
intro Q; rewrite Q; apply TC_o.
(* ren_ttt *)
specialize inv_TC_ttt with (1 := H2).
intro Q; rewrite Q; apply TC_ttt.
(* ren_fff *)
specialize inv_TC_fff with (1 := H2).
intro Q; rewrite Q; apply TC_fff.
(* ren_abs1 *)
specialize inv_TC_abs with (1 := H2).
simple induction 1; simple induction 1; intros Q T.
rewrite Q.
apply TC_abs.
apply ren_case1.
specialize  AABC_ABC with (B := ~ FV nv e0) (1 := H1).
intro AA; apply AA.
intro; apply notFV_abs with t; assumption.
assumption.
(* ren_abs2 *)
specialize inv_TC_abs with (1 := H10).
simple induction 1; simple induction 1; intros Q T.
rewrite Q.
apply TC_abs.
apply ren_case2 with v x0 e1 e2.
red in |- *; intro; apply H2; symmetry  in |- *; assumption.
assumption.
assumption.
rewrite H0; apply RenNotFree with nx0 e1; assumption || elim H0; assumption.
elim H9; intro S.
left; assumption.
right; elim S; intros F M; split.
apply notFV_abs with t; assumption.
assumption.
assumption.
assumption.
assumption.
(* ren_abs3 *)
specialize inv_TC_abs with (1 := H6).
simple induction 1; simple induction 1; intros Q T.
rewrite Q; apply TC_abs.
change (TC (((x0, t) :: HF) ++ (nv, s) :: H4) ne0 x1) in |- *.
apply H3.
elim H5; intro N.
left; assumption.
right; elim N; intros F M; split.
red in |- *; intro; apply F; apply FV_abs; assumption.
elim M; intros Mv Mnv.
split; simpl in |- *; red in |- *; simple induction 1; intro A.
apply H0; symmetry  in |- *; assumption.
apply Mv; assumption.
apply H1; symmetry  in |- *; assumption.
apply Mnv; assumption.
simpl in |- *; assumption.
(* ren_appl *)
specialize inv_TC_appl with (1 := H6).
simple induction 1; simple induction 1; intros T1 T2.
apply TC_appl with x0.
apply H1.
elim H5; intro N.
left; assumption.
right; elim N; intros F M; split.
red in |- *; intro; apply F; apply FV_appl1; assumption.
assumption.
assumption.
apply H3.
elim H5; intro N.
left; assumption.
right; elim N; intros F M; split.
red in |- *; intro; apply F; apply FV_appl2; assumption.
assumption.
assumption.
(* ren_cond *)
specialize inv_TC_cond with (1 := H8).
simple induction 1; intro T1.
simple induction 1; intros T2 T3.
apply TC_cond.
apply H1.
elim H7; intro N.
left; assumption.
right; elim N; intros F M; split.
red in |- *; intro; apply F; apply FV_cond1; assumption.
assumption.
assumption.
apply H3.
elim H7; intro N.
left; assumption.
right; elim N; intros F M; split.
red in |- *; intro; apply F; apply FV_cond2; assumption.
assumption.
assumption.
apply H5.
elim H7; intro N.
left; assumption.
right; elim N; intros F M; split.
red in |- *; intro; apply F; apply FV_cond3; assumption.
assumption.
assumption.
(* ren_var_eq *)
apply TC_var.
specialize inv_TC_var with (1 := H2).
intro; apply ren_var1 with v.
elim H1; intro.
left; assumption.
right; elim H4; intros; split.
apply notFV_var; assumption.
assumption.
assumption.
(* ren_var_not_eq *)
apply TC_var.
specialize inv_TC_var with (1 := H3).
intro; apply ren_var2 with v.
assumption.
elim H2; intro A.
left; assumption.
right; elim A; intros F M; split.
apply notFV_var; assumption.
assumption.
assumption.
(* ren_succ *)
specialize inv_TC_succ with (1 := H4).
simple induction 1; intros Q T; rewrite Q; apply TC_succ.
apply H1.
elim H3; intro A.
left; assumption.
right; elim A; intros F M.
split; assumption || red in |- *; intro; apply F; apply FV_succ; assumption.
assumption.
(* ren_prd *)
specialize inv_TC_prd with (1 := H4).
simple induction 1; intros Q T; rewrite Q; apply TC_prd.
apply H1.
elim H3; intro A.
left; assumption.
right; elim A; intros F M.
split; assumption || red in |- *; intro; apply F; apply FV_prd; assumption.
assumption.
(* ren_is_o *)
specialize inv_TC_is_o with (1 := H4).
simple induction 1; intros Q T; rewrite Q; apply TC_is_o.
apply H1. 
elim H3; intro A.
left; assumption.
right; elim A; intros F M.
split; assumption || red in |- *; intro; apply F; apply FV_is_o; assumption.
assumption.
(* ren_fix1 *)
specialize inv_TC_fix with (1 := H2).
simple induction 1; intros Q T.
elim Q.
apply TC_fix.
pattern t at 2 in |- *; rewrite Q.
apply ren_case1.
specialize  AABC_ABC with (1 := H1) (B := ~ FV nv e0).
intro AA; apply AA.
intro; apply notFV_fix with t; assumption.
assumption.
(* ren_fix2 *)
specialize inv_TC_fix with (1 := H10).
simple induction 1; intros Q T.
elim Q.
apply TC_fix.
pattern t at 2 in |- *; rewrite Q.
apply ren_case2 with v x0 e1 e2.
red in |- *; intro; apply H2; symmetry  in |- *; assumption.
assumption.
assumption.
rewrite H0; apply RenNotFree with nx0 e1; assumption || elim H0; assumption.
elim H9; intro S.
left; assumption.
right; elim S; intros F M; split.
apply notFV_fix with t; assumption.
assumption.
assumption.
assumption.
assumption.
(* ren_fix3 *)
specialize inv_TC_fix with (1 := H6).
simple induction 1; intros Q T.
elim Q; apply TC_fix.
pattern t at 2 in |- *; rewrite Q.
change (TC (((x0, t) :: HF) ++ (nv, s) :: H4) ne0 t0) in |- *.
apply H3.
elim H5; intro N.
left; assumption.
right; elim N; intros F M; split.
red in |- *; intro; apply F; apply FV_fix; assumption.
elim M; intros Mv Mnv.
split; simpl in |- *; red in |- *; simple induction 1; intro A.
apply H0; symmetry  in |- *; assumption.
apply Mv; assumption.
apply H1; symmetry  in |- *; assumption.
apply Mnv; assumption.
simpl in |- *; assumption.
(* ren_clos1 *)
specialize inv_TC_clos with (1 := H4).
simple induction 1; intros Ta Tb.
apply TC_clos.
apply H1.
elim H3; intro A.
left; assumption.
right; elim A; intros F M; split.
red in |- *; intro; apply F; apply FV_closa; assumption.
assumption.
assumption.
apply ren_case1.
specialize  AABC_ABC with (1 := H3) (B := ~ FV nv e0).
intro AA; apply AA.
intro F; specialize notFV_clos with (1 := F).
simple induction 1; intros; assumption.
assumption.
(* ren_clos2 *)
specialize inv_TC_clos with (1 := H12).
simple induction 1; intros Ta Tb.
apply TC_clos.
apply H9.
elim H11; intro A.
left; assumption.
right; elim A; intros F M; split.
red in |- *; intro; apply F; apply FV_closa; assumption.
assumption.
assumption.
apply ren_case2 with v x0 e0 e'.
red in |- *; intro; apply H2; symmetry  in |- *; assumption.
assumption.
assumption.
rewrite H0; apply RenNotFree with nx0 e0; assumption || elim H0; assumption.
elim H11; intro S.
left; assumption.
right; split.
left; assumption.
elim S; intros; assumption.
assumption.
assumption.
assumption.
(* ren_clos3 *)
specialize inv_TC_clos with (1 := H8).
simple induction 1; intros Ta Tb.
apply TC_clos.
apply H5.
elim H7; intro A.
left; assumption.
right; elim A; intros F M; split.
red in |- *; intro; apply F; apply FV_closa; assumption.
assumption.
assumption.
change (TC (((x0, t) :: HF) ++ (nv, s) :: H6) ne0 t0) in |- *.
apply H3.
elim H7; intro N.
left; assumption.
right; elim N; intros F M; split.
red in |- *; intro; apply F; apply FV_closb; assumption.
elim M; intros Mv Mnv.
split; simpl in |- *; red in |- *; simple induction 1; intro A.
apply H0; symmetry  in |- *; assumption.
apply Mv; assumption.
apply H1; symmetry  in |- *; assumption.
apply Mnv; assumption.
simpl in |- *; assumption.
Save TEp_RenExpGen.

(****************************************)
(* TEp_RenExp                           *)
(*   [nx/x]e=ne --->                    *)
(*   nx=x \/ nx not in FV(e) --->       *)
(*   [x:s]H  |- e:t                     *)
(*   [nx:s]H |- ne:t --->               *)
(****************************************)

Goal
forall (nx x : vari) (e ne : tm),
rename nx x e ne ->
nx = x \/ ~ FV nx e ->
forall (H : ty_env) (s t : ty),
TC ((x, s) :: H) e t -> TC ((nx, s) :: H) ne t.
intros.
change (TC (nil ++ (nx, s) :: H1) ne t) in |- *.
apply TEp_RenExpGen with x e.
assumption.
elim H0; intro N.
left; assumption.
right; simpl in |- *; split.
assumption.
split; red in |- *; intro; assumption.
simpl in |- *; assumption.
Save TEp_RenExp.


(****************************************)
(* TEp_Ap				*)
(*   This theorem states that the AP    *)
(*   function preserves types.		*)
(*                                      *)
(*   Ap(a,e,A) = <ne,[n:t->a]> --->	*)
(*   (x)(x in FV(e) -> x in Dom(A)) ->	*)
(*        H |- e :r->s   --->		*)
(*   [n:t]H |- ne:s  /\ r=t		*)
(****************************************)

Goal
forall (a e ne : tm) (A : OS_env) (n : vari) (t : ty),
Ap a e A ne n t ->
(forall x : vari, FV x e -> member vari x (OS_Dom A)) ->
forall (H : ty_env) (r s : ty),
TC H e (arr r s) -> TC ((n, t) :: H) ne s /\ r = t.

simple induction 1; intros.
specialize inv_TC_abs with (1 := H4).
simple induction 1; simple induction 1; intros Ar Te.
specialize subty_eq with (1 := Ar); simple induction 1; intros Q1 Q2.
split.  rewrite Q2.
apply TEp_RenExp with v e0.
assumption.
specialize (Xmidvar nv v); simple induction 1; intro N.
left; assumption.
right; red in |- *; intro F; apply H0; apply H2; apply FV_abs; assumption.
assumption.
assumption.
specialize inv_TC_clos with (1 := H4).
simple induction 1; intros T1 T0.
elim H1 with ((v, s) :: H3) r s0.
intros T Q.
specialize (ApNewVar a e0 ne0 (OScons v s e1 A0) n0 t0) with (1 := H0);
 intro M.
split.
apply TC_clos.
change (TC (nil ++ (n0, t0) :: H3) e1 s) in |- *.
apply TEp_nfvExt with H3.
assumption.
red in |- *; intro; apply M; simpl in |- *.
right; apply H2; apply FV_closa; assumption.
simpl in |- *; reflexivity.
change (TC (nil ++ (v, s) :: (n0, t0) :: H3) ne0 s0) in |- *.
apply TEp_swap with (nil ++ (n0, t0) :: (v, s) :: H3).
red in |- *; intro; apply M.
simpl in |- *; left; assumption.
simpl in |- *; assumption.
reflexivity.
assumption.
intros x F; simpl in |- *.
specialize (Xmidvar x v); simple induction 1; intro N.
left; symmetry  in |- *; assumption.
right; apply H2; apply FV_closb; assumption.
assumption.
Save TEp_Ap.
