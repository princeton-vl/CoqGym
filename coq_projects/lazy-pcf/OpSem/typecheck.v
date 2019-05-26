(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  typecheck.v                                                             *)
(*                                                                          *)
(*  This file contains the definition of the type judgment                  *)
(*  rules and the theorems stating their inverses.                          *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November  1993                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                               typecheck.v                                *)
(****************************************************************************)

Require Import environments.
Require Import List.

Require Import syntax.

(****************************************)
(*   Type Judgment Rules		*)
(*					*)
(*   (TC H e t) -> H |- e : t		*)
(****************************************)

Inductive TC : ty_env -> tm -> ty -> Prop :=
  | TC_o : forall H : ty_env, TC H o nat_ty
  | TC_ttt : forall H : ty_env, TC H ttt bool_ty
  | TC_fff : forall H : ty_env, TC H fff bool_ty
  | TC_succ :
      forall (H : ty_env) (e : tm), TC H e nat_ty -> TC H (succ e) nat_ty
  | TC_prd :
      forall (H : ty_env) (e : tm), TC H e nat_ty -> TC H (prd e) nat_ty
  | TC_is_o :
      forall (H : ty_env) (e : tm), TC H e nat_ty -> TC H (is_o e) bool_ty
  | TC_var :
      forall (H : ty_env) (v : vari) (t : ty), mapsto v t H -> TC H (var v) t
  | TC_appl :
      forall (H : ty_env) (e e1 : tm) (s t : ty),
      TC H e (arr s t) -> TC H e1 s -> TC H (appl e e1) t
  | TC_abs :
      forall (H : ty_env) (v : vari) (e : tm) (s t : ty),
      TC ((v, s) :: H) e t -> TC H (abs v s e) (arr s t)
  | TC_cond :
      forall (H : ty_env) (e1 e2 e3 : tm) (t : ty),
      TC H e1 bool_ty -> TC H e2 t -> TC H e3 t -> TC H (cond e1 e2 e3) t
  | TC_fix :
      forall (H : ty_env) (e : tm) (t : ty) (v : vari),
      TC ((v, t) :: H) e t -> TC H (Fix v t e) t
  | TC_clos :
      forall (H : ty_env) (e e1 : tm) (s t : ty) (v : vari),
      TC H e1 s -> TC ((v, s) :: H) e t -> TC H (clos e v s e1) t.
                                

(****************************************************************)
(*								*)
(*  tc								*)
(*    Uses Match to implement the type judgement rules.		*)
(*								*)
(*  tc_TC 							*)
(*    Proves (tc H e t) -> (TC H e t).  Each of the TC_inv_e	*)
(*    theorems is an instance of this one.			*)
(*								*)
(****************************************************************)

Definition tc (H : ty_env) (e : tm) (t : ty) :=
  match e return Prop with
  | o =>
      (* o *)	 t = nat_ty
      (* ttt *) 
  | ttt => t = bool_ty
      (* fff *) 
  | fff => t = bool_ty
      (* abs v s e *) 
  | abs v s e =>
      exists r : ty, t = arr s r /\ TC ((v, s) :: H) e r
      (* appl e1 e2 *) 
  | appl e1 e2 =>
      exists s : ty, TC H e1 (arr s t) /\ TC H e2 s
      (* cond e1 e2 e3 *)
  | cond e1 e2 e3 => TC H e1 bool_ty /\ TC H e2 t /\ TC H e3 t
                                        (* var v *)	
  | var v => mapsto v t H
      (* succ n *)	
  | succ n => t = nat_ty /\ TC H n nat_ty
              (* prd n *)	
  | prd n => t = nat_ty /\ TC H n nat_ty
             (* is_o n *)	
  | is_o n => t = bool_ty /\ TC H n nat_ty
              (* fix v s e1 *)
  | Fix v s e1 => s = t /\ TC ((v, s) :: H) e1 t
      (* clos e v s e1 *)
  | clos e v s e1 => TC H e1 s /\ TC ((v, s) :: H) e t
  end.


Goal forall (H : ty_env) (e : tm) (t : ty), TC H e t -> tc H e t.
simple induction 1; simpl in |- *; intros.
reflexivity.
reflexivity.
reflexivity.
split; reflexivity || assumption.
split; reflexivity || assumption.
split; reflexivity || assumption.
assumption.
exists s; split; assumption.
exists t0; split; reflexivity || assumption.
split; assumption || split; assumption.
split; reflexivity || assumption.
split; assumption.
Save TC_tc.


(********************************************************)
(*							*)
(*   inv_TC_e Rules:					*)
(*	For each term e, inv_TC_e claims the inverse of *)
(*	(TC H e t), meaning if an expression   		*)
(*	is type correct, then the hypotheses of its TC  *)
(*	Rule must hold.					*)
(*							*)
(********************************************************)

Goal forall (H : ty_env) (t : ty), TC H o t -> t = nat_ty.
 intros H t HTC.  change (tc H o t) in |- *.
 apply TC_tc; assumption.
Save inv_TC_o.

Goal forall (H : ty_env) (t : ty), TC H ttt t -> t = bool_ty.
 intros H t HTC.  change (tc H ttt t) in |- *.
 apply TC_tc; assumption.
Save inv_TC_ttt.

Goal forall (H : ty_env) (t : ty), TC H fff t -> t = bool_ty.
 intros H t HTC.  change (tc H fff t) in |- *.
 apply TC_tc; assumption.
Save inv_TC_fff.

Goal
forall (H : ty_env) (t : ty) (e0 : tm),
TC H (prd e0) t -> t = nat_ty /\ TC H e0 nat_ty.
 intros H t e0 HTC.  change (tc H (prd e0) t) in |- *.
 apply TC_tc; assumption.
Save inv_TC_prd.

Goal
forall (H : ty_env) (t : ty) (e0 : tm),
TC H (succ e0) t -> t = nat_ty /\ TC H e0 nat_ty.
 intros H t e0 HTC.  change (tc H (succ e0) t) in |- *.
 apply TC_tc; assumption.
Save inv_TC_succ.

Goal
forall (H : ty_env) (t : ty) (e0 : tm),
TC H (is_o e0) t -> t = bool_ty /\ TC H e0 nat_ty.
 intros H t e0 HTC.  change (tc H (is_o e0) t) in |- *.
 apply TC_tc; assumption.
Save inv_TC_is_o.

Goal forall (H : ty_env) (t : ty) (v : vari), TC H (var v) t -> mapsto v t H.
 intros H t v HTC.  change (tc H (var v) t) in |- *.
 apply TC_tc; assumption.
Save inv_TC_var.

Goal
forall (H : ty_env) (t : ty) (e1 e2 : tm),
TC H (appl e1 e2) t -> exists s : ty, TC H e1 (arr s t) /\ TC H e2 s.
 intros H t e1 e2 HTC.  change (tc H (appl e1 e2) t) in |- *.
 apply TC_tc; assumption.
Save inv_TC_appl.

Goal
forall (H : ty_env) (t s : ty) (v : vari) (e : tm),
TC H (abs v s e) t -> exists r : ty, t = arr s r /\ TC ((v, s) :: H) e r.
 intros H t s v e HTC.  change (tc H (abs v s e) t) in |- *.
 apply TC_tc; assumption.
Save inv_TC_abs.

Goal
forall (H : ty_env) (t : ty) (e1 e2 e3 : tm),
TC H (cond e1 e2 e3) t -> TC H e1 bool_ty /\ TC H e2 t /\ TC H e3 t.
 intros H t e1 e2 e3 HTC.  change (tc H (cond e1 e2 e3) t) in |- *.
 apply TC_tc; assumption.
Save inv_TC_cond.


Goal
forall (H : ty_env) (s t : ty) (e : tm) (v : vari),
TC H (Fix v s e) t -> s = t /\ TC ((v, s) :: H) e t.
 intros H s t e v HTC.  change (tc H (Fix v s e) t) in |- *.
 apply TC_tc; assumption.
Save inv_TC_fix.

Goal
forall (H : ty_env) (t s : ty) (e e1 : tm) (v : vari),
TC H (clos e v s e1) t -> TC H e1 s /\ TC ((v, s) :: H) e t.
 intros H t s e e1 v HTC.  change (tc H (clos e v s e1) t) in |- *.
 apply TC_tc; assumption.
Save inv_TC_clos.

