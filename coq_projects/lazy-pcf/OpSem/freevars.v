(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*  freevars.v                                                              *)
(*                                                                          *)
(*  This file contains the definition of free variables                     *)
(*  and some related properties.                                            *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November  1993                                                          *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                freevars.v                                *)
(****************************************************************************)

Require Import syntax.
Require Import utils.


(********************************************************)
(*   Free Variables, Definition                         *)
(*							*)
(*   (FV x e) -> x in FV(e)				*)
(*							*)
(********************************************************)

Inductive FV (z : vari) : tm -> Prop :=
  | FV_abs :
      forall e : tm,
      FV z e -> forall v : vari, z <> v -> forall t : ty, FV z (abs v t e)
  | FV_fix :
      forall e : tm,
      FV z e -> forall v : vari, z <> v -> forall t : ty, FV z (Fix v t e)
  | FV_appl1 : forall e_1 e_2 : tm, FV z e_1 -> FV z (appl e_1 e_2)
  | FV_appl2 : forall e_1 e_2 : tm, FV z e_2 -> FV z (appl e_1 e_2)
  | FV_cond1 : forall e_1 e_2 e_3 : tm, FV z e_1 -> FV z (cond e_1 e_2 e_3)
  | FV_cond2 : forall e_1 e_2 e_3 : tm, FV z e_2 -> FV z (cond e_1 e_2 e_3)
  | FV_cond3 : forall e_1 e_2 e_3 : tm, FV z e_3 -> FV z (cond e_1 e_2 e_3)
  | FV_var : forall v : vari, z = v -> FV z (var v)
  | FV_succ : forall e : tm, FV z e -> FV z (succ e)
  | FV_prd : forall e : tm, FV z e -> FV z (prd e)
  | FV_is_o : forall e : tm, FV z e -> FV z (is_o e)
  | FV_closa :
      forall (v : vari) (t : ty) (e e_1 : tm),
      FV z e_1 -> FV z (clos e v t e_1)
  | FV_closb :
      forall (v : vari) (t : ty) (e e_1 : tm),
      FV z e -> z <> v -> FV z (clos e v t e_1).



(****************************************************************)
(*  notFV							*)
(*    These theorems state what ~(FV v e) implies:		*)
(*								*)
(*    ~(FV x (abs v t e)) ---> x=v \/ ~(FV x e)		        *)
(*    ~(FV v (appl e1 e2)) ---> ~(FV v e1) /\ ~(FV v e2)	*)
(*    ~(FV v (cond e1 e2 e3)) ---> 				*)
(*		    ~(FV v e1) /\ ~(FV v e2) /\ ~(FV v e3)	*)
(*    ~(FV v (var x)) --->  ~v=x				*)
(*    ~(FV v (succ e)) ---> ~(FV v e)				*)
(*    ~(FV v (prd e)) ---> ~(FV v e)				*)
(*    ~(FV v (is_o e)) ---> ~(FV v e)				*)
(*    ~(FV x (fix v t e)) ---> x=v \/ ~(FV x e)		        *)
(*    ~(FV x (clos e v t a))->					*)
(*                   ~(FV x a) /\ (x=v \/ ~(FV x e))	        *)
(****************************************************************)


Goal
forall (x v : vari) (t : ty) (e : tm),
~ FV x (abs v t e) -> x = v \/ ~ FV x e.
intros.
specialize (Xmidvar x v); simple induction 1; intro A.
left; assumption.
right; red in |- *; intro; apply H; apply FV_abs; assumption.
Save notFV_abs.


Goal
forall (v : vari) (e1 e2 : tm), ~ FV v (appl e1 e2) -> ~ FV v e1 /\ ~ FV v e2.
intros v e1 e2 N.
split.
red in |- *; intro; apply N; apply FV_appl1; assumption.
red in |- *; intro; apply N; apply FV_appl2; assumption.
Save notFV_appl.

Goal
forall (v : vari) (e1 e2 e3 : tm),
~ FV v (cond e1 e2 e3) -> ~ FV v e1 /\ ~ FV v e2 /\ ~ FV v e3.
intros v e1 e2 e3 N.
split.
red in |- *; intro; apply N; apply FV_cond1; assumption.
split.
red in |- *; intro; apply N; apply FV_cond2; assumption.
red in |- *; intro; apply N; apply FV_cond3; assumption.
Save notFV_cond.


Goal forall v x : vari, ~ FV v (var x) -> v <> x.
intros v x N.
red in |- *; intro; apply N; apply FV_var; assumption.
Save notFV_var.

Goal forall (v : vari) (e : tm), ~ FV v (succ e) -> ~ FV v e.
intros v e N.
red in |- *; intro; apply N; apply FV_succ; assumption.
Save notFV_succ.


Goal forall (v : vari) (e : tm), ~ FV v (prd e) -> ~ FV v e.
intros v e N.
red in |- *; intro; apply N; apply FV_prd; assumption.
Save notFV_prd.

Goal forall (v : vari) (e : tm), ~ FV v (is_o e) -> ~ FV v e.
intros v e N.
red in |- *; intro; apply N; apply FV_is_o; assumption.
Save notFV_is_o.

Goal
forall (x v : vari) (t : ty) (e : tm),
~ FV x (Fix v t e) -> x = v \/ ~ FV x e.
intros.
specialize (Xmidvar x v); simple induction 1; intro A.
left; assumption.
right; red in |- *; intro; apply H; apply FV_fix; assumption.
Save notFV_fix.

Goal
forall (x v : vari) (t : ty) (e a : tm),
~ FV x (clos e v t a) -> ~ FV x a /\ (x = v \/ ~ FV x e).
intros.
split.
red in |- *; intro; apply H; apply FV_closa; assumption.
specialize (Xmidvar x v); simple induction 1; intro A.
left; assumption.
right; red in |- *; intro; apply H; apply FV_closb; assumption.
Save notFV_clos.



(********************************************************)
(*  inv_FV						*)
(*     These theorems state what (FV v e) implies.	*)
(*  							*)
(*  (FV v 0) ---> False					*)
(*  (FV v ttt) ---> False				*)
(*  (FV v fff) ---> False				*)
(*  (FV v (abs x t e)) ---> (FV v e) /\ ~v=x		*)
(*  (FV v (fix x t e)) ---> (FV v e) /\ ~v=x	        *)
(*  (FV v (appl e1 e2)) --->  (FV v e1)\/(FV v e2)	*)
(*  (FV v (succ e) ---> (FV v e)			*)
(*  (FV v (prd e) ---> (FV v e)			        *)
(*  (FV v (is_o e) ---> (FV v e)			*)
(*  (FV v (clos e x t a)) ---> (FV v a) \/ 		*)
(*                             (FV v e)/\~v=x	        *)
(*  							*)
(*  They use the function fv : vari->tm->Prop which	*)
(*  defines the free variable relation in terms of the	*)
(*  Match operator.  The theorem FV_fv is proved 	*)
(*  by induction, and each of the individual FV_e	*)
(*  theorems is an instance of the FV_fv theorem.	*)
(*  							*)
(********************************************************)

Definition fv (v : vari) (e : tm) :=
  match e return Prop with
  | o =>
      (* o *)	 False
      (* ttt *) 
  | ttt => False
      (* fff *) 
  | fff => False
      (* abs x s e *) 
  | abs y s e => FV v e /\ v <> y
                           (* appl e1 e2 *) 
  | appl e1 e2 => FV v e1 \/ FV v e2 
                  (* cond e1 e2 e3 *)
  | cond e1 e2 e3 => FV v e1 \/ FV v e2 \/ FV v e3 
                                (* var x *)	
  | var y => v = y
             (* succ n *)	
  | succ n => FV v n
      (* prd n *)	
  | prd n => FV v n
      (* is_o n *)	
  | is_o n => FV v n
      (* fix x s e *)	
  | Fix y s e => FV v e /\ v <> y
                           (* clos e x s e1 *)
  | clos e y s e1 => FV v e1 \/ FV v e /\ v <> y
  end.


Goal forall (v : vari) (e : tm), FV v e -> fv v e.

simple induction 1; simpl in |- *; intros.
split; assumption.
split; assumption.
left; assumption.
right; assumption.
left; assumption.
right; left; assumption.
right; right; assumption.
assumption.
assumption.
assumption.
assumption.
left; assumption.
right; split; assumption.
Save FV_fv.


Goal forall v : vari, ~ FV v o.
intro v; red in |- *; intro F.
change (fv v o) in |- *.
apply FV_fv; assumption.
Save inv_FV_o.


Goal forall v : vari, ~ FV v ttt.
intro v; red in |- *; intro F.
change (fv v ttt) in |- *.
apply FV_fv; assumption.
Save inv_FV_ttt.


Goal forall v : vari, ~ FV v fff.
intro v; red in |- *; intro F.
change (fv v fff) in |- *.
apply FV_fv; assumption.
Save inv_FV_fff.

Goal
forall (v x : vari) (t : ty) (e : tm), FV v (abs x t e) -> FV v e /\ v <> x.
intros v x t e F.
change (fv v (abs x t e)) in |- *.
apply FV_fv; assumption.
Save inv_FV_abs.

Goal
forall (v x : vari) (t : ty) (e : tm), FV v (Fix x t e) -> FV v e /\ v <> x.
intros v x t e F.
change (fv v (Fix x t e)) in |- *.
apply FV_fv; assumption.
Save inv_FV_fix.

Goal forall (v : vari) (e1 e2 : tm), FV v (appl e1 e2) -> FV v e1 \/ FV v e2.
intros v e1 e2 F.
change (fv v (appl e1 e2)) in |- *.
apply FV_fv; assumption.
Save inv_FV_appl.

Goal
forall (v : vari) (e1 e2 e3 : tm),
FV v (cond e1 e2 e3) -> FV v e1 \/ FV v e2 \/ FV v e3.
intros v e1 e2 e3 F.
change (fv v (cond e1 e2 e3)) in |- *.
apply FV_fv; assumption.
Save inv_FV_cond.

Goal forall v x : vari, FV v (var x) -> v = x.
intros v x F.
change (fv v (var x)) in |- *.
apply FV_fv; assumption.
Save inv_FV_var.

Goal forall (v : vari) (e : tm), FV v (succ e) -> FV v e.
intros v e F.
change (fv v (succ e)) in |- *.
apply FV_fv; assumption.
Save inv_FV_succ.


Goal forall (v : vari) (e : tm), FV v (prd e) -> FV v e.
intros v e F.
change (fv v (prd e)) in |- *.
apply FV_fv; assumption.
Save inv_FV_prd.


Goal forall (v : vari) (e : tm), FV v (is_o e) -> FV v e.
intros v e F.
change (fv v (is_o e)) in |- *.
apply FV_fv; assumption.
Save inv_FV_is_o.


Goal
forall (v x : vari) (t : ty) (e a : tm),
FV v (clos e x t a) -> FV v a \/ FV v e /\ v <> x.
intros v x t e a F.
change (fv v (clos e x t a)) in |- *.
apply FV_fv; assumption.
Save inv_FV_clos.

