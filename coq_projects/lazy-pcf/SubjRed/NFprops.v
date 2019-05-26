(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(* NF.v                                                                     *)
(*                                                                          *)
(* This file contains proofs of properties of the NF set                    *)
(* and its subsets F and Sno.                                               *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November 1993                                                           *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                NFprops.v                                 *)
(****************************************************************************)

Require Import NF.
Require Import List.
Require Import syntax.
Require Import typecheck.
Require Import environments.
Require Import freevars.
Require Import utils.

(********************************)
(* Fe_not_nat			*)
(*  e in F ---> ~(H |- e:nat)	*)
(********************************)

Goal forall e : tm, F e -> forall H : ty_env, ~ TC H e nat_ty.
   simple induction 1; intros.
   red in |- *; intro.
   specialize inv_TC_abs with (1 := H1).
   simple induction 1; simple induction 1; intros Q T.
   generalize Q; exact (nat_not_arr s x).
   red in |- *; intro.
   specialize inv_TC_clos with (1 := H3).
   simple induction 1; intros T1 T0.
   red in H1; apply H1 with ((v, s) :: H2); assumption.
Save Fe_not_nat.

(********************************)
(* Fe_not_bool			*)
(*  e in F ---> ~(H |- e:bool)	*)
(********************************)

Goal forall e : tm, F e -> forall H : ty_env, ~ TC H e bool_ty.
   simple induction 1; intros.
   red in |- *; intro.
   specialize inv_TC_abs with (1 := H1).
   simple induction 1; simple induction 1; intros Q T.
   generalize Q; exact (bool_not_arr s x).
   red in |- *; intro.
   specialize inv_TC_clos with (1 := H3).
   simple induction 1; intros T1 T0.
   red in H1; apply H1 with ((v, s) :: H2); assumption.
Save Fe_not_bool.


(********************************************************)
(* NFe_Fe						*)
(*							*)
(* e in NF /\ not H |- e:nat /\ not H |- e:bool ---->	*)
(*		e in F					*)
(********************************************************)

Goal
forall e : tm,
NF e ->
forall (H : ty_env) (t : ty),
TC H e t -> ~ (t = nat_ty \/ t = bool_ty) -> F e.
 simple induction 1; simpl in |- *; intros.
 elim H2; right.
 apply (inv_TC_ttt H0); assumption.
 elim H2; right.
 apply (inv_TC_fff H0); assumption.
 elim H3; left.
 generalize H2.
 elim H0.
 exact (inv_TC_o H1 t).
 intros.
 specialize inv_TC_succ with (1 := H6).
 simple induction 1; intros; assumption.
 assumption.
Save NFe_Fe.

(************************************************)
(* NFebool_TF 					*)
(*  e in NF /\ H |- e:bool--->  e=ttt \/ e=fff  *)
(************************************************)

Goal
forall e : tm,
NF e -> forall H : ty_env, TC H e bool_ty -> e = ttt \/ e = fff.
simple induction 1; intros.
left; reflexivity.
right; reflexivity.
generalize H2; elim H0; intros.
specialize inv_TC_o with (1 := H3); intro Q.
absurd (nat_ty = bool_ty).
exact nat_not_bool.
symmetry  in |- *; assumption.
specialize inv_TC_succ with (1 := H5); simple induction 1; intros Q T.
absurd (nat_ty = bool_ty).
exact nat_not_bool.
symmetry  in |- *; assumption.
absurd (TC H1 e0 bool_ty).
apply Fe_not_bool; assumption.
assumption.
Save NFebool_TF.


(************************************************)
(* NFenat_Snoe					*)
(*  e in NF /\ H |- e:nat --->  e in Sno	*)
(************************************************)

Goal forall e : tm, NF e -> forall H : ty_env, TC H e nat_ty -> Sno e.

   simple induction 1; intros.
   specialize inv_TC_ttt with (1 := H1); intro Q.
   absurd (nat_ty = bool_ty); assumption || exact nat_not_bool.
   specialize inv_TC_fff with (1 := H1); intro Q.
   absurd (nat_ty = bool_ty); assumption || exact nat_not_bool.
   assumption.
   absurd (TC H1 e0 nat_ty).
   apply Fe_not_nat.
   assumption.
   assumption.
Save NFenat_Snoe.


(********************************)
(* Snoe_notFVe			*)
(*  e in Sno --->  e closed 	*)
(********************************)

Goal forall e : tm, Sno e -> forall v : vari, ~ FV v e.
  simple induction 1; intros.
  apply inv_FV_o.
  red in |- *; intro.
  red in H1; apply H1 with v.
  apply inv_FV_succ; assumption.
Save Snoe_notFVe.
