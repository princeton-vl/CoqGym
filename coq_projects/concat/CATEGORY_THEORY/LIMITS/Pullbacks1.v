(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(*****************************************************************************)
(*          Projet Formel - Calculus of Inductive Constructions V5.10        *)
(*****************************************************************************)
(*									     *)
(*	                       Pullbacks                  		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export Limit.
Require Export PULB.
Require Export Pullbacks.

Set Implicit Arguments.
Unset Strict Implicit.

(* Pullbacks *)

Section Fpullback_limit_def.

Variables (C : Category) (G : Functor PULB C).

SubClass Fpullback1 := Limit G.

Variable l : Fpullback1.

Definition Fibred1_prod := Lim l.

Definition Fibred1_p : Fibred1_prod --> G P1 := Limiting_cone l P1.

Definition Fibred1_q : Fibred1_prod --> G P3 := Limiting_cone l P3.

Lemma Prf_pb1_law1 :
 Pullback_law1 (FMor G F12) (FMor G F32) Fibred1_p Fibred1_q.
Proof.
unfold Pullback_law1, Pullback_eq1 in |- *.
(* *) apply Trans with (Limiting_cone l P2).
apply Sym.
apply (Eq_cone (Limiting_cone l) F12).
apply (Eq_cone (Limiting_cone l) F32).
Qed.
 
 Section pb1_diese_def.

 Variables (r : C) (t1 : r --> G P1) (t2 : r --> G P3).

 Hypothesis H : Pullback_eq1 (FMor G F12) (FMor G F32) t1 t2.

 (* construction de r# *) 

 Definition Pulb_tau (a : PULB) :=
   match a as a' return (Carrier (r --> G a')) with
   | P1 => t1
   | P2 => t1 o FMor G F12
   | P3 => t2
   end.
 
 Lemma Pulb_cone_law : Cone_law Pulb_tau.
 Proof.
 unfold Cone_law in |- *; intros x x1 t.
 elim t; simpl in |- *; unfold FMor at 1 in |- *; simpl in |- *.
 apply Trans with (t1 o Id (G P1)).
 apply Idr.
 apply Comp_l; apply (FId1 G P1).
 apply Trans with ((t1 o FMor G F12) o Id (G P2)).
 apply Idr.
 apply Comp_l; apply (FId1 G P2).
 apply Trans with (t2 o Id (G P3)).
 apply Idr.
 apply Comp_l; apply (FId1 G P3).
 apply Refl.
 apply H.
 Qed.
 
 Definition Pulb_cone : Cone r G := Pulb_cone_law.

 Definition Pb1_diese : r --> Fibred1_prod := Lim_diese l Pulb_cone.

 End pb1_diese_def.

Lemma Prf_pb1_law2 : Pullback_law2 Fibred1_p Pb1_diese.
Proof.
unfold Pullback_law2, Pullback_eq1, Pullback_eq2 in |- *; intros r t1 t2 H.
apply Sym; apply (Prf_limit1 l (Pulb_cone H) P1).
Qed.

Lemma Prf_pb1_law3 : Pullback_law3 Fibred1_q Pb1_diese.
Proof.
unfold Pullback_law3, Pullback_eq1, Pullback_eq2 in |- *; intros r t1 t2 H.
apply Sym; apply (Prf_limit1 l (Pulb_cone H) P3).
Qed.

(* unicite' de r# *)

Lemma Prf_pb1_law4 : Pullback_law4 Fibred1_p Fibred1_q Pb1_diese.
Proof.
unfold Pullback_law4, Pullback_eq1, Pullback_eq2 in |- *;
 intros r t1 t2 H h H1 H2.
unfold Pb1_diese in |- *.
apply (Prf_limit2 l).
unfold Limit_eq in |- *; simpl in |- *.
intro x; elim x; simpl in |- *.
apply Sym; exact H1.
(* *) apply Trans with (h o Fibred1_p o FMor G F12).
apply Comp_l; apply (Eq_cone (Limiting_cone l) F12).
(* *) apply Trans with ((h o Fibred1_p) o FMor G F12).
apply Ass.
apply Comp_r.
apply Sym; exact H1.
apply Sym; exact H2.
Qed.

Canonical Structure Pullback1_to_Pullback :=
  Build_Pullback Prf_pb1_law1 Prf_pb1_law2 Prf_pb1_law3 Prf_pb1_law4. 

End Fpullback_limit_def.

Coercion Pullback1_to_Pullback : Fpullback1 >-> Pullback. 

(* Functor PULB -> C *)

Section pullback_limit_def.

Variables (C : Category) (a b c : C) (f : a --> b) (g : c --> b).

Definition Fpulb_ob (x : PULB) :=
  match x return (Ob C) with
  | P1 => a
  | P2 => b
  | P3 => c
  end.

Definition Fpulb_mor (x y : PULB) (h : PULB_mor_setoid x y) :=
  match
    h in (PULB_mor x' y') return (Carrier (Fpulb_ob x' --> Fpulb_ob y'))
  with
  | IP1 => Id a
  | IP2 => Id b
  | IP3 => Id c
  | F12 => f
  | F32 => g
  end.

Lemma Fpulb_map_law : forall x y : PULB_ob, Map_law (Fpulb_mor (x:=x) (y:=y)).
Proof.
unfold Map_law in |- *; intros x y h1.
elim h1; simpl in |- *.
(* 1 *)
intro h2;
 lapply
  (PULB_11_ind
     (P:=fun t : PULB_mor P1 P1 =>
         Equal_PULB_mor IP1 t -> Id a =_S Fpulb_mor t)).
intros H H0; apply (H h2 H0).
intro H; simpl in |- *; apply Refl.
(* 2 *)
intro h2;
 lapply
  (PULB_22_ind
     (P:=fun t : PULB_mor P2 P2 =>
         Equal_PULB_mor IP2 t -> Id b =_S Fpulb_mor t)).
intros H H0; apply (H h2 H0).
intro H; simpl in |- *; apply Refl.
(* 3 *)
intro h2;
 lapply
  (PULB_33_ind
     (P:=fun t : PULB_mor P3 P3 =>
         Equal_PULB_mor IP3 t -> Id c =_S Fpulb_mor t)).
intros H H0; apply (H h2 H0).
intro H; simpl in |- *; apply Refl.
(* 4 *)
intro h2;
 lapply
  (PULB_12_ind
     (P:=fun t : PULB_mor P1 P2 => Equal_PULB_mor F12 t -> f =_S Fpulb_mor t)).
intros H H0; apply (H h2 H0).
intro H; simpl in |- *; apply Refl.
(* 5 *)
intro h2;
 lapply
  (PULB_32_ind
     (P:=fun t : PULB_mor P3 P2 => Equal_PULB_mor F32 t -> g =_S Fpulb_mor t)).
intros H H0; apply (H h2 H0).
intro H; simpl in |- *; apply Refl.
Qed.

Canonical Structure Fpulb_map (x y : PULB) :=
  Build_Map (Fpulb_map_law (x:=x) (y:=y)).

Lemma Fpulb_comp_law : Fcomp_law Fpulb_map.
Proof.
unfold Fcomp_law in |- *; simpl in |- *; intros x y z h1.
elim h1; simpl in |- *.
(* 1 *)
elim z; intro h2.
(* 1.1 *)
simpl in |- *;
 lapply
  (PULB_11_ind (P:=fun t : PULB_mor P1 P1 => Id a =_S Id a o Fpulb_mor t)).
intro H; apply (H h2).
simpl in |- *; apply Idr.
(* 1.2 *)
simpl in |- *;
 lapply (PULB_12_ind (P:=fun t : PULB_mor P1 P2 => f =_S Id a o Fpulb_mor t)).
intro H; apply (H h2).
simpl in |- *; apply Idl1.
(* 1.3 *)
apply
 (PULB_13_ind
    (fun t : PULB_mor P1 P3 =>
     Fpulb_mor (Comp_PULB_mor IP1 h2) =_S Id a o Fpulb_mor h2) h2).
(* 2 *)
elim z; intro h2.
(* 2.1 *)
apply
 (PULB_21_ind
    (fun a : PULB_mor P2 P1 =>
     Fpulb_mor (Comp_PULB_mor IP2 h2) =_S Id b o Fpulb_mor h2) h2).
(* 2.2 *)
simpl in |- *;
 lapply
  (PULB_22_ind (P:=fun t : PULB_mor P2 P2 => Id b =_S Id b o Fpulb_mor t)).
intro H; apply (H h2).
simpl in |- *; apply Idr.
(* 2.3 *)
apply
 (PULB_23_ind
    (fun a : PULB_mor P2 P3 =>
     Fpulb_mor (Comp_PULB_mor IP2 h2) =_S Id b o Fpulb_mor h2) h2).
(* 3 *)
elim z; intro h2.
(* 3.1 *)
apply
 (PULB_31_ind
    (fun a : PULB_mor P3 P1 =>
     Fpulb_mor (Comp_PULB_mor IP3 h2) =_S Id c o Fpulb_mor h2) h2).
(* 3.2 *)
simpl in |- *;
 apply (PULB_32_ind (P:=fun a : PULB_mor P3 P2 => g =_S Id c o Fpulb_mor a)).
simpl in |- *; apply Idl1.
(* 3.3 *)
simpl in |- *;
 lapply
  (PULB_33_ind (P:=fun t : PULB_mor P3 P3 => Id c =_S Id c o Fpulb_mor t)).
intro H; apply (H h2).
simpl in |- *; apply Idr.
(* 4 *)
elim z; intro h2.
(* 4.1 *)
apply
 (PULB_21_ind
    (fun a : PULB_mor P2 P1 =>
     Fpulb_mor (Comp_PULB_mor F12 h2) =_S f o Fpulb_mor h2) h2).
(* 4.2 *)
simpl in |- *;
 lapply (PULB_22_ind (P:=fun t : PULB_mor P2 P2 => f =_S f o Fpulb_mor t)).
intro H; apply (H h2).
simpl in |- *; apply Idr.
(* 4.3 *)
apply
 (PULB_23_ind
    (fun a : PULB_mor P2 P3 =>
     Fpulb_mor (Comp_PULB_mor F12 h2) =_S f o Fpulb_mor h2) h2).
(* 5 *)
elim z; intro h2.
(* 5.1 *)
apply
 (PULB_21_ind
    (fun a : PULB_mor P2 P1 =>
     Fpulb_mor (Comp_PULB_mor F32 h2) =_S g o Fpulb_mor h2) h2).
(* 5.2 *)
simpl in |- *;
 lapply (PULB_22_ind (P:=fun t : PULB_mor P2 P2 => g =_S g o Fpulb_mor t)).
intro H; apply (H h2).
simpl in |- *; apply Idr.
(* 5.3 *)
apply
 (PULB_23_ind
    (fun a : PULB_mor P2 P3 =>
     Fpulb_mor (Comp_PULB_mor F32 h2) =_S g o Fpulb_mor h2) h2).
Qed.

Lemma Fpulb_id_law : Fid_law Fpulb_map.
Proof.
unfold Fid_law in |- *; simpl in |- *; intro x.
elim x; simpl in |- *; apply Refl.
Qed.

Canonical Structure Fpulb := Build_Functor Fpulb_comp_law Fpulb_id_law.

SubClass Pullback1 := Fpullback1 Fpulb.

End pullback_limit_def.
