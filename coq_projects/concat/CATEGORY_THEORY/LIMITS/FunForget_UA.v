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
(*            Example of Universal Arrow : Universal Arrow from the          *)
(*		Set A to the Forgetful Functor MON -> SET                    *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)



Require Export FunForget.
Require Export FreeMonoid.
Require Export UniversalArrow.

Set Implicit Arguments.
Unset Strict Implicit.

Section ua_fm.

Variable A : Setoid.

Definition UA_FM_fun (a : A) : FunForget A := Concat1 a (Empty A).

Lemma UA_FM_map_law : Map_law UA_FM_fun.
Proof.
unfold Map_law in |- *; simpl in |- *; intros a b H; split; trivial. 
Qed.

Canonical Structure UA_FM_mor := Build_Map UA_FM_map_law.

 Section ua_fm_diese_def.

 Variables (B : Monoid) (f : Map A (FunForget B)). 

 Fixpoint UA_FM_diese_fun (l : FreeMonoid A) : B :=
   match l with
   | Empty => Munit B
   | Concat1 a m => f a +_M UA_FM_diese_fun m
   end.

 Lemma UA_FM_diese_map_law : Map_law UA_FM_diese_fun.
 Proof.
 unfold Map_law in |- *; simpl in |- *.
 intros l1; elim l1.
 intro l2; elim l2.
 simpl in |- *; intro; apply Refl.
 intros c t H1 H2; elim H2.
 intros c t H1 l2; elim l2.
 intro H2; absurd (Equal_Tlist (Concat1 c t) (Empty A)).
 apply Diff_Concat1_Empty.
 trivial.
 intros c0 t0 H2; simpl in |- *; intro H3; elim H3; intros H4 H5.
 apply Trans with (f c +_M UA_FM_diese_fun t0).
 unfold ApMop in |- *; apply Map2_l.
 apply H1; trivial.
 trivial.
 unfold ApMop in |- *; apply Map2_r.
 apply Pres1; trivial.
 Qed.
 
 Canonical Structure UA_FM_diese_map := Build_Map UA_FM_diese_map_law.
 
 Lemma UA_FM_diese_unit_law : MonUnit_law UA_FM_diese_map.
 Proof.
 unfold MonUnit_law in |- *; simpl in |- *.
 apply Refl.
 Qed. 

 Lemma UA_FM_diese_op_law : MonOp_law UA_FM_diese_map.
 Proof.
 unfold MonOp_law in |- *; simpl in |- *.
 intro l1; elim l1.
 simpl in |- *; intro l2.
 apply Trans with (UA_FM_diese_fun l2).
 apply Refl.
 apply Midl1.
 simpl in |- *; intros c t H l2.
 apply Trans with (f c +_M (UA_FM_diese_fun t +_M UA_FM_diese_fun l2)).
 unfold ApMop in |- *; apply Map2_l; exact (H l2).
 apply Mass. 
 Qed.

 Canonical Structure UA_FM_diese :=
   Build_MonMor UA_FM_diese_unit_law UA_FM_diese_op_law.

 End ua_fm_diese_def.

Lemma UA_FM_law1 : UA_law1 UA_FM_mor UA_FM_diese.
Proof.
unfold UA_law1, UA_eq in |- *; intros B f.
unfold UA_FM_mor in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
intro a; apply Midr1.
Qed.

Lemma UA_FM_law2 : UA_law2 UA_FM_mor UA_FM_diese.
Proof.
unfold UA_law2 in |- *; simpl in |- *.
unfold UA_eq, Equal_MonMor in |- *; simpl in |- *.
unfold UA_FM_diese_map, Ext in |- *; simpl in |- *.
unfold Comp_fun, UA_FM_fun, FMor at 1 in |- *; simpl in |- *.
intros B f h H l; elim l; simpl in |- *.
apply (MMon_unit h).
intros c t H1. 
apply Trans with (h (Concat1 c (Empty A)) +_M h t).
apply (MMon_op h (Concat1 c (Empty A)) t).
apply Trans with (f c +_M h t).
unfold ApMop in |- *; apply Map2_r; exact (H c). 
unfold ApMop in |- *; apply Map2_l; trivial.
Qed.
  
Lemma IsUA_FM : IsUA UA_FM_mor.
Proof.
exact (Build_IsUA UA_FM_law1 UA_FM_law2).
Defined.

Definition UA_FM : UA A FunForget := IsUA_FM.

End ua_fm.

