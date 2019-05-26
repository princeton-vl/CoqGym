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
(*	                   Monoids Category                		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export SET.
Require Export Monoid.

Set Implicit Arguments.
Unset Strict Implicit.

(* Monoid Morphism composition *)

Section comp_mon.

Variables (m1 m2 m3 : Monoid) (f : MonMor m1 m2) (g : MonMor m2 m3).

Definition Comp_MonMor_map := f o_M g.

Lemma Comp_MonMor_unit_law : MonUnit_law Comp_MonMor_map.
Proof.
unfold MonUnit_law, Comp_MonMor_map in |- *. 
simpl in |- *; unfold Comp_fun in |- *.
apply Trans with (g (Munit m2)).
apply Pres1; apply MMon_unit.
apply MMon_unit.
Qed.

Lemma Comp_MonMor_op_law : MonOp_law Comp_MonMor_map.
Proof.
unfold MonOp_law, Comp_MonMor_map in |- *.
simpl in |- *; unfold Comp_fun in |- *.
intros a b.
apply Trans with (g (f a +_M f b)).
apply (Pres g); apply MMon_op.
apply MMon_op.
Qed.
 
Canonical Structure Comp_MonMor : MonMor_setoid m1 m3 :=
  Build_MonMor Comp_MonMor_unit_law Comp_MonMor_op_law.

End comp_mon.

Lemma Comp_MonMor_congl : Congl_law Comp_MonMor.
Proof.
unfold Congl_law in |- *; simpl in |- *.
unfold Equal_MonMor, Ext in |- *; simpl in |- *.
unfold Comp_fun in |- *.
intros m1 m2 m3 f g h H a.
apply H.
Qed.

Lemma Comp_MonMor_congr : Congr_law Comp_MonMor.
Proof.
unfold Congr_law in |- *; simpl in |- *.
unfold Equal_MonMor, Ext in |- *; simpl in |- *.
unfold Comp_fun in |- *.
intros m1 m2 m3 f g h H a.
apply Pres1.
apply H.
Qed.

Definition Comp_MON := Build_Comp Comp_MonMor_congl Comp_MonMor_congr.

Lemma Assoc_MON : Assoc_law Comp_MON.
Proof.
unfold Assoc_law in |- *; simpl in |- *; intros m1 m2 m3 m4 f g h.
unfold Equal_MonMor, Ext in |- *; simpl in |- *.
unfold Comp_fun in |- *; intro a.
apply Refl.
Qed.

(* Id *)

Section id_mon_def.

Variable m : Monoid.

Definition Id_MON_map := Id_SET m.

Lemma Id_MON_unit_law : MonUnit_law Id_MON_map.
Proof.
unfold MonUnit_law, Id_MON_map in |- *; simpl in |- *.
unfold Id_fun in |- *; apply Refl. 
Qed.

Lemma Id_MON_op_law : MonOp_law Id_MON_map.
Proof.
unfold MonOp_law, Id_MON_map in |- *; simpl in |- *.
unfold Id_fun in |- *; intros a b.
apply Refl.
Qed.

Canonical Structure Id_MON : MonMor_setoid m m :=
  Build_MonMor Id_MON_unit_law Id_MON_op_law.

End id_mon_def.

Lemma Idl_MON : Idl_law Comp_MON Id_MON.
Proof.
unfold Idl_law in |- *; intros m1 m2 f; simpl in |- *.
unfold Equal_MonMor, Ext in |- *; simpl in |- *.
unfold Comp_fun in |- *; intro a.
unfold Id_MON_map in |- *; simpl in |- *; unfold Id_fun in |- *.
apply Refl.
Qed.

Lemma Idr_MON : Idr_law Comp_MON Id_MON.
Proof.
unfold Idr_law in |- *; intros m1 m2 f; simpl in |- *.
unfold Equal_MonMor, Ext in |- *; simpl in |- *.
unfold Comp_fun in |- *; intro a.
unfold Id_MON_map in |- *; simpl in |- *; unfold Id_fun in |- *.
apply Refl.
Qed.

Canonical Structure MON := Build_Category Assoc_MON Idl_MON Idr_MON.