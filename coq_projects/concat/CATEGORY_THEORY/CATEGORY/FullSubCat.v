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
(*	                   Full SubCategory                   		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Category.

Set Implicit Arguments.
Unset Strict Implicit.

Section fscat.

Variables (C : Category) (I : Type) (a : I -> C).

Definition FSC_mor_setoid (i j : I) := a i --> a j.

(* composition *)

Definition Comp_FSC (i j l : I) :
  Map2 (FSC_mor_setoid i j) (FSC_mor_setoid j l) (FSC_mor_setoid i l) :=
  Op_comp (a i) (a j) (a l).

Lemma Assoc_FSC : Assoc_law Comp_FSC.
Proof.
unfold Assoc_law in |- *; intros i1 i2 i3 i4 f g h.
exact (Ass f g h).
Qed.

(* Id *)

Definition Id_FSC (i : I) := Id (a i).

Lemma Idl_FSC : Idl_law Comp_FSC Id_FSC.
Proof.
unfold Idl_law in |- *; intros i j f.
exact (Idl f).
Qed.

Lemma Idr_FSC : Idr_law Comp_FSC Id_FSC.
Proof.
unfold Idr_law in |- *; intros i j f.
exact (Idr f).
Qed.

Canonical Structure FullSubCat := Build_Category Assoc_FSC Idl_FSC Idr_FSC.

End fscat.