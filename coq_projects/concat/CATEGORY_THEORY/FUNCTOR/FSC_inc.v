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
(*	                   Full SubCategory : Inclusion functor		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export FullSubCat.
Require Export FunctorProperty.

Set Implicit Arguments.
Unset Strict Implicit.

(* Inclusion Functor *)

Section fsc_inc_def.

Variables (C : Category) (I : Type) (a : I -> C).

Definition Inc_map (i j : FullSubCat a) := Id_map (a i --> a j).

Lemma Inc_comp_law : Fcomp_law Inc_map.
Proof.
unfold Fcomp_law in |- *; simpl in |- *.
intros i1 i2 i3 f g; apply Refl.
Qed.

Lemma Inc_id_law : Fid_law Inc_map.
Proof.
unfold Fid_law in |- *; simpl in |- *.
intros i; apply Refl.
Qed.

Canonical Structure FSC_inc := Build_Functor Inc_comp_law Inc_id_law.

(* proprie'te's de Inc *)

Lemma Inc_faith : Faithful_law FSC_inc.
Proof.
unfold Faithful_law in |- *; simpl in |- *.
unfold FMor in |- *; simpl in |- *; auto.
Qed.

Lemma Inc_full :
 Full_law (F:=FSC_inc) (fun i j : I => Id_fun (A:=a i --> a j)).
Proof.
unfold Full_law in |- *; simpl in |- *; intros i j f.
apply Refl.
Qed.

End fsc_inc_def.
