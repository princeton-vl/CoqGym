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
(*	                      Comma Category (x|G) : Projection		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Comma.

Set Implicit Arguments.
Unset Strict Implicit.

(* Functor Projection *)

Section comma_proj_def.

Variables (A X : Category) (G : Functor A X) (x : X).

Definition Comma_proj_ob (a : Com_ob G x) := Ob_com_ob a.

 Section comma_proj_map_def.

 Variable a b : Com_ob G x.

 Definition Comma_proj_mor (f : a --> b) := Mor_com_arrow f.

 Lemma Comma_proj_map_law : Map_law Comma_proj_mor.
 Proof.
 unfold Map_law, Comma_proj_mor in |- *; simpl in |- *.
 intros f g; unfold Equal_com_arrow in |- *; auto.
 Qed.

 Definition Comma_proj_map := Build_Map Comma_proj_map_law.

 End comma_proj_map_def.

Lemma Comma_proj_comp_law : Fcomp_law Comma_proj_map.
Proof.
unfold Fcomp_law in |- *; simpl in |- *.
intros a b c f g; unfold Comp_com_arrow, Comma_proj_mor in |- *.
apply Refl.
Qed.

Lemma Comma_proj_id_law : Fid_law Comma_proj_map.
Proof.
unfold Fid_law in |- *; simpl in |- *.
intro a; apply Refl.
Qed.

Canonical Structure Comma_proj :=
  Build_Functor Comma_proj_comp_law Comma_proj_id_law.

End comma_proj_def.
