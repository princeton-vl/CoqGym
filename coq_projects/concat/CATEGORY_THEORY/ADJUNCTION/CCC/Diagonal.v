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
(*	Diagonal Functor (used in the definition of Cartesian) 		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export PROD.
Require Export Functor.

Set Implicit Arguments.
Unset Strict Implicit.

Section diag.

Variable C : Category.

Definition Diag_ob (c : C) := Build_POb c c.

 Section diag_map_def.

 Variable a b : C.
 
 Definition Diag_mor (f : a --> b) :=
   Build_Pmor (u:=Diag_ob a) (t:=Diag_ob b) f f. 

 Lemma Diag_map_law : Map_law Diag_mor.
 Proof.
 unfold Map_law, Diag_mor in |- *; simpl in |- *.
 intros f g H; unfold Equal_Pmor in |- *; simpl in |- *.
 split; trivial.
 Qed.

 Canonical Structure Diag_map := Build_Map Diag_map_law.

 End diag_map_def.

Lemma Diag_comp_law : Fcomp_law Diag_map.
Proof.
unfold Fcomp_law, Diag_map, Diag_mor in |- *; simpl in |- *.
unfold Equal_Pmor in |- *; simpl in |- *.
intros a b c f g; split; apply Refl.
Qed.

Lemma Diag_id_law : Fid_law Diag_map.
Proof.
unfold Fid_law, Diag_map, Diag_mor in |- *; simpl in |- *.
unfold Equal_Pmor, Id_PROD in |- *; simpl in |- *.
intro a; split; apply Refl.
Qed.

Canonical Structure Diag := Build_Functor Diag_comp_law Diag_id_law. 

End diag.

