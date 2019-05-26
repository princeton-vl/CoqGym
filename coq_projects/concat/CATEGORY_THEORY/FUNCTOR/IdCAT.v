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
(*	                     Identity Functor             		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export Functor.

Set Implicit Arguments.
Unset Strict Implicit.

(* Id(C) : C -> C *)

Section idCat.

Variable C : Category.

Definition Id_CAT_ob (a : C) := a.
                      
Definition Id_CAT_map (a b : C) := Id_map (a --> b).
                   
Lemma Id_CAT_comp_law : Fcomp_law (FOb:=Id_CAT_ob) Id_CAT_map.
Proof.
unfold Fcomp_law in |- *; intros; apply Refl.
Qed.

Lemma Id_CAT_id_law : Fid_law (FOb:=Id_CAT_ob) Id_CAT_map.
Proof.
unfold Fid_law, Id_CAT_ob in |- *; intros a; apply Refl.
Qed.

Canonical Structure Id_CAT := Build_Functor Id_CAT_comp_law Id_CAT_id_law.

End idCat.



