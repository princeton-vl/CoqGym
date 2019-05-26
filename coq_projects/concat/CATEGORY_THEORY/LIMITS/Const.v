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
(*	            Delta Functor (used in Limits)             		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Functor.

Set Implicit Arguments.
Unset Strict Implicit.

(* Const(b) : A->B 
   Const(b)(a) = b 
   Const(b)(f) = Id(b) *)

Section constFun.

Variables (A B : Category) (b : B).

Definition Const_ob (a : A) := b.

 Section const_map_def.

 Variable a1 a2 : A.

 Definition Const_mor (f : a1 --> a2) := Id b.

 Lemma Const_mor_map_law : Map_law Const_mor.
 Proof.
 unfold Map_law, Const_mor in |- *.
 intros f g H; apply Refl.
 Qed.

 Canonical Structure Const_map :
   Map (a1 --> a2) (Const_ob a1 --> Const_ob a1) := Const_mor_map_law.

 End const_map_def.

Lemma Const_comp_law : Fcomp_law Const_map.
Proof.
unfold Fcomp_law, Const_map, Const_mor in |- *; simpl in |- *.
intros a1 a2 a3 f g; apply Idr.
Qed.

Lemma Const_id_law : Fid_law Const_map.
Proof.
unfold Fid_law, Const_map, Const_mor, Const_ob in |- *; simpl in |- *.
intros; apply Refl.
Qed.

Canonical Structure Const := Build_Functor Const_comp_law Const_id_law.

End constFun.
