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
(*	                    Category ONE                  		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export ONE.
Require Export Functor.

Set Implicit Arguments.
Unset Strict Implicit.

(* !C : C -> One *)

Section Fun_One.

Variable C : Category.

Definition FunOne_ob (a : C) := Obone.

 Section funone_map_def.

 Variable a b : C.

 Definition FunOne_mor (f : a --> b) : FunOne_ob a --> FunOne_ob b :=
   Id_Obone.

 Lemma FunOne_map_law : Map_law FunOne_mor.
 Proof.
 unfold Map_law, FunOne_mor in |- *.
 intros; apply Refl.
 Qed.

 Canonical Structure FunOne_map := Build_Map FunOne_map_law.

 End funone_map_def. 

Lemma FunOne_comp_law : Fcomp_law FunOne_map.
Proof.
unfold Fcomp_law in |- *; simpl in |- *.
unfold Equal_One_mor in |- *; auto.
Qed.

Lemma FunOne_id_law : Fid_law FunOne_map.
Proof.
unfold Fid_law in |- *; simpl in |- *.
unfold Equal_One_mor in |- *; auto.
Qed.

Canonical Structure FunOne := Build_Functor FunOne_comp_law FunOne_id_law.

End Fun_One.
