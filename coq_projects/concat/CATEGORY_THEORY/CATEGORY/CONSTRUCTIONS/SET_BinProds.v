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
(*	                       SET is CCC                		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export SetoidPROD.
Require Export Binary_Products.
Require Export SET.

Set Implicit Arguments.
Unset Strict Implicit.

Section verif_prod.

Variable A B : Setoid.

(* construction de together *)

 Section set_op_together_def.

 Variable C : Setoid.

  Section set_together_def.

  Variables (f : Map C A) (g : Map C B).

  Definition S_together_fun (c : C) := Build_Sprod (f c) (g c).

  Lemma S_together_map_law : Map_law S_together_fun.
  Proof.
  unfold Map_law in |- *.
  intros c1 c2 H; unfold S_together_fun in |- *; simpl in |- *.
  unfold Equal_Sprod in |- *; simpl in |- *; split; apply Pres1; trivial.
  Qed.

  Definition S_together := Build_Map S_together_map_law.

  End set_together_def.

 (* ve'rification des lois *)

 Lemma S_together_l : Map2_congl_law S_together.
 Proof.
 unfold Map2_congl_law in |- *; simpl in |- *; intros g g' f H;
  unfold Ext in |- *; simpl in |- *.
 intro c; unfold Equal_Sprod in |- *; simpl in |- *; split.
 apply Refl.
 apply (H c).
 Qed.

 Lemma S_together_r : Map2_congr_law S_together.
 Proof.
 unfold Map2_congr_law in |- *; simpl in |- *; intros f f' g H;
  unfold Ext in |- *; simpl in |- *.
 intro c; unfold Equal_Sprod in |- *; simpl in |- *; split.
 apply (H c).
 apply Refl.
 Qed.

 Definition S_op_together := Build_Map2 S_together_l S_together_r.
 
 End set_op_together_def. 

Lemma Eq1_Sprod : Eq1_prod_law (Proj1_SPROD A B) S_op_together.
Proof.
unfold S_op_together, Eq1_prod_law in |- *; simpl in |- *; intros C f g.
unfold Ext in |- *; simpl in |- *.
intro c; apply Refl.
Qed.

Lemma Eq2_Sprod : Eq2_prod_law (Proj2_SPROD A B) S_op_together.
Proof.
unfold S_op_together, Eq2_prod_law in |- *; simpl in |- *; intros C f g.
unfold Ext in |- *; simpl in |- *.
intro c; apply Refl.
Qed.

Lemma Unique_S_together :
 Unique_together_law (Proj1_SPROD A B) (Proj2_SPROD A B) S_op_together.
Proof.
unfold Unique_together_law, S_op_together in |- *; simpl in |- *; intros C h.
unfold Ext in |- *; simpl in |- *.
intro c; unfold Equal_Sprod in |- *; simpl in |- *; split; apply Refl.
Qed.

Definition SET_hasBinProd :=
  Build_BinProd Eq1_Sprod Eq2_Sprod Unique_S_together.

End verif_prod.