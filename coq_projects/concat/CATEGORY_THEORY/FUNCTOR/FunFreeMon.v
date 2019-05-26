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
(*	            Functor Free Monoid : SET -> MON                         *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export FreeMonoid.
Require Export Functor.
Require Export MON.

Set Implicit Arguments.
Unset Strict Implicit.

(* SET -> MON *)

Section funfreemon_map_def.

Variable A B : Setoid.

 Section funfreemon_mor_def.

 Variable f : Map A B.

 Fixpoint Dist_fun (l : Tlist A) : Tlist B :=
   match l with
   | Empty => Empty B
   | Concat1 a l1 => Concat1 (f a) (Dist_fun l1)
   end.

 Lemma Dist_map_law : Map_law Dist_fun.
 Proof.
 unfold Map_law in |- *; intros l1; elim l1.
 intro l2; elim l2.
 intros; apply Refl.
 intros c t H H1; elim H1.
 intros c t H l2; elim l2.
 intro H1; absurd (Equal_Tlist (Concat1 c t) (Empty A)).
 apply (Diff_Concat1_Empty (A:=A)).
 trivial.
 intros c0 t0 H1 H2.
 elim H2; intros H3 H4.
 simpl in |- *; split.
 apply Pres1; trivial.
 exact (H t0 H4).
 Qed.

 Canonical Structure Dist_map := Build_Map Dist_map_law.

 Lemma Dist_map_unit_law : MonUnit_law Dist_map.
 Proof.
 unfold MonUnit_law in |- *; simpl in |- *; trivial.
 Qed.

 Lemma Dist_map_op_law : MonOp_law Dist_map.
 Proof.
 unfold MonOp_law in |- *.
 intros l1 l2; elim l1.
 unfold ApMop in |- *; apply Refl.
 intros; split.
 apply Refl.
 trivial.
 Qed.

 Canonical Structure FunFreeMon_mor :=
   Build_MonMor Dist_map_unit_law Dist_map_op_law.

 End funfreemon_mor_def.

Lemma FunFreeMon_map_law : Map_law FunFreeMon_mor.
Proof.
unfold Map_law in |- *; simpl in |- *.
intros f g; unfold Equal_MonMor in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *; intro H; intro l; elim l; simpl in |- *.
trivial.
intros c t H1; split.
apply H.
trivial.
Qed.

Canonical Structure FunFreeMon_map := Build_Map FunFreeMon_map_law.

End funfreemon_map_def.

Lemma FunFreeMon_fcomp_law : Fcomp_law FunFreeMon_map.
Proof.
unfold Fcomp_law in |- *; simpl in |- *.
intros A B C f g; unfold Equal_MonMor in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *; intro l; elim l; simpl in |- *.
trivial.
intros c t H; split.
apply Refl.
trivial.
Qed.

Lemma FunFreeMon_fid_law : Fid_law FunFreeMon_map.
Proof.
unfold Fid_law in |- *; simpl in |- *.
intro A; unfold Equal_MonMor in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *; intro l; elim l; simpl in |- *.
trivial.
intros c t H; split.
apply Refl.
trivial.
Qed.

Canonical Structure FunFreeMon :=
  Build_Functor FunFreeMon_fcomp_law FunFreeMon_fid_law.

